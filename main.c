/*
 * Build: cc -std=c89 -O2 -o jvi main.c
 * Usage: jvi [file]
 *
 * Normal mode
 *   move    h j k l, 0 ^ $, w b, gg G (3G = line 3), /pat, n
 *   edit    x, r<c>, dd, dw, d$, D, yy, p, P, J, u (multi-level undo)
 *   insert  i a I A o O
 *   ex      :w  :q  :q!  :wq  :x  :w <file>  :<line number>
 *   counts  work on most commands (3dd, 5j, 2w, ...)
 * Insert mode
 *   type, Enter, Backspace
 *   Ctrl-C returns to normal mode.  It is the ONLY way: escape sequences are
 *   not parsed, so ESC does nothing and arrow/Home/End/Delete keys are unsupported.
 *
 * MEMORY MODEL (this is where all the RAM goes, nothing else is allocated)
 *   text   one gap buffer: the whole file as a single byte array plus a
 *          small hole (the gap) at the edit point.  Cost = file size + at
 *          most GAP_CHUNK spare bytes.  No per-line structures at all;
 *          lines are found by scanning for '\n'.
 *   undo   a log of edits, not copies of the text.  One record is 24 bytes.
 *          Deleted text of up to 8 bytes lives inside the record itself
 *          (union), longer deleted text is malloc'd.  Typed characters in a
 *          row are merged into one record.  At most UNDO_MAX records.
 *   yank   one malloc'd string holding the last yanked/deleted lines.
 *
 * Limits: no redo, tabs render at TABSTOP, UTF-8 is supported by treating
 * continuation bytes as part of the previous character (no wide chars).
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <termios.h>

#define TABSTOP    8
#define GAP_CHUNK  256		/* spare bytes added whenever the gap must grow */
#define UNDO_MAX   4096		/* undo records kept before dropping the oldest */
#define PATH_LEN   256
#define MSG_LEN    300
#define PROMPT_LEN 200
#define CTRL_C     3

#define TEXT_LEN() (gb_cap - (gb_end - gb_start))

typedef unsigned long Pos;	/* byte offset into the text */

enum { NORMAL, INSERT };
enum { UNDO_INSERT, UNDO_DELETE };

/* One undo record: either "text was inserted here" or "text was deleted". */
typedef struct {
	Pos pos;
	Pos len;
	unsigned step;		/* records with the same step undo together */
	unsigned char kind;	/* UNDO_INSERT or UNDO_DELETE */
	union {
		char *heap;			/* deleted text, len > sizeof(char *) */
		char small[sizeof(char *)];	/* deleted text, short */
	} data;			/* unused for UNDO_INSERT */
} Undo;

/* ---------- global state ---------- */

/* text: gap buffer.  Logical text = gb[0..gb_start) + gb[gb_end..gb_cap) */
static char *gb;
static Pos gb_start, gb_end, gb_cap;

/* undo log */
static Undo *ulog;
static unsigned ucount, ucap, ustep;

/* yank register: whole lines, always ends with '\n' */
static char *yank;
static Pos yank_len;

/* cursor and view */
static Pos pos;			/* cursor offset in text */
static Pos top;			/* offset of the first line on screen */
static Pos want_col;		/* column j/k try to return to */
static int keep_col;		/* set by j/k so want_col survives the key */
static int leftcol;		/* horizontal scroll, in screen columns */
static int rows = 24, cols = 80;

/* editor */
static int mode = NORMAL;
static int dirty;		/* unsaved changes */
static int eol = 1;		/* file ends with a newline */
static int in_prompt;
static char msg[MSG_LEN];
static char fname[PATH_LEN];
static char last_search[PROMPT_LEN];

/* terminal */
static struct termios orig_term;
static int term_is_raw;

/* screen output buffer, flushed with a single write() per redraw */
static char *out;
static size_t out_len, out_cap;

/* ---------- small utilities ---------- */

static void wr(const char *s, size_t n)
{
	ssize_t k;

	while (n > 0) {
		k = write(1, s, n);
		if (k <= 0) return;
		s += k;
		n -= (size_t)k;
	}
}

static void term_restore(void)
{
	if (!term_is_raw) return;
	term_is_raw = 0;
	tcsetattr(0, TCSAFLUSH, &orig_term);
	wr("\033[2J\033[H", 7);
}

static void die(const char *what)
{
	if (term_is_raw) {
		term_is_raw = 0;
		tcsetattr(0, TCSAFLUSH, &orig_term);
	}
	perror(what);
	_exit(1);
}

static void *xrealloc(void *p, size_t n)
{
	p = realloc(p, n ? n : 1);
	if (!p) die("out of memory");
	return p;
}

static void term_raw(void)
{
	struct termios t;

	if (tcgetattr(0, &orig_term) < 0) die("tcgetattr");
	t = orig_term;
	t.c_iflag &= ~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
	t.c_oflag &= ~(OPOST);
	t.c_cflag |= CS8;
	t.c_lflag &= ~(ECHO | ICANON | IEXTEN | ISIG);
	t.c_cc[VMIN] = 1;
	t.c_cc[VTIME] = 0;
	if (tcsetattr(0, TCSAFLUSH, &t) < 0) die("tcsetattr");
	term_is_raw = 1;
	atexit(term_restore);
}

/* ---------- keyboard ---------- */

/* read one raw byte (no escape-sequence parsing at all) */
static int read_key(void)
{
        int c = getchar();

        if (c != EOF) return c;
        if (feof(stdin)) exit(0);       /* stdin closed */
        clearerr(stdin);                /* needed if using VMIN=0 timeouts */
        die("read");
        return -1;
}

/* ---------- gap buffer ---------- */

static int text_at(Pos i)
{
	return (unsigned char)(i < gb_start ? gb[i] : gb[i + (gb_end - gb_start)]);
}

static void gap_move(Pos to)
{
	Pos gap = gb_end - gb_start;

	if (to < gb_start)
		memmove(gb + to + gap, gb + to, gb_start - to);
	else if (to > gb_start)
		memmove(gb + gb_start, gb + gb_end, to - gb_start);
	gb_start = to;
	gb_end = to + gap;
}

static void gap_reserve(Pos need)
{
	Pos gap = gb_end - gb_start, grow, tail;

	if (gap >= need) return;
	grow = need - gap + GAP_CHUNK;
	tail = gb_cap - gb_end;
	gb = xrealloc(gb, gb_cap + grow);
	memmove(gb + gb_end + grow, gb + gb_end, tail);
	gb_end += grow;
	gb_cap += grow;
}

static void raw_insert(Pos at, const char *s, Pos n)
{
	gap_move(at);
	gap_reserve(n);
	memcpy(gb + gb_start, s, n);
	gb_start += n;
}

static void raw_delete(Pos at, Pos n)
{
	gap_move(at);
	gb_end += n;
}

/* copy text[at, at+n) into dst without moving the gap */
static void text_copy(Pos at, Pos n, char *dst)
{
	Pos gap = gb_end - gb_start, k;

	if (at < gb_start) {
		k = gb_start - at;
		if (k > n) k = n;
		memcpy(dst, gb + at, k);
		dst += k;
		at += k;
		n -= k;
	}
	if (n) memcpy(dst, gb + at + gap, n);
}

/* ---------- text navigation ---------- */

static int is_cont(int c)
{
	return (c & 0xC0) == 0x80;	/* UTF-8 continuation byte */
}

static Pos line_start(Pos p)
{
	while (p > 0 && text_at(p - 1) != '\n') p--;
	return p;
}

static Pos line_end(Pos p)
{
	Pos n = TEXT_LEN();

	while (p < n && text_at(p) != '\n') p++;
	return p;
}

static Pos utf8_next(Pos p)
{
	Pos n = TEXT_LEN();

	if (p >= n) return n;
	p++;
	while (p < n && is_cont(text_at(p))) p++;
	return p;
}

static Pos utf8_prev(Pos p)
{
	if (p == 0) return 0;
	p--;
	while (p > 0 && is_cont(text_at(p))) p--;
	return p;
}

static Pos first_nonblank(Pos p)
{
	Pos n = TEXT_LEN();

	while (p < n && (text_at(p) == ' ' || text_at(p) == '\t')) p++;
	return p;
}

/* offset of the start of line number n (1-based) */
static Pos goto_line(unsigned long n)
{
	Pos p = 0, len = TEXT_LEN(), e;

	while (n > 1) {
		e = line_end(p);
		if (e >= len) break;
		p = e + 1;
		n--;
	}
	return p;
}

static unsigned long line_number(Pos p)
{
	unsigned long n = 1;
	Pos i;

	for (i = 0; i < p; i++)
		if (text_at(i) == '\n') n++;
	return n;
}

static int char_class(int c)
{
	if (c == 0 || isspace(c)) return 0;
	if (isalnum(c) || c == '_' || c >= 128) return 1;
	return 2;
}

static Pos word_next(Pos p)
{
	Pos n = TEXT_LEN();
	int c;

	if (p < n) {
		c = char_class(text_at(p));
		if (c)
			while (p < n && char_class(text_at(p)) == c) p++;
	}
	while (p < n && char_class(text_at(p)) == 0) p++;
	return p;
}

static Pos word_prev(Pos p)
{
	int c;

	if (p == 0) return 0;
	p--;
	while (p > 0 && char_class(text_at(p)) == 0) p--;
	c = char_class(text_at(p));
	while (p > 0 && char_class(text_at(p - 1)) == c) p--;
	return p;
}

/* ---------- undo log ---------- */

static void undo_free(Undo *u)
{
	if (u->kind == UNDO_DELETE && u->len > sizeof(u->data.small))
		free(u->data.heap);
}

static void undo_drop_oldest_step(void)
{
	unsigned step = ulog[0].step, k = 0;

	if (step == ustep) return;	/* never drop the step being recorded */
	while (k < ucount && ulog[k].step == step)
		undo_free(&ulog[k++]);
	memmove(ulog, ulog + k, (ucount - k) * sizeof(Undo));
	ucount -= k;
}

static Undo *undo_push(void)
{
	if (ucount >= UNDO_MAX) undo_drop_oldest_step();
	if (ucount == ucap) {
		ucap = ucap ? ucap * 2 : 64;
		ulog = xrealloc(ulog, ucap * sizeof(Undo));
	}
	return &ulog[ucount++];
}

/* start a new undo step: everything until the next call undoes as one */
static void begin_change(void)
{
	ustep++;
}

static void edit_insert(Pos at, const char *s, Pos n)
{
	Undo *u;

	if (n == 0) return;
	u = ucount ? &ulog[ucount - 1] : NULL;
	if (u && u->step == ustep && u->kind == UNDO_INSERT && u->pos + u->len == at) {
		u->len += n;		/* typing in a row: extend the record */
	} else {
		u = undo_push();
		u->kind = UNDO_INSERT;
		u->pos = at;
		u->len = n;
		u->step = ustep;
	}
	raw_insert(at, s, n);
	dirty = 1;
}

static void edit_delete(Pos at, Pos n)
{
	Undo *u;
	char *dst;

	if (n == 0) return;
	u = undo_push();
	u->kind = UNDO_DELETE;
	u->pos = at;
	u->len = n;
	u->step = ustep;
	if (n <= sizeof(u->data.small)) {
		dst = u->data.small;
	} else {
		u->data.heap = xrealloc(NULL, n);
		dst = u->data.heap;
	}
	text_copy(at, n, dst);
	raw_delete(at, n);
	dirty = 1;
}

static void undo(void)
{
	unsigned step;
	Undo *u;

	if (ucount == 0) {
		strcpy(msg, "Already at oldest change");
		return;
	}
	step = ulog[ucount - 1].step;
	while (ucount > 0 && ulog[ucount - 1].step == step) {
		u = &ulog[--ucount];
		if (u->kind == UNDO_INSERT)
			raw_delete(u->pos, u->len);
		else if (u->len > sizeof(u->data.small))
			raw_insert(u->pos, u->data.heap, u->len);
		else
			raw_insert(u->pos, u->data.small, u->len);
		pos = u->pos;
		undo_free(u);
	}
	ustep++;
	dirty = 1;
}

/* ---------- yank register ---------- */

/* store text[from, to) as whole lines (a trailing '\n' is added if missing) */
static void yank_set(Pos from, Pos to)
{
	int need_nl = (to == from || text_at(to - 1) != '\n');

	free(yank);
	yank_len = to - from;
	yank = xrealloc(NULL, yank_len + 1);
	text_copy(from, yank_len, yank);
	if (need_nl) yank[yank_len++] = '\n';
}

/* range of n whole lines starting at the cursor line; *to is exclusive and
 * includes the final '\n' when there is one */
static void lines_range(int n, Pos *from, Pos *to)
{
	Pos len = TEXT_LEN();
	int i;

	*from = line_start(pos);
	*to = line_end(pos);
	for (i = 1; i < n && *to < len; i++)
		*to = line_end(*to + 1);
	if (*to < len) (*to)++;
}

/* ---------- file io ---------- */

static void load(const char *path)
{
	FILE *f = fopen(path, "r");
	long size;

	if (!f) {
		sprintf(msg, "\"%.200s\" [New File]", path);
		return;
	}
	if (fseek(f, 0, SEEK_END) != 0 || (size = ftell(f)) < 0 ||
	    fseek(f, 0, SEEK_SET) != 0) {
		sprintf(msg, "Cannot read %.200s", path);
		fclose(f);
		return;
	}
	gb = xrealloc(NULL, (Pos)size + GAP_CHUNK);
	gb_start = 0;
	gb_end = GAP_CHUNK;
	gb_cap = (Pos)size + GAP_CHUNK;
	if (fread(gb + gb_end, 1, (size_t)size, f) != (size_t)size)
		strcpy(msg, "Read error");
	fclose(f);
	if (size > 0 && gb[gb_cap - 1] == '\n') {
		gb_cap--;		/* the final newline is implied, not stored */
	} else if (size > 0) {
		eol = 0;
	}
	if (!msg[0])
		sprintf(msg, "\"%.200s\" %lu lines, %ld bytes", path,
			line_number(TEXT_LEN()), size);
}

static int save(void)
{
	FILE *f = fopen(fname, "w");
	Pos len = TEXT_LEN();

	if (!f) {
		sprintf(msg, "Cannot write %.200s", fname);
		return 0;
	}
	fwrite(gb, 1, gb_start, f);
	fwrite(gb + gb_end, 1, gb_cap - gb_end, f);
	if (eol && len > 0) fputc('\n', f);
	if (fclose(f) != 0) {
		strcpy(msg, "Write error");
		return 0;
	}
	dirty = 0;
	sprintf(msg, "\"%.200s\" %lu lines written", fname, line_number(len));
	return 1;
}

/* ---------- screen ---------- */

static void out_ch(int c)
{
	if (out_len + 1 > out_cap) {
		out_cap = out_cap ? out_cap * 2 : 4096;
		out = xrealloc(out, out_cap);
	}
	out[out_len++] = (char)c;
}

static void out_str(const char *s)
{
	while (*s) out_ch(*s++);
}

/* screen column of offset p on the line starting at ls */
static int screen_col(Pos ls, Pos p)
{
	int col = 0;
	Pos i;

	for (i = ls; i < p; i++) {
		if (text_at(i) == '\t') col += TABSTOP - col % TABSTOP;
		else if (!is_cont(text_at(i))) col++;
	}
	return col;
}

/* emit the visible part of the line starting at p; returns the line's end */
static Pos draw_row(Pos p)
{
	Pos n = TEXT_LEN(), q, r;
	int col = 0, c, w, i;

	while (p < n && (c = text_at(p)) != '\n') {
		q = p + 1;
		while (q < n && is_cont(text_at(q))) q++;
		w = (c == '\t') ? TABSTOP - col % TABSTOP : 1;
		if (c == '\t') {
			for (i = 0; i < w; i++)
				if (col + i >= leftcol && col + i < leftcol + cols)
					out_ch(' ');
		} else if (col >= leftcol && col < leftcol + cols) {
			if (c < 32 || c == 127) out_ch('?');
			else for (r = p; r < q; r++) out_ch(text_at(r));
		}
		col += w;
		p = q;
	}
	return p;
}

/* keep the cursor line inside the th text rows */
static void scroll_vertical(int th)
{
	Pos len = TEXT_LEN(), s, p;
	int lines = 0, i;

	if (top > len) top = len;
	top = line_start(top);
	s = line_start(pos);
	if (s < top) {
		top = s;
		return;
	}
	for (p = top; p < s && lines < th; p++)
		if (text_at(p) == '\n') lines++;
	if (lines >= th) {
		top = s;
		for (i = 1; i < th && top > 0; i++)
			top = line_start(top - 1);
	}
}

static void clamp_cursor(void)
{
	Pos len = TEXT_LEN(), s, e;

	if (pos > len) pos = len;
	if (mode == INSERT) return;
	s = line_start(pos);
	e = line_end(pos);
	if (pos >= e && e > s) pos = utf8_prev(e);	/* normal mode: stay on a char */
}

static int query_size(int *r, int *c)
{
        static const char q[] = "\033[999;999H\033[6n";
        char b[32];
        int i = 0;

        if (write(1, q, sizeof q - 1) < 0) return -1;
        while (i < (int)sizeof b - 1) {
                if (read(0, &b[i], 1) != 1) return -1;
                if (b[i++] == 'R') break;
        }
        b[i] = 0;
        return sscanf(b, "\033[%d;%dR", r, c) == 2 ? 0 : -1;
}

static void draw(void)
{
	struct winsize ws;
	char b[PATH_LEN + 128];
	Pos p, s, n;
	int y, th, col, cur_row = 0, past_end = 0, w;


	int r, c;
	if (query_size(&r, &c) == 0 && r > 2 && c > 0) { rows = r; cols = c; }

	clamp_cursor();
	th = rows - 2;
	scroll_vertical(th);
	s = line_start(pos);
	col = screen_col(s, pos);
	if (col < leftcol) leftcol = col;
	if (col >= leftcol + cols) leftcol = col - cols + 1;

	out_len = 0;
	out_str("\033[?25l\033[H");
	n = TEXT_LEN();
	p = top;
	for (y = 0; y < th; y++) {
		if (past_end) {
			out_ch('~');
		} else {
			if (p == s) cur_row = y;
			p = draw_row(p);
			if (p >= n) past_end = 1;
			else p++;
		}
		out_str("\033[K\r\n");
	}

	sprintf(b, " %s  %.200s%s  %lu,%d  %lu bytes",
		mode == INSERT ? "-- INSERT --" : "NORMAL",
		fname[0] ? fname : "[No Name]", dirty ? " [+]" : "",
		line_number(pos), col + 1, (unsigned long)n);
	w = (int)strlen(b);
	if (w > cols) w = cols;
	out_str("\033[7m");
	for (y = 0; y < w; y++) out_ch(b[y]);
	for (; y < cols; y++) out_ch(' ');
	out_str("\033[m\r\n");

	w = (int)strlen(msg);
	if (w > cols - 1) w = cols - 1;
	for (y = 0; y < w; y++) out_ch(msg[y]);
	out_str("\033[K");

	if (in_prompt) sprintf(b, "\033[%d;%dH", rows, w + 1);
	else sprintf(b, "\033[%d;%dH", cur_row + 1, col - leftcol + 1);
	out_str(b);
	out_str("\033[?25h");
	wr(out, out_len);
}

/* read a line on the bottom row; returns 0 if cancelled */
static int prompt(const char *label, char *buf, int max)
{
	int n = 0, c;

	buf[0] = 0;
	in_prompt = 1;
	for (;;) {
		sprintf(msg, "%s%s", label, buf);
		draw();
		c = read_key();
		if (c == '\r' || c == '\n') break;
		if (c == CTRL_C || ((c == 127 || c == 8) && n == 0)) {
			n = -1;
			break;
		}
		if (c == 127 || c == 8) buf[--n] = 0;
		else if (c >= 32 && c < 256 && n < max - 1) {
			buf[n++] = (char)c;
			buf[n] = 0;
		}
	}
	in_prompt = 0;
	msg[0] = 0;
	return n >= 0;
}

/* ---------- cursor motions ---------- */

static void move_left(void)
{
	if (pos > line_start(pos)) pos = utf8_prev(pos);
}

static void move_right(void)
{
	Pos e = line_end(pos), nx;

	if (pos >= e) return;
	nx = utf8_next(pos);
	if (mode == INSERT || nx < e) pos = nx;
}

static void move_vertical(int dir)
{
	Pos s = line_start(pos), t, e, width;

	if (dir < 0) {
		if (s == 0) return;
		t = line_start(s - 1);
	} else {
		e = line_end(pos);
		if (e >= TEXT_LEN()) return;
		t = e + 1;
	}
	width = line_end(t) - t;
	pos = t + (want_col < width ? want_col : width);
	while (pos > t && pos < TEXT_LEN() && is_cont(text_at(pos))) pos--;
	keep_col = 1;
}

static void move_up(void)   { move_vertical(-1); }
static void move_down(void) { move_vertical(1); }
static void word_forward(void)  { pos = word_next(pos); }
static void word_backward(void) { pos = word_prev(pos); }

static void repeat(void (*fn)(void), int n)
{
	while (n-- > 0) fn();
}

static void search(const char *pat)
{
	Pos len = TEXT_LEN(), m = strlen(pat), i, p, k;

	if (m == 0) {
		strcpy(msg, "No previous pattern");
		return;
	}
	for (i = 0; i < len && m <= len; i++) {
		p = (pos + 1 + i) % len;
		if (p + m > len) continue;
		for (k = 0; k < m && text_at(p + k) == (unsigned char)pat[k]; k++)
			;
		if (k == m) {
			pos = p;
			return;
		}
	}
	sprintf(msg, "Pattern not found: %.200s", pat);
}

/* ---------- editing commands ---------- */

static void delete_chars(int n)
{
	Pos le = line_end(pos), e = pos;

	while (n-- > 0 && e < le) e = utf8_next(e);
	edit_delete(pos, e - pos);
}

static void replace_char(int c)
{
	char ch = (char)c;
	Pos e = utf8_next(pos);

	if (pos >= line_end(pos)) return;
	edit_delete(pos, e - pos);
	edit_insert(pos, &ch, 1);
}

static void delete_words(int n)
{
	Pos e;

	while (n-- > 0) {
		e = word_next(pos);
		if (e > line_end(pos)) e = line_end(pos);
		edit_delete(pos, e - pos);
	}
}

static void delete_to_eol(void)
{
	edit_delete(pos, line_end(pos) - pos);
}

static void delete_lines(int n)
{
	Pos from, to, len = TEXT_LEN();

	lines_range(n, &from, &to);
	yank_set(from, to);
	/* last line has no '\n' after it: take the one before it instead */
	if (to == len && (to == from || text_at(to - 1) != '\n') && from > 0)
		from--;
	edit_delete(from, to - from);
	pos = line_start(from);
}

static void yank_lines(int n)
{
	Pos from, to;

	lines_range(n, &from, &to);
	yank_set(from, to);
	sprintf(msg, "%lu bytes yanked", yank_len);
}

static void paste_lines(int below)
{
	Pos e, s;

	if (!yank) {
		strcpy(msg, "Nothing to paste");
		return;
	}
	if (below) {
		e = line_end(pos);
		if (e < TEXT_LEN()) {
			edit_insert(e + 1, yank, yank_len);
		} else {	/* cursor is on the last line, which has no '\n' */
			edit_insert(e, "\n", 1);
			edit_insert(e + 1, yank, yank_len - 1);
		}
		pos = e + 1;
	} else {
		s = line_start(pos);
		edit_insert(s, yank, yank_len);
		pos = s;
	}
}

static void join_line(void)
{
	Pos len = TEXT_LEN(), e = line_end(pos), k;

	if (e >= len) return;
	k = e + 1;
	while (k < len && (text_at(k) == ' ' || text_at(k) == '\t')) k++;
	edit_delete(e, k - e);
	if (e > line_start(e) && e < TEXT_LEN() && text_at(e) != '\n')
		edit_insert(e, " ", 1);
	pos = e;
}

static void open_line_below(void)
{
	Pos e = line_end(pos);

	edit_insert(e, "\n", 1);
	pos = e + 1;
	mode = INSERT;
}

static void open_line_above(void)
{
	Pos s = line_start(pos);

	edit_insert(s, "\n", 1);
	pos = s;
	mode = INSERT;
}

static void leave_insert(void)
{
	mode = NORMAL;
	if (pos > line_start(pos)) pos = utf8_prev(pos);
}

/* ---------- ex commands (:w :q ...) ---------- */

static void run_ex(char *cmd)
{
	char *arg;
	int len, force = 0, saved;

	while (*cmd == ' ') cmd++;
	if (!*cmd) return;
	if (isdigit((unsigned char)*cmd)) {
		pos = goto_line((unsigned long)atol(cmd));
		return;
	}
	arg = cmd;
	while (*arg && *arg != ' ') arg++;
	if (*arg) {
		*arg++ = 0;
		while (*arg == ' ') arg++;
	}
	len = (int)strlen(cmd);
	if (len && cmd[len - 1] == '!') {
		force = 1;
		cmd[len - 1] = 0;
	}

	if (!strcmp(cmd, "w") || !strcmp(cmd, "wq") || !strcmp(cmd, "x")) {
		if (*arg) {
			strncpy(fname, arg, PATH_LEN - 1);
			fname[PATH_LEN - 1] = 0;
		}
		if (!fname[0]) {
			strcpy(msg, "No file name");
			return;
		}
		saved = save();
		if (saved && strcmp(cmd, "w")) exit(0);
	} else if (!strcmp(cmd, "q")) {
		if (dirty && !force) strcpy(msg, "No write since last change (use :q!)");
		else exit(0);
	} else {
		sprintf(msg, "Not an editor command: %.200s", cmd);
	}
}

/* ---------- key handlers ---------- */

static void insert_key(int c)
{
	char ch;
	Pos p;

	switch (c) {
	case CTRL_C:
		leave_insert();
		return;
	case '\r': case '\n':
		ch = '\n';
		edit_insert(pos, &ch, 1);
		pos++;
		return;
	case 127: case 8:			/* backspace, also joins lines */
		p = utf8_prev(pos);
		edit_delete(p, pos - p);
		pos = p;
		return;
	}
	if (c == '\t' || (c >= 32 && c < 127) || (c >= 128 && c < 256)) {
		ch = (char)c;
		edit_insert(pos, &ch, 1);
		pos++;
	}
}

static void normal_key(int c)
{
	static int count;
	int n, had, c2;

	if ((c >= '1' && c <= '9') || (c == '0' && count > 0)) {
		count = count * 10 + (c - '0');
		return;
	}
	had = count;
	n = count ? count : 1;
	count = 0;

	switch (c) {
	/* motions */
	case 'h':  repeat(move_left, n); break;
	case 'l': repeat(move_right, n); break;
	case 'j':  repeat(move_down, n); break;
	case 'k':  repeat(move_up, n); break;
	case 'w': repeat(word_forward, n); break;
	case 'b': repeat(word_backward, n); break;
	case '0': pos = line_start(pos); break;
	case '^': pos = first_nonblank(line_start(pos)); break;
	case '$': pos = line_end(pos); break;
	case 'G':
		pos = had ? goto_line((unsigned long)had) : line_start(TEXT_LEN());
		break;
	case 'g':
		if (read_key() == 'g') pos = goto_line(had ? (unsigned long)had : 1);
		break;
	case '/':
		if (prompt("/", last_search, PROMPT_LEN)) search(last_search);
		break;
	case 'n': search(last_search); break;

	/* changes */
	case 'x': begin_change(); delete_chars(n); break;
	case 'r':
		c2 = read_key();
		if (c2 >= 32 && c2 < 127) {
			begin_change();
			replace_char(c2);
		}
		break;
	case 'd':
		c2 = read_key();
		if (c2 == 'd') { begin_change(); delete_lines(n); }
		else if (c2 == 'w') { begin_change(); delete_words(n); }
		else if (c2 == '$') { begin_change(); delete_to_eol(); }
		break;
	case 'D': begin_change(); delete_to_eol(); break;
	case 'y':
		if (read_key() == 'y') yank_lines(n);
		break;
	case 'p': begin_change(); paste_lines(1); break;
	case 'P': begin_change(); paste_lines(0); break;
	case 'J': begin_change(); repeat(join_line, n); break;
	case 'u': undo(); break;

	/* enter insert mode */
	case 'i': begin_change(); mode = INSERT; break;
	case 'a':
		begin_change();
		if (pos < line_end(pos)) pos = utf8_next(pos);
		mode = INSERT;
		break;
	case 'I':
		begin_change();
		pos = first_nonblank(line_start(pos));
		mode = INSERT;
		break;
	case 'A':
		begin_change();
		pos = line_end(pos);
		mode = INSERT;
		break;
	case 'o': begin_change(); open_line_below(); break;
	case 'O': begin_change(); open_line_above(); break;

	case ':': {
		char buf[PROMPT_LEN];
		if (prompt(":", buf, PROMPT_LEN)) run_ex(buf);
		break;
	}
	default:
		break;
	}
}

int main(int argc, char **argv)
{
	int c;

	if (argc > 1) {
		strncpy(fname, argv[1], PATH_LEN - 1);
		load(fname);
	}
	term_raw();
	for (;;) {
		draw();
		c = read_key();
		msg[0] = 0;
		keep_col = 0;
		if (mode == INSERT) insert_key(c);
		else normal_key(c);
		clamp_cursor();
		if (!keep_col) want_col = pos - line_start(pos);
	}
	return 0;
}
