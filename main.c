/*
 * Build: cc -std=c89 -O2 -o jvi main.c
 * Usage: jvi [file]
 *
 * Normal mode
 *   move    h j k l, 0 ^ $, w b, gg G (3G = line 3), /pat, n
 *   edit    x, r<c>, dd, dw, d$, D, yy, p, P, J, u (multi-level undo)
 *   insert  i a I A o O
 *   select  v (characters), V (lines)
 *   ex      :w  :q  :q!  :wq  :x  :w <file>  :<line number>
 *   counts  work on most commands (3dd, 5j, 2w, ...)
 * Select mode (v / V)
 *   move    every normal-mode motion extends the selection
 *   act     d or x delete, y yank, c change, o swap ends
 *   leave   v or V again (switches between the two kinds), or Ctrl-C
 * Insert mode
 *   type, Enter, Backspace
 *   Ctrl-C returns to normal mode.  It is the ONLY way: escape sequences are
 *   not parsed, so ESC does nothing and arrow/Home/End/Delete keys are unsupported.
 *
 * DEPENDENCIES
 *   headers   stdlib.h  (realloc, free)
 *             unistd.h  (read, write, close, _exit)
 *             fcntl.h   (open)
 *             termios.h (raw mode)
 *   Everything else (string functions, number formatting, ctype, file
 *   buffering) is implemented below, so there is no stdio at all.
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
 *   yank   one malloc'd string holding the last yanked/deleted text.
 *
 * Limits: no redo, tabs render at TABSTOP, UTF-8 is supported by treating
 * continuation bytes as part of the previous character (no wide chars).
 */

#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <termios.h>

#define TABSTOP    8
#define GAP_CHUNK  256		/* spare bytes added whenever the gap must grow */
#define UNDO_MAX   4096		/* undo records kept before dropping the oldest */
#define COUNT_MAX  999999
#define PATH_LEN   256
#define MSG_LEN    300
#define PROMPT_LEN 200
#define CTRL_C     3

#define TEXT_LEN() (gb_cap - (gb_end - gb_start))

typedef unsigned long Pos;	/* byte offset into the text */

/* growable-less string builder over a fixed buffer */
typedef struct {
	char *s;
	int len, max;
} Str;

enum { NORMAL, INSERT, VISUAL };
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

/* An ex command: ":name [arg]".  force is set when written as ":name!". */
typedef void (*ExFn)(const char *arg, int force);

typedef struct {
	const char *name;
	ExFn fn;
} ExCmd;

/* ---------- global state ---------- */

/* text: gap buffer.  Logical text = gb[0..gb_start) + gb[gb_end..gb_cap) */
static char *gb;
static Pos gb_start, gb_end, gb_cap;

/* undo log */
static Undo *ulog;
static unsigned ucount, ucap, ustep;

/* yank register */
static char *yank;
static Pos yank_len;
static int yank_linewise;	/* whole lines (ends with '\n') or plain text */

/* cursor and view */
static Pos pos;			/* cursor offset in text */
static Pos top;			/* offset of the first line on screen */
static Pos want_col;		/* column j/k try to return to */
static int keep_col;		/* set by j/k so want_col survives the key */
static int leftcol;		/* horizontal scroll, in screen columns */
static int rows = 24, cols = 80;

/* selection (select mode) */
static Pos sel_anchor;		/* where v/V was pressed; the cursor is the other end */
static int sel_line;		/* V: select whole lines */
static Pos sel_from, sel_to;	/* range drawn highlighted, refreshed every redraw */

/* editor */
static int mode = NORMAL;
static int dirty;		/* unsaved changes */
static int eol = 1;		/* file ends with a newline */
static int in_prompt;
static unsigned count;		/* pending numeric prefix, 0 = none */
static char msg_buf[MSG_LEN];
static Str msg = { msg_buf, 0, MSG_LEN };
static char fname[PATH_LEN];
static char last_search[PROMPT_LEN];

/* terminal */
static struct termios orig_term;
static int term_is_raw;

/* screen output buffer, flushed with a single write() per redraw */
static char *out;
static size_t out_len, out_cap;

/* ---------- tiny replacements for libc ---------- */

static int is_digit(int c) { return c >= '0' && c <= '9'; }
static int is_alnum(int c) { return is_digit(c) || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'); }
static int is_space(int c) { return c == ' ' || (c >= '\t' && c <= '\r'); }

static void mem_copy(char *dst, const char *src, Pos n)
{
	while (n--) *dst++ = *src++;
}

/* like memmove: the ranges may overlap */
static void mem_move(char *dst, const char *src, Pos n)
{
	if (dst < src) {
		mem_copy(dst, src, n);
	} else {
		dst += n;
		src += n;
		while (n--) *--dst = *--src;
	}
}

static int str_len(const char *s)
{
	int n = 0;

	while (s[n]) n++;
	return n;
}

static int str_eq(const char *a, const char *b)
{
	while (*a && *a == *b) a++, b++;
	return *a == *b;
}

/* copy at most max-1 bytes and always terminate */
static void str_copy(char *dst, const char *src, int max)
{
	int i;

	for (i = 0; i < max - 1 && src[i]; i++) dst[i] = src[i];
	dst[i] = 0;
}

static unsigned long parse_num(const char **s)
{
	unsigned long n = 0;

	while (is_digit(**s)) n = n * 10 + (unsigned long)(*(*s)++ - '0');
	return n;
}

static void str_init(Str *b, char *s, int max)
{
	b->s = s;
	b->len = 0;
	b->max = max;
	s[0] = 0;
}

static void str_chr(Str *b, int c)
{
	if (b->len < b->max - 1) {
		b->s[b->len++] = (char)c;
		b->s[b->len] = 0;
	}
}

static void str_add(Str *b, const char *t)
{
	while (*t) str_chr(b, *t++);
}

static void str_num(Str *b, unsigned long n)
{
	char t[24];
	int i = 0;

	do t[i++] = (char)('0' + n % 10); while (n /= 10);
	while (i > 0) str_chr(b, t[--i]);
}

/* the status-line message */
static void say(const char *s)
{
	str_init(&msg, msg_buf, MSG_LEN);
	str_add(&msg, s);
}

/* ---------- terminal ---------- */

static int write_all(int fd, const char *s, size_t n)
{
	ssize_t k;

	while (n > 0) {
		k = write(fd, s, n);
		if (k <= 0) return 0;
		s += k;
		n -= (size_t)k;
	}
	return 1;
}

static void wr(const char *s, size_t n)
{
	write_all(1, s, n);
}

static void term_restore(void)
{
	if (!term_is_raw) return;
	term_is_raw = 0;
	tcsetattr(0, TCSAFLUSH, &orig_term);
	wr("\033[2J\033[H", 7);
}

/* the one way out of the program */
static void quit(int status)
{
	term_restore();
	_exit(status);
}

static void die(const char *what)
{
	if (term_is_raw) {
		term_is_raw = 0;
		tcsetattr(0, TCSAFLUSH, &orig_term);
	}
	wr("jvi: ", 5);
	wr(what, (size_t)str_len(what));
	wr("\n", 1);
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

	if (tcgetattr(0, &orig_term) < 0) die("tcgetattr failed");
	t = orig_term;
	t.c_iflag &= ~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
	t.c_oflag &= ~(OPOST);
	t.c_cflag |= CS8;
	t.c_lflag &= ~(ECHO | ICANON | IEXTEN | ISIG);
	t.c_cc[VMIN] = 1;
	t.c_cc[VTIME] = 0;
	if (tcsetattr(0, TCSAFLUSH, &t) < 0) die("tcsetattr failed");
	term_is_raw = 1;
}

/* read one raw byte */
static int read_key(void)
{
	unsigned char c;
	ssize_t k = read(0, &c, 1);

	if (k == 1) return c;
	if (k == 0) quit(0);		/* stdin closed */
	die("read failed");
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
		mem_move(gb + to + gap, gb + to, gb_start - to);
	else if (to > gb_start)
		mem_move(gb + gb_start, gb + gb_end, to - gb_start);
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
	mem_move(gb + gb_end + grow, gb + gb_end, tail);
	gb_end += grow;
	gb_cap += grow;
}

static void raw_insert(Pos at, const char *s, Pos n)
{
	gap_move(at);
	gap_reserve(n);
	mem_copy(gb + gb_start, s, n);
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
		mem_copy(dst, gb + at, k);
		dst += k;
		at += k;
		n -= k;
	}
	if (n) mem_copy(dst, gb + at + gap, n);
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
	if (c == 0 || is_space(c)) return 0;
	if (is_alnum(c) || c == '_' || c >= 128) return 1;
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
	mem_move((char *)ulog, (const char *)(ulog + k), (ucount - k) * sizeof(Undo));
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
		say("Already at oldest change");
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

/* store text[from, to).  Whole lines get a trailing '\n' if they lack one. */
static void yank_store(Pos from, Pos to, int linewise)
{
	int need_nl = linewise && (to == from || text_at(to - 1) != '\n');

	free(yank);
	yank_len = to - from;
	yank = xrealloc(NULL, yank_len + 1);
	text_copy(from, yank_len, yank);
	if (need_nl) yank[yank_len++] = '\n';
	yank_linewise = linewise;
}

static void say_yanked(void)
{
	str_init(&msg, msg_buf, MSG_LEN);
	str_num(&msg, yank_len);
	str_add(&msg, " bytes yanked");
}

/* range of n whole lines starting at the cursor line; *to is exclusive and
 * includes the final '\n' when there is one */
static void lines_range(unsigned n, Pos *from, Pos *to)
{
	Pos len = TEXT_LEN();
	unsigned i;

	*from = line_start(pos);
	*to = line_end(pos);
	for (i = 1; i < n && *to < len; i++)
		*to = line_end(*to + 1);
	if (*to < len) (*to)++;
}

/* ---------- file io ---------- */

static void load_file(const char *path)
{
	int fd = open(path, O_RDONLY);
	Pos size = 0, room = 4096;
	ssize_t k;

	if (fd < 0) {
		say("\"");
		str_add(&msg, path);
		str_add(&msg, "\" [New File]");
		return;
	}
	gb = xrealloc(NULL, GAP_CHUNK + room);
	while ((k = read(fd, gb + GAP_CHUNK + size, room - size)) > 0) {
		size += (Pos)k;
		if (size == room) {
			room *= 2;
			gb = xrealloc(gb, GAP_CHUNK + room);
		}
	}
	close(fd);
	gb_start = 0;
	gb_end = GAP_CHUNK;
	gb_cap = GAP_CHUNK + size;
	if (size > 0 && gb[gb_cap - 1] == '\n')
		gb_cap--;		/* the final newline is implied, not stored */
	else if (size > 0)
		eol = 0;

	if (k < 0) {
		say("Read error");
		return;
	}
	say("\"");
	str_add(&msg, path);
	str_add(&msg, "\" ");
	str_num(&msg, line_number(TEXT_LEN()));
	str_add(&msg, " lines, ");
	str_num(&msg, size);
	str_add(&msg, " bytes");
}

static int save_file(void)
{
	int fd = open(fname, O_WRONLY | O_CREAT | O_TRUNC, 0666);
	Pos len = TEXT_LEN();
	int ok;

	if (fd < 0) {
		say("Cannot write ");
		str_add(&msg, fname);
		return 0;
	}
	ok = write_all(fd, gb, gb_start) &&
	     write_all(fd, gb + gb_end, gb_cap - gb_end) &&
	     (!(eol && len > 0) || write_all(fd, "\n", 1));
	if (close(fd) != 0) ok = 0;
	if (!ok) {
		say("Write error");
		return 0;
	}
	dirty = 0;
	say("\"");
	str_add(&msg, fname);
	str_add(&msg, "\" ");
	str_num(&msg, line_number(len));
	str_add(&msg, " lines written");
	return 1;
}

/* ---------- selection ---------- */

/* the selected range [*from, *to).  Character selections include the
 * character under the cursor; line selections include the final '\n'. */
static void sel_range(Pos *from, Pos *to)
{
	Pos lo = sel_anchor < pos ? sel_anchor : pos;
	Pos hi = sel_anchor < pos ? pos : sel_anchor;

	if (sel_line) {
		*from = line_start(lo);
		*to = line_end(hi);
		if (*to < TEXT_LEN()) (*to)++;
	} else {
		*from = lo;
		*to = utf8_next(hi);
	}
}

static int in_selection(Pos p)
{
	return mode == VISUAL && p >= sel_from && p < sel_to;
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

static void out_goto(int row, int col)
{
	Str s;
	char b[32];

	str_init(&s, b, sizeof b);
	str_add(&s, "\033[");
	str_num(&s, (unsigned long)row);
	str_add(&s, ";");
	str_num(&s, (unsigned long)col);
	str_add(&s, "H");
	out_str(b);
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
	int col = 0, c, w, i, hl = 0, want;

	while (p < n && (c = text_at(p)) != '\n') {
		q = p + 1;
		while (q < n && is_cont(text_at(q))) q++;
		want = in_selection(p);
		if (want != hl) {
			out_str(want ? "\033[7m" : "\033[m");
			hl = want;
		}
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
	if (p < n && in_selection(p)) {		/* show the selected newline */
		if (!hl) {
			out_str("\033[7m");
			hl = 1;
		}
		if (col >= leftcol && col < leftcol + cols) out_ch(' ');
	}
	if (hl) out_str("\033[m");
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

/* ask the terminal how big it is: park the cursor far away, ask where it is */
static int query_size(int *r, int *c)
{
	static const char q[] = "\033[999;999H\033[6n";
	const char *p;
	char b[32];
	int i = 0;

	if (!write_all(1, q, sizeof q - 1)) return -1;
	while (i < (int)sizeof b - 1) {
		if (read(0, &b[i], 1) != 1) return -1;
		if (b[i++] == 'R') break;
	}
	b[i] = 0;

	p = b;
	if (*p++ != '\033' || *p++ != '[') return -1;
	*r = (int)parse_num(&p);
	if (*p++ != ';') return -1;
	*c = (int)parse_num(&p);
	return *p == 'R' ? 0 : -1;
}

static const char *mode_label(void)
{
	if (mode == INSERT) return "-- INSERT --";
	if (mode == VISUAL) return sel_line ? "-- V-LINE --" : "-- VISUAL --";
	return "NORMAL";
}

static void draw(void)
{
	char b[PATH_LEN + 128];
	Str st;
	Pos p, s, n;
	int y, th, col, w, r, c, cur_row = 0, past_end = 0;

	if (query_size(&r, &c) == 0 && r > 2 && c > 0) {
		rows = r;
		cols = c;
	}

	clamp_cursor();
	th = rows - 2;
	scroll_vertical(th);
	s = line_start(pos);
	col = screen_col(s, pos);
	if (col < leftcol) leftcol = col;
	if (col >= leftcol + cols) leftcol = col - cols + 1;
	if (mode == VISUAL) sel_range(&sel_from, &sel_to);

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

	/* status line */
	str_init(&st, b, sizeof b);
	str_add(&st, " ");
	str_add(&st, mode_label());
	str_add(&st, "  ");
	str_add(&st, fname[0] ? fname : "[No Name]");
	if (dirty) str_add(&st, " [+]");
	str_add(&st, "  ");
	str_num(&st, line_number(pos));
	str_add(&st, ",");
	str_num(&st, (unsigned long)(col + 1));
	str_add(&st, "  ");
	str_num(&st, n);
	str_add(&st, " bytes");
	w = st.len < cols ? st.len : cols;
	out_str("\033[7m");
	for (y = 0; y < w; y++) out_ch(b[y]);
	for (; y < cols; y++) out_ch(' ');
	out_str("\033[m\r\n");

	/* message line */
	w = msg.len < cols - 1 ? msg.len : cols - 1;
	for (y = 0; y < w; y++) out_ch(msg.s[y]);
	out_str("\033[K");

	if (in_prompt) out_goto(rows, w + 1);
	else out_goto(cur_row + 1, col - leftcol + 1);
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
		say(label);
		str_add(&msg, buf);
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
	say("");
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

static void move_up(void)       { move_vertical(-1); }
static void move_down(void)     { move_vertical(1); }
static void word_forward(void)  { pos = word_next(pos); }
static void word_backward(void) { pos = word_prev(pos); }

static void repeat(void (*fn)(void), unsigned n)
{
	while (n-- > 0) fn();
}

static void search(const char *pat)
{
	Pos len = TEXT_LEN(), m = (Pos)str_len(pat), i, p, k;

	if (m == 0) {
		say("No previous pattern");
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
	say("Pattern not found: ");
	str_add(&msg, pat);
}

/* ---------- editing commands ---------- */

static void delete_chars(unsigned n)
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

static void delete_words(unsigned n)
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

/* delete whole lines [from, to), remembering them in the yank register */
static void delete_line_range(Pos from, Pos to)
{
	Pos len = TEXT_LEN();

	yank_store(from, to, 1);
	/* last line has no '\n' after it: take the one before it instead */
	if (to == len && (to == from || text_at(to - 1) != '\n') && from > 0)
		from--;
	edit_delete(from, to - from);
	pos = line_start(from);
}

static void delete_lines(unsigned n)
{
	Pos from, to;

	lines_range(n, &from, &to);
	delete_line_range(from, to);
}

/* the operator after 'd': dd, dw or d$ */
static void delete_op(unsigned n)
{
	int c = read_key();

	if (c == 'd')      { begin_change(); delete_lines(n); }
	else if (c == 'w') { begin_change(); delete_words(n); }
	else if (c == '$') { begin_change(); delete_to_eol(); }
}

static void yank_lines(unsigned n)
{
	Pos from, to;

	lines_range(n, &from, &to);
	yank_store(from, to, 1);
	say_yanked();
}

static void paste_lines(int below)
{
	Pos e, s;

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

static void paste_text(int after)
{
	Pos at = pos;

	if (after && pos < line_end(pos)) at = utf8_next(pos);
	edit_insert(at, yank, yank_len);
	pos = utf8_prev(at + yank_len);		/* cursor ends on the last pasted char */
}

static void paste(int after)
{
	if (!yank) {
		say("Nothing to paste");
		return;
	}
	if (yank_linewise) paste_lines(after);
	else paste_text(after);
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

/* ---------- mode switches ---------- */

static void insert_at(Pos at)
{
	begin_change();
	pos = at;
	mode = INSERT;
}

static void leave_insert(void)
{
	mode = NORMAL;
	if (pos > line_start(pos)) pos = utf8_prev(pos);
}

static void open_line_below(void)
{
	Pos e = line_end(pos);

	begin_change();
	edit_insert(e, "\n", 1);
	insert_at(e + 1);
}

static void open_line_above(void)
{
	Pos s = line_start(pos);

	begin_change();
	edit_insert(s, "\n", 1);
	insert_at(s);
}

static void enter_select(int linewise)
{
	sel_anchor = pos;
	sel_line = linewise;
	mode = VISUAL;
}

/* ---------- selection commands ---------- */

static void select_yank(void)
{
	Pos from, to;

	sel_range(&from, &to);
	yank_store(from, to, sel_line);
	pos = from;
	mode = NORMAL;
	say_yanked();
}

static void select_delete(void)
{
	Pos from, to;

	begin_change();
	sel_range(&from, &to);
	if (sel_line) {
		delete_line_range(from, to);
	} else {
		yank_store(from, to, 0);
		edit_delete(from, to - from);
		pos = from;
	}
	mode = NORMAL;
}

/* delete the selection and start typing; selected lines leave one empty line */
static void select_change(void)
{
	Pos from, to;

	begin_change();
	sel_range(&from, &to);
	yank_store(from, to, sel_line);
	if (sel_line && to > from && text_at(to - 1) == '\n') to--;
	edit_delete(from, to - from);
	insert_at(from);
}

static void select_swap_ends(void)
{
	Pos t = pos;

	pos = sel_anchor;
	sel_anchor = t;
}

/* ---------- ex commands (:w :q ...) ---------- */

/* :w [file] -- returns 1 if the file was written */
static int write_cmd(const char *arg)
{
	if (*arg) str_copy(fname, arg, PATH_LEN);
	if (!fname[0]) {
		say("No file name");
		return 0;
	}
	return save_file();
}

static void ex_write(const char *arg, int force)
{
	(void)force;
	write_cmd(arg);
}

static void ex_write_quit(const char *arg, int force)
{
	(void)force;
	if (write_cmd(arg)) quit(0);
}

static void ex_quit(const char *arg, int force)
{
	(void)arg;
	if (dirty && !force) say("No write since last change (use :q!)");
	else quit(0);
}

static const ExCmd ex_cmds[] = {
	{ "w",  ex_write },
	{ "wq", ex_write_quit },
	{ "x",  ex_write_quit },
	{ "q",  ex_quit },
	{ NULL, NULL }
};

static void run_ex(char *cmd)
{
	const ExCmd *e;
	const char *num;
	char *arg;
	int len, force = 0;

	while (*cmd == ' ') cmd++;
	if (!*cmd) return;
	if (is_digit(*cmd)) {
		num = cmd;
		pos = goto_line(parse_num(&num));
		return;
	}
	arg = cmd;
	while (*arg && *arg != ' ') arg++;
	if (*arg) {
		*arg++ = 0;
		while (*arg == ' ') arg++;
	}
	len = str_len(cmd);
	if (len && cmd[len - 1] == '!') {
		force = 1;
		cmd[len - 1] = 0;
	}

	for (e = ex_cmds; e->name; e++) {
		if (str_eq(cmd, e->name)) {
			e->fn(arg, force);
			return;
		}
	}
	say("Not an editor command: ");
	str_add(&msg, cmd);
}

static void ex_prompt(void)
{
	char buf[PROMPT_LEN];

	if (prompt(":", buf, PROMPT_LEN)) run_ex(buf);
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

/* digits build up a count; returns 1 if c was one */
static int count_key(int c)
{
	if ((c >= '1' && c <= '9') || (c == '0' && count > 0)) {
		count = count * 10 + (unsigned)(c - '0');
		if (count > COUNT_MAX) count = COUNT_MAX;
		return 1;
	}
	return 0;
}

/* motions shared by normal and select mode; returns 1 if c was one */
static int motion_key(int c, unsigned n, unsigned had)
{
	switch (c) {
	case 'h': repeat(move_left, n); break;
	case 'l': repeat(move_right, n); break;
	case 'j': repeat(move_down, n); break;
	case 'k': repeat(move_up, n); break;
	case 'w': repeat(word_forward, n); break;
	case 'b': repeat(word_backward, n); break;
	case '0': pos = line_start(pos); break;
	case '^': pos = first_nonblank(line_start(pos)); break;
	case '$': pos = line_end(pos); break;
	case 'G':
		pos = had ? goto_line(had) : line_start(TEXT_LEN());
		break;
	case 'g':
		if (read_key() == 'g') pos = goto_line(had ? had : 1);
		break;
	case '/':
		if (prompt("/", last_search, PROMPT_LEN)) search(last_search);
		break;
	case 'n': search(last_search); break;
	default: return 0;
	}
	return 1;
}

static void normal_key(int c)
{
	unsigned had, n;
	int c2;

	if (count_key(c)) return;
	had = count;
	n = had ? had : 1;
	count = 0;
	if (motion_key(c, n, had)) return;

	switch (c) {
	/* changes */
	case 'x': begin_change(); delete_chars(n); break;
	case 'r':
		c2 = read_key();
		if (c2 >= 32 && c2 < 127) {
			begin_change();
			replace_char(c2);
		}
		break;
	case 'd': delete_op(n); break;
	case 'D': begin_change(); delete_to_eol(); break;
	case 'y':
		if (read_key() == 'y') yank_lines(n);
		break;
	case 'p': begin_change(); paste(1); break;
	case 'P': begin_change(); paste(0); break;
	case 'J': begin_change(); repeat(join_line, n); break;
	case 'u': undo(); break;

	/* enter insert mode */
	case 'i': insert_at(pos); break;
	case 'a': insert_at(pos < line_end(pos) ? utf8_next(pos) : pos); break;
	case 'I': insert_at(first_nonblank(line_start(pos))); break;
	case 'A': insert_at(line_end(pos)); break;
	case 'o': open_line_below(); break;
	case 'O': open_line_above(); break;

	/* enter select mode */
	case 'v': enter_select(0); break;
	case 'V': enter_select(1); break;

	case ':': ex_prompt(); break;
	default: break;
	}
}

static void visual_key(int c)
{
	unsigned had, n;

	if (count_key(c)) return;
	had = count;
	n = had ? had : 1;
	count = 0;
	if (motion_key(c, n, had)) return;

	switch (c) {
	case CTRL_C: mode = NORMAL; break;
	case 'v':
		if (sel_line) sel_line = 0;
		else mode = NORMAL;
		break;
	case 'V':
		if (!sel_line) sel_line = 1;
		else mode = NORMAL;
		break;
	case 'o': select_swap_ends(); break;
	case 'y': select_yank(); break;
	case 'd': case 'x': select_delete(); break;
	case 'c': select_change(); break;
	default: break;
	}
}

int main(int argc, char **argv)
{
	int c;

	if (argc > 1) {
		str_copy(fname, argv[1], PATH_LEN);
		load_file(fname);
	}
	term_raw();
	for (;;) {
		draw();
		c = read_key();
		say("");
		keep_col = 0;
		switch (mode) {
		case INSERT: insert_key(c); break;
		case VISUAL: visual_key(c); break;
		default:     normal_key(c); break;
		}
		clamp_cursor();
		if (!keep_col) want_col = pos - line_start(pos);
	}
}
