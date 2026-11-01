#define _CRT_SECURE_NO_WARNINGS

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define REB_ALPHA 26
#define REB_WORDS 8
#define REB_LEN   16
#define REB_LINE  512
#define REB_MAXP  64

static double now_sec(void){
    return (double)clock() / CLOCKS_PER_SEC;
}

typedef struct {
    int  nwords;
    int  swords;
    int  len[REB_WORDS];
    char text[REB_WORDS][REB_LEN + 1];
    int  idx[REB_WORDS][REB_LEN];
    int  nletters;
    char letters[REB_ALPHA];
    int  lidx[REB_ALPHA];
    int  lead_nonzero[REB_WORDS];
    int  nonzero[REB_ALPHA];
} Puzzle;

enum { OK = 0, SYNTAX, TOO_LONG, TOO_MANY, NOT_ADDITION };

static int is_letter(unsigned char c){
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
}

static int puzzle(const char *s, Puzzle *p, int relaxed){
    int i, w = 0, expect_word = 1, seen_eq = 0;

    memset(p, 0, sizeof *p);
    if (strlen(s) >= REB_LINE)
        return TOO_LONG;
    for (i = 0; i < REB_ALPHA; i++)
        p->lidx[i] = -1;

    while (*s) {
        unsigned char ch = (unsigned char)*s;
        if (ch == ' ' || ch == '\t') {
            s++;
            continue;
        }

        if (is_letter(ch)) {
            int len = 0;
            if (!expect_word)
                return SYNTAX;
            if (w >= REB_WORDS)
                return NOT_ADDITION;
            while (is_letter((unsigned char)*s)) {
                if (len >= REB_LEN)
                    return TOO_LONG;
                p->text[w][len++] = (char)toupper((unsigned char)*s);
                s++;
            }
            p->len[w++] = len;
            expect_word = 0;
            continue;
        }
        if (ch == '+' && !seen_eq) {
            if (expect_word)
                return SYNTAX;
            expect_word = 1; s++;
            continue;
        }
        if (ch == '=' && !seen_eq) {
            if (expect_word)
                return SYNTAX;
            seen_eq = 1; expect_word = 1; p->swords = w; s++;
            continue;
        }
        if (ch == '-' || ch == '*' || ch == '/' || ch == '(' || ch == ')' || ch == '+')
            return NOT_ADDITION;
        return SYNTAX;
    }
    if (!seen_eq || expect_word || p->swords < 1)
        return SYNTAX;
    p->nwords = w;
    if (p->nwords != p->swords + 1)
        return SYNTAX;

    for (w = 0; w < p->nwords; w++) {
        for (i = 0; i < p->len[w]; i++) {
            int c = p->text[w][i] - 'A';
            if (p->lidx[c] < 0) {
                if (p->nletters >= 10)
                    return TOO_MANY;
                p->lidx[c] = p->nletters;
                p->letters[p->nletters++] = p->text[w][i];
            }
            p->idx[w][i] = p->lidx[c];
        }
        p->lead_nonzero[w] = relaxed ? (p->len[w] > 1) : 1;
        if (p->lead_nonzero[w])
            p->nonzero[p->idx[w][0]] = 1;
    }
    return OK;
}

static char *substitute(const char *src, const int dig26[REB_ALPHA]){
    size_t n = strlen(src), i;
    char *out = (char *)malloc(n + 1);
    if (!out)
        return NULL;
    for (i = 0; i < n; i++) {
        unsigned char c = (unsigned char)src[i];
        if (is_letter(c)) {
            int d = dig26[toupper(c) - 'A'];
            out[i] = (d >= 0 && d <= 9) ? (char)('0' + d) : '?';
        } else {
            out[i] = (char)c;
        }
    }
    out[n] = '\0';
    return out;
}

typedef struct {
    int n, ncols;
    int order[REB_ALPHA];
    int intro[REB_LEN];
    int colN[REB_LEN];
    int colL[REB_LEN][REB_WORDS];
    int colC[REB_LEN][REB_WORDS];
    const int *nonzero;
    int digit[REB_ALPHA];
} Cols;

static void build(const Puzzle *p, Cols *s){
    int cnt[REB_LEN][REB_ALPHA];
    int placed[REB_ALPHA];
    int w, k, c, i;

    memset(cnt, 0, sizeof cnt);
    memset(placed, 0, sizeof placed);
    memset(s, 0, sizeof *s);
    s->n = p->nletters;
    s->nonzero = p->nonzero;
    for (w = 0; w < p->nwords; w++) {
        if (p->len[w] > s->ncols)
            s->ncols = p->len[w];
        for (k = 0; k < p->len[w]; k++)
            cnt[p->len[w] - 1 - k][p->idx[w][k]] += (w < p->swords) ? 1 : -1;
    }
    for (c = 0; c < s->ncols; c++) {
        for (i = 0; i < p->nletters; i++) {
            if (cnt[c][i] == 0)
                continue;
            s->colL[c][s->colN[c]] = i;
            s->colC[c][s->colN[c]++] = cnt[c][i];
            if (!placed[i]) {
                placed[i] = 1;
                s->order[s->intro[c]++] = i;
            }
        }
        if (c + 1 < s->ncols)
            s->intro[c + 1] = s->intro[c];
    }
    k = s->ncols ? s->intro[s->ncols - 1] : 0;
    for (i = 0; i < p->nletters; i++)
        if (!placed[i])
            s->order[k++] = i;
}

static int dfs(Cols *s, int j, unsigned used, int col, long long carry){
    int letter, d;
    if (j == s->n)
        return 1;
    letter = s->order[j];
    for (d = s->nonzero[letter] ? 1 : 0; d < 10; d++) {
        int c = col, ok = 1;
        long long cr = carry;
        if ((used >> d) & 1u)
            continue;
        s->digit[letter] = d;
        while (c < s->ncols && s->intro[c] <= j + 1) {
            long long sum = cr;
            int t;
            for (t = 0; t < s->colN[c]; t++)
                sum += (long long)s->colC[c][t] * s->digit[s->colL[c][t]];
            if (sum % 10 != 0) {
                ok = 0;
                break;
            }
            cr = sum / 10;
            c++;
        }
        if (!ok || (c == s->ncols && cr != 0))
            continue;
        if (dfs(s, j + 1, used | (1u << d), c, cr))
            return 1;
    }
    return 0;
}

static int solve_puzzle(const Puzzle *p, int digit[REB_ALPHA]){
    Cols s;
    build(p, &s);
    if (!dfs(&s, 0, 0u, 0, 0))
        return 0;
    memcpy(digit, s.digit, sizeof(int) * (size_t)p->nletters);
    return 1;
}

#include <limits.h>

#define E_WORDS 16
#define E_LEN   16
#define E_TOK   64

typedef struct {
    int op;
    int word;
} Tok;
typedef struct {
    char kind;
    int word;
} Raw;

typedef struct {
    int nwords;
    int len[E_WORDS];
    char text[E_WORDS][E_LEN + 1];
    int idx[E_WORDS][E_LEN];
    int lead_nonzero[E_WORDS];
    int nletters;
    char letters[REB_ALPHA];
    int nonzero[REB_ALPHA];
    Tok a[E_TOK], b[E_TOK];
    int na, nb;
    int decode, target;
    int m;
    int ewords[E_WORDS], new_words;
    int trunc_div;
} Ext;

static int prec(int op) { return (op == '*' || op == '/') ? 2 : 1; }

static int to_rpn(const Raw *t, int n, Tok *out, int *nout){
    int ops[E_TOK], sp = 0, no = 0, expect = 1, depth = 0, i;
    for (i = 0; i < n; i++) {
        char k = t[i].kind;
        if (k == 'W') {
            if (!expect)
                return -1;
            out[no].op = 0; out[no++].word = t[i].word; expect = 0;
        } else if (k == '(') {
            if (!expect)
                return -1;
            ops[sp++] = '('; depth++;
        } else if (k == ')') {
            if (expect || depth == 0)
                return -1;
            while (sp && ops[sp - 1] != '(') {
                out[no].op = ops[--sp];
                out[no++].word = 0;
            }
            sp--; depth--;
        } else {
            if (expect)
                return -1;
            while (sp && ops[sp - 1] != '(' && prec(ops[sp - 1]) >= prec(k)) {
                out[no].op = ops[--sp]; out[no++].word = 0;
            }
            ops[sp++] = k; expect = 1;
        }
    }
    if (expect || depth)
        return -1;
    while (sp) {
        out[no].op = ops[--sp];
        out[no++].word = 0;
    }
    *nout = no;
    return 0;
}

static void add_letter(int *rank_of, int *order, int *norder, char ch){
    int c = ch - 'A';
    if (rank_of[c] < 0) {
        rank_of[c] = *norder;
        order[(*norder)++] = c;
    }
}

static int ext_parse(Ext *e, const char *s, int relaxed, int trunc_div){
    Raw raw[E_TOK * 2];
    Tok lt[E_TOK], rt[E_TOK];
    int nraw = 0, eq = -1, w, k, i, nlt = 0, nrt = 0, norder = 0;
    int rank_of[REB_ALPHA], order[REB_ALPHA];

    memset(e, 0, sizeof *e);
    e->trunc_div = trunc_div;
    while (*s) {
        unsigned char ch = (unsigned char)*s;
        if (ch == ' ' || ch == '\t') {
            s++;
            continue;
        }
        if (nraw >= E_TOK * 2 - 1)
            return -1;
        if (is_letter(ch)) {
            char buf[E_LEN + 1];
            int len = 0, found = -1;
            while (is_letter((unsigned char)*s)) {
                if (len >= E_LEN)
                    return -1;
                buf[len++] = (char)toupper((unsigned char)*s);
                s++;
            }
            buf[len] = '\0';
            for (w = 0; w < e->nwords; w++)
                if (strcmp(e->text[w], buf) == 0) {
                    found = w;
                    break;
                }
            if (found < 0) {
                if (e->nwords >= E_WORDS)
                    return -1;
                found = e->nwords++;
                memcpy(e->text[found], buf, (size_t)len + 1);
                e->len[found] = len;
            }
            raw[nraw].kind = 'W'; raw[nraw++].word = found;
            continue;
        }
        if (ch == '+' || ch == '-' || ch == '*' || ch == '/' || ch == '(' || ch == ')') {
            raw[nraw].kind = (char)ch; raw[nraw++].word = 0; s++;
            continue;
        }
        if (ch == '=') {
            if (eq >= 0)
                return -1;
            eq = nraw; raw[nraw].kind = '='; raw[nraw++].word = 0; s++;
            continue;
        }
        return -1;
    }
    if (eq <= 0 || eq == nraw - 1)
        return -1;
    if (to_rpn(raw, eq, lt, &nlt) || to_rpn(raw + eq + 1, nraw - eq - 1, rt, &nrt))
        return -1;

    if (nrt == 1) {
        memcpy(e->a, lt, sizeof(Tok) * (size_t)nlt); e->na = nlt;
        e->decode = 1; e->target = rt[0].word;
    } else if (nlt == 1) {
        memcpy(e->a, rt, sizeof(Tok) * (size_t)nrt); e->na = nrt;
        e->decode = 1; e->target = lt[0].word;
    } else {
        memcpy(e->a, lt, sizeof(Tok) * (size_t)nlt); e->na = nlt;
        memcpy(e->b, rt, sizeof(Tok) * (size_t)nrt); e->nb = nrt;
    }

    for (i = 0; i < REB_ALPHA; i++)
        rank_of[i] = -1;
    for (i = 0; i < e->na + e->nb; i++) {
        const Tok *t = (i < e->na) ? &e->a[i] : &e->b[i - e->na];
        int dup = 0, q;
        if (t->op != 0)
            continue;
        for (q = 0; q < e->new_words; q++)
            if (e->ewords[q] == t->word)
                dup = 1;
        if (!dup)
            e->ewords[e->new_words++] = t->word;
        for (k = 0; k < e->len[t->word]; k++)
            add_letter(rank_of, order, &norder, e->text[t->word][k]);
    }
    e->m = norder;
    for (w = 0; w < e->nwords; w++)
        for (k = 0; k < e->len[w]; k++)
            add_letter(rank_of, order, &norder, e->text[w][k]);
    if (norder > 10)
        return -2;
    e->nletters = norder;
    for (i = 0; i < norder; i++)
        e->letters[i] = (char)('A' + order[i]);
    for (w = 0; w < e->nwords; w++) {
        for (k = 0; k < e->len[w]; k++)
            e->idx[w][k] = rank_of[e->text[w][k] - 'A'];
        e->lead_nonzero[w] = relaxed ? (e->len[w] > 1) : 1;
        if (e->lead_nonzero[w])
            e->nonzero[e->idx[w][0]] = 1;
    }
    return 0;
}

static int eval(const Tok *t, int n, const long long *wv, int trunc_div, long long *out){
    long long st[E_TOK];
    int sp = 0, i;
    for (i = 0; i < n; i++) {
        long long x, y, r = 0;
        if (t[i].op == 0) {
            st[sp++] = wv[t[i].word];
            continue;
        }
        y = st[--sp];
        x = st[--sp];
        switch (t[i].op) {
        case '+': r = x + y; break;
        case '-': r = x - y; break;
        case '*':
            if (x != 0 && y != 0 && llabs(x) > LLONG_MAX / llabs(y))
                return 0;
            r = x * y;
            break;
        case '/':
            if (y == 0)
                return 0;
            if (!trunc_div && x % y != 0)
                return 0;
            r = x / y;
            break;
        }
        st[sp++] = r;
    }
    *out = st[0];
    return 1;
}

static int leaf(const Ext *e, int *digit, unsigned used){
    long long wv[E_WORDS], v, v2;
    int t, k, i;

    for (t = 0; t < e->new_words; t++) {
        int w = e->ewords[t];
        long long x = 0;
        for (k = 0; k < e->len[w]; k++)
            x = x * 10 + digit[e->idx[w][k]];
        wv[w] = x;
    }
    if (!eval(e->a, e->na, wv, e->trunc_div, &v))
        return 0;

    if (!e->decode) {
        if (!eval(e->b, e->nb, wv, e->trunc_div, &v2))
            return 0;
        return v == v2;
    }

    {
        int w = e->target, L = e->len[w], nd = 0, newd[REB_ALPHA], dg[24];
        long long x = v;
        unsigned u = used;
        if (v < 0)
            return 0;
        do {
            dg[nd++] = (int)(x % 10);
            x /= 10;
        } while (x && nd < 24);
        if (nd != L)
            return 0;
        for (i = e->m; i < e->nletters; i++)
            newd[i] = -1;
        for (k = 0; k < L; k++) {
            int lt = e->idx[w][k], dd = dg[L - 1 - k];
            if (lt < e->m) {
                if (digit[lt] != dd)
                    return 0;
            } else if (newd[lt] >= 0) {
                if (newd[lt] != dd)
                    return 0;
            } else {
                if ((u >> dd) & 1u)
                    return 0;
                if (dd == 0 && e->nonzero[lt])
                    return 0;
                newd[lt] = dd;
                u |= 1u << dd;
            }
        }
        for (i = e->m; i < e->nletters; i++)
            digit[i] = newd[i];
        return 1;
    }
}

static int ext_dfs(const Ext *e, int *digit, int k, unsigned used){
    int d;
    if (k == e->m)
        return leaf(e, digit, used);
    for (d = e->nonzero[k] ? 1 : 0; d < 10; d++) {
        if ((used >> d) & 1u)
            continue;
        digit[k] = d;
        if (ext_dfs(e, digit, k + 1, used | (1u << d)))
            return 1;
    }
    return 0;
}

static char *ext_solve(const char *src){
    static const int opts[3][2] = { {0, 0}, {1, 0}, {1, 1} };
    int o, w, has_single = 0, has_div = (strchr(src, '/') != NULL);
    Ext e;

    for (o = 0; o < 3; o++) {
        int digit[REB_ALPHA], dig26[REB_ALPHA], i;
        if (ext_parse(&e, src, opts[o][0], opts[o][1]) != 0)
            return NULL;
        if (o == 0)
            for (w = 0; w < e.nwords; w++)
                if (e.len[w] == 1)
                    has_single = 1;
        if (o == 1 && !has_single)
            continue;
        if (o == 2 && !has_div)
            continue;
        if (ext_dfs(&e, digit, 0, 0u)) {
            for (i = 0; i < REB_ALPHA; i++)
                dig26[i] = -1;
            for (i = 0; i < e.nletters; i++)
                dig26[e.letters[i] - 'A'] = digit[i];
            return substitute(src, dig26);
        }
    }
    return NULL;
}

static int has_single_letter_word(const Puzzle *p){
    int w;
    for (w = 0; w < p->nwords; w++)
        if (p->len[w] == 1)
            return 1;
    return 0;
}

char *solve_rebus(const char *apuzzle){
    Puzzle p;
    int digit[REB_ALPHA], dig26[REB_ALPHA], i, rc;

    rc = puzzle(apuzzle, &p, 0);
    if (rc == NOT_ADDITION)
        return ext_solve(apuzzle);
    if (rc != OK)
        return NULL;
    if (!solve_puzzle(&p, digit)) {
        if (!has_single_letter_word(&p))
            return NULL;
        if (puzzle(apuzzle, &p, 1) != OK || !solve_puzzle(&p, digit))
            return NULL;
    }
    for (i = 0; i < REB_ALPHA; i++)
        dig26[i] = -1;
    for (i = 0; i < p.nletters; i++)
        dig26[p.letters[i] - 'A'] = digit[i];
    return substitute(apuzzle, dig26);
}

static char *clean_line(char *line, int first_line){
    char *s = line;
    size_t n;
    if (first_line && (unsigned char)s[0] == 0xEF && (unsigned char)s[1] == 0xBB && (unsigned char)s[2] == 0xBF)
        s += 3;
    n = strlen(s);
    while (n > 0 && (s[n - 1] == '\n' || s[n - 1] == '\r' || s[n - 1] == ' ' || s[n - 1] == '\t'))
        s[--n] = '\0';
    while (*s == ' ' || *s == '\t')
        s++;
    if (*s == '\0' || *s == '#')
        return NULL;
    return s;
}

int solve_file(const char *path, FILE *out){
    FILE *f = fopen(path, "r");
    char line[REB_LINE], *s, *ans;
    int solved = 0, first = 1;

    if (!f)
        return -1;
    while (fgets(line, sizeof line, f)) {
        s = clean_line(line, first);
        first = 0;
        if (!s)
            continue;
        ans = solve_rebus(s);
        if (ans) {
            fprintf(out, "%s\n", ans);
            free(ans); solved++;
        }
        else
            fprintf(out, "%s  ->  no solution\n", s);
    }
    fclose(f);
    return solved;
}

static char g_puzzles[REB_MAXP][REB_LINE];

static int load_puzzles(const char *path){
    FILE *f = fopen(path, "r");
    char line[REB_LINE], *s;
    int n = 0, first = 1;
    if (!f)
        return -1;
    while (n < REB_MAXP && fgets(line, sizeof line, f)) {
        s = clean_line(line, first);
        first = 0;
        if (s) {
            strcpy(g_puzzles[n], s);
            n++;
        }
    }
    fclose(f);
    return n;
}

int main(int argc, char **argv){
    const char *path = (argc > 1) ? argv[1] : "puzzles.txt";
    int n, i, passes = 0;
    double t0, elapsed;

    if (solve_file(path, stdout) < 0) {
        printf("Cannot open %s.\n", path);
        return 1;
    }

    n = load_puzzles(path);
    t0 = now_sec();
    do {
        for (i = 0; i < n; i++)
            free(solve_rebus(g_puzzles[i]));
        passes++;
        elapsed = now_sec() - t0;
    } while (elapsed < 0.2);
    printf("\nPuzzles: %d, passes: %d, time per pass: %.3f ms\n", n, passes, elapsed / passes * 1000.0);

    printf("\n--- puzzles_ext.txt (+ - * / and '()' ) ---\n");
    if (solve_file("puzzles_ext.txt", stdout) < 0) {
        printf("puzzles_ext.txt not found\n");
    } else {
        n = load_puzzles("puzzles_ext.txt");
        passes = 0;
        t0 = now_sec();
        do {
            for (i = 0; i < n; i++)
                free(solve_rebus(g_puzzles[i]));
            passes++;
            elapsed = now_sec() - t0;
        } while (elapsed < 0.2);
        printf("\nPuzzles: %d, passes: %d, time per pass: %.3f ms\n", n, passes, elapsed / passes * 1000.0);
    }

    return 0;
}
