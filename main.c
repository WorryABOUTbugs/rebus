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
    const Puzzle *p;
    int digit[REB_ALPHA];
    int used[10];
} Ctx;

static long long word_value(const Ctx *c, int w){
    const Puzzle *p = c->p;
    long long v = 0;
    int k;
    for (k = 0; k < p->len[w]; k++) {
        int letter = p->lidx[p->text[w][k] - 'A'];
        v = v * 10 + c->digit[letter];
    }
    return v;
}

static int check(const Ctx *c){
    const Puzzle *p = c->p;
    long long sum = 0;
    int w;
    for (w = 0; w < p->nwords; w++)
        if (p->lead_nonzero[w] && c->digit[p->lidx[p->text[w][0] - 'A']] == 0)
            return 0;
    for (w = 0; w < p->swords; w++)
        sum += word_value(c, w);
    return sum == word_value(c, p->swords);
}

static int dfs(Ctx *c, int k){
    int d;
    if (k == c->p->nletters)
        return check(c);
    for (d = 0; d < 10; d++) {
        if (c->used[d])
            continue;
        c->used[d] = 1;
        c->digit[k] = d;
        if (dfs(c, k + 1))
            return 1;
        c->used[d] = 0;
    }
    return 0;
}

static int solve_puzzle(const Puzzle *p, int digit[REB_ALPHA]){
    Ctx c;
    memset(&c, 0, sizeof c);
    c.p = p;
    if (!dfs(&c, 0))
        return 0;
    memcpy(digit, c.digit, sizeof c.digit);
    return 1;
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
    return 0;
}
