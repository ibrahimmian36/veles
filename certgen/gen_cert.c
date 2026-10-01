/* gen_cert: refutation certificate, with symmetry reduction, that no exact cover of the
 * (k-1)-subsets of [v] by k-subsets extends a given state (a Steiner system S(k-1,k,v)).
 *
 * State: the set X of covered items ((k-1)-subsets, named by point mask). A certificate is a set
 * of TREEs, one per root state. A tree node is either
 *   I T        branch on the uncovered item T: children are the compatible blocks T+{x}, x
 *              ascending, each followed by its subtree;
 *   R j perm   reduce: perm (a permutation of [v]) maps the current state onto the root state of
 *              tree j exactly, so the current state has no extension if that root has none.
 * Tree 0 is the start state. Symmetry is used in two places, both emitted as R nodes:
 *   - sibling pruning: at the first D branchings of phase 0, a child whose state is isomorphic
 *     to an earlier kept sibling's is reduced to it; each kept child becomes its own tree;
 *   - phase classification: when every item of phase p is covered, the state is reduced to the
 *     first-seen isomorphic representative (new representatives become new trees).
 * Phases: item classes "items containing the point set P_p", filled in order; after the last
 * phase all remaining items are free. Branching uses fewest-compatible-blocks within the current
 * phase (ties: smallest mask).
 *
 * Usage: gen_cert k v D DP phasefile startfile > cert.txt   (pruning depth D in phases < DP;
 *   an isomorphism search that exceeds its step budget counts as failed: sound, only costlier)
 *   phasefile: one point mask per line (P_0, P_1, ...); startfile: blocks of the start state, or "-".
 * Output format: "TREE id nblocks b1 ... bn" then nodes, then "END"; summary on stderr.
 * Exit 1 if a complete cover is found (then the certificate is impossible).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXV 24
#define MAXB 4096
static int K, V, D, DP, NPH;
static int phase[16];
static int *items, nitems;
static long long nodes = 0, reduces = 0;

typedef struct { uint64_t *bits; int nb; int blocks[MAXB]; } State;
static int startItems[1 << 16], nStart = 0;   /* pre-covered items, shared by every tree */
static size_t WORDS;

static int getb(const uint64_t *b, int m) { return (b[m >> 6] >> (m & 63)) & 1; }
static void setb(uint64_t *b, int m, int on) { if (on) b[m >> 6] |= 1ULL << (m & 63); else b[m >> 6] &= ~(1ULL << (m & 63)); }
static int compat(const State *s, int B) { for (int y = 0; y < V; y++) if (B >> y & 1) if (getb(s->bits, B ^ (1 << y))) return 0; return 1; }
static void place(State *s, int B, int on) {
  for (int y = 0; y < V; y++) if (B >> y & 1) setb(s->bits, B ^ (1 << y), on);
  if (on) s->blocks[s->nb++] = B; else s->nb--;
}
static State *clone(const State *s) { State *t = malloc(sizeof(State)); *t = *s; t->bits = malloc(WORDS * 8); memcpy(t->bits, s->bits, WORDS * 8); return t; }

/* ---- isomorphism search: perm p with p(A) == B as item sets ---- */
static int isoA[1 << 16], nA;           /* items of A */
static uint64_t *isoB; static int isoPerm[MAXV], isoUsed[MAXV], degA[MAXV], degB[MAXV];
static int *byLast[MAXV]; static int nByLast[MAXV];
static int mapMask(int m, const int *p) { int r = 0; for (int y = 0; y < V; y++) if (m >> y & 1) r |= 1 << p[y]; return r; }
static int order[MAXV], posOf[MAXV];  /* assignment order: points by descending degree in A */
static long long isoSteps, isoBudget = 2000000, isoGaveUp = 0;
static int isoRec(int i) {
  if (i == V) return 1;
  if (++isoSteps > isoBudget) return 0;
  int y = order[i];
  if (degA[y] == 0) {                     /* the rest lie in no item: map them in any order */
    for (int r = i; r < V; r++) {
      int z = 0; while (isoUsed[z] || degB[z] != 0) z++;
      isoPerm[order[r]] = z; isoUsed[z] = 1;
    }
    return 1;
  }
  for (int z = 0; z < V; z++) {
    if (isoUsed[z] || degA[y] != degB[z]) continue;
    isoPerm[y] = z; isoUsed[z] = 1;
    int ok = 1;
    for (int q = 0; q < nByLast[i] && ok; q++) if (!getb(isoB, mapMask(byLast[i][q], isoPerm))) ok = 0;
    if (ok && isoRec(i + 1)) return 1;
    isoUsed[z] = 0;
  }
  return 0;
}
static int findIso(const uint64_t *A, const uint64_t *B, int *out) {
  int cA = 0, cB = 0;
  memset(degA, 0, sizeof degA); memset(degB, 0, sizeof degB);
  nA = 0;
  for (int i = 0; i < nitems; i++) {
    int m = items[i];
    if (getb(A, m)) { isoA[nA++] = m; cA++; for (int y = 0; y < V; y++) if (m >> y & 1) degA[y]++; }
    if (getb(B, m)) { cB++; for (int y = 0; y < V; y++) if (m >> y & 1) degB[y]++; }
  }
  if (cA != cB) return 0;
  { int da[MAXV], db[MAXV]; memcpy(da, degA, sizeof da); memcpy(db, degB, sizeof db);
    for (int a = 0; a < V; a++) for (int b = a + 1; b < V; b++) {
      if (da[b] > da[a]) { int t = da[a]; da[a] = da[b]; da[b] = t; }
      if (db[b] > db[a]) { int t = db[a]; db[a] = db[b]; db[b] = t; } }
    if (memcmp(da, db, sizeof da)) return 0; }       /* degree multisets differ */
  for (int y = 0; y < V; y++) order[y] = y;
  for (int a = 0; a < V; a++) for (int b = a + 1; b < V; b++)
    if (degA[order[b]] > degA[order[a]]) { int t = order[a]; order[a] = order[b]; order[b] = t; }
  for (int i = 0; i < V; i++) posOf[order[i]] = i;
  for (int y = 0; y < V; y++) nByLast[y] = 0;
  for (int i = 0; i < nA; i++) {
    int m = isoA[i], last = 0;
    for (int y = 0; y < V; y++) if ((m >> y & 1) && posOf[y] > last) last = posOf[y];
    byLast[last][nByLast[last]++] = m;
  }
  isoB = (uint64_t *)B; memset(isoUsed, 0, sizeof isoUsed); isoSteps = 0;
  if (!isoRec(0)) { if (isoSteps > isoBudget) isoGaveUp++; return 0; }
  memcpy(out, isoPerm, sizeof(int) * V);
  return 1;
}

/* ---- trees and representatives ---- */
#define MAXT (1 << 22)
static State *roots[MAXT]; static int nroots = 0, done_upto = 0;
static int repOf[MAXT], startOf[MAXT];  /* startOf: blocks when the tree's phase began */              /* for representative trees: phase they represent, else -1 */
static int newTree(const State *s, int rep, int start) { if (nroots >= MAXT) { fprintf(stderr, "too many trees\n"); exit(3); } roots[nroots] = clone(s); repOf[nroots] = rep; startOf[nroots] = start; return nroots++; }
static void emitR(int j, const int *p) {
  reduces++; printf("R %d", j);
  for (int y = 0; y < V; y++) printf("%c%d", y ? ',' : ' ', p[y]);
  printf("\n");
}
static int ident[MAXV];

static int curPhase(const State *s) {   /* first phase with an uncovered item, or NPH */
  for (int p = 0; p < NPH; p++)
    for (int i = 0; i < nitems; i++) { int m = items[i]; if ((m & phase[p]) == phase[p] && !getb(s->bits, m)) return p; }
  return NPH;
}

static int solutions = 0;
static void search(State *s, int start, int lastPhase, int isRoot) {
  int ph = curPhase(s);
  if (!isRoot && ph > lastPhase && ph <= NPH && lastPhase < NPH) {
    /* phase lastPhase just completed: classify */
    int p[MAXV];
    for (int j = 0; j < nroots; j++)
      if (repOf[j] == lastPhase && findIso(s->bits, roots[j]->bits, p)) { emitR(j, p); return; }
    int j = newTree(s, lastPhase, s->nb); emitR(j, ident); return;
  }
  int best = -1, bestc = 1 << 30;
  for (int i = 0; i < nitems; i++) {
    int it = items[i];
    if (getb(s->bits, it)) continue;
    if (ph < NPH && (it & phase[ph]) != phase[ph]) continue;
    int c = 0;
    for (int x = 0; x < V; x++) if (!(it >> x & 1) && compat(s, it | 1 << x)) c++;
    if (c < bestc) { bestc = c; best = it; if (c == 0) break; }
  }
  if (best < 0) { solutions++; fprintf(stderr, "SOLUTION FOUND\n"); return; }
  nodes++; printf("I %d\n", best);
  int kept[MAXV], nk = 0;
  for (int x = 0; x < V; x++) {
    if (best >> x & 1) continue;
    int B = best | 1 << x;
    if (!compat(s, B)) continue;
    place(s, B, 1);
    if (ph < DP && s->nb - 1 - start < D) {
      int p[MAXV], hit = -1;
      for (int q = 0; q < nk && hit < 0; q++) if (findIso(s->bits, roots[kept[q]]->bits, p)) hit = kept[q];
      if (hit >= 0) emitR(hit, p);
      else { int j = newTree(s, -1, start); kept[nk++] = j; emitR(j, ident); }
    } else search(s, start, ph, 0);
    place(s, B, 0);
  }
}

int main(int argc, char **argv) {
  if (argc != 7) { fprintf(stderr, "usage: gen_cert k v D DP phasefile startfile\n"); return 2; }
  K = atoi(argv[1]); V = atoi(argv[2]); D = atoi(argv[3]); DP = atoi(argv[4]);
  for (int y = 0; y < V; y++) { ident[y] = y; byLast[y] = malloc(sizeof(int) << 16); }
  FILE *f = fopen(argv[5], "r"); int m;
  while (fscanf(f, "%d", &m) == 1) phase[NPH++] = m;
  fclose(f);
  WORDS = ((size_t)1 << V) / 64 + 1;
  items = malloc(sizeof(int) << V);
  for (int x = 0; x < (1 << V); x++) if (__builtin_popcount(x) == K - 1) items[nitems++] = x;
  static State s0; s0.nb = 0; s0.bits = calloc(WORDS, 8);
  if (strcmp(argv[6], "-")) {
    f = fopen(argv[6], "r");
    while (fscanf(f, "%d", &m) == 1) {
      if (__builtin_popcount(m) != K || !compat(&s0, m)) { fprintf(stderr, "bad start block %d\n", m); return 2; }
      place(&s0, m, 1);
    }
    fclose(f);
  }
  /* optional pre-covered items (not from blocks): env START_ITEMS = file of item masks */
  if (getenv("START_ITEMS")) {
    FILE *g = fopen(getenv("START_ITEMS"), "r"); int it;
    while (fscanf(g, "%d", &it) == 1) {
      if (__builtin_popcount(it) != K - 1 || getb(s0.bits, it)) { fprintf(stderr, "bad start item %d\n", it); return 2; }
      setb(s0.bits, it, 1); startItems[nStart++] = it;
    }
    fclose(g);
  }
  newTree(&s0, -1, 0);
  while (done_upto < nroots) {
    int j = done_upto++;
    State *s = clone(roots[j]);
    printf("TREE %d %d", j, s->nb);
    for (int i = 0; i < s->nb; i++) printf(" %d", s->blocks[i]);
    if (nStart) { printf(" ITEMS"); for (int i = 0; i < nStart; i++) printf(" %d", startItems[i]); }
    printf("\n");
    search(s, startOf[j], curPhase(s), 1);
    printf("END\n");
    fprintf(stderr, "tree %d (rep of phase %d): cumulative nodes=%lld reduces=%lld trees=%d\n", j, repOf[j], nodes, reduces, nroots);
  }
  fprintf(stderr, "TOTAL nodes=%lld reduces=%lld trees=%d solutions=%d isoGaveUp=%lld\n", nodes, reduces, nroots, solutions, isoGaveUp);
  return solutions ? 1 : 0;
}
