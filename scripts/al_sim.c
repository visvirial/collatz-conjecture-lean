// al_sim.c: C mirror of the kernel check `Collatz.LSA.cover` (Collatz/LSA/Basic.lean).
//
// gcc -O2 -fopenmp -o al_sim scripts/al_sim.c
// ./al_sim P Q D split Lmax T1 [T2 ...] > table
//   For every non-closed class at level `split` (the chunks) and every band T, runs the exact
//   kernel algorithm and prints one line per chunk: r, then (ok, work, codewords, entries) per T.
//   work = kernel `chain` steps, D = max path depth (0 = no depth prune). Env SAMPLE=s runs
//   every s-th chunk only.
//
// Kernel state: a frontier of entries (x, p, d) of weight w = m - 1 for the class (r, 3^m): x is
// the backward iterate of the representative r along a path of length k with w odd moves,
// p = 2^k, d = P k - Q w > 0. The class element r + 3^m t has the node x + 3 p t.
// Child digit j: x' = x + 3 j p; chain x' 2^i (i = 0, 1, ...); a chain node y with y % 9 in
// {2, 8} gives the odd child ((2y - 1)/3, 2 p 2^i, d + (i+1) P - Q). The child class closes as
// soon as some odd child has d + (i+1) P <= Q (ratio >= P/Q). Entries with deficit > T are
// dropped (the band hint), as are entries that cannot reach a codeword within depth D.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

typedef unsigned __int128 u128;
typedef unsigned long long u64;
typedef struct { u128 x, p; int d; } Ent;
static int P, Q, D, Lmax;

typedef struct { u64 work, cw, ent, cap; } St;

// usefulness of an entry of weight w with deficit d (k = (d + Q w)/P): exact depth prune
static inline int useful(int d, int w, int T) {
  if (d > T) return 0;
  if (!D) return 1;
  int k = (d + Q * w) / P, e = k - w;
  if (k > D) return 0;
  int Lmin = (P * e + (Q - P) - 1) / (Q - P);
  if (Lmin < w) Lmin = w;
  return Lmin <= D - e;
}

// generate child frontier; returns 1 if closed. Mirrors `Collatz.LSA.ext`: each entry jumps
// to the first node of its even chain with an odd move (i0 by x % 9), then from y = 2 (mod 9)
// to 4y, from y = 8 to 16y. work = kernel `chain` steps.
static const int I0[9] = {0, 1, 0, 0, 1, 2, 0, 3, 0};
static int ext(Ent *f, int n, int j, int w, int T, Ent **g, int *gn, int *cap, St *s) {
  *gn = 0;
  for (int i = n - 1; i >= 0; i--) { // the kernel's List.rec runs the list in order; the
    // frontier list is built by consing, so it is reversed relative to creation order
    u128 y = f[i].x + (u128)3 * j * f[i].p, p = f[i].p;
    int i0 = I0[(int)(y % 9)];
    y <<= i0; p <<= i0; int d = f[i].d + i0 * P;
    for (;;) {
      s->work++;
      int y9 = (int)(y % 9);
      if (y9 != 2 && y9 != 8) break;
      if (d + P <= Q) return 1;
      if (!useful(d + P - Q, w + 1, T)) break;
      if (*gn == *cap) { *cap *= 2; *g = realloc(*g, sizeof(Ent) * *cap); }
      (*g)[(*gn)++] = (Ent){(2 * y - 1) / 3, 2 * p, d + P - Q};
      s->ent++;
      int gg = y9 == 2 ? 2 : 4;
      y <<= gg; p <<= gg; d += gg * P;
    }
    s->work++; // the final `some acc` step
  }
  return 0;
}

// class with frontier f of weight w; returns 1 if covered
static int cover(Ent *f, int n, int w, int T, St *s) {
  if (n == 0 || w >= Lmax || (s->cap && s->work > s->cap)) return 0;
  int cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  int ok = 1;
  for (int j = 0; j < 3 && ok; j++) {
    if (ext(f, n, j, w, T, &g, &gn, &cap, s)) { s->cw++; continue; }
    Ent *h = malloc(sizeof(Ent) * (gn ? gn : 1)); memcpy(h, g, sizeof(Ent) * gn);
    ok = cover(h, gn, w + 1, T, s);
    free(h);
  }
  free(g);
  return ok;
}

// enumerate the non-closed classes at level `split` with T = Tmax frontier... chunks are defined
// by digits; their frontier is recomputed per T.
typedef struct { u64 r; int m; } Chunk;
static Chunk *ch; static int nch, chcap;
static int split, nT, Ts[64];

// descend from root along digits of r (level m), with band T; returns frontier in *f
// returns -1 if some prefix closed, else frontier size
static int frontier(u64 r, int m, int T, Ent **f, St *s) {
  int n = 1, cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  *f = malloc(sizeof(Ent) * 64); int fcap = 64;
  (*f)[0] = (Ent){r % 3, 1, 0};
  u64 rr = r / 3;
  for (int lev = 1; lev < m; lev++) {
    int j = rr % 3; rr /= 3;
    if (ext(*f, n, j, lev - 1, T, &g, &gn, &cap, s)) { free(g); return -1; }
    if (gn > fcap) { fcap = gn; *f = realloc(*f, sizeof(Ent) * fcap); }
    memcpy(*f, g, sizeof(Ent) * gn); n = gn;
  }
  free(g);
  return n;
}

static void enumc(u64 r, int m, u64 pw) { // r < pw = 3^(m-1)... collect classes at level split
  if (m == split) {
    // keep only if not closed with the largest T
    St s = {0}; Ent *f; int n = frontier(r, m, Ts[nT - 1], &f, &s); free(f);
    if (n != -1) { if (nch == chcap) { chcap = chcap ? 2 * chcap : 1024; ch = realloc(ch, sizeof(Chunk) * chcap); } ch[nch++] = (Chunk){r, m}; }
    return;
  }
  for (int j = 0; j < 3; j++) enumc(r + j * pw, m + 1, pw * 3);
}

#ifdef ONE
// ./al_one P Q D Lmax T m seed count: list `count` random non-closed classes at level m with their
// work under band T (for picking kernel sample chunks); prints r, digits, ok, work, cw.
int main(int argc, char **argv) {
  P = atoi(argv[1]); Q = atoi(argv[2]); D = atoi(argv[3]); Lmax = atoi(argv[4]);
  int T = atoi(argv[5]), m = atoi(argv[6]); srand(atoi(argv[7])); int cnt = atoi(argv[8]);
  u64 pw = 1; for (int i = 0; i < m; i++) pw *= 3;
  for (int found = 0; found < cnt;) {
    u64 r = (((u64)rand() << 31) ^ rand()) % pw; if (r % 3 == 0) continue;
    St s = {0}; Ent *f; int n = frontier(r, m, T, &f, &s);
    if (n == -1) { free(f); continue; }
    int ok = cover(f, n, m - 1, T, &s); free(f); found++;
    printf("%llu r0=%llu digits=[", r, r % 3); u64 rr = r / 3;
    for (int i = 1; i < m; i++) { printf(i > 1 ? ",%llu" : "%llu", rr % 3); rr /= 3; }
    printf("] ok=%d work=%llu cw=%llu\n", ok, s.work, s.cw);
  }
  return 0;
}
#else
int main(int argc, char **argv) {
  P = atoi(argv[1]); Q = atoi(argv[2]); D = atoi(argv[3]); split = atoi(argv[4]); Lmax = atoi(argv[5]);
  nT = argc - 6; for (int i = 0; i < nT; i++) Ts[i] = atoi(argv[6 + i]);
  enumc(1, 1, 3); enumc(2, 1, 3);
  fprintf(stderr, "chunks=%d\n", nch);
  u64 *res = calloc((size_t)nch * nT * 4, sizeof(u64));
  int sample = getenv("SAMPLE") ? atoi(getenv("SAMPLE")) : 1; // run every sample-th chunk
  #pragma omp parallel for schedule(dynamic, 1)
  for (int c = 0; c < nch; c += sample) {
    u64 capw = 0;
    for (int t = nT - 1; t >= 0; t--) {
      St s = {0}; s.cap = capw; Ent *f; int n = frontier(ch[c].r, ch[c].m, Ts[t], &f, &s);
      int ok = n == -1 ? 1 : cover(f, n, ch[c].m - 1, Ts[t], &s);
      free(f);
      u64 *o = res + ((size_t)c * nT + t) * 4;
      o[0] = ok; o[1] = s.work; o[2] = s.cw; o[3] = s.ent;
      if (ok && (capw == 0 || 2 * s.work < capw)) capw = 2 * s.work;
    }
  }
  printf("# P=%d Q=%d D=%d split=%d Lmax=%d T:", P, Q, D, split, Lmax);
  for (int t = 0; t < nT; t++) printf(" %d", Ts[t]);
  printf("\n");
  for (int c = 0; c < nch; c += sample) {
    printf("%llu", ch[c].r);
    for (int t = 0; t < nT; t++) { u64 *o = res + ((size_t)c * nT + t) * 4; printf(" %llu %llu %llu %llu", o[0], o[1], o[2], o[3]); }
    printf("\n");
  }
  return 0;
}
#endif
