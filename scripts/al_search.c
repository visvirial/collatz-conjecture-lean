// al_search.c: Applegate-Lagarias lower-bound certificate search (Math. Comp. 72 (2003)).
//
// gcc -O2 -fopenmp -o al_search scripts/al_search.c
// ./al_search P Q D T [split]     e.g. ./al_search 14 29 60 1000000 10
//
// A class is a residue r mod 3^m (r % 3 != 0), the ternary prefix of a 3-adic unit a.
// Backward moves on a node x (pruned tree): x -> 2x always, x -> (2x-1)/3 iff x % 9 in {2,8}.
// The weight w of a node is the number of odd moves on its path from the root a, its depth k the
// path length; a node of weight w is determined by a mod 3^(w+1).
// Deficit of a node: delta = P k - Q w. AL's rule: the class (r, m) closes (is a codeword) iff
// some node of weight l = m-1 entered by an odd move (an "entry") has delta <= 0, i.e.
// l/k >= P/Q. Otherwise it is split into (r + j 3^m, m+1), j = 0, 1, 2.
//
// Incremental frontier: the entries of weight m-1 of the class (r, m). The entries of weight m
// of a child are the odd children of the even chains x, 2x, 4x, ... of these entries. Values are
// kept mod 3^(N-w), computed from the representative r, and lifted when a digit is added.
//
// Pruning:
//  * exact (never changes the codeword set): an entry with e = k - w even moves can lead to a
//    codeword at some level L >= w only if e + L <= D and P (e + L) <= Q L (D = max path depth);
//  * band T (a hint; may only make the search fail or produce more codewords): entries with
//    delta > T are dropped.  T = huge gives AL's canonical certificate (for paths <= D).
// Output: codewords, max level, max depth, work (= chain nodes visited), histogram of the
// "needed band" of codewords (min over closing paths of the max entry deficit on the path).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

#define N 39
typedef unsigned long long u64;
typedef unsigned __int128 u128;
static u64 P3[N + 2];
static int P, Q, D, T, splitLevel;

typedef struct { u64 v; short k, w; int pm; } Ent; // value mod 3^(N-w), depth, weight, max prefix delta

#define HB 512
typedef struct {
  u64 codewords, internal, work, entries, failed, maxFront, sumFront;
  int maxLevel, maxDepth;
  u64 cwByLevel[80], intByLevel[80], workByLevel[80];
  u64 band[HB];
} Stats;

static inline int useful(int k, int w) {
  int e = k - w;
  if (k > D) return 0;
  if (P * k - Q * w > T) return 0;
  int Lmin = (P * e + (Q - P) - 1) / (Q - P);
  if (Lmin < w) Lmin = w;
  return Lmin <= D - e;
}

typedef struct { u64 r; int m, n; Ent *f; } Task;
static Task *tasks; static int ntasks, tcap;

static void rec(u64 r, int m, Ent *f, int n, Stats *s, int collect) {
  int l = m - 1, dmin = 1 << 30, bmin = 1 << 30;
  for (int i = 0; i < n; i++) {
    if (f[i].k < dmin) dmin = f[i].k;
    if (P * f[i].k - Q * l <= 0 && f[i].pm < bmin) bmin = f[i].pm;
  }
  if (l >= 1 && n > 0 && Q * l >= P * dmin) {
    s->codewords++; s->cwByLevel[m]++;
    if (m > s->maxLevel) s->maxLevel = m;
    if (dmin > s->maxDepth) s->maxDepth = dmin;
    s->band[bmin < 0 ? 0 : bmin >= HB ? HB - 1 : bmin]++;
    return;
  }
  if (n == 0) { s->failed++; return; }
  if (collect && m == splitLevel) {
    #pragma omp critical
    {
      if (ntasks == tcap) { tcap = tcap ? 2 * tcap : 1024; tasks = realloc(tasks, sizeof(Task) * tcap); }
      Ent *c = malloc(sizeof(Ent) * n); memcpy(c, f, sizeof(Ent) * n);
      tasks[ntasks++] = (Task){r, m, n, c};
    }
    return;
  }
  s->internal++; s->intByLevel[m]++; s->sumFront += n;
  if ((u64)n > s->maxFront) s->maxFront = n;
  int cap = 64; Ent *g = malloc(sizeof(Ent) * cap);
  for (int j = 0; j < 3; j++) {
    u64 r2 = r + (u64)j * P3[m];
    int gn = 0;
    for (int i = 0; i < n; i++) {
      int w = f[i].w, k = f[i].k; u64 mod = P3[N - w];
      u64 t = 1; for (int q = 0; q < k; q++) { t <<= 1; if (t >= mod) t -= mod; }
      // lift by the new digit: x += j 2^k 3^(m-w) with m - w = 1
      u64 x = (u64)(((u128)f[i].v + (u128)j * t % mod * 3) % mod);
      for (int kk = k; ; kk++) {
        s->work++; s->workByLevel[m]++;
        int x9 = (int)(x % 9);
        if ((x9 == 2 || x9 == 8) && useful(kk + 1, w + 1)) {
          u64 y = (u64)((((u128)2 * x - 1) / 3) % P3[N - w - 1]);
          if (gn == cap) { cap *= 2; g = realloc(g, sizeof(Ent) * cap); }
          int dl = P * (kk + 1) - Q * (w + 1);
          g[gn++] = (Ent){y, (short)(kk + 1), (short)(w + 1), dl > f[i].pm ? dl : f[i].pm};
          s->entries++;
        }
        if (!useful(kk + 2, w + 1)) break;
        x = (u64)(((u128)x * 2) % mod);
      }
    }
    rec(r2, m + 1, g, gn, s, collect);
  }
  free(g);
}

int main(int argc, char **argv) {
  P = atoi(argv[1]); Q = atoi(argv[2]); D = atoi(argv[3]); T = atoi(argv[4]);
  splitLevel = argc > 5 ? atoi(argv[5]) : 10;
  P3[0] = 1; for (int i = 1; i <= N + 1; i++) P3[i] = P3[i - 1] * 3;
  Stats *tot = calloc(1, sizeof(Stats));
  for (u64 r = 1; r <= 2; r++) { Ent e = {r, 0, 0, 0}; rec(r, 1, &e, 1, tot, 1); }
  double t0 = omp_get_wtime();
  #pragma omp parallel
  {
    Stats *s = calloc(1, sizeof(Stats));
    #pragma omp for schedule(dynamic, 1)
    for (int i = 0; i < ntasks; i++) rec(tasks[i].r, tasks[i].m, tasks[i].f, tasks[i].n, s, 0);
    #pragma omp critical
    {
      tot->codewords += s->codewords; tot->internal += s->internal; tot->work += s->work;
      tot->entries += s->entries; tot->failed += s->failed; tot->sumFront += s->sumFront;
      if (s->maxFront > tot->maxFront) tot->maxFront = s->maxFront;
      if (s->maxLevel > tot->maxLevel) tot->maxLevel = s->maxLevel;
      if (s->maxDepth > tot->maxDepth) tot->maxDepth = s->maxDepth;
      for (int i = 0; i < 80; i++) { tot->cwByLevel[i] += s->cwByLevel[i]; tot->intByLevel[i] += s->intByLevel[i]; tot->workByLevel[i] += s->workByLevel[i]; }
      for (int i = 0; i < HB; i++) tot->band[i] += s->band[i];
    }
  }
  printf("alpha=%d/%d D=%d T=%d split=%d tasks=%d: %s codewords=%llu internal=%llu failed=%llu "
         "maxLevel(m)=%d maxDepth=%d work=%llu entries=%llu maxFrontier=%llu avgFrontier=%.1f time=%.1fs\n",
         P, Q, D, T, splitLevel, ntasks, tot->failed ? "FAIL" : "OK", tot->codewords, tot->internal,
         tot->failed, tot->maxLevel, tot->maxDepth, tot->work, tot->entries, tot->maxFront,
         tot->internal ? (double)tot->sumFront / tot->internal : 0.0, omp_get_wtime() - t0);
  printf("per level m: codewords/internal/work\n");
  for (int i = 0; i < 80; i++) if (tot->cwByLevel[i] || tot->intByLevel[i])
    printf("  m=%d %llu %llu %llu\n", i, tot->cwByLevel[i], tot->intByLevel[i], tot->workByLevel[i]);
  printf("needed band (max entry deficit on best closing path), cumulative codewords:\n ");
  u64 c = 0;
  for (int i = 0; i < HB; i++) if (tot->band[i]) { c += tot->band[i]; printf(" <=%d:%llu", i, c); }
  printf("\n");
  return 0;
}
