// al_vec.c: per-chunk, per-level band hints for the kernel check (Collatz/LSA/Basic.lean).
//
// gcc -O2 -fopenmp -o al_vec scripts/al_vec.c
// ./al_vec P Q D split Lmax Tbig sample [slack]
//   Chunks: the non-closed classes at level `split`; every `sample`-th is processed.
//   Stage 1: full search of the chunk with band Tbig (no early exit); for every codeword pick the
//   closing path with the least maximal entry deficit and record its entry deficits per weight;
//   the hint is T_w = max over the chunk's codewords of these (+ slack).
//   Stage 2: the kernel mirror (early exit, list order) with the per-level bands T_w.
//   Env OFFSET=o starts at chunk o (to split a full run over machines); HINTS=1 prints hints;
//   ADAPT="W0 mmax" refines chunks whose kernel work exceeds W0 (see adapt()).
//   Prints totals scaled by `sample`: stage-1 work and codewords, stage-2 kernel steps,
//   codewords, failures, and a histogram of stage-2 chunk work.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

typedef unsigned __int128 u128;
typedef unsigned long long u64;
#define LW 48
typedef struct { u128 x, p; int d; short pm; short dl[LW]; } Ent;
static int P, Q, D, Lmax;
static u64 P3[41];
typedef struct { u64 work, cw, ent; int Tv[LW]; } St;

static inline int useful(int d, int w, int T) {
  if (d > T) return 0;
  if (!D) return 1;
  int k = (d + Q * w) / P, e = k - w;
  if (k > D) return 0;
  int Lmin = (P * e + (Q - P) - 1) / (Q - P);
  if (Lmin < w) Lmin = w;
  return Lmin <= D - e;
}
static const int I0[9] = {0, 1, 0, 0, 1, 2, 0, 3, 0};

// child frontier of weight w+1 with band T. full=1: no early exit, record best closing path
// into s->Tv (returns 1 if closed). full=0: kernel mirror.
static int ext(Ent *f, int n, int j, int w, int T, Ent **g, int *gn, int *cap, St *s, int full) {
  *gn = 0; int best = -1, bpm = 1 << 30;
  for (int i = n - 1; i >= 0; i--) {
    u128 y = f[i].x + (u128)3 * j * f[i].p, p = f[i].p;
    int i0 = I0[(int)(y % 9)];
    y <<= i0; p <<= i0; int d = f[i].d + i0 * P;
    for (;;) {
      s->work++;
      int y9 = (int)(y % 9);
      if (y9 != 2 && y9 != 8) break;
      if (d + P <= Q) {
        if (!full) return 1;
        if (f[i].pm < bpm) { bpm = f[i].pm; best = i; }
        break;
      }
      if (!useful(d + P - Q, w + 1, T)) break;
      if (*gn == *cap) { *cap *= 2; *g = realloc(*g, sizeof(Ent) * *cap); }
      Ent *e = &(*g)[(*gn)++];
      e->x = (2 * y - 1) / 3; e->p = 2 * p; e->d = d + P - Q;
      if (full) { memcpy(e->dl, f[i].dl, sizeof(short) * (w + 1)); e->dl[w + 1] = e->d; e->pm = f[i].pm > e->d ? f[i].pm : e->d; }
      s->ent++;
      int gg = y9 == 2 ? 2 : 4;
      y <<= gg; p <<= gg; d += gg * P;
    }
    s->work++;
  }
  if (best >= 0) {
    for (int v = 1; v <= w; v++) if (f[best].dl[v] > s->Tv[v]) s->Tv[v] = f[best].dl[v];
    return 1;
  }
  return 0;
}

static int Tbig;
static int bandAt(int w, int full) { (void)w; (void)full; return Tbig; }
int cover2(u64 r, int m, int *tb, St *s);

static int cover(Ent *f, int n, int w, St *s, int full) {
  if (n == 0 || w >= Lmax) return 0;
  int cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  int ok = 1;
  for (int j = 0; j < 3 && ok; j++) {
    if (ext(f, n, j, w, bandAt(w + 1, full), &g, &gn, &cap, s, full)) { s->cw++; continue; }
    Ent *h = malloc(sizeof(Ent) * (gn ? gn : 1)); memcpy(h, g, sizeof(Ent) * gn);
    ok = cover(h, gn, w + 1, s, full);
    free(h);
  }
  free(g);
  return ok;
}

static int frontier(u64 r, int m, Ent **f, St *s, int full) {
  int n = 1, cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  *f = malloc(sizeof(Ent) * 64); int fcap = 64;
  memset(*f, 0, sizeof(Ent)); (*f)[0].x = r % 3; (*f)[0].p = 1;
  u64 rr = r / 3;
  for (int lev = 1; lev < m; lev++) {
    int j = rr % 3; rr /= 3;
    if (ext(*f, n, j, lev - 1, bandAt(lev, full), &g, &gn, &cap, s, full)) { free(g); return -1; }
    if (gn > fcap) { fcap = gn; *f = realloc(*f, sizeof(Ent) * fcap); }
    memcpy(*f, g, sizeof(Ent) * gn); n = gn;
  }
  free(g);
  return n;
}

typedef struct { u64 r; int m; } Chunk;
static Chunk *ch; static int nch, chcap, split;
static void enumc(u64 r, int m) {
  if (m == split) {
    St s = {0}; Ent *f; int n = frontier(r, m, &f, &s, 1); free(f);
    if (n != -1) { if (nch == chcap) { chcap = chcap ? 2 * chcap : 1024; ch = realloc(ch, sizeof(Chunk) * chcap); } ch[nch++] = (Chunk){r, m}; }
    return;
  }
  for (int j = 0; j < 3; j++) enumc(r + j * P3[m], m + 1);
}

// Adaptive chunks: a chunk whose stage-2 work exceeds W0 is replaced by its three children
// (each with its own hints), down to level mmax.
typedef struct { u64 w1, w2, cw, chunks, big, fail; u64 hist[40]; } Ad;
static u64 W0; static int mmax;
static void adapt(u64 r, int m, Ad *a) {
  St s = {0}; Ent *f;
  int n = frontier(r, m, &f, &s, 1);
  if (n == -1) { free(f); return; } // closed above: covered by the parent's chunk structure
  int ok = cover(f, n, m - 1, &s, 1);
  free(f);
  a->w1 += s.work;
  int tb[LW]; for (int v = 0; v < LW; v++) tb[v] = s.Tv[v];
  St s2 = {0};
  int ok2 = cover2(r, m, tb, &s2);
  if (s2.work > W0 && m < mmax) {
    for (int j = 0; j < 3; j++) adapt(r + j * P3[m], m + 1, a);
    return;
  }
  a->w2 += s2.work; a->cw += s2.cw; a->chunks++; a->fail += !ok || !ok2;
  if (s2.work > W0) a->big++;
  int b = 0; u64 x = s2.work; while (x >>= 1) b++;
  a->hist[b]++;
  if (getenv("HINTS")) {
    #pragma omp critical
    {
      printf("H %llu %d ok=%d work=%llu cw=%llu T=", r, m, ok2, s2.work, s2.cw);
      for (int v = 1; v < Lmax; v++) printf("%d,", tb[v]);
      printf("\n");
    }
  }
}

int main(int argc, char **argv) {
  if (getenv("ADAPT")) { // ADAPT="W0 mmax": ./al_vec P Q D split Lmax Tbig sample
    P = atoi(argv[1]); Q = atoi(argv[2]); D = atoi(argv[3]); split = atoi(argv[4]); Lmax = atoi(argv[5]);
    Tbig = atoi(argv[6]); int sample = atoi(argv[7]);
    sscanf(getenv("ADAPT"), "%llu %d", &W0, &mmax);
    P3[0] = 1; for (int i = 1; i <= 40; i++) P3[i] = P3[i - 1] * 3;
    enumc(1, 1); enumc(2, 1);
    Ad tot = {0}; u64 nrun = 0; double t0 = omp_get_wtime();
    int off = getenv("OFFSET") ? atoi(getenv("OFFSET")) : 0; // run chunks off, off + sample, ...
    #pragma omp parallel
    {
      Ad a = {0}; u64 nr = 0;
      #pragma omp for schedule(dynamic, 1)
      for (int c = off; c < nch; c += sample) { adapt(ch[c].r, ch[c].m, &a); nr++; }
      #pragma omp critical
      {
        tot.w1 += a.w1; tot.w2 += a.w2; tot.cw += a.cw; tot.chunks += a.chunks; tot.big += a.big; tot.fail += a.fail; nrun += nr;
        for (int i = 0; i < 40; i++) tot.hist[i] += a.hist[i];
      }
    }
    double sc = (double)nch / nrun;
    printf("ADAPT alpha=%d/%d D=%d split=%d W0=%llu mmax=%d Tbig=%d base chunks=%d run=%llu | stage1 work=%.4g | "
           "kernel steps=%.4g cw=%.4g chunks=%.4g over-W0=%.4g fail=%llu time=%.0fs\n",
           P, Q, D, split, W0, mmax, Tbig, nch, nrun, tot.w1 * sc, tot.w2 * sc, tot.cw * sc, tot.chunks * sc,
           tot.big * sc, tot.fail, omp_get_wtime() - t0);
    printf("chunk work histogram (log2 bucket:count, sampled):");
    for (int i = 0; i < 40; i++) if (tot.hist[i]) printf(" %d:%llu", i, tot.hist[i]);
    printf("\n");
    return 0;
  }
  P = atoi(argv[1]); Q = atoi(argv[2]); D = atoi(argv[3]); split = atoi(argv[4]); Lmax = atoi(argv[5]);
  Tbig = atoi(argv[6]); int sample = atoi(argv[7]); int slack = argc > 8 ? atoi(argv[8]) : 0;
  P3[0] = 1; for (int i = 1; i <= 40; i++) P3[i] = P3[i - 1] * 3;
  enumc(1, 1); enumc(2, 1);
  u64 W1 = 0, C1 = 0, W2 = 0, C2 = 0, F2 = 0, F1 = 0, nrun = 0, hist[40] = {0}, maxW = 0;
  double t0 = omp_get_wtime();
  int dumpHints = getenv("HINTS") != NULL;
  int off = getenv("OFFSET") ? atoi(getenv("OFFSET")) : 0; // run chunks off, off + sample, ...
  #pragma omp parallel for schedule(dynamic, 1) reduction(+:W1,C1,W2,C2,F2,F1,nrun) reduction(max:maxW)
  for (int c = off; c < nch; c += sample) {
    St s = {0}; Ent *f;
    int n = frontier(ch[c].r, ch[c].m, &f, &s, 1);
    int ok = n == -1 ? 1 : cover(f, n, ch[c].m - 1, &s, 1);
    free(f);
    W1 += s.work; C1 += s.cw; F1 += !ok; nrun++;
    int tb[LW]; for (int v = 0; v < LW; v++) tb[v] = s.Tv[v] ? s.Tv[v] + slack : 0;
    St s2 = {0};
    int ok2 = cover2(ch[c].r, ch[c].m, tb, &s2);
    W2 += s2.work; C2 += s2.cw; F2 += !ok2;
    if (s2.work > maxW) maxW = s2.work;
    int b = 0; u64 x = s2.work; while (x >>= 1) b++;
    #pragma omp atomic
    hist[b]++;
    if (dumpHints) {
      #pragma omp critical
      {
        printf("H %llu %d ok=%d work=%llu cw=%llu T=", ch[c].r, ch[c].m, ok2, s2.work, s2.cw);
        for (int v = 1; v < Lmax; v++) printf("%d,", tb[v]);
        printf("\n");
      }
    }
  }
  double sc = (double)nch / nrun;
  printf("alpha=%d/%d D=%d split=%d Lmax=%d Tbig=%d slack=%d chunks=%d run=%llu | stage1 work=%.4g cw=%.4g fail=%llu | "
         "stage2 kernel steps=%.4g cw=%.4g fail=%llu maxChunk=%llu time=%.0fs\n",
         P, Q, D, split, Lmax, Tbig, slack, nch, nrun, W1 * sc, C1 * sc, F1, W2 * sc, C2 * sc, F2, maxW, omp_get_wtime() - t0);
  printf("stage2 chunk work histogram (log2 bucket:count):");
  for (int i = 0; i < 40; i++) if (hist[i]) printf(" %d:%llu", i, hist[i]);
  printf("\n");
  return 0;
}

// stage 2: kernel mirror with per-level bands tb (thread safe: bands passed explicitly)
static int ext2(Ent *f, int n, int j, int w, int T, Ent **g, int *gn, int *cap, St *s) {
  return ext(f, n, j, w, T, g, gn, cap, s, 0);
}
static int cov2(Ent *f, int n, int w, int *tb, St *s) {
  if (n == 0 || w >= Lmax) return 0;
  int cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  int ok = 1;
  for (int j = 0; j < 3 && ok; j++) {
    if (ext2(f, n, j, w, tb[w + 1], &g, &gn, &cap, s)) { s->cw++; continue; }
    Ent *h = malloc(sizeof(Ent) * (gn ? gn : 1)); memcpy(h, g, sizeof(Ent) * gn);
    ok = cov2(h, gn, w + 1, tb, s);
    free(h);
  }
  free(g);
  return ok;
}
int cover2(u64 r, int m, int *tb, St *s) {
  int n = 1, cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  Ent *f = malloc(sizeof(Ent) * 64); int fcap = 64;
  memset(f, 0, sizeof(Ent)); f[0].x = r % 3; f[0].p = 1;
  u64 rr = r / 3;
  for (int lev = 1; lev < m; lev++) {
    int j = rr % 3; rr /= 3;
    if (ext2(f, n, j, lev - 1, tb[lev], &g, &gn, &cap, s)) { free(g); free(f); return 1; }
    if (gn > fcap) { fcap = gn; f = realloc(f, sizeof(Ent) * fcap); }
    memcpy(f, g, sizeof(Ent) * gn); n = gn;
  }
  free(g);
  int ok = cov2(f, n, m - 1, tb, s);
  free(f);
  return ok;
}
