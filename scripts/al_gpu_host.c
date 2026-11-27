// al_gpu_host.c: host side of al_gpu (TREE mode of al_vec with the stage 1 on the GPU); see the
// comment at the top of scripts/al_gpu.cu for the build, the usage and the method.
//
// al_vec.c is included verbatim: top(), tree(), frontier(), cover(), cover2() and emitLeaf() are
// al_vec's own code. Per task (class at level `split`) the host computes the root frontier with
// al_vec's frontier(), the GPU (or the CPU reference refTask() below, GPU=0) searches the whole
// task subtree once and returns per-class summaries (T_v and stage-1 work of tree(X) for every
// class X), and treeG() replays tree() on them: same S / L decisions, same hints, same stage-2
// runs (al_vec's cover2), same counters. A task with a failure or a resource flag is rerun by
// al_vec's tree().
#define main al_vec_main
#include "al_vec.c"
#undef main
#include "al_gpu.h"
#include <stdint.h>

static int dmaxv[64];
static int useGPU = 1, checkN = 0, s2cap = 0;
static FILE *dumpf;

// ---------- the record semantics (CPU reference, mirrored by kTasks in al_gpu.cu) ----------
static inline int pmOfMask(u64 mk) {
  int pm = 0, v = 0;
  while (mk) { int pos = __builtin_ctzll(mk); mk &= mk - 1; v++; int dl = P * (pos + 1) - Q * v; if (dl > pm) pm = dl; }
  return pm;
}
static inline int chainCount(unsigned x9, int k, int w, int j, int dm, int *i0o, int *go) {
  int pm3 = (k & 1) ? 2 : 1;
  int u = (x9 + 3 * ((j * pm3) % 3)) % 9;
  if (u % 3 == 0) return 0;
  int i0 = I0[u];
  int d0 = P * k - Q * w + i0 * P;
  if (d0 + P <= Q) return -1;
  int y9 = (u << i0) % 9, g = y9 == 2 ? 2 : 4;
  *i0o = i0; *go = g;
  int dd = d0 + P - Q, c = 0;
  while (dd <= dm) { c++; dd += g * P; g = 6 - g; }
  return c;
}

typedef struct { u64 *x, *m; size_t n, cap; } Buf;
typedef struct { Summ *s; size_t ns, cap; unsigned flags; int task; u64 classes; Buf b[MAXLV][3]; } Ref;

static void refEmit(Ref *R, u64 r, int m, u64 w1rel, int flags, const short *tv) {
  if (R->ns == R->cap) { R->cap = R->cap ? 2 * R->cap : 256; R->s = realloc(R->s, sizeof(Summ) * R->cap); }
  Summ *s = &R->s[R->ns++];
  memset(s, 0, sizeof *s);
  s->r = r; s->w1rel = w1rel; s->task = R->task; s->m = m; s->flags = flags;
  memcpy(s->Tv, tv, sizeof(short) * TVN);
}
static void bufPush(Buf *b, u64 x, u64 m) {
  if (b->n == b->cap) { b->cap = b->cap ? 2 * b->cap : 64; b->x = realloc(b->x, 8 * b->cap); b->m = realloc(b->m, 8 * b->cap); }
  b->x[b->n] = x; b->m[b->n++] = m;
}

// the class r mod 3^m (level d = m - split below the task root) with frontier X/M[0..n)
static void refClass(Ref *R, int d, u64 r, const u64 *X, const u64 *M, size_t n, u64 pathWork, u64 *subOut, short *tvOut) {
  int w = split - 1 + d, m = split + d, dm = dmaxv[w + 1];
  u64 wk[3] = {0, 0, 0}, key[3] = {~0ULL, ~0ULL, ~0ULL};
  R->classes++;
  for (int j = 0; j < 3; j++) R->b[d][j].n = 0;
  for (size_t ii = n; ii-- > 0;) {
    u64 x = X[ii], mk = M[ii];
    unsigned x9 = x % 9; int k = 64 - __builtin_clzll(mk), pm = -1;
    for (int j = 0; j < 3; j++) {
      int i0 = 0, g = 0, c = chainCount(x9, k, w, j, dm, &i0, &g);
      if (c < 0) {
        wk[j] += 2;
        if (pm < 0) pm = pmOfMask(mk);
        u64 kk = ((u64)pm << 32) | (u64)(n - 1 - ii);
        if (kk < key[j]) key[j] = kk;
        continue;
      }
      wk[j] += c + 2;
      if (!c || key[j] != ~0ULL) continue; // a closed j needs no children
      u64 y = (x + ((u64)(3 * j) << k)) << i0; int kk = k + i0;
      for (int q = 0; q < c; q++) {
        if (kk > 59) { R->flags |= TF_OVF; return; }
        bufPush(&R->b[d][j], (2 * y - 1) * 0xAAAAAAAAAAAAAAABULL, mk | (1ULL << kk));
        y <<= g; kk += g; g = 6 - g;
      }
    }
  }
  short tv[TVN]; memset(tv, 0, sizeof tv);
  u64 sub = wk[0] + wk[1] + wk[2];
  int open[3] = {0, 0, 0};
  for (int j = 0; j < 3; j++) {
    if (key[j] != ~0ULL) {
      size_t best = n - 1 - (size_t)(key[j] & 0xffffffffu);
      u64 mk = M[best]; short ctv[TVN]; memset(ctv, 0, sizeof ctv);
      int v = 0;
      while (mk) { int pos = __builtin_ctzll(mk); mk &= mk - 1; v++; ctv[v - 1] = P * (pos + 1) - Q * v; }
      for (int q = 0; q < TVN; q++) if (ctv[q] > tv[q]) tv[q] = ctv[q];
      if (m + 1 <= mmax) refEmit(R, r + j * P3[m], m + 1, pathWork + wk[j], SF_CLOSED, ctv);
    } else if (R->b[d][j].n == 0 || w + 1 >= Lmax) { R->flags |= TF_FAIL; return; }
    else open[j] = 1;
  }
  for (int j = 2; j >= 0; j--) {
    if (!open[j]) continue;
    u64 cs; short ctv[TVN];
    refClass(R, d + 1, r + j * P3[m], R->b[d][j].x, R->b[d][j].m, R->b[d][j].n, pathWork + wk[j], &cs, ctv);
    if (R->flags) return;
    sub += cs;
    for (int q = 0; q < TVN; q++) if (ctv[q] > tv[q]) tv[q] = ctv[q];
  }
  if (m <= mmax) refEmit(R, r, m, pathWork + sub, 0, tv);
  *subOut = sub; memcpy(tvOut, tv, sizeof tv);
}

// ---------- tasks ----------
typedef struct {
  int c; u64 r; unsigned n; u64 rootWork;
  u64 *x, *mk;          // root frontier (freed after the upload)
  unsigned flags;
  Summ *s; size_t ns;   // summaries, sorted by (m, r)
  u64 hw, classes;
} Task;

static void die(const char *m) { fprintf(stderr, "al_gpu: %s\n", m); exit(2); }

// root frontier of the task with al_vec's frontier(), converted to {x, mask}
static void prepTask(Task *t) {
  St s = {0}; Ent *f;
  int n = frontier(t->r, split, &f, &s, 1);
  t->rootWork = s.work; t->x = t->mk = NULL; t->n = 0;
  if (n == -1) die("task closed above split");
  if (n == 0) { t->flags |= TF_FAIL; free(f); return; }
  int w = split - 1;
  t->x = malloc(8 * n); t->mk = malloc(8 * n); t->n = n;
  for (int i = 0; i < n; i++) {
    Ent *e = &f[i];
    if (e->x >> 64 || e->p == 0 || (e->p & (e->p - 1))) { t->flags |= TF_OVF; break; }
    int k = 0; u128 p = e->p; while (p > 1) { p >>= 1; k++; }
    if (k > 60 || e->x >= 3 * e->p) { t->flags |= TF_OVF; break; }
    if (e->d != P * k - Q * w) die("entry deficit != P k - Q w");
    u64 mk = 0; int prev = 0, pm = 0;
    for (int v = 1; v <= w; v++) {
      int num = e->dl[v] + Q * v;
      if (num % P) die("dl not of the form P k - Q v");
      int kv = num / P;
      if (kv <= prev || kv > 60) die("dl exponents not increasing");
      mk |= 1ULL << (kv - 1); prev = kv;
      if (e->dl[v] > pm) pm = e->dl[v];
    }
    if (prev != k || pm != e->pm) die("mask conversion mismatch");
    t->x[i] = (u64)e->x; t->mk[i] = mk;
  }
  free(f);
}

static int cmpS(const void *a, const void *b) {
  const Summ *x = a, *y = b;
  if (x->m != y->m) return x->m < y->m ? -1 : 1;
  return x->r < y->r ? -1 : x->r > y->r;
}
static Summ *findS(Task *t, u64 r, int m) {
  size_t lo = 0, hi = t->ns;
  while (lo < hi) {
    size_t mid = (lo + hi) / 2; Summ *s = &t->s[mid];
    if (s->m < m || (s->m == m && s->r < r)) lo = mid + 1; else hi = mid;
  }
  if (lo < t->ns && t->s[lo].m == m && t->s[lo].r == r) return &t->s[lo];
  return NULL;
}

// ---------- stage 2 with a cap (S2CAP=1; only used for the predicate work > W0 of split nodes) ----------
// copies of ext (full = 0), cov2 and cover2 of al_vec.c that stop (return 2) once s->work > W0
static int extc(Ent *f, int n, int j, int w, int T, Ent **g, int *gn, int *cap, St *s) {
  *gn = 0;
  for (int i = n - 1; i >= 0; i--) {
    u128 y = f[i].x + (u128)3 * j * f[i].p, p = f[i].p;
    int i0 = I0[(int)(y % 9)];
    y <<= i0; p <<= i0; int d = f[i].d + i0 * P;
    for (;;) {
      s->work++;
      if (s->work > W0) return 2;
      int y9 = (int)(y % 9);
      if (y9 != 2 && y9 != 8) break;
      if (d + P <= Q) return 1;
      if (!useful(d + P - Q, w + 1, T)) break;
      if (*gn == *cap) { *cap *= 2; *g = realloc(*g, sizeof(Ent) * *cap); }
      Ent *e = &(*g)[(*gn)++];
      e->x = (2 * y - 1) / 3; e->p = 2 * p; e->d = d + P - Q;
      s->ent++;
      int gg = y9 == 2 ? 2 : 4;
      y <<= gg; p <<= gg; d += gg * P;
    }
    s->work++;
    if (s->work > W0) return 2;
  }
  return 0;
}
static int cov2c(Ent *f, int n, int w, int *tb, St *s) {
  if (n == 0 || w >= Lmax) return 0;
  int cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  int ok = 1;
  for (int j = 0; j < 3 && ok == 1; j++) {
    int e = extc(f, n, j, w, tb[w + 1], &g, &gn, &cap, s);
    if (e == 2) { ok = 2; break; }
    if (e) { s->cw++; continue; }
    Ent *h = malloc(sizeof(Ent) * (gn ? gn : 1)); memcpy(h, g, sizeof(Ent) * gn);
    ok = cov2c(h, gn, w + 1, tb, s);
    free(h);
  }
  free(g);
  return ok;
}
// returns 1 iff the stage-2 work of cover2(r, m, tb) exceeds W0
static int over2(u64 r, int m, int *tb) {
  St st = {0}, *s = &st;
  int n = 1, cap = 64, gn; Ent *g = malloc(sizeof(Ent) * cap);
  Ent *f = malloc(sizeof(Ent) * 64); int fcap = 64;
  memset(f, 0, sizeof(Ent)); f[0].x = r % 3; f[0].p = 1;
  u64 rr = r / 3;
  for (int lev = 1; lev < m; lev++) {
    int j = rr % 3; rr /= 3;
    int e = extc(f, n, j, lev - 1, tb[lev], &g, &gn, &cap, s);
    if (e) { free(g); free(f); return e == 2; }
    if (gn > fcap) { fcap = gn; f = realloc(f, sizeof(Ent) * fcap); }
    memcpy(f, g, sizeof(Ent) * gn); n = gn;
  }
  free(g);
  int ok = cov2c(f, n, m - 1, tb, s);
  free(f);
  return ok == 2;
}

// ---------- tree() replayed on the summaries ----------
static u64 nCheck, nCheckBad, nMissing;
static void checkNode(u64 r, int m, int *tb, u64 w1, int closed) {
  St s = {0}; Ent *f;
  int n = frontier(r, m, &f, &s, 1), ok = 1;
  if (n != -1) ok = cover(f, n, m - 1, &s, 1);
  free(f);
  int bad = s.work != w1 || (n == -1) != closed || !ok;
  for (int v = 0; v < LW; v++) if (s.Tv[v] != tb[v]) bad = 1;
  #pragma omp atomic
  nCheck++;
  if (bad) {
    #pragma omp atomic
    nCheckBad++;
    #pragma omp critical(chk)
    fprintf(stderr, "CHECK MISMATCH r=%llu m=%d work %llu vs %llu closed %d vs %d ok=%d\n", r, m, s.work, w1, n == -1, closed, ok);
  }
}

static void treeG(Task *t, u64 r, int m, Ad *a) {
  Summ *S = findS(t, r, m);
  if (!S) { // cannot happen (every class up to mmax has a summary); al_vec's own tree() is exact
    #pragma omp atomic
    nMissing++;
    tree(r, m, a); return;
  }
  int tb[LW]; memset(tb, 0, sizeof tb);
  for (int v = 1; v <= TVN && v < LW; v++) tb[v] = S->Tv[v - 1];
  u64 w1 = t->rootWork + S->w1rel;
  int closed = S->flags & SF_CLOSED;
  if (checkN) {
    u64 h = r * 64 + m; h ^= h >> 30; h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 27; h *= 0x94D049BB133111EBULL; h ^= h >> 31;
    if (h % checkN == 0) checkNode(r, m, tb, w1, closed);
  }
  if (closed) { // tree()'s n == -1 branch
    St s2 = {0}; int ok2 = cover2(r, m, tb, &s2);
    a->w1 += w1; a->w2 += s2.work; a->chunks++; a->fail += !ok2;
    emitLeaf(r, m, tb, ok2, s2.work);
    return;
  }
  a->w1 += w1;
  if (s2cap && m < mmax) {
    if (over2(r, m, tb)) {
      #pragma omp critical
      printf("S %llu %d\n", r, m);
      for (int j = 0; j < 3; j++) treeG(t, r + j * P3[m], m + 1, a);
      return;
    }
  }
  St s2 = {0}; int ok2 = cover2(r, m, tb, &s2);
  if (s2.work > W0 && m < mmax) {
    #pragma omp critical
    printf("S %llu %d\n", r, m);
    for (int j = 0; j < 3; j++) treeG(t, r + j * P3[m], m + 1, a);
    return;
  }
  a->w2 += s2.work; a->cw += s2.cw; a->chunks++; a->fail += !ok2;
  if (s2.work > W0) a->big++;
  emitLeaf(r, m, tb, ok2, s2.work);
}

static void dumpTask(Task *t) {
  if (!dumpf) return;
  #pragma omp critical(dump)
  {
    for (size_t i = 0; i < t->ns; i++) {
      Summ *s = &t->s[i];
      fprintf(dumpf, "%llu %llu %d %d %llu ", t->r, s->r, s->m, s->flags, t->rootWork + s->w1rel);
      for (int v = 0; v < TVN; v++) fprintf(dumpf, "%d,", s->Tv[v]);
      fprintf(dumpf, "\n");
    }
  }
}

static u64 nFallback, nFail;
static void finishTask(Task *t, Ad *a) {
  if (t->flags) {
    #pragma omp atomic
    nFallback++;
    if (t->flags & TF_FAIL) {
      #pragma omp atomic
      nFail++;
    }
    tree(t->r, split, a);
  } else {
    qsort(t->s, t->ns, sizeof(Summ), cmpS);
    dumpTask(t);
    treeG(t, t->r, split, a);
  }
  free(t->s); t->s = NULL; t->ns = 0;
}

static void refTask(Task *t) {
  if (t->flags) return;
  Ref *R = calloc(1, sizeof(Ref));
  R->task = 0;
  u64 sub; short tv[TVN];
  refClass(R, 0, t->r, t->x, t->mk, t->n, 0, &sub, tv);
  t->flags |= R->flags; t->s = R->s; t->ns = R->ns; t->classes = R->classes;
  for (int d = 0; d < MAXLV; d++) for (int j = 0; j < 3; j++) { free(R->b[d][j].x); free(R->b[d][j].m); }
  free(R);
}

static int envi(const char *n, int dflt) { const char *s = getenv(n); return s ? atoi(s) : dflt; }

#ifndef NOGPU
// launch the tasks t[0..nt) on the GPU (asynchronously)
typedef struct { Task *t; int nt; } Batch;
static TaskIn *bTin; static u64 *bX, *bM; static size_t bTcap, bXcap;
static int gBlocks;
static void launchTasks(Task **ts, int nt, int blocks) {
  if ((size_t)nt > bTcap) { bTcap = nt; bTin = realloc(bTin, sizeof(TaskIn) * bTcap); }
  size_t nin = 0;
  for (int i = 0; i < nt; i++) nin += ts[i]->n;
  if (nin > bXcap) { bXcap = nin; bX = realloc(bX, 8 * bXcap); bM = realloc(bM, 8 * bXcap); }
  size_t o = 0;
  for (int i = 0; i < nt; i++) {
    Task *t = ts[i];
    bTin[i].r = t->r; bTin[i].inOff = o; bTin[i].n = t->n; bTin[i].pad = 0;
    memcpy(bX + o, t->x, 8 * t->n); memcpy(bM + o, t->mk, 8 * t->n); o += t->n;
  }
  gpu_launch(nt, bTin, bX, bM, nin ? nin : 1, blocks);
}
static Summ *hPool; static TaskOut *hOut; static size_t hOutCap;
static double gpuMs; static u64 gpuSumm, gpuClasses, gpuHw, nRetry;
// wait for the launch of ts[0..nt); distribute the summaries; returns the tasks to retry
static int collect(Task **ts, int nt, Task **retry) {
  if ((size_t)nt > hOutCap) { hOutCap = nt; hOut = realloc(hOut, sizeof(TaskOut) * hOutCap); }
  double ms;
  u64 cnt = gpu_wait(hOut, nt, hPool, gpu_pool_cap(), &ms);
  gpuMs += ms;
  u64 c = cnt < gpu_pool_cap() ? cnt : gpu_pool_cap();
  size_t *num = calloc(nt + 1, sizeof(size_t));
  for (u64 i = 0; i < c; i++) num[hPool[i].task]++;
  for (int i = 0; i < nt; i++) {
    Task *t = ts[i];
    t->flags |= hOut[i].flags; t->hw = hOut[i].hw; t->classes = hOut[i].classes;
    if (t->hw > gpuHw) gpuHw = t->hw;
    if (!t->flags) { t->s = malloc(sizeof(Summ) * (num[i] ? num[i] : 1)); t->ns = 0; }
  }
  for (u64 i = 0; i < c; i++) { Task *t = ts[hPool[i].task]; if (!t->flags) t->s[t->ns++] = hPool[i]; }
  int nr = 0;
  for (int i = 0; i < nt; i++) {
    Task *t = ts[i];
    gpuClasses += t->classes;
    if (!t->flags) { gpuSumm += t->ns; continue; }
    if ((t->flags & (TF_ARENA | TF_QUOTA)) && !(t->flags & (TF_FAIL | TF_OVF))) { retry[nr++] = t; }
  }
  free(num);
  return nr;
}
// finish a launched batch: collect, rerun arena/quota-flagged tasks (alone or in small groups,
// with a large arena per block); tasks still flagged go to the CPU fallback
static void finishGPU(Task **ts, int nt) {
  Task **retry = malloc(sizeof(Task *) * nt);
  int nr = collect(ts, nt, retry);
  int blocks = gBlocks, group = nt;
  while (nr) {
    nRetry += nr;
    int arena = 0; for (int i = 0; i < nr; i++) if (retry[i]->flags & TF_ARENA) arena = 1;
    if (arena) blocks = blocks / 4 > 0 ? blocks / 4 : 1; // a larger arena per block
    else group = group / 2 > 0 ? group / 2 : 1;          // fewer tasks share the summary pool
    if (group > nr) group = nr;
    int nn = 0; Task **next = malloc(sizeof(Task *) * (size_t)(nr > 0 ? nr : 1));
    for (int g0 = 0; g0 < nr; g0 += group) {
      int gn = nr - g0 < group ? nr - g0 : group;
      for (int i = 0; i < gn; i++) retry[g0 + i]->flags = 0;
      launchTasks(retry + g0, gn, blocks < gn ? blocks : gn);
      nn += collect(retry + g0, gn, next + nn);
    }
    int stuck = nn == nr && (arena ? blocks == 1 : group == 1);
    memcpy(retry, next, sizeof(Task *) * nn); nr = nn; free(next);
    if (stuck) break; // CPU fallback for the rest (flags kept)
  }
  free(retry);
}
#endif

static int cmpTaskN(const void *a, const void *b) {
  const Task *x = a, *y = b;
  return x->n > y->n ? -1 : x->n < y->n;
}

int main(int argc, char **argv) {
  if (!getenv("TREE")) return al_vec_main(argc, argv);
  P = atoi(argv[1]); Q = atoi(argv[2]); D = atoi(argv[3]); split = atoi(argv[4]); Lmax = atoi(argv[5]);
  Tbig = atoi(argv[6]); int sample = atoi(argv[7]);
  sscanf(getenv("TREE"), "%llu %d", &W0, &mmax);
  P3[0] = 1; for (int i = 1; i <= 40; i++) P3[i] = P3[i - 1] * 3;
  int off = getenv("OFFSET") ? atoi(getenv("OFFSET")) : 0;
  Ad tot = {0}; double t0 = omp_get_wtime();
  printf("# TREE P=%d Q=%d D=%d split=%d Lmax=%d Tbig=%d W0=%llu mmax=%d sample=%d offset=%d\n",
         P, Q, D, split, Lmax, Tbig, W0, mmax, sample, off);
  if (D < 1 || D > 60) die("needs 1 <= D <= 60 (u64 entries)");
  if (Lmax > TVN + 1 || Lmax + 1 >= 64 || Lmax - split + 2 > MAXLV || split < 2) die("needs split >= 2, Lmax <= TVN + 1, Lmax - split + 2 <= MAXLV");
  if (Q <= P || mmax > 40) die("needs Q > P, mmax <= 40");
  useGPU = envi("GPU", 1); checkN = envi("CHECK", 0); s2cap = envi("S2CAP", 0);
  if (getenv("DUMP")) dumpf = fopen(getenv("DUMP"), "w");
#ifdef NOGPU
  useGPU = 0;
#endif
  // useful(d, w, Tbig) for d >= 1 is d <= dmax[w] (monotone in d)
  for (int w = 1; w <= Lmax; w++) {
    int dm = 0;
    for (int d = 1; d <= Tbig + 1; d++) {
      int u = useful(d, w, Tbig);
      if (u && d != dm + 1) die("useful() not monotone in d");
      if (u) dm = d;
    }
    dmaxv[w] = dm;
  }
  top(1, 1, off == 0, &tot); top(2, 1, off == 0, &tot);
  fflush(stdout);
  int nt = 0;
  for (int c = off; c < ntk; c += sample) nt++;
  Task *T = calloc(nt ? nt : 1, sizeof(Task));
  for (int i = 0; i < nt; i++) { T[i].c = off + i * sample; T[i].r = tk[off + i * sample]; }
  double tp = omp_get_wtime(); (void)tp;
  if (!useGPU) {
    #pragma omp parallel
    {
      Ad a = {0};
      #pragma omp for schedule(dynamic, 1)
      for (int i = 0; i < nt; i++) {
        prepTask(&T[i]); refTask(&T[i]);
        free(T[i].x); free(T[i].mk); T[i].x = T[i].mk = NULL;
        finishTask(&T[i], &a);
      }
      #pragma omp critical
      { tot.w1 += a.w1; tot.w2 += a.w2; tot.cw += a.cw; tot.chunks += a.chunks; tot.big += a.big; tot.fail += a.fail; }
    }
  }
#ifndef NOGPU
  else {
    // order: largest root frontier first (sizes from a first pass)
    #pragma omp parallel for schedule(dynamic, 16)
    for (int i = 0; i < nt; i++) { St s = {0}; Ent *f; int n = frontier(T[i].r, split, &f, &s, 1); free(f); T[i].n = n > 0 ? n : 0; }
    qsort(T, nt, sizeof(Task), cmpTaskN);
    for (int i = 0; i < nt; i++) T[i].n = 0;
    GParams gp; memset(&gp, 0, sizeof gp);
    gp.P = P; gp.Q = Q; gp.D = D; gp.Lmax = Lmax; gp.split = split; gp.mmax = mmax;
    for (int w = 0; w < 64; w++) gp.dmax[w] = w <= Lmax ? dmaxv[w] : 0;
    for (int i = 0; i <= 40; i++) gp.P3[i] = P3[i];
    u64 pool = getenv("GPU_REC") ? strtoull(getenv("GPU_REC"), 0, 10) : 4000000ULL;
    u64 arena = getenv("GPU_ARENA") ? strtoull(getenv("GPU_ARENA"), 0, 10) : 0;
    gpu_init(&gp, arena, pool);
    gBlocks = envi("GPU_BLOCKS", 272);
    hPool = malloc(sizeof(Summ) * pool);
    int bs = envi("GPU_BATCH", 1024);
    int nb = (nt + bs - 1) / bs;
    fprintf(stderr, "al_gpu: %d tasks, %d batches, blocks=%d arena/block=%llu pool=%llu, prep %.1fs\n",
            nt, nb, gBlocks, gpu_arena_total() / gBlocks, pool, omp_get_wtime() - tp);
    Task **ptr = malloc(sizeof(Task *) * (nt ? nt : 1));
    for (int i = 0; i < nt; i++) ptr[i] = &T[i];
    double tq = omp_get_wtime();
    // pipeline: prep(b+1) and stage 2 of b on the CPU while the GPU runs the next batch
    #define BLO(b) ((b) * bs)
    #define BN(b) ((b) + 1 < nb ? bs : nt - (b) * bs)
    if (nb) {
      #pragma omp parallel for schedule(dynamic, 4)
      for (int i = 0; i < BN(0); i++) prepTask(ptr[i]);
      launchTasks(ptr, BN(0), gBlocks);
    }
    for (int b = 0; b < nb; b++) {
      if (b + 1 < nb) {
        #pragma omp parallel for schedule(dynamic, 4)
        for (int i = 0; i < BN(b + 1); i++) prepTask(ptr[BLO(b + 1) + i]);
      }
      double tw = omp_get_wtime();
      finishGPU(ptr + BLO(b), BN(b));
      double tw2 = omp_get_wtime();
      for (int i = 0; i < BN(b); i++) { free(ptr[BLO(b) + i]->x); free(ptr[BLO(b) + i]->mk); ptr[BLO(b) + i]->x = ptr[BLO(b) + i]->mk = NULL; }
      if (b + 1 < nb) launchTasks(ptr + BLO(b + 1), BN(b + 1), gBlocks);
      #pragma omp parallel
      {
        Ad a = {0};
        #pragma omp for schedule(dynamic, 1)
        for (int i = 0; i < BN(b); i++) finishTask(ptr[BLO(b) + i], &a);
        #pragma omp critical
        { tot.w1 += a.w1; tot.w2 += a.w2; tot.cw += a.cw; tot.chunks += a.chunks; tot.big += a.big; tot.fail += a.fail; }
      }
      fflush(stdout);
      fprintf(stderr, "al_gpu: batch %d/%d tasks=%d gpu=%.1fs(total) wait=%.1fs stage2=%.1fs summ=%llu classes=%llu hw=%llu retry=%llu fallback=%llu t=%.0fs\n",
              b + 1, nb, BN(b), gpuMs / 1000, tw2 - tw, omp_get_wtime() - tw2, gpuSumm, gpuClasses, gpuHw, nRetry, nFallback, omp_get_wtime() - tq);
    }
  }
#endif
  if (dumpf) fclose(dumpf);
  fprintf(stderr, "al_gpu: fallback tasks=%llu (fail %llu) missing=%llu check=%llu bad=%llu\n", nFallback, nFail, nMissing, nCheck, nCheckBad);
  printf("# done tasks=%d stage1=%llu kernel=%llu leaves=%llu overW0=%llu fail=%llu time=%.0fs\n",
         ntk, tot.w1, tot.w2, tot.chunks, tot.big, tot.fail, omp_get_wtime() - t0);
  return tot.fail || nCheckBad ? 1 : 0;
}
