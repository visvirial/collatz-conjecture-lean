// al_gpu.cu: GPU stage 1 for scripts/al_vec.c in TREE mode (same arguments, same output).
//
// Build (scripts/al_gpu.mk; on a host with CUDA, e.g. sm_86):
//   gcc -O3 -fopenmp -c scripts/al_gpu_host.c -o al_gpu_host.o
//   /usr/local/cuda/bin/nvcc -O3 -arch=sm_86 -Xcompiler -fopenmp scripts/al_gpu.cu al_gpu_host.o -o al_gpu
// CPU-only build of the same algorithm (no CUDA): gcc -O3 -fopenmp -DNOGPU scripts/al_gpu_host.c -o al_s1ref
//
// Usage, identical to al_vec:  TREE="W0 mmax" [OFFSET=o] ./al_gpu P Q D split Lmax Tbig sample
//   The stdout is the same set of lines as al_vec's (line order differs, as between two al_vec
//   runs), the `# done` line included (except time=). Without TREE, al_gpu runs al_vec's main.
//   Measured on an RTX 3080 + 4 CPU threads: 28/59 full tree ("28 59 60 11 40 420 1", TREE="100000 34")
//   127 s with S2CAP=1 (375 s without) vs 7610 s for al_vec on 28 threads, output identical.
//   Env: GPU=0       stage 1 by the CPU reference (same records, one task per thread)
//        GPU_BLOCKS  resident blocks (default 4 per SM); GPU_REC summary pool (default 4M);
//        GPU_ARENA   total arena entries (default: most of the free memory); GPU_BATCH tasks per
//                    batch (default 1024); CHECK=n re-runs al_vec's stage 1 (frontier + cover) on
//                    every n-th tree node and compares T_v and the work; S2CAP=1 stops the stage-2
//                    run of a node at W0 + 1 steps when only `work > W0` is needed (split nodes);
//                    DUMP=file writes all summaries (for GPU vs CPU-reference comparisons).
//
// What the GPU does (soundness does not depend on it: hints only steer the kernel search, and
// every leaf is checked by the unchanged CPU kernel mirror cover2 of al_vec.c):
//   For a task (a non-closed class r mod 3^split) the stage 1 of al_vec's tree() at a node X is a
//   full search (band Tbig, no early exit) of X's subtree; X's hints T_v are the maximum over the
//   closed exts of the subtree of the closing path's entry deficits, its work is the descent work
//   plus the subtree work. One DFS of the task subtree gives these for every class X at once
//   (al_vec repeats the search at every split depth). The GPU runs one task per block: per class,
//   pass A counts, for each entry and j, the children (or the closing), the work and the best
//   closing entry (min max deficit, ties: largest index, as al_vec's ext); pass C writes the
//   children of the open j in al_vec's list order (block scan over the entries in reverse order).
//   Entries are {x (u64), mask (u64)}: the deficit list dl of al_vec is rebuilt from the mask
//   (dl[v] = P (pos_v + 1) - Q v), k = 64 - clz(mask), d = P k - Q w. x < 3 * 2^k and the child
//   exponent is <= D <= 60, so every y used to make a child is < 9 * 2^59 and 2y - 1 fits in u64.
//   The host (al_gpu_host.c) turns the summaries into exactly al_vec's tree() decisions; tasks
//   with a failure (an empty or too deep open class) or a GPU resource flag are rerun by al_vec's
//   own tree() on the CPU.
#include <cstdio>
#include <cstdlib>
#include <cub/block/block_scan.cuh>
#include "al_gpu.h"

#define BT 256
#define CK(x) do { cudaError_t e_ = (x); if (e_ != cudaSuccess) { fprintf(stderr, "CUDA %s at %s:%d\n", cudaGetErrorString(e_), __FILE__, __LINE__); exit(3); } } while (0)

__constant__ int cP, cQ, cLmax, cSplit, cMmax;
__constant__ int cDmax[64];
__constant__ u64 cP3[41];
__constant__ int cI0[9] = {0, 1, 0, 0, 1, 2, 0, 3, 0};

enum { CS_NONE = 0, CS_OPEN = 1, CS_CLOSED = 2 };

struct Lv {
  u64 r, pathWork, subWork;
  unsigned off, n;
  int nextj;
  unsigned coff[3], cn[3];
  u64 cwork[3];
  int cst[3];
};

typedef cub::BlockScan<u64, BT> Scan;
struct Sh {
  Lv lv[MAXLV];
  short tv[MAXLV][TVN];
  unsigned long long work[3], key[3];
  unsigned cnt[3];
  unsigned flags, tot;
  u64 hw, classes;
  int go, task;
  typename Scan::TempStorage scan;
};

__device__ __forceinline__ unsigned mod9(u64 x) {
  unsigned hi = (unsigned)(x >> 32), lo = (unsigned)x;
  return (4 * (hi % 9) + lo % 9) % 9; // 2^32 = 4 mod 9
}

__device__ __forceinline__ int pmOf(u64 mk) {
  int pm = 0, v = 0;
  while (mk) { int pos = __ffsll((long long)mk) - 1; mk &= mk - 1; v++; int dl = cP * (pos + 1) - cQ * v; if (dl > pm) pm = dl; }
  return pm;
}

// the chain of entry (x9, k) at weight w for digit j: returns the child count c (>= 0), or -1 if
// the entry closes; *i0o, *go: the first shift and the first chain step
__device__ __forceinline__ int chainCount(unsigned x9, int k, int w, int j, int dm, int *i0o, int *go) {
  int pm3 = (k & 1) ? 2 : 1;
  int u = (x9 + 3 * ((j * pm3) % 3)) % 9;
  if (u % 3 == 0) return 0;
  int i0 = cI0[u];
  int d0 = cP * k - cQ * w + i0 * cP;
  if (d0 + cP <= cQ) return -1;
  int y9 = (u << i0) % 9;
  int g = y9 == 2 ? 2 : 4;
  *i0o = i0; *go = g;
  int dd = d0 + cP - cQ, c = 0;
  while (dd <= dm) { c++; dd += g * cP; g = 6 - g; }
  return c;
}

__device__ void emitSumm(Sh &sh, Summ *pool, u64 cap, unsigned long long *poolCnt, int task, u64 r, int m,
                         u64 w1rel, int flags, const short *tv) {
  unsigned long long idx = atomicAdd(poolCnt, 1ULL);
  if (idx >= cap) { sh.flags |= TF_QUOTA; return; }
  Summ *s = &pool[idx];
  s->r = r; s->w1rel = w1rel; s->task = task; s->m = (unsigned char)m; s->flags = (unsigned char)flags; s->pad = 0;
  for (int v = 0; v < TVN; v++) s->Tv[v] = tv[v];
}

// expand the class at level d: records for j = 0..2, child frames of the open j (compacted to the
// class's own arena position, j = 0 first)
__device__ void expand(Sh &sh, int d, u64 *X, u64 *M, u64 E, Summ *pool, u64 cap, unsigned long long *poolCnt) {
  int tid = threadIdx.x;
  Lv &L = sh.lv[d];
  const unsigned off = L.off, n = L.n;
  const int w = cSplit - 1 + d, m = cSplit + d;
  const int dm = cDmax[w + 1];
  if (tid < 3) { sh.work[tid] = 0; sh.key[tid] = ~0ULL; sh.cnt[tid] = 0; }
  __syncthreads();
  // pass A
  u64 wk[3] = {0, 0, 0}, key[3] = {~0ULL, ~0ULL, ~0ULL};
  unsigned cc[3] = {0, 0, 0};
  for (unsigned i = tid; i < n; i += BT) {
    u64 mk = M[off + i];
    unsigned x9 = mod9(X[off + i]);
    int k = 64 - __clzll((long long)mk);
    int pm = -1;
#pragma unroll
    for (int j = 0; j < 3; j++) {
      int i0, g;
      int c = chainCount(x9, k, w, j, dm, &i0, &g);
      if (c < 0) {
        wk[j] += 2;
        if (pm < 0) pm = pmOf(mk);
        u64 kk = ((u64)pm << 32) | (u64)(n - 1 - i);
        if (kk < key[j]) key[j] = kk;
      } else { wk[j] += c + 2; cc[j] += c; }
    }
  }
#pragma unroll
  for (int j = 0; j < 3; j++) {
    for (int o = 16; o > 0; o >>= 1) {
      wk[j] += __shfl_down_sync(0xffffffffu, wk[j], o);
      cc[j] += __shfl_down_sync(0xffffffffu, cc[j], o);
      u64 ok = __shfl_down_sync(0xffffffffu, key[j], o);
      if (ok < key[j]) key[j] = ok;
    }
    if ((tid & 31) == 0) {
      if (wk[j]) atomicAdd(&sh.work[j], (unsigned long long)wk[j]);
      if (cc[j]) atomicAdd(&sh.cnt[j], cc[j]);
      if (key[j] != ~0ULL) atomicMin(&sh.key[j], (unsigned long long)key[j]);
    }
  }
  __syncthreads();
  if (tid == 0) {
    sh.classes++;
    unsigned top = off + n, tot = 0;
    for (int j = 0; j < 3; j++) {
      L.cwork[j] = sh.work[j]; L.subWork += sh.work[j];
      L.cst[j] = CS_NONE; L.cn[j] = 0; L.coff[j] = top + tot;
      if (sh.key[j] != ~0ULL) {
        L.cst[j] = CS_CLOSED;
        unsigned best = n - 1 - (unsigned)(sh.key[j] & 0xffffffffu);
        u64 mk = M[off + best];
        short ctv[TVN];
        for (int v = 0; v < TVN; v++) ctv[v] = 0;
        int v = 0;
        while (mk) { int pos = __ffsll((long long)mk) - 1; mk &= mk - 1; v++; ctv[v - 1] = (short)(cP * (pos + 1) - cQ * v); }
        for (int q = 0; q < TVN; q++) if (ctv[q] > sh.tv[d][q]) sh.tv[d][q] = ctv[q];
        if (m + 1 <= cMmax) emitSumm(sh, pool, cap, poolCnt, sh.task, L.r + (u64)j * cP3[m], m + 1, L.pathWork + sh.work[j], SF_CLOSED, ctv);
      } else if (sh.cnt[j] == 0 || w + 1 >= cLmax) {
        sh.flags |= TF_FAIL;
      } else {
        L.cst[j] = CS_OPEN; L.cn[j] = sh.cnt[j]; tot += sh.cnt[j];
      }
    }
    if ((u64)top + tot > E) sh.flags |= TF_ARENA;
    if ((u64)top + tot > sh.hw) sh.hw = (u64)top + tot;
    sh.tot = tot;
  }
  __syncthreads();
  if (sh.flags || sh.tot == 0) return;
  // pass C: children in al_vec's order (entries n-1 .. 0, chain order within an entry)
  const unsigned top = off + n, tot = sh.tot;
  int op[3]; unsigned co[3];
#pragma unroll
  for (int j = 0; j < 3; j++) { op[j] = L.cst[j] == CS_OPEN; co[j] = L.coff[j]; }
  unsigned carry[3] = {0, 0, 0};
  const u64 M21 = (1ULL << 21) - 1;
  for (unsigned b = 0; b < n; b += BT) {
    unsigned t = b + tid;
    bool valid = t < n;
    unsigned i = n - 1 - t;
    u64 x = 0, mk = 0; int k = 0; unsigned x9 = 0;
    int c[3] = {0, 0, 0}, i0s[3] = {0, 0, 0}, gs[3] = {0, 0, 0};
    if (valid) {
      x = X[off + i]; mk = M[off + i]; x9 = mod9(x); k = 64 - __clzll((long long)mk);
#pragma unroll
      for (int j = 0; j < 3; j++) if (op[j]) { int cj = chainCount(x9, k, w, j, dm, &i0s[j], &gs[j]); c[j] = cj > 0 ? cj : 0; }
    }
    u64 v = (u64)c[0] | ((u64)c[1] << 21) | ((u64)c[2] << 42), pre, agg;
    Scan(sh.scan).ExclusiveSum(v, pre, agg);
    if (valid) {
#pragma unroll
      for (int j = 0; j < 3; j++) {
        if (!c[j]) continue;
        unsigned pos = co[j] + carry[j] + (unsigned)((pre >> (21 * j)) & M21);
        u64 y = (x + ((u64)(3 * j) << k)) << i0s[j];
        int kk = k + i0s[j], g = gs[j];
        for (int q = 0; q < c[j]; q++) {
          if (kk > 59) atomicOr(&sh.flags, (unsigned)TF_OVF); // unreachable: the host asserts D <= 60
          u64 xc = (2 * y - 1) * 0xAAAAAAAAAAAAAAABULL;
          X[pos + q] = xc; M[pos + q] = mk | (1ULL << kk);
          y <<= g; kk += g; g = 6 - g;
        }
      }
    }
#pragma unroll
    for (int j = 0; j < 3; j++) carry[j] += (unsigned)((agg >> (21 * j)) & M21);
    __syncthreads();
  }
  // compaction: [top, top + tot) -> [off, off + tot)
  if (tot <= n) {
    for (unsigned q = tid; q < tot; q += BT) { X[off + q] = X[top + q]; M[off + q] = M[top + q]; }
  } else {
    for (unsigned b = 0; b < tot; b += BT) {
      unsigned q = b + tid; u64 a = 0, bb = 0;
      if (q < tot) { a = X[top + q]; bb = M[top + q]; }
      __syncthreads();
      if (q < tot) { X[off + q] = a; M[off + q] = bb; }
    }
  }
  if (tid == 0) for (int j = 0; j < 3; j++) L.coff[j] -= n;
  __syncthreads();
}

__global__ void __launch_bounds__(BT) kTasks(int nt, const TaskIn *__restrict__ tin, const u64 *__restrict__ xin,
                                             const u64 *__restrict__ min, u64 *AX, u64 *AM, u64 E, Summ *pool, u64 cap,
                                             unsigned long long *poolCnt, unsigned *jobCnt, TaskOut *tout) {
  __shared__ Sh sh;
  int tid = threadIdx.x;
  u64 *X = AX + (u64)blockIdx.x * E, *M = AM + (u64)blockIdx.x * E;
  for (;;) {
    if (tid == 0) sh.task = (int)atomicAdd(jobCnt, 1u);
    __syncthreads();
    int task = sh.task;
    if (task >= nt) return;
    TaskIn ti = tin[task];
    if (tid == 0) {
      sh.flags = (u64)ti.n > E ? TF_ARENA : 0; sh.hw = ti.n; sh.classes = 0;
      Lv &L = sh.lv[0];
      L.r = ti.r; L.pathWork = 0; L.subWork = 0; L.off = 0; L.n = ti.n; L.nextj = 2;
    }
    for (int v = tid; v < TVN; v += BT) sh.tv[0][v] = 0;
    __syncthreads();
    if (!sh.flags) {
      for (unsigned q = tid; q < ti.n; q += BT) { X[q] = xin[ti.inOff + q]; M[q] = min[ti.inOff + q]; }
      __syncthreads();
      int d = 0;
      expand(sh, 0, X, M, E, pool, cap, poolCnt);
      while (!sh.flags) {
        if (tid == 0) {
          Lv &L = sh.lv[d];
          int j = -1;
          while (L.nextj >= 0) { int jj = L.nextj--; if (L.cst[jj] == CS_OPEN) { j = jj; break; } }
          if (j >= 0) {
            Lv &C = sh.lv[d + 1];
            C.r = L.r + (u64)j * cP3[cSplit + d]; C.pathWork = L.pathWork + L.cwork[j]; C.subWork = 0;
            C.off = L.coff[j]; C.n = L.cn[j]; C.nextj = 2;
            sh.go = 1;
          } else {
            sh.go = 0;
            if (cSplit + d <= cMmax) emitSumm(sh, pool, cap, poolCnt, task, L.r, cSplit + d, L.pathWork + L.subWork, 0, sh.tv[d]);
            if (d > 0) sh.lv[d - 1].subWork += L.subWork;
          }
        }
        __syncthreads();
        if (sh.go) {
          d++;
          for (int v = tid; v < TVN; v += BT) sh.tv[d][v] = 0;
          __syncthreads();
          expand(sh, d, X, M, E, pool, cap, poolCnt);
        } else {
          if (d == 0) break;
          for (int v = tid; v < TVN; v += BT) if (sh.tv[d][v] > sh.tv[d - 1][v]) sh.tv[d - 1][v] = sh.tv[d][v];
          d--;
          __syncthreads();
        }
      }
    }
    __syncthreads();
    if (tid == 0) { TaskOut o; o.flags = sh.flags; o.nsumm = 0; o.hw = sh.hw; o.classes = sh.classes; tout[task] = o; }
    __syncthreads();
  }
}

// ---- host wrappers ----
static u64 *dAX, *dAM, *dXin, *dMin, gArena, gInCap;
static Summ *dPool; static u64 gPoolCap;
static unsigned long long *dPoolCnt; static unsigned *dJob;
static TaskIn *dTin; static TaskOut *dTout; static int gTcap;
static cudaEvent_t ev0, ev1;

extern "C" u64 gpu_arena_total(void) { return gArena; }
extern "C" u64 gpu_pool_cap(void) { return gPoolCap; }

extern "C" int gpu_init(const GParams *g, u64 arenaTotal, u64 poolCap) {
  CK(cudaSetDeviceFlags(cudaDeviceScheduleBlockingSync));
  CK(cudaFree(0));
  CK(cudaMemcpyToSymbol(cP, &g->P, sizeof(int))); CK(cudaMemcpyToSymbol(cQ, &g->Q, sizeof(int)));
  CK(cudaMemcpyToSymbol(cLmax, &g->Lmax, sizeof(int))); CK(cudaMemcpyToSymbol(cSplit, &g->split, sizeof(int)));
  CK(cudaMemcpyToSymbol(cMmax, &g->mmax, sizeof(int)));
  CK(cudaMemcpyToSymbol(cDmax, g->dmax, sizeof(int) * 64)); CK(cudaMemcpyToSymbol(cP3, g->P3, sizeof(u64) * 41));
  gPoolCap = poolCap;
  CK(cudaMalloc(&dPool, sizeof(Summ) * poolCap));
  CK(cudaMalloc(&dPoolCnt, 8)); CK(cudaMalloc(&dJob, 4));
  gInCap = 1 << 22; CK(cudaMalloc(&dXin, 8 * gInCap)); CK(cudaMalloc(&dMin, 8 * gInCap));
  gTcap = 1 << 14; CK(cudaMalloc(&dTin, sizeof(TaskIn) * gTcap)); CK(cudaMalloc(&dTout, sizeof(TaskOut) * gTcap));
  size_t fr, tt; CK(cudaMemGetInfo(&fr, &tt));
  if (!arenaTotal) arenaTotal = (fr > (768ULL << 20) ? fr - (768ULL << 20) : fr / 2) / 16;
  gArena = arenaTotal;
  CK(cudaMalloc(&dAX, 8 * arenaTotal)); CK(cudaMalloc(&dAM, 8 * arenaTotal));
  CK(cudaEventCreate(&ev0)); CK(cudaEventCreate(&ev1));
  return 0;
}

extern "C" void gpu_launch(int nt, const TaskIn *t, const u64 *xin, const u64 *min, u64 nin, int blocks) {
  if (nin > gInCap) { CK(cudaFree(dXin)); CK(cudaFree(dMin)); gInCap = nin; CK(cudaMalloc(&dXin, 8 * gInCap)); CK(cudaMalloc(&dMin, 8 * gInCap)); }
  if (nt > gTcap) { CK(cudaFree(dTin)); CK(cudaFree(dTout)); gTcap = nt; CK(cudaMalloc(&dTin, sizeof(TaskIn) * gTcap)); CK(cudaMalloc(&dTout, sizeof(TaskOut) * gTcap)); }
  CK(cudaMemcpy(dXin, xin, 8 * nin, cudaMemcpyHostToDevice));
  CK(cudaMemcpy(dMin, min, 8 * nin, cudaMemcpyHostToDevice));
  CK(cudaMemcpy(dTin, t, sizeof(TaskIn) * nt, cudaMemcpyHostToDevice));
  CK(cudaMemset(dPoolCnt, 0, 8)); CK(cudaMemset(dJob, 0, 4));
  u64 E = gArena / blocks;
  CK(cudaEventRecord(ev0));
  kTasks<<<blocks, BT>>>(nt, dTin, dXin, dMin, dAX, dAM, E, dPool, gPoolCap, dPoolCnt, dJob, dTout);
  CK(cudaGetLastError());
  CK(cudaEventRecord(ev1));
}

extern "C" u64 gpu_wait(TaskOut *out, int nt, Summ *dst, u64 dstcap, double *ms) {
  CK(cudaEventSynchronize(ev1));
  CK(cudaGetLastError());
  float f; CK(cudaEventElapsedTime(&f, ev0, ev1)); *ms = f;
  unsigned long long cnt; CK(cudaMemcpy(&cnt, dPoolCnt, 8, cudaMemcpyDeviceToHost));
  CK(cudaMemcpy(out, dTout, sizeof(TaskOut) * nt, cudaMemcpyDeviceToHost));
  u64 c = cnt < gPoolCap ? cnt : gPoolCap;
  if (c > dstcap) c = dstcap;
  if (c) CK(cudaMemcpy(dst, dPool, sizeof(Summ) * c, cudaMemcpyDeviceToHost));
  return cnt;
}
