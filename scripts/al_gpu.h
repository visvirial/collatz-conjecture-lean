// al_gpu.h: the contract between the GPU stage 1 (scripts/al_gpu.cu) and its host
// (scripts/al_gpu_host.c). See the comment at the top of scripts/al_gpu.cu.
#ifndef AL_GPU_H
#define AL_GPU_H

typedef unsigned long long u64;

#define TVN 40   // per-weight hints T_1..T_TVN kept per class (needs Lmax <= TVN + 1)
#define MAXLV 48 // levels below `split` in one task (needs Lmax - split + 2 <= MAXLV)

// One summary per class X of a task subtree (X open, or X closed at its own level), m <= mmax.
// w1rel: stage-1 work of tree(X) minus the root descent work of the task (the path ext works
// from the task root down to X, plus the whole subtree search below X when X is open).
// Tv: the per-weight hints of tree(X), Tv[v - 1] = T_v.
typedef struct {
  u64 r, w1rel;
  unsigned task;
  unsigned char m, flags; // flags: SF_CLOSED
  unsigned short pad;
  short Tv[TVN];
} Summ;
#define SF_CLOSED 1

// task input: the root frontier (weight split - 1) of class r mod 3^split, entries {x, mask}
// at xin/min[inOff .. inOff + n). mask: bit k_v - 1 for the k of the entry made by the v-th odd move.
typedef struct { u64 r, inOff; unsigned n, pad; } TaskIn;
typedef struct { unsigned flags, nsumm; u64 hw, classes; } TaskOut;
enum { TF_FAIL = 1, TF_ARENA = 2, TF_QUOTA = 4, TF_OVF = 8 };

typedef struct { int P, Q, D, Lmax, split, mmax; int dmax[64]; u64 P3[41]; } GParams;

#ifdef __cplusplus
extern "C" {
#endif
// allocate everything; returns 0 on success. poolCap summaries, arenaTotal entries (shared by all blocks).
int gpu_init(const GParams *g, u64 arenaTotal, u64 poolCap);
// run nt tasks asynchronously with `blocks` blocks (arena per block = arenaTotal / blocks).
void gpu_launch(int nt, const TaskIn *t, const u64 *xin, const u64 *min, u64 nin, int blocks);
// wait for the last launch; copy the per-task outputs and the summaries; returns the summary
// count (> dstcap: truncated, cannot happen when dstcap >= poolCap). *ms: kernel milliseconds.
u64 gpu_wait(TaskOut *out, int nt, Summ *dst, u64 dstcap, double *ms);
u64 gpu_arena_total(void);
u64 gpu_pool_cap(void);
#ifdef __cplusplus
}
#endif
#endif
