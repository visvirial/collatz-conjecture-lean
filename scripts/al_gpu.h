// al_gpu.h: the contract between the GPU stage 1 (scripts/al_gpu.cu) and its host
// (scripts/al_gpu_host.c). See the comment at the top of scripts/al_gpu.cu.
#ifndef AL_GPU_H
#define AL_GPU_H

typedef unsigned long long u64;

#define TVN 40   // per-weight hints T_1..T_TVN kept per class (needs Lmax <= TVN + 1)
#define MAXLV 48 // levels below `split` in one task (needs Lmax - split + 2 <= MAXLV)
// Entries keep x mod 3^K3 (not x itself): the search reads x only mod 9, and one level (one odd
// move (2y - 1)/3) loses one power of 3, so x is right mod 3^(K3 - d) at task depth d, at least
// mod 9 (needs Lmax - split + 2 <= K3). 16 * 3^K3 < 2^64, so every y fits a u64 for any D <= 64.
#define K3 37
#define DMAXG 64 // D <= DMAXG: the mask has bit k - 1 for the exponent k of each odd move

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

// task input: the root frontier (weight split - 1) of class r mod 3^split, entries {x mod 3^K3, mask}
// at xin/min[inOff .. inOff + n). mask: bit k_v - 1 for the k of the entry made by the v-th odd move.
typedef struct { u64 r, inOff; unsigned n, pad; } TaskIn;
typedef struct { unsigned flags, nsumm; u64 hw, classes; } TaskOut;
enum { TF_FAIL = 1, TF_ARENA = 2, TF_QUOTA = 4, TF_OVF = 8 };

typedef struct { int P, Q, D, Lmax, split, mmax; int dmax[64]; u64 P3[41]; u64 M3, P2M[DMAXG + 8]; } GParams;

#ifdef __cplusplus
extern "C" {
#endif
// All functions return 0 on success and nonzero on a CUDA error (message on stderr); they never exit.
// gpu_init allocates everything once (no allocation later): poolCap summaries, arenaTotal arena entries shared by all blocks (0: perBlock * blocks,
// capped by the free memory), inputs of up to tCap tasks with up to inCap frontier entries per launch.
int gpu_init(const GParams *g, u64 arenaTotal, u64 perBlock, int blocks, u64 poolCap, u64 inCap, int tCap);
// run nt tasks asynchronously with `blocks` blocks (arena per block = arenaTotal / blocks).
// returns 1 (nothing launched) if nt > tCap or nin > inCap, 2 on a CUDA error.
int gpu_launch(int nt, const TaskIn *t, const u64 *xin, const u64 *min, u64 nin, int blocks);
// wait for the last launch; copy the per-task outputs (flags, nsumm = the summaries of the task in
// the pool). *cnt: the number of summaries emitted (> poolCap: the pool overflowed; the tasks
// concerned are flagged TF_QUOTA). *ms: kernel milliseconds.
int gpu_wait(TaskOut *out, int nt, u64 *cnt, double *ms);
// after gpu_wait: the n[i] summaries of task i to dst[off[i] .. off[i] + n[i]) (any order within a
// task), for each i with off[i] != ~0 (off increasing in i). dst: preferably from gpu_host_alloc.
int gpu_fetch(int nt, const u64 *off, const unsigned *n, Summ *dst);
Summ *gpu_host_alloc(u64 n); // pinned host memory (NULL on failure)
void gpu_host_free(Summ *p);
u64 gpu_arena_total(void);
u64 gpu_pool_cap(void);
#ifdef __cplusplus
}
#endif
#endif
