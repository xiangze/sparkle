/*
  sparkle cuda_emu — run Sparkle's generated CUDA on a CPU, bit-exactly.

  Purpose: SEMANTIC co-simulation of the emitted kernels on machines without
  a GPU (CI, laptops).  It is a drop-in `cuda_runtime.h` for the subset the
  Sparkle CUDA backends emit:

    * __global__/__device__/__host__/__shared__/__forceinline__ → host C++;
    * dim3, threadIdx/blockIdx/blockDim/gridDim;
    * kernel launches — the test driver rewrites `k<<<g, b[, smem]>>>(args)`
      into `SPARKLE_EMU_LAUNCH(k, g, b[, smem])(args)` (see
      Tests/Drivers/CudaArrayCosimMain.lean, `emuRewrite`);
    * __syncthreads(): every CUDA thread of a block is a ucontext fiber; the
      scheduler runs all fibers to the barrier, then releases them, so a
      barrier-separated kernel sees exactly the CUDA memory ordering
      guarantees (and a missing barrier shows up as a real race, because
      fibers run to the barrier in thread order while reading shared state);
    * dynamic shared memory `extern __shared__ unsigned long long
      sparkle_dyn_smem[]` (poisoned with 0xA5 before each block, so a read
      of an unpublished exchange slot is visible as garbage);
    * cudaMalloc/cudaMemcpy/… on host memory; launch-configuration checks
      (≤ 1024 threads, blockDim.z ≤ 64, smem ≤ 48 KiB by default) report
      cudaErrorInvalidConfiguration through cudaGetLastError like the real
      runtime.

  Threads of a block are run in a deterministic order; blocks sequentially.
  This is slow (it is a correctness tool, not a simulator) and it does not
  model warps: code that relies on warp-synchronous execution without
  barriers is outside its scope (Sparkle's kernels don't).
*/
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstddef>
#include <functional>
#include <vector>
#include <ucontext.h>

#define SPARKLE_CUDA_EMU 1
#define __global__
#define __device__
#define __host__
#define __shared__
#define __constant__
#define __forceinline__ inline
#define __restrict__ __restrict

struct dim3 {
  unsigned x, y, z;
  constexpr dim3(unsigned x_ = 1, unsigned y_ = 1, unsigned z_ = 1) : x(x_), y(y_), z(z_) {}
};
typedef dim3 uint3;

typedef enum {
  cudaSuccess = 0,
  cudaErrorMemoryAllocation = 2,
  cudaErrorInvalidConfiguration = 9,
  cudaErrorLaunchFailure = 719
} cudaError_t;
typedef enum {
  cudaMemcpyHostToHost = 0, cudaMemcpyHostToDevice = 1,
  cudaMemcpyDeviceToHost = 2, cudaMemcpyDeviceToDevice = 3, cudaMemcpyDefault = 4
} cudaMemcpyKind;
typedef enum { cudaDevAttrCooperativeLaunch = 95 } cudaDeviceAttr;
typedef void* cudaStream_t;
struct cudaDeviceProp { int multiProcessorCount = 1; char name[256] = "sparkle-cuda-emu"; };

/* Storage for `extern __shared__ unsigned long long sparkle_dyn_smem[]`. */
#ifndef SPARKLE_EMU_SMEM_BYTES
#define SPARKLE_EMU_SMEM_BYTES (48u * 1024u)
#endif
unsigned long long sparkle_dyn_smem[(SPARKLE_EMU_SMEM_BYTES + 7) / 8];

namespace sparkle_emu {
inline dim3 threadIdx_, blockIdx_, blockDim_, gridDim_;
inline cudaError_t lastErr = cudaSuccess;
inline unsigned long long launches = 0, threadsRun = 0, barriers = 0;

struct Fiber {
  ucontext_t ctx;
  std::vector<char> stack;
  dim3 tid;
  int state = 0;   // 0 runnable, 1 waiting at barrier, 2 finished
};
inline ucontext_t schedCtx;
inline Fiber* cur = nullptr;
inline std::function<void()>* body = nullptr;

inline void fiberEntry() {
  (*body)();
  cur->state = 2;
  swapcontext(&cur->ctx, &schedCtx);
}
inline void syncthreads() {
  ++barriers;
  cur->state = 1;
  swapcontext(&cur->ctx, &schedCtx);
}

inline void runGrid(dim3 g, dim3 b, size_t smem, std::function<void()> fn) {
  const unsigned long long nt = (unsigned long long)b.x * b.y * b.z;
  if (nt == 0 || nt > 1024 || b.x > 1024 || b.y > 1024 || b.z > 64 ||
      g.x == 0 || g.y == 0 || g.z == 0 || g.y > 65535 || g.z > 65535 ||
      smem > SPARKLE_EMU_SMEM_BYTES) {
    lastErr = cudaErrorInvalidConfiguration;
    return;
  }
  ++launches;
  static std::vector<Fiber> fibers;
  if (fibers.size() < nt) fibers.resize(nt);
  const size_t stackBytes = 256 * 1024;
  body = &fn;
  gridDim_ = g; blockDim_ = b;
  for (unsigned bz = 0; bz < g.z; ++bz)
  for (unsigned by = 0; by < g.y; ++by)
  for (unsigned bx = 0; bx < g.x; ++bx) {
    blockIdx_ = dim3(bx, by, bz);
    if (smem) memset(sparkle_dyn_smem, 0xA5, smem);
    unsigned long long t = 0;
    for (unsigned tz = 0; tz < b.z; ++tz)
    for (unsigned ty = 0; ty < b.y; ++ty)
    for (unsigned tx = 0; tx < b.x; ++tx, ++t) {
      Fiber& f = fibers[t];
      if (f.stack.size() != stackBytes) f.stack.resize(stackBytes);
      getcontext(&f.ctx);
      f.ctx.uc_stack.ss_sp = f.stack.data();
      f.ctx.uc_stack.ss_size = f.stack.size();
      f.ctx.uc_link = nullptr;
      makecontext(&f.ctx, fiberEntry, 0);
      f.tid = dim3(tx, ty, tz);
      f.state = 0;
    }
    for (;;) {
      for (unsigned long long i = 0; i < nt; ++i) {
        Fiber& f = fibers[i];
        if (f.state != 0) continue;
        cur = &f;
        threadIdx_ = f.tid;
        swapcontext(&schedCtx, &f.ctx);
      }
      unsigned long long waiting = 0, done = 0;
      for (unsigned long long i = 0; i < nt; ++i) {
        waiting += fibers[i].state == 1;
        done += fibers[i].state == 2;
      }
      if (done == nt) break;
      if (done != 0) {
        fprintf(stderr, "[cuda_emu] divergent __syncthreads: %llu threads exited while %llu wait\n",
                done, waiting);
        abort();
      }
      for (unsigned long long i = 0; i < nt; ++i) fibers[i].state = 0;   // release barrier
    }
    threadsRun += nt;
  }
}

template <class F>
struct Launch {
  F* f; dim3 g, b; size_t smem;
  template <class... A>
  void operator()(A... a) const {
    F* fp = f;
    runGrid(g, b, smem, [=]() { fp(a...); });
  }
};
template <class F>
inline Launch<F> makeLaunch(F* f, dim3 g, dim3 b, size_t smem = 0, cudaStream_t = nullptr) {
  return Launch<F>{f, g, b, smem};
}
}  // namespace sparkle_emu

#define threadIdx ::sparkle_emu::threadIdx_
#define blockIdx  ::sparkle_emu::blockIdx_
#define blockDim  ::sparkle_emu::blockDim_
#define gridDim   ::sparkle_emu::gridDim_
#define __syncthreads() ::sparkle_emu::syncthreads()
#define SPARKLE_EMU_LAUNCH(k, ...) ::sparkle_emu::makeLaunch(k, __VA_ARGS__)

inline cudaError_t cudaMalloc(void** p, size_t n) {
  *p = calloc(1, n ? n : 1);
  return *p ? cudaSuccess : cudaErrorMemoryAllocation;
}
inline cudaError_t cudaMallocHost(void** p, size_t n) { return cudaMalloc(p, n); }
inline cudaError_t cudaFree(void* p) { free(p); return cudaSuccess; }
inline cudaError_t cudaFreeHost(void* p) { free(p); return cudaSuccess; }
inline cudaError_t cudaMemcpy(void* d, const void* s, size_t n, cudaMemcpyKind) {
  memmove(d, s, n); return cudaSuccess;
}
inline cudaError_t cudaMemset(void* d, int v, size_t n) { memset(d, v, n); return cudaSuccess; }
inline cudaError_t cudaDeviceSynchronize() { return cudaSuccess; }
inline cudaError_t cudaGetLastError() {
  cudaError_t e = sparkle_emu::lastErr; sparkle_emu::lastErr = cudaSuccess; return e;
}
inline cudaError_t cudaPeekAtLastError() { return sparkle_emu::lastErr; }
inline const char* cudaGetErrorString(cudaError_t e) {
  return e == cudaSuccess ? "no error" : "cuda_emu error";
}
inline cudaError_t cudaGetDevice(int* d) { *d = 0; return cudaSuccess; }
inline cudaError_t cudaDeviceGetAttribute(int* v, cudaDeviceAttr, int) { *v = 0; return cudaSuccess; }
inline cudaError_t cudaGetDeviceProperties(cudaDeviceProp* p, int) { *p = cudaDeviceProp(); return cudaSuccess; }
