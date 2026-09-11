# Design: topology-aware CUDA lowering (`toCudaArrayDesign`)

Status: **v1 implemented** (`Sparkle/Backend/CudaArray.lean`).  Verified
cycle- and register-exact against CSim on a CPU CUDA emulator for 7 designs ×
all schedules, `nvcc` 12.0 (sm_80) compiles and links every emitted file;
real-GPU numbers pending (`SPARKLE_CUDA=1 lake exe cuda-array-cosim`).

## 1. Goal

`toCudaIntraDesign` gives each top-level `.inst` a thread and moves data
through `offsetof` copy tables — general, but it does not know that a
systolic array, an image filter or a cellular automaton is *one cell
replicated on a lattice*.  This backend **detects** that structure and lowers
it to `kernel<<<dim3 grid, dim3 block>>>` where the thread coordinate *is*
the lattice coordinate and neighbours are found by index arithmetic.

## 2. Detection (`analyzeArray`)

1. The top must contain instances of **one** module plus const/ref assigns.
2. Every cell input is resolved through top-level ref chains to a
   neighbour output, a top input, or a constant (hash maps; 10⁴ cells OK).
3. **Link types** `(input p ← output q)` are grouped into **directions**:
   two types are the same direction when they relate the same instance pairs
   (FIR: `x_in←x_out` and `acc_in←acc_out`), or opposite when one is the
   reverse of the other (Life: west ↔ east).
4. **Basis.** Directions are tried most-links-first; one joins the basis if a
   BFS with the basis as *free generators* stays consistent and connects more
   of the graph.  Axes are therefore chosen before diagonals.
5. Every other direction must be a **constant integer offset** in the basis
   frame (diagonals become `(±1, ±1)`).
6. Each connected component must be a **full box**, all of the same shape;
   several identical components add one axis (4 independent FIR chains →
   2-D `8×4`).  Fully independent cells take their shape from instance names
   `prefix_<row>_<col>` when those form a box, else 1-D.
7. **Translation invariance:** each link type must exist on exactly the cells
   whose producer lies inside the box; boundary cells get that input from
   the top level instead (an "ext" entry).
8. Connected arrays: every neighbour-visible output must be **Moore**
   (`CudaIntra.combDeps` = ∅) and not a register field itself.

Rejections name the offender: Mealy link, non-lattice link, heterogeneous
top, top-level register/memory, compound connection, > 3 axes.

## 3. Schedules

| topology | kernel | barrier / cycle | state |
|---|---|---|---|
| independent | `indep_kernel<<<grid, block>>>`, all cycles in one launch | none | thread-local copy of the cell |
| connected, fits one block (≤ 1024 cells, both exchange buffers ≤ 48 KiB) | `block_kernel<<<1, dim3(X,Y,Z), smem>>>` | 1 × `__syncthreads` | thread-local cell, exchange in shared memory |
| connected, any size | `prologue_kernel` + `step_kernel<<<grid, block>>>` per cycle | kernel boundary | cells in global memory |

Connected cycle (ping-pong exchange of Moore outputs only):

```
prologue: load_ext; eval; publish(xch[0]); barrier
cycle k:  gather(xch[k%2]) → eval_tick → (k<last: eval → publish(xch[(k+1)%2])) → barrier
```

Why it is exact: after cycle *k*'s latch, a Moore output is a function of the
registers only, so the post-latch `eval` publishes precisely the value CSim's
cycle-*k+1* eval exposes on that port.  Readers only touch the `cur` buffer,
writers only `nxt`; the single barrier separates a buffer's last read from
its next write.  The last cycle ends with `eval_tick`, so the final cell
struct equals CSim's byte-for-byte on every register.  Top outputs are copied
from cell fields after the last `eval_tick` (CSim's observation point) —
Mealy outputs are fine there.

Compared with the intra schedule: 1 barrier instead of 3, no copy tables,
exchange traffic limited to the neighbour-visible ports, cell state kept in
registers/local memory in the single-launch paths (nvcc: 56-byte frame, no
spills for the mesh PE).

## 4. Host API

Same `.so` as the batch backend (`jit_cuda_alloc(1)`, `jit_cuda_set_input`,
`jit_cuda_get_output`), plus

```c
int  jit_array_run_mode(void* h, long cycles, int mode); // 0 auto, 1 block, 2 step
void jit_array_run(void* h, long cycles);
const char* jit_array_topology(void);                    // detection summary
```

`toCudaAuto d` picks array → intra → batch.

## 5. Verification (`lake exe cuda-array-cosim`)

For each fixture (`Tests/CudaArrayFixtures.lean`) the generated `main` runs
the same multi-phase stimulus (inputs change between phases) through CSim
`eval_tick`, CSim `eval`+`tick`, and the kernels in every mode, per cycle and
as one launch, comparing **all top outputs and every register of every
cell**.

| fixture | detected | modes |
|---|---|---|
| Mesh 2×2 / 16×16 | connected 2-D | auto, block, step: PASS |
| Mesh 36×36 (1296 cells) | connected 2-D | auto→step PASS, block correctly refused |
| FIR 1×24 | connected 1-D (2 links, 1 direction) | PASS |
| FIR 4×8 | 1-D × 4 copies → 2-D 8×4 | PASS |
| Pixel IIR 20×36 | independent 2-D (names), Mealy output | PASS |
| Life 12×12 | connected 2-D, 8 links incl. diagonals | PASS; also equals an independent Python Life for 36 generations |

The emulator (`tools/cuda_emu/cuda_runtime.h`) runs each block's threads as
ucontext fibers so `__syncthreads` is a real barrier.  Mutation check: removing
the barrier, skipping the post-latch publish, not swapping buffers, a wrong
neighbour offset, and a broken step-kernel publish are each caught.

**CSim bug found and fixed.** With a statement-level cycle at the top
(bidirectional coupling — Life), `sparkle_<Top>_eval_tick` read back-edge
wires before writing them (uninitialised stack locals), because the
fixed-point relaxation added in 451c976 was applied to `eval` only.
`eval_tick` now delegates to `eval` + `tick` when the schedule has a cycle;
before the fix it disagreed with the true Life evolution on 17 of 36
generations, after it all three references agree.  `JIT.evalTick` uses this
function, so `#sim` on such designs was affected.

## 6. Limits / next steps

- Flat designs: the detector needs `@[hardware_module]` hierarchy; per-pixel
  logic inlined into one module is invisible (next: structural hashing of
  register cones to re-hierarchise).
- Heterogeneous boundaries (edge cells of another module) → intra fallback.
- Mealy neighbour links → K-round relaxation (as intra memo §7).
- Periodic (torus) lattices are rejected (inconsistent embedding) — could
  be recognised as wrap-around offsets.
- Performance: CUDA Graph capture of the per-cycle step loop, temporal
  blocking (several cycles per launch with a halo), SoA cell layout for
  coalescing, batch × array (blockIdx.z over instances).
