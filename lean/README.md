# OP31 graph-matrix main theorem in Lean

This repository contains the frozen Lean proof of the original R16 two-sided
graph-matrix norm theorem. The final entry point is
`GraphMatrixReplica.root_original_injectiveTwoSided` in
[`R6/M1OriginalMain.lean`](R6/M1OriginalMain.lean).

For each `G : PaperShape`, there exist positive graph-dependent constants
`c`, `C` and a threshold `N` such that, for all `n >= N`, the expected L2
operator norm of the original injectively indexed graph matrix is bounded
above and below by these constants times

```
n ^ ((v + h - s) / 2) * (log n) ^ (a* / 2).
```

The final theorem takes only the graph shape as input. Its counting,
probability and witness obligations are proved within the dependency chain.
Empty or overlapping boundaries, disconnected shapes and isolated roles are
retained. This release covers the main theorem; it does not certify all
manuscript applications or a line-by-line correspondence with the manuscript.

## Build

Install Lean through elan. The toolchain and mathlib revision are pinned.
From this directory:

```sh
lake exe cache get
lake build
lake env lean -j1 FinalMainCheck.lean
```

`FinalMainCheck.lean` prints the final theorem types and the axioms of five
key results. The frozen local verification passed with Lean 4.33.0.
The five axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
The 373 copied Lean source files match the frozen release byte for byte.
See [`verification/REPORT.json`](verification/REPORT.json) for source hashes
and the recorded local checks. This source packaging has not yet been
validated by a fresh dependency download and clean build.

Precompiled binaries, local machine paths, task conversations and unrelated
research materials are not included.
