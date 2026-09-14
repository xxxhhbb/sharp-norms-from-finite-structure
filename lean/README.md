# Sharp graph-matrix norms in Lean

This library formalizes the two-sided norm theorem for dense Rademacher graph
matrices from *Sharp Norms from Finite Structure*.

For every fixed graph shape, there are positive constants depending only on
the shape such that, for all sufficiently large `n`,

```math
\mathbb{E}\lVert M_G(n)\rVert_{\mathrm{op}}
\asymp_G n^{(v+h-s)/2}(\log n)^{a_*/2}.
```

Here `v` is the vertex count, `h` counts isolated summation vertices, `s` is
the minimum boundary-separator size, and `a*` is the maximum active-component
count over minimum separators. The formal model includes empty or overlapping
boundaries, disconnected shapes, and isolated summation vertices.

The main theorem is
[`GraphMatrixReplica.injective_expected_norm_two_sided`](GraphMatrix/MainTheorem.lean).
Its only input is `G : PaperShape`; the counting estimates and probability
bounds are established within the library. The norm is the L2 operator norm.

## Building

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
lake env lean -j1 Verify.lean
```

`lean-toolchain` pins Lean 4.33.0. The mathlib commit and its transitive
dependencies are pinned in `lakefile.toml` and `lake-manifest.json`.

## Organization

| Location | Content |
| --- | --- |
| [`GraphMatrix/MainTheorem.lean`](GraphMatrix/MainTheorem.lean) | Lower and two-sided expected-norm bounds |
| [`GraphMatrix/Main/`](GraphMatrix/Main/) | Assembly, isolated vertices, boundary indices, and scale identities |
| [`GraphMatrix/Counting/`](GraphMatrix/Counting/) | Replica partitions, path restrictions, seeds, and defect counts |
| [`GraphMatrix/Probability/`](GraphMatrix/Probability/) | Internal moments, conditional laws, and synchronized trials |
| [`GraphMatrix/Lower/`](GraphMatrix/Lower/) | Separator contractions and weighted flattenings |
| [`GraphMatrix/Model/`](GraphMatrix/Model/) | Model identifications, color projections, and factor decompositions |
| [`Verify.lean`](Verify.lean) | Final theorem types and axiom dependencies |

The remaining modules contain finite graph theory, matrix inequalities,
Rademacher moment expansions, and exponential-tilting estimates.

## Verification

[`verification/REPORT.json`](verification/REPORT.json) records the source hashes
and local compilation results. `Verify.lean` checks the final theorem types
and prints the axiom dependencies of the main results and two probability
lemmas. Their axiom sets contain only `propext`, `Classical.choice`, and
`Quot.sound`.
