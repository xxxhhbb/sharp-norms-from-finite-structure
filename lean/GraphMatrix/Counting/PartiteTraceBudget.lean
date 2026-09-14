import GraphMatrix.PartiteBoundaryMatrixTrace
import GraphMatrix.Counting.ExplicitConstants

/-! # Single C079 trace-budget output for the fully-partite matrix

This is the only matrix-facing theorem exported by the C079 branch.  It
combines the existing exact Gram-trace/state-polynomial identity with the
explicit all-defect coefficient endpoint.  No operator-norm, tail, Menger,
paper-model transfer, or generic NCK statement is proved here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Explicit fully-partite Gram-trace budget, conditional only on the visible
C079 exact-stratum cardinality estimate. -/
theorem c079_partiteBoundaryGramTraceAverage_le_explicit
    (G : PartiteShape) (p s a n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hscale : (p + 1) ^ c079K G.roles ≤ n)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta.1)) :
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) ≤
      (((c079BlockTarget G p s + 1) *
        (c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s) : ℕ) : ℚ) := by
  rw [partiteBoundaryMatrixGramTracePowAverage_eq_statePolynomial]
  exact_mod_cast
    c079_statePolynomial_le_of_disjointPaths_and_explicit_count
      G p s a n dimension hDimension hCovered family hscale hCount


end GraphMatrixReplica
