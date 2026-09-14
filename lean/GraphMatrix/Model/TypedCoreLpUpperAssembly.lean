import GraphMatrix.Model.GeometricTraceAssembly
import GraphMatrix.Model.RealLpTraceEndpoint
import GraphMatrix.Model.AnyOrderTraceDomination

/-! # Conditional finite-size real-`q` upper bound for the typed core

The manuscript's exact trace expansion, explicit defect count, half-ratio
geometric window, arbitrary-order norm-to-trace comparison, and real-`q`
Lyapunov step are assembled here.  The defect count remains an explicit
hypothesis.  Lean's replica parameter `p` represents trace order `p + 1`.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The exact `(2 * (p + 1))`-th root of the twice-leading trace budget. -/
def paperR16TypedCoreFiniteLpScale
    (G : PartiteShape) (p s a n : ℕ) : ℝ :=
  (((2 * c079C G.roles ^ (2 * (p + 1)) *
      (p + 1) ^ (a * (p + 1)) *
        n ^ c079BlockTarget G p s : ℕ) : ℝ) ^
    ((((2 * (p + 1) : ℕ) : ℝ))⁻¹))

theorem paperR16TypedCoreFiniteLpScale_nonneg
    (G : PartiteShape) (p s a n : ℕ) :
    0 ≤ paperR16TypedCoreFiniteLpScale G p s a n := by
  unfold paperR16TypedCoreFiniteLpScale
  positivity

/-- No moment-budget assumption is used to establish this exact power
identity; it follows solely from the definition of the explicit scale. -/
theorem paperR16TypedCoreFiniteLpScale_pow
    (G : PartiteShape) (p s a n : ℕ) :
    paperR16TypedCoreFiniteLpScale G p s a n ^ (2 * (p + 1)) =
      ((2 * c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s : ℕ) : ℝ) := by
  unfold paperR16TypedCoreFiniteLpScale
  apply Real.rpow_inv_natCast_pow
  · exact Nat.cast_nonneg _
  · positivity

/-- Finite-size `L^q` core estimate for every positive real `q` within the
chosen even-moment order.  The all-defect cardinality estimate `hCount` and
the concrete half-ratio window `hRatio` are both visible. -/
theorem paperR16_typedCore_realLpRoot_le_finiteScale
    (G : PartiteShape) (p s a n : ℕ) (q : ℝ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hq : 0 < q) (hqp : q ≤ ((2 * (p + 1) : ℕ) : ℝ))
    (hRatio : 2 * (p + 1) ^ c079K G.roles ≤ n)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta.1)) :
    (paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      ‖c079PartiteBoundaryMatrixReal G dimension epsilon‖ ^ q)) ^ q⁻¹ ≤
        paperR16TypedCoreFiniteLpScale G p s a n := by
  apply paperR16_realLpRoot_le_of_traceBudget
    (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      c079PartiteBoundaryMatrixReal G dimension epsilon)
    q (p + 1) (paperR16TypedCoreFiniteLpScale G p s a n)
    hq (by simpa only [Nat.mul_assoc] using hqp)
    (paperR16TypedCoreFiniteLpScale_nonneg G p s a n)
  · intro epsilon
    exact paperR16_matrix_l2_opNorm_pow_le_gramTrace
      (c079PartiteBoundaryMatrixReal G dimension epsilon) (p + 1)
        (by omega)
  · exact (paperR16_partiteMeanGramTrace_le_twiceLeadingScale
      G p s a n dimension hDimension hCovered family hRatio hCount).trans_eq
        (paperR16TypedCoreFiniteLpScale_pow G p s a n).symm


end GraphMatrixReplica
