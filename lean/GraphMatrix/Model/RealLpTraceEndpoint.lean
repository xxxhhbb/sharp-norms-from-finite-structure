import GraphMatrix.Model.RealLpFiniteMean

/-! # Real-`q` norm endpoint from an even Gram-trace budget

This is the final Lyapunov step in R16, Proposition `prop:core-upper`.
The pointwise operator-norm-to-trace inequality remains a visible argument.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- An even Gram-trace budget controls the `L^q` operator norm for every
positive real `q` no larger than the even moment order.  The pointwise
norm-to-trace comparison is an explicit hypothesis. -/
theorem paperR16_realLpRoot_le_of_traceBudget
    {Ω ι κ : Type}
    [Fintype Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Ω → Matrix ι κ ℝ) (q : ℝ) (p : ℕ) (B : ℝ)
    (hq : 0 < q) (hqp : q ≤ ((2 * p : ℕ) : ℝ)) (hB : 0 ≤ B)
    (hPointwise : ∀ ω : Ω,
      ‖M ω‖ ^ (2 * p) ≤
        Matrix.trace ((M ω * (M ω).transpose) ^ p))
    (hTrace : paperMean (fun ω : Ω =>
      Matrix.trace ((M ω * (M ω).transpose) ^ p)) ≤
        B ^ (2 * p)) :
    (paperMean (fun ω : Ω => ‖M ω‖ ^ q)) ^ q⁻¹ ≤ B := by
  apply paperMean_realLpRoot_le_of_higherMoment_budget
    (fun ω : Ω => ‖M ω‖) q (2 * p) B
      (fun ω => norm_nonneg (M ω)) hq hqp hB
  exact (paperMean_mono hPointwise).trans hTrace


end GraphMatrixReplica
