import R6.PaperNCKEndpoint
import Mathlib.Analysis.MeanInequalitiesPow

/-! # From finite moments to finite means

This file records the exact finite-uniform Jensen endpoint needed after the
moment estimates in `PaperNCKEndpoint`.  The empty indexing type is handled
explicitly: positivity of the exponent makes both sides zero.  No probability
or measure-theoretic interface is used.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Jensen's power inequality for the finite uniform average `paperMean`.
The hypothesis `0 < m` is essential when the indexing type is empty, because
Lean uses `0 ^ 0 = 1`. -/
theorem paperMean_pow_le_mean_pow
    {α : Type} [Fintype α] (f : α → ℝ) (m : ℕ)
    (hm : 0 < m) (hf : ∀ a, 0 ≤ f a) :
    paperMean f ^ m ≤ paperMean (fun a => f a ^ m) := by
  classical
  cases isEmpty_or_nonempty α with
  | inl hEmpty =>
      letI := hEmpty
      simp [paperMean, Nat.ne_of_gt hm]
  | inr hNonempty =>
      letI := hNonempty
      have hCardPos : 0 < (Fintype.card α : ℝ) := by positivity
      have hWeightNonneg :
          ∀ a ∈ (Finset.univ : Finset α),
            0 ≤ (Fintype.card α : ℝ)⁻¹ := by
        intro _ _
        positivity
      have hWeightSum :
          ∑ _a : α, (Fintype.card α : ℝ)⁻¹ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      have hJensen :=
        Real.pow_arith_mean_le_arith_mean_pow
          (s := (Finset.univ : Finset α))
          (fun _ : α => (Fintype.card α : ℝ)⁻¹) f
          hWeightNonneg hWeightSum (fun a _ => hf a) m
      simpa only [Finset.mul_sum, paperMean] using hJensen

/-- A positive moment bound by `B ^ m` implies the corresponding finite
uniform first-moment bound by `B`. -/
theorem paperMean_le_of_mean_pow_le_pow
    {α : Type} [Fintype α] (f : α → ℝ) (m : ℕ) (B : ℝ)
    (hm : 0 < m) (hf : ∀ a, 0 ≤ f a) (hB : 0 ≤ B)
    (hMoment : paperMean (fun a => f a ^ m) ≤ B ^ m) :
    paperMean f ≤ B := by
  apply le_of_pow_le_pow_left₀ (Nat.ne_of_gt hm) hB
  exact (paperMean_pow_le_mean_pow f m hm hf).trans hMoment

/-- Jensen's endpoint specialized to the real `L2` operator norm of a finite
matrix family. -/
theorem matrix_l2_opNorm_paperMean_pow_le_moment
    {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : α → Matrix ι κ ℝ) (m : ℕ) (hm : 0 < m) :
    paperMean (fun a => ‖A a‖) ^ m ≤
      paperMean (fun a => ‖A a‖ ^ m) := by
  exact paperMean_pow_le_mean_pow
    (fun a => ‖A a‖) m hm (fun a => norm_nonneg (A a))

/-- A uniform matrix norm moment estimate yields the matching bound for the
finite uniform mean operator norm. -/
theorem matrix_l2_opNorm_paperMean_le_of_moment_le_pow
    {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : α → Matrix ι κ ℝ) (m : ℕ) (B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B)
    (hMoment : paperMean (fun a => ‖A a‖ ^ m) ≤ B ^ m) :
    paperMean (fun a => ‖A a‖) ≤ B := by
  exact paperMean_le_of_mean_pow_le_pow
    (fun a => ‖A a‖) m B hm (fun a => norm_nonneg (A a)) hB hMoment

/-- The same moment-to-mean endpoint for the exact globally injective paper
graph matrix and its finite noise space. -/
theorem paperGraphMatrix_l2_opNorm_mean_le_of_moment_le_pow
    (G : PaperShape) (n m : ℕ) (B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B)
    (hMoment : paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix G n w‖ ^ m) ≤ B ^ m) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤ B := by
  exact matrix_l2_opNorm_paperMean_le_of_moment_le_pow
    (fun w : PaperNoise n => paperGraphMatrix G n w) m B hm hB hMoment

#print axioms paperMean_pow_le_mean_pow
#print axioms paperMean_le_of_mean_pow_le_pow
#print axioms matrix_l2_opNorm_paperMean_pow_le_moment
#print axioms matrix_l2_opNorm_paperMean_le_of_moment_le_pow
#print axioms paperGraphMatrix_l2_opNorm_mean_le_of_moment_le_pow

end GraphMatrixReplica
