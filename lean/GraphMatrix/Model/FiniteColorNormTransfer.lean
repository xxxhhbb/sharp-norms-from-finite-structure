import GraphMatrix.GraphMatrixEntryMoments

/-! # Finite-color expected-norm transfer

The upper reduction is an exact average of zero-padded colored matrices.
This generic lemma is the expectation-level triangle/Fubini step.  Its
coefficient is explicit: when an exact color identity uses `v^v / |Color|`,
the resulting norm loss is `v^v`, not one.  It does not construct the color
identity or assert identical distributions for distinct colored models.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Finite uniform expectation commutes with multiplication by a scalar. -/
theorem paperMean_const_mul_color {α : Type} [Fintype α]
    (f : α → ℝ) (c : ℝ) :
    paperMean (fun a => c * f a) = c * paperMean f := by
  unfold paperMean
  rw [← Finset.mul_sum]
  ring

/-- The `L¹` consequence of a pointwise finite color sum.  No independence
between the color and noise indices is required for this inequality. -/
theorem paperMean_norm_le_of_finiteColorSum
    {Ω Color E : Type} [Fintype Ω] [Fintype Color]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : Ω → E) (colored : Color → Ω → E)
    (coefficient : ℝ) (hCoefficient : 0 ≤ coefficient)
    (hIdentity : ∀ ω, target ω =
      coefficient • ∑ c : Color, colored c ω) :
    paperMean (fun ω => ‖target ω‖) ≤
      coefficient * ∑ c : Color,
        paperMean (fun ω => ‖colored c ω‖) := by
  have hPointwise : ∀ ω, ‖target ω‖ ≤
      coefficient * ∑ c : Color, ‖colored c ω‖ := by
    intro ω
    rw [hIdentity ω, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hCoefficient]
    exact mul_le_mul_of_nonneg_left
      (norm_sum_le Finset.univ (fun c => colored c ω)) hCoefficient
  calc
    paperMean (fun ω => ‖target ω‖) ≤
        paperMean (fun ω =>
          coefficient * ∑ c : Color, ‖colored c ω‖) := by
      unfold paperMean
      apply mul_le_mul_of_nonneg_left
      exact Finset.sum_le_sum (fun ω _ => hPointwise ω)
      exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le (Fintype.card Ω))
    _ = coefficient * ∑ c : Color,
          paperMean (fun ω => ‖colored c ω‖) := by
      rw [paperMean_const_mul_color, paperMean_sum]


end GraphMatrixReplica
