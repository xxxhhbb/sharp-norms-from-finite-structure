import R6.WeightedSignTiltCore

noncomputable section
open scoped BigOperators
namespace WeightedSignTilt
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem tiltedAtom_nonneg (Y : Ω → ℝ) (lam : ℝ) (ω : Ω) :
    0 ≤ tiltedAtom Y lam ω :=
  le_of_lt (div_pos (Real.exp_pos _) (partition_pos Y lam))

theorem tiltedAtom_sum_one (Y : Ω → ℝ) (lam : ℝ) :
    (∑ ω : Ω, tiltedAtom Y lam ω) = 1 := by
  simp only [tiltedAtom, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos Y lam))

theorem tiltedProbability_eq_sum_indicator (Y : Ω → ℝ) (lam : ℝ)
    (P : Ω → Prop) [DecidablePred P] :
    tiltedProbability Y lam P = ∑ ω : Ω, if P ω then tiltedAtom Y lam ω else 0 := by
  simp [tiltedProbability, bandMass, tiltedAtom, Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

/-- A single two-sided Chebyshev estimate suffices on the paper's wider band.
The center is at least 3t from either boundary, so the discarded mass is at
most 1/9 when the centered second moment is at most t². -/
theorem tilted_band_half_of_mean_variance
    (Y : Ω → ℝ) (lam mu t sigmaSq : ℝ) (ht : 0 < t)
    (hlo : 4 * t ≤ mu) (hhi : mu ≤ 8 * t)
    (hvar : (∑ ω : Ω, tiltedAtom Y lam ω * (Y ω - mu) ^ 2) ≤ sigmaSq)
    (hsigma : sigmaSq ≤ t ^ 2) :
    (1 / 2 : ℝ) ≤ tiltedProbability Y lam (fun ω => t ≤ Y ω ∧ Y ω ≤ 12 * t) := by
  classical
  let P : Ω → Prop := fun ω => t ≤ Y ω ∧ Y ω ≤ 12 * t
  have hpoint (ω : Ω) :
      (9 * t ^ 2) * tiltedAtom Y lam ω ≤
        (9 * t ^ 2) * (if P ω then tiltedAtom Y lam ω else 0) +
          tiltedAtom Y lam ω * (Y ω - mu) ^ 2 := by
    have hp := tiltedAtom_nonneg Y lam ω
    by_cases hP : P ω
    · simp only [if_pos hP]
      exact le_add_of_nonneg_right (mul_nonneg hp (sq_nonneg _))
    · simp only [if_neg hP, mul_zero, zero_add]
      have hs : 9 * t ^ 2 ≤ (Y ω - mu) ^ 2 := by
        have hnot : ¬ (t ≤ Y ω ∧ Y ω ≤ 12 * t) := hP
        by_cases hleft : t ≤ Y ω
        · have hright : 12 * t < Y ω := lt_of_not_ge (fun h => hnot ⟨hleft, h⟩)
          have hprod := mul_nonneg (show 0 ≤ Y ω - mu - 3 * t by linarith)
            (show 0 ≤ Y ω - mu + 3 * t by linarith)
          nlinarith
        · have hy : Y ω < t := lt_of_not_ge hleft
          have hprod := mul_nonneg (show 0 ≤ mu - Y ω - 3 * t by linarith)
            (show 0 ≤ mu - Y ω + 3 * t by linarith)
          nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs hp]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, tiltedAtom_sum_one,
    mul_one] at hsum
  have hprob : (∑ ω : Ω, if P ω then tiltedAtom Y lam ω else 0) =
      tiltedProbability Y lam P := (tiltedProbability_eq_sum_indicator Y lam P).symm
  rw [hprob] at hsum
  change (1 / 2 : ℝ) ≤ tiltedProbability Y lam P
  by_contra hn
  have hlt : tiltedProbability Y lam P < 1 / 2 := lt_of_not_ge hn
  have hmul := mul_lt_mul_of_pos_left hlt (show 0 < 9 * t ^ 2 by positivity)
  nlinarith [sq_pos_of_pos ht]

#print axioms tilted_band_half_of_mean_variance
end WeightedSignTilt
