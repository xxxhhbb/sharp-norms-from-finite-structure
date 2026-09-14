import R6.WeightedSignTiltConcreteVariance
import R6.WeightedSignTiltTanh
import R6.WeightedSignTiltChebyshev

/-!
The R16 weighted sign tilt, with the actual finite tilted distribution.
No mean, variance, or band-mass premise is left in the final tail theorem.
The pointwise small-coefficient premise is the finite maximum condition
written without requiring a chosen maximum element; the final corollary
accepts any common coefficient bound M, including max_j |z_j|.
-/

noncomputable section
open scoped BigOperators
namespace WeightedSignTilt
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem tiltedMean_bounds (z : J → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hsmall : ∀ j, |lam * z j| ≤ 1) :
    lam * (∑ j : J, z j ^ 2) / 2 ≤ tiltedMean z lam ∧
      tiltedMean z lam ≤ lam * (∑ j : J, z j ^ 2) := by
  constructor
  · calc
      lam * (∑ j : J, z j ^ 2) / 2 = ∑ j : J, lam * z j ^ 2 / 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ tiltedMean z lam := by
        apply Finset.sum_le_sum
        intro j _
        exact (tilted_coordinate_mean_bounds (z j) lam hlam (hsmall j)).1
  · calc
      tiltedMean z lam ≤ ∑ j : J, lam * z j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (tilted_coordinate_mean_bounds (z j) lam hlam (hsmall j)).2
      _ = lam * (∑ j : J, z j ^ 2) := (Finset.mul_sum _ _ _).symm

theorem paper_weighted_tilt_band
    (z : J → ℝ) (t sigmaSq : ℝ) (hσ : 0 < sigmaSq)
    (hsigma : (∑ j : J, z j ^ 2) = sigmaSq)
    (ht : Real.sqrt sigmaSq ≤ t)
    (hsmall : ∀ j, 8 * t * |z j| / sigmaSq ≤ 1) :
    (1 / 2 : ℝ) ≤ tiltedProbability (weightedSum z) (8 * t / sigmaSq)
      (fun ε => t ≤ weightedSum z ε ∧ weightedSum z ε ≤ 12 * t) := by
  let lam : ℝ := 8 * t / sigmaSq
  have htpos : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.mpr hσ) ht
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hsmall' (j : J) : |lam * z j| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlam]
    change (8 * t / sigmaSq) * |z j| ≤ 1
    convert hsmall j using 1 <;> ring
  have hmean := tiltedMean_bounds z lam hlam hsmall'
  rw [hsigma] at hmean
  have hscale : lam * sigmaSq = 8 * t := by
    exact div_mul_cancel₀ (8 * t) (ne_of_gt hσ)
  have hlo : 4 * t ≤ tiltedMean z lam := by nlinarith [hmean.1]
  have hhi : tiltedMean z lam ≤ 8 * t := by nlinarith [hmean.2]
  have hsquare : sigmaSq ≤ t ^ 2 := by
    have hs := Real.sq_sqrt (le_of_lt hσ)
    nlinarith [Real.sqrt_nonneg sigmaSq]
  apply tilted_band_half_of_mean_variance (weightedSum z) lam (tiltedMean z lam)
    t sigmaSq htpos hlo hhi
  · simpa only [hsigma] using weightedSum_tilted_variance_le z lam
  · exact hsquare

/-- The exact one-sided paper tail constant, now without a tilted-band premise. -/
theorem paper_weighted_sign_tail
    (z : J → ℝ) (t sigmaSq : ℝ) (hσ : 0 < sigmaSq)
    (hsigma : (∑ j : J, z j ^ 2) = sigmaSq)
    (ht : Real.sqrt sigmaSq ≤ t)
    (hsmall : ∀ j, 8 * t * |z j| / sigmaSq ≤ 1) :
    (1 / 2 : ℝ) * Real.exp (-(96 * t ^ 2 / sigmaSq)) ≤
      uniformProbability (fun ε => t ≤ weightedSum z ε) := by
  exact paper_weighted_tail_of_tilted_band z t sigmaSq hσ
    ((Real.sqrt_nonneg sigmaSq).trans ht)
    (paper_weighted_tilt_band z t sigmaSq hσ hsigma ht hsmall)

/-- In particular, M may be the finite maximum of the absolute coefficients. -/
theorem paper_weighted_sign_tail_of_coefficient_bound
    (z : J → ℝ) (t sigmaSq M : ℝ) (hσ : 0 < sigmaSq)
    (hsigma : (∑ j : J, z j ^ 2) = sigmaSq)
    (ht : Real.sqrt sigmaSq ≤ t) (hM : ∀ j, |z j| ≤ M)
    (hsmall : 8 * t * M / sigmaSq ≤ 1) :
    (1 / 2 : ℝ) * Real.exp (-(96 * t ^ 2 / sigmaSq)) ≤
      uniformProbability (fun ε => t ≤ weightedSum z ε) := by
  apply paper_weighted_sign_tail z t sigmaSq hσ hsigma ht
  intro j
  have ht0 : 0 ≤ t := (Real.sqrt_nonneg sigmaSq).trans ht
  have hmul := mul_le_mul_of_nonneg_left (hM j) (show 0 ≤ 8 * t by positivity)
  exact (div_le_div_of_nonneg_right hmul (le_of_lt hσ)).trans hsmall

#print axioms tiltedMean_bounds
#print axioms paper_weighted_tilt_band
#print axioms paper_weighted_sign_tail
#print axioms paper_weighted_sign_tail_of_coefficient_bound
end WeightedSignTilt
