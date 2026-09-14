import GraphMatrix.WeightedSignTiltVariance

noncomputable section
open scoped BigOperators
namespace WeightedSignTilt
variable {J : Type*} [Fintype J] [DecidableEq J]

def tiltedMean (z : J → ℝ) (lam : ℝ) : ℝ :=
  ∑ j : J, z j * Real.tanh (lam * z j)

theorem coordinate_centered_mean (z : J → ℝ) (lam : ℝ) (j : J) :
    (∑ b : Bool, coordinateProbability z lam j b *
      (z j * sign b - z j * Real.tanh (lam * z j))) = 0 := by
  have hu := coordinateProbability_sum_one z lam j
  have hm := coordinateProbability_expected_sign z lam j
  simp only [Fintype.sum_bool, sign, Bool.false_eq_true, if_false, if_true,
    mul_one, mul_neg_one] at hu hm ⊢
  simp only [← sub_eq_add_neg] at hm
  calc
    _ = z j * ((coordinateProbability z lam j true -
        coordinateProbability z lam j false) - Real.tanh (lam * z j) *
          (coordinateProbability z lam j true + coordinateProbability z lam j false)) := by ring
    _ = 0 := by rw [hu, hm]; ring

theorem coordinate_centered_square (z : J → ℝ) (lam : ℝ) (j : J) :
    (∑ b : Bool, coordinateProbability z lam j b *
      (z j * sign b - z j * Real.tanh (lam * z j)) ^ 2) =
      z j ^ 2 * (1 - Real.tanh (lam * z j) ^ 2) := by
  have hu := coordinateProbability_sum_one z lam j
  have hm := coordinateProbability_expected_sign z lam j
  simp only [Fintype.sum_bool, sign, Bool.false_eq_true, if_false, if_true,
    mul_one, mul_neg_one] at hu hm ⊢
  simp only [← sub_eq_add_neg] at hm
  calc
    _ = z j ^ 2 * ((coordinateProbability z lam j true + coordinateProbability z lam j false) -
        2 * Real.tanh (lam * z j) *
          (coordinateProbability z lam j true - coordinateProbability z lam j false) +
        Real.tanh (lam * z j) ^ 2 *
          (coordinateProbability z lam j true + coordinateProbability z lam j false)) := by ring
    _ = _ := by rw [hu, hm]; ring

theorem weightedSum_tilted_variance_eq (z : J → ℝ) (lam : ℝ) :
    (∑ ε : J → Bool, tiltedAtom (weightedSum z) lam ε *
      (weightedSum z ε - tiltedMean z lam) ^ 2) =
      ∑ j : J, z j ^ 2 * (1 - Real.tanh (lam * z j) ^ 2) := by
  let X : J → Bool → ℝ := fun j b => z j * sign b - z j * Real.tanh (lam * z j)
  have hc : ∀ j, (∑ b : Bool, coordinateProbability z lam j b * X j b) = 0 :=
    coordinate_centered_mean z lam
  have h := product_centered_sum_square (coordinateProbability z lam)
    (coordinateProbability_sum_one z lam) X hc
  have hsum (ε : J → Bool) :
      (∑ j : J, X j (ε j)) = weightedSum z ε - tiltedMean z lam := by
    simp [X, weightedSum, tiltedMean, Finset.sum_sub_distrib]
  simp_rw [hsum] at h
  dsimp only [X] at h
  simp_rw [coordinate_centered_square] at h
  simpa only [weightedSum_tiltedAtom_eq_prod, coordinateProbability] using h

theorem weightedSum_tilted_variance_le (z : J → ℝ) (lam : ℝ) :
    (∑ ε : J → Bool, tiltedAtom (weightedSum z) lam ε *
      (weightedSum z ε - tiltedMean z lam) ^ 2) ≤ ∑ j : J, z j ^ 2 := by
  rw [weightedSum_tilted_variance_eq]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [mul_nonneg (sq_nonneg (z j)) (sq_nonneg (Real.tanh (lam * z j)))]

end WeightedSignTilt
