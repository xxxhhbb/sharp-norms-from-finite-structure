import R6.WeightedSignTiltCore

noncomputable section
open scoped BigOperators

namespace WeightedSignTilt

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A coordinate moment under an arbitrary normalized finite product law. -/
theorem product_coordinate_expectation
    (q : J → Bool → ℝ)
    (hunit : ∀ k, (∑ b : Bool, q k b) = 1)
    (j : J) (f : Bool → ℝ) :
    (∑ ε : J → Bool, (∏ k : J, q k (ε k)) * f (ε j)) =
      ∑ b : Bool, q j b * f b := by
  classical
  calc
    (∑ ε : J → Bool, (∏ k : J, q k (ε k)) * f (ε j)) =
        ∑ ε : J → Bool,
          ∏ k : J, q k (ε k) * (if k = j then f (ε k) else 1) := by
      congr 1
      funext ε
      simp only [Finset.prod_mul_distrib]
      simp
    _ = ∏ k : J, ∑ b : Bool, q k b * (if k = j then f b else 1) := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset (s := Finset.univ)
          (g := fun k b => q k b * (if k = j then f b else 1)))
    _ = ∑ b : Bool, q j b * f b := by
      have hunit' (k : J) : q k true + q k false = 1 := by
        simpa using hunit k
      simp [hunit']

def coordinateProbability (z : J → ℝ) (lam : ℝ) (j : J) (b : Bool) : ℝ :=
  coordinateWeight z lam j b / coordinatePartition z lam j

theorem coordinateProbability_sum_one (z : J → ℝ) (lam : ℝ) (j : J) :
    (∑ b : Bool, coordinateProbability z lam j b) = 1 := by
  unfold coordinateProbability
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (coordinatePartition_pos z lam j))

theorem coordinateProbability_expected_sign (z : J → ℝ) (lam : ℝ) (j : J) :
    (∑ b : Bool, coordinateProbability z lam j b * sign b) =
      Real.tanh (lam * z j) := by
  have hp : 0 < coordinatePartition z lam j := coordinatePartition_pos z lam j
  have hden : Real.exp (lam * z j) + Real.exp (-(lam * z j)) ≠ 0 := by
    positivity
  simp only [Fintype.sum_bool]
  simp [coordinateProbability, coordinatePartition, coordinateWeight,
    sign, Real.tanh_eq, mul_assoc] at *
  field_simp [hden]
  ring

/-- The exact tilted first moment of the weighted Rademacher sum. -/
theorem weightedSum_tilted_mean (z : J → ℝ) (lam : ℝ) :
    (∑ ε : J → Bool,
      tiltedAtom (weightedSum z) lam ε * weightedSum z ε) =
      ∑ j : J, z j * Real.tanh (lam * z j) := by
  classical
  simp_rw [weightedSum_tiltedAtom_eq_prod]
  simp_rw [weightedSum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hcoord := product_coordinate_expectation
    (q := coordinateProbability z lam)
    (coordinateProbability_sum_one z lam) j
    (fun b => z j * sign b)
  change (∑ ε : J → Bool,
    (∏ k : J, coordinateProbability z lam k (ε k)) * (z j * sign (ε j))) =
      z j * Real.tanh (lam * z j)
  rw [hcoord]
  calc
    (∑ b : Bool, coordinateProbability z lam j b * (z j * sign b)) =
        ∑ b : Bool, z j * (coordinateProbability z lam j b * sign b) := by
          apply Finset.sum_congr rfl
          intro b _
          ring
    _ = z j * (∑ b : Bool, coordinateProbability z lam j b * sign b) := by
      rw [Finset.mul_sum]
    _ = z j * Real.tanh (lam * z j) := by
      rw [coordinateProbability_expected_sign]

#print axioms product_coordinate_expectation
#print axioms coordinateProbability_sum_one
#print axioms coordinateProbability_expected_sign
#print axioms weightedSum_tilted_mean

end WeightedSignTilt
