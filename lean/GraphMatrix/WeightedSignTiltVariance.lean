import GraphMatrix.WeightedSignTiltMoments

noncomputable section
open scoped BigOperators

namespace WeightedSignTilt

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Two distinct coordinates factor under a normalized finite product law. -/
theorem product_two_coordinate_expectation
    (q : J → Bool → ℝ)
    (hunit : ∀ k, (∑ b : Bool, q k b) = 1)
    (j k : J) (hjk : j ≠ k) (f g : Bool → ℝ) :
    (∑ ε : J → Bool,
      (∏ i : J, q i (ε i)) * (f (ε j) * g (ε k))) =
      (∑ b : Bool, q j b * f b) *
      (∑ b : Bool, q k b * g b) := by
  classical
  calc
    (∑ ε : J → Bool,
      (∏ i : J, q i (ε i)) * (f (ε j) * g (ε k))) =
        ∑ ε : J → Bool,
          ∏ i : J, q i (ε i) *
            (if i = j then f (ε i) else if i = k then g (ε i) else 1) := by
      congr 1
      funext ε
      have hfactor (i : J) :
          (if i = j then f (ε i) else if i = k then g (ε i) else 1) =
            (if i = j then f (ε i) else 1) *
            (if i = k then g (ε i) else 1) := by
        by_cases hij : i = j
        · subst i
          simp [hjk]
        · by_cases hik : i = k
          · subst i
            simp [Ne.symm hjk]
          · simp [hij, hik]
      simp_rw [hfactor, Finset.prod_mul_distrib]
      simp [Fintype.prod_ite_eq']

    _ = ∏ i : J, ∑ b : Bool, q i b *
          (if i = j then f b else if i = k then g b else 1) := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset (s := Finset.univ)
          (g := fun i b => q i b *
            (if i = j then f b else if i = k then g b else 1)))
    _ = (∑ b : Bool, q j b * f b) *
          (∑ b : Bool, q k b * g b) := by
      have hfactor (i : J) :
          (∑ b : Bool, q i b *
            (if i = j then f b else if i = k then g b else 1)) =
          (if i = j then ∑ b : Bool, q i b * f b else 1) *
          (if i = k then ∑ b : Bool, q i b * g b else 1) := by
        by_cases hij : i = j
        · subst i
          simp [hjk]
        · by_cases hik : i = k
          · subst i
            simp [Ne.symm hjk]
          · simpa [hij, hik] using hunit i
      simp_rw [hfactor, Finset.prod_mul_distrib]
      simp [Fintype.prod_ite_eq']

/-- Variance additivity for a finite product law, expressed with centered
coordinate observables.  The diagonal terms remain exact. -/
theorem product_centered_sum_square
    (q : J → Bool → ℝ)
    (hunit : ∀ k, (∑ b : Bool, q k b) = 1)
    (X : J → Bool → ℝ)
    (hcenter : ∀ j, (∑ b : Bool, q j b * X j b) = 0) :
    (∑ ε : J → Bool,
      (∏ i : J, q i (ε i)) * (∑ j : J, X j (ε j)) ^ 2) =
      ∑ j : J, ∑ b : Bool, q j b * (X j b) ^ 2 := by
  classical
  have hterm (j k : J) :
      (∑ ε : J → Bool,
        (∏ i : J, q i (ε i)) * (X j (ε j) * X k (ε k))) =
        if j = k then (∑ b : Bool, q j b * (X j b) ^ 2) else 0 := by
    by_cases hjk : j = k
    · subst k
      simpa [pow_two] using
        product_coordinate_expectation q hunit j
          (fun b => X j b * X j b)
    · simp only [if_neg hjk]
      rw [product_two_coordinate_expectation q hunit j k hjk
        (X j) (X k), hcenter j, zero_mul]
  calc
    (∑ ε : J → Bool,
      (∏ i : J, q i (ε i)) * (∑ j : J, X j (ε j)) ^ 2) =
        ∑ ε : J → Bool, ∑ j : J, ∑ k : J,
          (∏ i : J, q i (ε i)) * (X j (ε j) * X k (ε k)) := by
      apply Finset.sum_congr rfl
      intro ε _
      rw [sq, Finset.sum_mul_sum]
      simp_rw [Finset.mul_sum]
    _ = ∑ j : J, ∑ k : J, ∑ ε : J → Bool,
          (∏ i : J, q i (ε i)) * (X j (ε j) * X k (ε k)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j : J, ∑ k : J,
          if j = k then (∑ b : Bool, q j b * (X j b) ^ 2) else 0 := by
      simp_rw [hterm]
    _ = ∑ j : J, ∑ b : Bool, q j b * (X j b) ^ 2 := by
      simp


end WeightedSignTilt
