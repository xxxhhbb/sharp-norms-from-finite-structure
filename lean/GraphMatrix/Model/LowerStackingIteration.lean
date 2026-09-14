import GraphMatrix.Model.LowerStackingConditional

/-!
# Two genuinely independent sign groups, stacked on the row side

The coefficient tensor has two independently signed coordinates, and its
final flattening keeps the original column index while adding both sign
coordinates to the row index. No flattening norm is inserted as a premise.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model

def lowerTwoGroupChaos
    {ι κ : Type*} (n₀ n₁ : ℕ)
    (A : Fin n₀ → Fin n₁ → Matrix ι κ ℝ)
    (w₀ : Fin n₀ → Bool) (w₁ : Fin n₁ → Bool) : Matrix ι κ ℝ :=
  lowerMatrixSignSum n₀
    (fun e₀ => lowerMatrixSignSum n₁ (A e₀) w₁) w₀

def lowerTwoGroupVerticalFlatten
    {ι κ : Type*} (n₀ n₁ : ℕ)
    (A : Fin n₀ → Fin n₁ → Matrix ι κ ℝ) :
    Matrix (Fin n₁ × (Fin n₀ × ι)) κ ℝ :=
  lowerVerticallyStackedMatrix n₁ (fun e₁ =>
    lowerVerticallyStackedMatrix n₀ (fun e₀ => A e₀ e₁))

/-- No multiplicity or coefficient summation is hidden in this row
flattening: each row coordinate recovers both signed coordinates and the
original row coordinate. -/
theorem lowerTwoGroupVerticalFlatten_apply
    {ι κ : Type*} (n₀ n₁ : ℕ)
    (A : Fin n₀ → Fin n₁ → Matrix ι κ ℝ)
    (e₁ : Fin n₁) (e₀ : Fin n₀) (i : ι) (j : κ) :
    lowerTwoGroupVerticalFlatten n₀ n₁ A (e₁, (e₀, i)) j =
      A e₀ e₁ i j := rfl

/-- Stacking in the first sign coordinate commutes exactly with the
second independent Rademacher sum, entry by entry. -/
theorem lowerVerticalStack_signSum_commute
    {ι κ : Type*} (n₀ n₁ : ℕ)
    (A : Fin n₀ → Fin n₁ → Matrix ι κ ℝ)
    (w₁ : Fin n₁ → Bool) :
    lowerVerticallyStackedMatrix n₀
        (fun e₀ => lowerMatrixSignSum n₁ (A e₀) w₁) =
      lowerMatrixSignSum n₁
        (fun e₁ => lowerVerticallyStackedMatrix n₀
          (fun e₀ => A e₀ e₁)) w₁ := by
  ext ⟨e₀, i⟩ j
  rfl

theorem allSignsMean_mono
    (n : ℕ) (f g : (Fin n → Bool) → ℝ)
    (h : ∀ w, f w ≤ g w) :
    allSignsMean n f ≤ allSignsMean n g := by
  unfold allSignsMean
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro w _
  exact h w

theorem lowerVerticalStack_norm_le_sqrtThree_mean
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) :
    ‖lowerVerticallyStackedMatrix n A‖ ≤
      Real.sqrt 3 *
        allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖) :=
  (le_max_left _ _).trans (lowerOneGroupStackMax_le_sqrtThree_mean n A)

/-- Exact two-group lower stacking for the all-row flattening. The joint
mean is nested in the order `w₁` then `w₀`, which is the uniform product
mean by `allSignsMean_twoGroups_eq_productMean`. -/
theorem lowerTwoGroupVerticalFlatten_norm_le_three_jointMean
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n₀ n₁ : ℕ)
    (A : Fin n₀ → Fin n₁ → Matrix ι κ ℝ) :
    ‖lowerTwoGroupVerticalFlatten n₀ n₁ A‖ ≤
      3 * allSignsMean n₁ (fun w₁ =>
        allSignsMean n₀ (fun w₀ =>
          ‖lowerTwoGroupChaos n₀ n₁ A w₀ w₁‖)) := by
  let B : Fin n₁ → Matrix (Fin n₀ × ι) κ ℝ :=
    fun e₁ => lowerVerticallyStackedMatrix n₀ (fun e₀ => A e₀ e₁)
  have hSecond :
      ‖lowerTwoGroupVerticalFlatten n₀ n₁ A‖ ≤
        Real.sqrt 3 * allSignsMean n₁ (fun w₁ =>
          ‖lowerMatrixSignSum n₁ B w₁‖) := by
    exact lowerVerticalStack_norm_le_sqrtThree_mean n₁ B
  have hFirst :
      allSignsMean n₁ (fun w₁ => ‖lowerMatrixSignSum n₁ B w₁‖) ≤
        Real.sqrt 3 * allSignsMean n₁ (fun w₁ =>
          allSignsMean n₀ (fun w₀ =>
            ‖lowerTwoGroupChaos n₀ n₁ A w₀ w₁‖)) := by
    calc
      _ = allSignsMean n₁ (fun w₁ =>
          ‖lowerVerticallyStackedMatrix n₀
            (fun e₀ => lowerMatrixSignSum n₁ (A e₀) w₁)‖) := by
        apply congrArg (allSignsMean n₁)
        funext w₁
        rw [lowerVerticalStack_signSum_commute]
      _ ≤ allSignsMean n₁ (fun w₁ =>
          lowerOneGroupStackMax n₀
            (fun e₀ => lowerMatrixSignSum n₁ (A e₀) w₁)) := by
        apply allSignsMean_mono
        intro w₁
        exact le_max_left _ _
      _ ≤ Real.sqrt 3 * allSignsMean n₁ (fun w₁ =>
          allSignsMean n₀ (fun w₀ =>
            ‖lowerTwoGroupChaos n₀ n₁ A w₀ w₁‖)) := by
        exact lowerOneGroupStackMax_outerMean_le n₁ n₀
          (fun w₁ e₀ => lowerMatrixSignSum n₁ (A e₀) w₁)
  have hNonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  calc
    ‖lowerTwoGroupVerticalFlatten n₀ n₁ A‖ ≤
        Real.sqrt 3 * allSignsMean n₁ (fun w₁ =>
          ‖lowerMatrixSignSum n₁ B w₁‖) := hSecond
    _ ≤ Real.sqrt 3 *
        (Real.sqrt 3 * allSignsMean n₁ (fun w₁ =>
          allSignsMean n₀ (fun w₀ =>
            ‖lowerTwoGroupChaos n₀ n₁ A w₀ w₁‖))) :=
      mul_le_mul_of_nonneg_left hFirst hNonneg
    _ = 3 * allSignsMean n₁ (fun w₁ =>
          allSignsMean n₀ (fun w₀ =>
            ‖lowerTwoGroupChaos n₀ n₁ A w₀ w₁‖)) := by
      rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- The same two-group statement with the actual joint product sample
explicit: there are `2^n₁ * 2^n₀` equally weighted pairs of sign vectors. -/
theorem lowerTwoGroupVerticalFlatten_norm_le_three_productMean
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n₀ n₁ : ℕ)
    (A : Fin n₀ → Fin n₁ → Matrix ι κ ℝ) :
    ‖lowerTwoGroupVerticalFlatten n₀ n₁ A‖ ≤
      3 * ((∑ pair : (Fin n₁ → Bool) × (Fin n₀ → Bool),
        ‖lowerTwoGroupChaos n₀ n₁ A pair.2 pair.1‖) /
        ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ n₀)) := by
  simpa only [allSignsMean_twoGroups_eq_productMean] using
    (lowerTwoGroupVerticalFlatten_norm_le_three_jointMean n₀ n₁ A)


end GraphMatrixReplica.Model
