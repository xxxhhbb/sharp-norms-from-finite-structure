import GraphMatrix.Model.LowerStackingIteration

/-! A third fully independent finite sign group in the all-row flattening. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model

def lowerThreeGroupChaos
    {ι κ : Type*} (n₀ n₁ n₂ : ℕ)
    (A : Fin n₀ → Fin n₁ → Fin n₂ → Matrix ι κ ℝ)
    (w₀ : Fin n₀ → Bool) (w₁ : Fin n₁ → Bool)
    (w₂ : Fin n₂ → Bool) : Matrix ι κ ℝ :=
  lowerTwoGroupChaos n₀ n₁
    (fun e₀ e₁ => lowerMatrixSignSum n₂ (A e₀ e₁) w₂) w₀ w₁

def lowerThreeGroupVerticalFlatten
    {ι κ : Type*} (n₀ n₁ n₂ : ℕ)
    (A : Fin n₀ → Fin n₁ → Fin n₂ → Matrix ι κ ℝ) :
    Matrix (Fin n₂ × (Fin n₁ × (Fin n₀ × ι))) κ ℝ :=
  lowerVerticallyStackedMatrix n₂ (fun e₂ =>
    lowerTwoGroupVerticalFlatten n₀ n₁ (fun e₀ e₁ => A e₀ e₁ e₂))

theorem lowerThreeGroupVerticalFlatten_apply
    {ι κ : Type*} (n₀ n₁ n₂ : ℕ)
    (A : Fin n₀ → Fin n₁ → Fin n₂ → Matrix ι κ ℝ)
    (e₂ : Fin n₂) (e₁ : Fin n₁) (e₀ : Fin n₀)
    (i : ι) (j : κ) :
    lowerThreeGroupVerticalFlatten n₀ n₁ n₂ A
      (e₂, (e₁, (e₀, i))) j = A e₀ e₁ e₂ i j := rfl

/-- The third signed sum commutes exactly with the two already stacked
coefficient coordinates. -/
theorem lowerTwoGroupVerticalFlatten_signSum_commute
    {ι κ : Type*} (n₀ n₁ n₂ : ℕ)
    (A : Fin n₀ → Fin n₁ → Fin n₂ → Matrix ι κ ℝ)
    (w₂ : Fin n₂ → Bool) :
    lowerTwoGroupVerticalFlatten n₀ n₁
        (fun e₀ e₁ => lowerMatrixSignSum n₂ (A e₀ e₁) w₂) =
      lowerMatrixSignSum n₂ (fun e₂ =>
        lowerTwoGroupVerticalFlatten n₀ n₁
          (fun e₀ e₁ => A e₀ e₁ e₂)) w₂ := by
  ext ⟨e₁, ⟨e₀, i⟩⟩ j
  rfl

theorem lowerAllSignsMean_const_mul
    (n : ℕ) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    allSignsMean n (fun w => c * f w) = c * allSignsMean n f := by
  unfold allSignsMean
  rw [← Finset.mul_sum]
  ring

theorem lowerThreeGroupVerticalFlatten_norm_le_sqrtThree_cubed_mean
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n₀ n₁ n₂ : ℕ)
    (A : Fin n₀ → Fin n₁ → Fin n₂ → Matrix ι κ ℝ) :
    ‖lowerThreeGroupVerticalFlatten n₀ n₁ n₂ A‖ ≤
      Real.sqrt 3 ^ 3 * allSignsMean n₂ (fun w₂ =>
        allSignsMean n₁ (fun w₁ =>
          allSignsMean n₀ (fun w₀ =>
            ‖lowerThreeGroupChaos n₀ n₁ n₂ A w₀ w₁ w₂‖))) := by
  let B : Fin n₂ → Matrix (Fin n₁ × (Fin n₀ × ι)) κ ℝ :=
    fun e₂ => lowerTwoGroupVerticalFlatten n₀ n₁
      (fun e₀ e₁ => A e₀ e₁ e₂)
  let F : (Fin n₂ → Bool) → ℝ := fun w₂ =>
    allSignsMean n₁ (fun w₁ =>
      allSignsMean n₀ (fun w₀ =>
        ‖lowerThreeGroupChaos n₀ n₁ n₂ A w₀ w₁ w₂‖))
  have hThird :
      ‖lowerThreeGroupVerticalFlatten n₀ n₁ n₂ A‖ ≤
        Real.sqrt 3 * allSignsMean n₂ (fun w₂ =>
          ‖lowerMatrixSignSum n₂ B w₂‖) := by
    exact lowerVerticalStack_norm_le_sqrtThree_mean n₂ B
  have hTwoPoint : ∀ w₂ : Fin n₂ → Bool,
      ‖lowerMatrixSignSum n₂ B w₂‖ ≤ 3 * F w₂ := by
    intro w₂
    have h := lowerTwoGroupVerticalFlatten_norm_le_three_jointMean
      n₀ n₁ (fun e₀ e₁ => lowerMatrixSignSum n₂ (A e₀ e₁) w₂)
    rw [lowerTwoGroupVerticalFlatten_signSum_commute] at h
    exact h
  have hTwoMean :
      allSignsMean n₂ (fun w₂ => ‖lowerMatrixSignSum n₂ B w₂‖) ≤
        3 * allSignsMean n₂ F := by
    calc
      _ ≤ allSignsMean n₂ (fun w₂ => 3 * F w₂) :=
        allSignsMean_mono n₂ _ _ hTwoPoint
      _ = 3 * allSignsMean n₂ F := lowerAllSignsMean_const_mul n₂ 3 F
  calc
    ‖lowerThreeGroupVerticalFlatten n₀ n₁ n₂ A‖ ≤
        Real.sqrt 3 * allSignsMean n₂ (fun w₂ =>
          ‖lowerMatrixSignSum n₂ B w₂‖) := hThird
    _ ≤ Real.sqrt 3 * (3 * allSignsMean n₂ F) :=
      mul_le_mul_of_nonneg_left hTwoMean (Real.sqrt_nonneg _)
    _ = Real.sqrt 3 ^ 3 * allSignsMean n₂ F := by
      have hs : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) :=
        Real.mul_self_sqrt (by norm_num)
      calc
        Real.sqrt 3 * (3 * allSignsMean n₂ F) =
            (Real.sqrt 3 * Real.sqrt 3 * Real.sqrt 3) *
              allSignsMean n₂ F := by rw [hs]; ring
        _ = Real.sqrt 3 ^ 3 * allSignsMean n₂ F := by ring


end GraphMatrixReplica.Model
