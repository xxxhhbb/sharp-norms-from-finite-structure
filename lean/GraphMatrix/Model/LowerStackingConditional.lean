import GraphMatrix.Model.LowerStackingBridge

/-!
# Conditional finite-sign lower stacking

The outer Boolean coordinates stand for sign groups not yet integrated.
For each fixed outer assignment, the inner `Fin n → Bool` is the complete
uniform product sample for one fresh group. The coefficient matrices may
depend arbitrarily on the outer assignment.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model

def lowerOneGroupStackMax
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) : ℝ :=
  max ‖lowerVerticallyStackedMatrix n A‖
    ‖lowerHorizontallyStackedMatrix n A‖

/-- The one-group bound with the paper's exact `√3` loss, simultaneously
for either matrix stacking orientation. -/
theorem lowerOneGroupStackMax_le_sqrtThree_mean
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) :
    lowerOneGroupStackMax n A ≤
      Real.sqrt 3 *
        allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖) := by
  let M := allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖)
  have hM : 0 ≤ M := by
    unfold M allSignsMean
    apply div_nonneg
    · exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
    · positivity
  have hC : 0 ≤ Real.sqrt 3 * M :=
    mul_nonneg (Real.sqrt_nonneg 3) hM
  have hCsq : (Real.sqrt 3 * M) ^ 2 = 3 * M ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hVertical :
      ‖lowerVerticallyStackedMatrix n A‖ ≤ Real.sqrt 3 * M := by
    have hSq := lowerVerticallyStackedMatrix_norm_sq_le n A
    rw [← hCsq] at hSq
    nlinarith [hSq, norm_nonneg (lowerVerticallyStackedMatrix n A)]
  have hHorizontal :
      ‖lowerHorizontallyStackedMatrix n A‖ ≤ Real.sqrt 3 * M := by
    have hSq := lowerHorizontallyStackedMatrix_norm_sq_le n A
    rw [← hCsq] at hSq
    nlinarith [hSq, norm_nonneg (lowerHorizontallyStackedMatrix n A)]
  exact max_le hVertical hHorizontal

/-- Conditional one-group stacking: outer signs can make each coefficient
matrix random, provided the fresh inner signs are the separate coordinates
of the full product sample. No bound on the coefficients is assumed. -/
theorem lowerOneGroupStackMax_outerMean_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (q n : ℕ)
    (A : (Fin q → Bool) → Fin n → Matrix ι κ ℝ) :
    allSignsMean q (fun outer => lowerOneGroupStackMax n (A outer)) ≤
      Real.sqrt 3 * allSignsMean q (fun outer =>
        allSignsMean n (fun inner =>
          ‖lowerMatrixSignSum n (A outer) inner‖)) := by
  let N : ℝ := (2 : ℝ) ^ q
  have hN : 0 ≤ N := by positivity
  change (∑ outer : Fin q → Bool,
      lowerOneGroupStackMax n (A outer)) / N ≤
    Real.sqrt 3 *
      ((∑ outer : Fin q → Bool,
        allSignsMean n (fun inner =>
          ‖lowerMatrixSignSum n (A outer) inner‖)) / N)
  calc
    _ ≤ (∑ outer : Fin q → Bool,
          Real.sqrt 3 * allSignsMean n (fun inner =>
            ‖lowerMatrixSignSum n (A outer) inner‖)) / N := by
      apply div_le_div_of_nonneg_right _ hN
      apply Finset.sum_le_sum
      intro outer _
      exact lowerOneGroupStackMax_le_sqrtThree_mean n (A outer)
    _ = Real.sqrt 3 *
        ((∑ outer : Fin q → Bool,
          allSignsMean n (fun inner =>
            ‖lowerMatrixSignSum n (A outer) inner‖)) / N) := by
      rw [← Finset.mul_sum]
      ring

/-- Exact Fubini formula for two disjoint finite Boolean sign groups. -/
theorem allSignsMean_twoGroups_eq_productMean
    (q n : ℕ)
    (f : (Fin q → Bool) → (Fin n → Bool) → ℝ) :
    allSignsMean q (fun outer => allSignsMean n (f outer)) =
      (∑ pair : (Fin q → Bool) × (Fin n → Bool),
        f pair.1 pair.2) / ((2 : ℝ) ^ q * (2 : ℝ) ^ n) := by
  simp only [allSignsMean, Fintype.sum_prod_type, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro outer _
  apply Finset.sum_congr rfl
  intro inner _
  ring

/-- Joint-sample form of the conditional inequality.  The denominator is
exactly the cardinality `2^q 2^n` of the two disjoint sign groups. -/
theorem lowerOneGroupStackMax_jointMean_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (q n : ℕ)
    (A : (Fin q → Bool) → Fin n → Matrix ι κ ℝ) :
    allSignsMean q (fun outer => lowerOneGroupStackMax n (A outer)) ≤
      Real.sqrt 3 *
        ((∑ pair : (Fin q → Bool) × (Fin n → Bool),
          ‖lowerMatrixSignSum n (A pair.1) pair.2‖) /
          ((2 : ℝ) ^ q * (2 : ℝ) ^ n)) := by
  simpa only [allSignsMean_twoGroups_eq_productMean] using
    (lowerOneGroupStackMax_outerMean_le q n A)


end GraphMatrixReplica.Model
