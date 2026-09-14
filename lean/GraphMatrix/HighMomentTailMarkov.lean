import GraphMatrix.TraceNormBridge

/-! # Finite high-moment tail bounds

This module isolates the probability-theory endpoint used after a moment or
trace estimate.  The probability space is the exact finite uniform space used
throughout R6.  No independence, replica counting, or graph hypothesis is
hidden here.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Uniform probability of a decidable event on a finite type.  It is written
using `paperMean`, so it also has the project's explicit empty-space behavior. -/
def finiteUniformProbability
    {Ω : Type} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] : ℝ :=
  paperMean (fun ω => if P ω then 1 else 0)

/-- The finite-uniform probability is monotone under event inclusion. -/
theorem finiteUniformProbability_mono
    {Ω : Type} [Fintype Ω]
    {P Q : Ω → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ ω, P ω → Q ω) :
    finiteUniformProbability P ≤ finiteUniformProbability Q := by
  apply paperMean_mono
  intro ω
  by_cases hP : P ω
  · have hQ : Q ω := hPQ ω hP
    simp [hP, hQ]
  · by_cases hQ : Q ω <;> simp [hP, hQ]

/-- Two-event union bound.  This records how independently obtained endpoint
failure bounds add when a later assembly must enforce both events. -/
theorem finiteUniformProbability_or_le
    {Ω : Type} [Fintype Ω]
    (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q] :
    finiteUniformProbability (fun ω => P ω ∨ Q ω) ≤
      finiteUniformProbability P + finiteUniformProbability Q := by
  unfold finiteUniformProbability paperMean
  calc
    (Fintype.card Ω : ℝ)⁻¹ *
        (∑ ω : Ω, if (P ω ∨ Q ω) then (1 : ℝ) else 0) ≤
        (Fintype.card Ω : ℝ)⁻¹ *
          (∑ ω : Ω,
            ((if P ω then (1 : ℝ) else 0) +
              (if Q ω then (1 : ℝ) else 0))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro ω _
      by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
    _ = (Fintype.card Ω : ℝ)⁻¹ *
          (∑ ω : Ω, if P ω then (1 : ℝ) else 0) +
        (Fintype.card Ω : ℝ)⁻¹ *
          (∑ ω : Ω, if Q ω then (1 : ℝ) else 0) := by
      rw [Finset.sum_add_distrib]
      ring

/-- Pointwise powered Markov inequality, expressed as an indicator bound. -/
theorem highMoment_indicator_mul_le
    (x threshold : ℝ) (m : ℕ)
    (hx : 0 ≤ x) (hthreshold : 0 ≤ threshold) :
    (if threshold < x then 1 else 0) * threshold ^ m ≤ x ^ m := by
  by_cases h : threshold < x
  · simp only [h, if_true, one_mul]
    exact pow_le_pow_left₀ hthreshold (le_of_lt h) m
  · simp only [h, if_false, zero_mul]
    exact pow_nonneg hx m

/-- Markov's inequality for a nonnegative function on the finite uniform
space.  The statement keeps the threshold power on the left, which avoids any
division until strict positivity is actually available. -/
theorem finiteUniformProbability_mul_pow_le_mean_pow
    {Ω : Type} [Fintype Ω]
    (X : Ω → ℝ) (threshold : ℝ) (m : ℕ)
    (hX : ∀ ω, 0 ≤ X ω) (hthreshold : 0 ≤ threshold) :
    finiteUniformProbability (fun ω => threshold < X ω) * threshold ^ m ≤
      paperMean (fun ω => X ω ^ m) := by
  unfold finiteUniformProbability paperMean
  calc
    ((Fintype.card Ω : ℝ)⁻¹ *
        ∑ ω : Ω, if threshold < X ω then 1 else 0) * threshold ^ m =
        (Fintype.card Ω : ℝ)⁻¹ *
          ∑ ω : Ω,
            (if threshold < X ω then 1 else 0) * threshold ^ m := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (Fintype.card Ω : ℝ)⁻¹ * ∑ ω : Ω, X ω ^ m := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ω _ =>
        highMoment_indicator_mul_le
          (X ω) threshold m (hX ω) hthreshold

/-- Divided form of finite-uniform Markov. -/
theorem finiteUniformProbability_le_mean_pow_div
    {Ω : Type} [Fintype Ω]
    (X : Ω → ℝ) (threshold : ℝ) (m : ℕ)
    (hX : ∀ ω, 0 ≤ X ω) (hthreshold : 0 < threshold) :
    finiteUniformProbability (fun ω => threshold < X ω) ≤
      paperMean (fun ω => X ω ^ m) / threshold ^ m := by
  rw [le_div_iff₀ (pow_pos hthreshold m)]
  exact finiteUniformProbability_mul_pow_le_mean_pow
    X threshold m hX hthreshold.le

/-- A moment budget `M` gives the transparent failure bound
`M / threshold^m`.  This is the main scalar interface for upstream estimates. -/
theorem finiteUniformProbability_le_budget_div_pow
    {Ω : Type} [Fintype Ω]
    (X : Ω → ℝ) (threshold M : ℝ) (m : ℕ)
    (hX : ∀ ω, 0 ≤ X ω) (hthreshold : 0 < threshold)
    (hMoment : paperMean (fun ω => X ω ^ m) ≤ M) :
    finiteUniformProbability (fun ω => threshold < X ω) ≤
      M / threshold ^ m := by
  exact (finiteUniformProbability_le_mean_pow_div
    X threshold m hX hthreshold).trans
      (div_le_div_of_nonneg_right hMoment (pow_nonneg hthreshold.le m))

/-- If the `m`-th moment is bounded by `B^m`, multiplying the threshold by a
positive factor `c` costs exactly `c^{-m}` in failure probability. -/
theorem finiteUniformProbability_le_inv_pow_of_moment_le_pow
    {Ω : Type} [Fintype Ω]
    (X : Ω → ℝ) (B c : ℝ) (m : ℕ)
    (hX : ∀ ω, 0 ≤ X ω) (hB : 0 < B) (hc : 0 < c)
    (hMoment : paperMean (fun ω => X ω ^ m) ≤ B ^ m) :
    finiteUniformProbability (fun ω => c * B < X ω) ≤ c⁻¹ ^ m := by
  have hMarkov := finiteUniformProbability_le_budget_div_pow
    X (c * B) (B ^ m) m hX (mul_pos hc hB) hMoment
  calc
    finiteUniformProbability (fun ω => c * B < X ω) ≤
        B ^ m / (c * B) ^ m := hMarkov
    _ = c⁻¹ ^ m := by
      rw [mul_pow, inv_pow]
      field_simp [hB.ne', hc.ne']

/-- The exponential threshold factor converts the Markov loss into the exact
`exp (-m)` form used for logarithmic moment-order selection. -/
theorem inv_exp_one_pow_eq_exp_neg_nat (m : ℕ) :
    (Real.exp 1)⁻¹ ^ m = Real.exp (-(m : ℝ)) := by
  rw [← Real.exp_neg]
  rw [show -(m : ℝ) = (m : ℕ) * (-1 : ℝ) by simp,
    Real.exp_nat_mul]

/-- Exponential-threshold form of the high-moment tail inequality. -/
theorem finiteUniformProbability_le_exp_neg_nat_of_moment_le_pow
    {Ω : Type} [Fintype Ω]
    (X : Ω → ℝ) (B : ℝ) (m : ℕ)
    (hX : ∀ ω, 0 ≤ X ω) (hB : 0 < B)
    (hMoment : paperMean (fun ω => X ω ^ m) ≤ B ^ m) :
    finiteUniformProbability (fun ω => Real.exp 1 * B < X ω) ≤
      Real.exp (-(m : ℝ)) := by
  rw [← inv_exp_one_pow_eq_exp_neg_nat]
  exact finiteUniformProbability_le_inv_pow_of_moment_le_pow
    X B (Real.exp 1) m hX hB (Real.exp_pos 1) hMoment


end GraphMatrixReplica
