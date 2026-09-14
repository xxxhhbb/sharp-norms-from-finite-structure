import GraphMatrix.WeightedSignTiltComplete
import GraphMatrix.HighMomentTailMarkov
import GraphMatrix.Probability.Synchronization.FiniteProductLaw

/-!
# deterministic P1-to-tilt transfer and one-component tail

The theorem `p3_component_tail_from_p1_bounds` takes exactly the deterministic
information that supplies on one second-layer good realization:

* lower/upper conditional variance bounds,
* a common coefficient bound,
* the global small-coefficient arithmetic inequality,
* and the chosen threshold square identity.

It then invokes the already-proved `WeightedSignTiltComplete` theorem.  No part
of the weighted tilt is reproved here.

-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

open WeightedSignTilt

/-- Bridge the tilt module's count/cardinality probability to the R6
`finiteUniformProbability`.  Nonemptiness removes the explicit empty-space
convention difference. -/
theorem p3_weightedUniformProbability_eq_finiteUniformProbability
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] :
    WeightedSignTilt.uniformProbability P = finiteUniformProbability P := by
  classical
  have hsum :
      (∑ ω : Ω, if P ω then (1 : ℝ) else 0) =
        ((Finset.univ.filter P).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  unfold WeightedSignTilt.uniformProbability
  unfold finiteUniformProbability paperMean
  rw [hsum]
  simp [div_eq_mul_inv, mul_comm]

/-- The two analytic hypotheses needed by the weighted tilt follow from the
P1-style variance sandwich plus the two global threshold inequalities. -/
theorem p3_tilt_conditions_of_p1_bounds
    (t sigmaSq M a A nPow : ℝ)
    (ht0 : 0 ≤ t)
    (haN : 0 < a * nPow)
    (hvarLower : a * nPow ≤ sigmaSq)
    (hvarUpper : sigmaSq ≤ A * nPow)
    (hthreshold : A * nPow ≤ t ^ 2)
    (hsmallScale : 8 * t * M ≤ a * nPow) :
    0 < sigmaSq ∧
      Real.sqrt sigmaSq ≤ t ∧
      8 * t * M / sigmaSq ≤ 1 := by
  have hσ : 0 < sigmaSq := lt_of_lt_of_le haN hvarLower
  have hσt : sigmaSq ≤ t ^ 2 := hvarUpper.trans hthreshold
  have hsqrtSq : (Real.sqrt sigmaSq) ^ 2 = sigmaSq :=
    Real.sq_sqrt (le_of_lt hσ)
  have hsqrt0 : 0 ≤ Real.sqrt sigmaSq := Real.sqrt_nonneg sigmaSq
  have ht : Real.sqrt sigmaSq ≤ t := by
    nlinarith
  have hnum : 8 * t * M ≤ sigmaSq := hsmallScale.trans hvarLower
  have hsmall : 8 * t * M / sigmaSq ≤ 1 := by
    apply (div_le_iff₀ hσ).2
    simpa using hnum
  exact ⟨hσ, ht, hsmall⟩

/-- The `t ≥ σ` large-`n` condition is reduced to the scalar inequality
`A ≤ eps² * logn`, uniformly in the realization. -/
theorem p3_threshold_square_from_log
    (t A nPow eps logn : ℝ)
    (hnPow0 : 0 ≤ nPow)
    (hAlog : A ≤ eps ^ 2 * logn)
    (htsq : t ^ 2 = eps ^ 2 * nPow * logn) :
    A * nPow ≤ t ^ 2 := by
  rw [htsq]
  have hmul := mul_le_mul_of_nonneg_right hAlog hnPow0
  nlinarith

/-- A realization-independent coefficient envelope `Mbar` is enough for the
small-coefficient tilt condition. -/
theorem p3_small_scale_from_uniform_envelope
    (t M Mbar a nPow : ℝ)
    (ht0 : 0 ≤ t)
    (hM : M ≤ Mbar)
    (hlarge : 8 * t * Mbar ≤ a * nPow) :
    8 * t * M ≤ a * nPow := by
  have h8t : 0 ≤ 8 * t := by positivity
  exact (mul_le_mul_of_nonneg_left hM h8t).trans hlarge

/--
One-component one-sided tail on a fixed second-layer good realization.

`nPow` stands for `n^k` and `logn` for `log n`.  The manuscript proves,
uniformly for all good internal realizations, that for sufficiently large `n`
`hthreshold` and `hsmallScale` hold.  This theorem formalizes the deterministic
consequence once those two arithmetic inequalities are available.
-/
theorem p3_component_tail_from_p1_bounds
    {J : Type} [Fintype J] [DecidableEq J]
    (z : J → ℝ)
    (t sigmaSq M a A nPow eps logn : ℝ)
    (ha : 0 < a) (hnPow : 0 < nPow) (ht0 : 0 ≤ t)
    (hsigma : (∑ j : J, z j ^ 2) = sigmaSq)
    (hvarLower : a * nPow ≤ sigmaSq)
    (hvarUpper : sigmaSq ≤ A * nPow)
    (hthreshold : A * nPow ≤ t ^ 2)
    (hM : ∀ j, |z j| ≤ M)
    (hsmallScale : 8 * t * M ≤ a * nPow)
    (htsq : t ^ 2 = eps ^ 2 * nPow * logn) :
    (1 / 2 : ℝ) * Real.exp (-(96 * eps ^ 2 * logn / a)) ≤
      WeightedSignTilt.uniformProbability
        (fun ε : J → Bool => t ≤ WeightedSignTilt.weightedSum z ε) := by
  have haN : 0 < a * nPow := mul_pos ha hnPow
  obtain ⟨hσ, ht, hsmall⟩ :=
    p3_tilt_conditions_of_p1_bounds t sigmaSq M a A nPow
      ht0 haN hvarLower hvarUpper hthreshold hsmallScale
  have htilt := WeightedSignTilt.paper_weighted_sign_tail_of_coefficient_bound
    z t sigmaSq M hσ hsigma ht hM hsmall
  have hnum0 : 0 ≤ 96 * t ^ 2 := by positivity
  have hquot :
      96 * t ^ 2 / sigmaSq ≤ 96 * t ^ 2 / (a * nPow) := by
    apply (div_le_div_iff₀ hσ haN).2
    exact mul_le_mul_of_nonneg_left hvarLower hnum0
  have hexp :
      Real.exp (-(96 * t ^ 2 / (a * nPow))) ≤
        Real.exp (-(96 * t ^ 2 / sigmaSq)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hquot)
  have hcancel :
      96 * t ^ 2 / (a * nPow) = 96 * eps ^ 2 * logn / a := by
    rw [htsq]
    field_simp [ne_of_gt ha, ne_of_gt hnPow]
    <;> ring
  calc
    (1 / 2 : ℝ) * Real.exp (-(96 * eps ^ 2 * logn / a)) =
        (1 / 2 : ℝ) * Real.exp (-(96 * t ^ 2 / (a * nPow))) := by
      rw [hcancel]
    _ ≤ (1 / 2 : ℝ) * Real.exp (-(96 * t ^ 2 / sigmaSq)) := by
      exact mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ WeightedSignTilt.uniformProbability
        (fun ε : J → Bool => t ≤ WeightedSignTilt.weightedSum z ε) := htilt

/-- finite-uniform version of the previous theorem. -/
theorem p3_component_tail_finite_uniform
    {J : Type} [Fintype J] [DecidableEq J]
    (z : J → ℝ)
    (t sigmaSq M a A nPow eps logn : ℝ)
    (ha : 0 < a) (hnPow : 0 < nPow) (ht0 : 0 ≤ t)
    (hsigma : (∑ j : J, z j ^ 2) = sigmaSq)
    (hvarLower : a * nPow ≤ sigmaSq)
    (hvarUpper : sigmaSq ≤ A * nPow)
    (hthreshold : A * nPow ≤ t ^ 2)
    (hM : ∀ j, |z j| ≤ M)
    (hsmallScale : 8 * t * M ≤ a * nPow)
    (htsq : t ^ 2 = eps ^ 2 * nPow * logn) :
    (1 / 2 : ℝ) * Real.exp (-(96 * eps ^ 2 * logn / a)) ≤
      finiteUniformProbability
        (fun ε : J → Bool => t ≤ WeightedSignTilt.weightedSum z ε) := by
  rw [← p3_weightedUniformProbability_eq_finiteUniformProbability]
  exact p3_component_tail_from_p1_bounds z t sigmaSq M a A nPow eps logn
    ha hnPow ht0 hsigma hvarLower hvarUpper hthreshold hM hsmallScale htsq

/--
Integrate the second good event, still with the complete internal
realization fixed outside this theorem.

The result is already an absolute-value tail: the proof uses only the
one-sided event supplied by the weighted tilt and the inclusion
`{t ≤ Y} ⊆ {t ≤ |Y|}`.
-/
theorem p3_component_tail_after_second_good
    {H J : Type} [Fintype H] [Nonempty H]
    [Fintype J] [DecidableEq J]
    (G2 : H → Prop) [DecidablePred G2]
    (z : H → J → ℝ) (sigmaSq : H → ℝ)
    (t M a A nPow eps logn pExt : ℝ)
    (ha : 0 < a) (hnPow : 0 < nPow) (ht0 : 0 ≤ t)
    (hpExt0 : 0 ≤ pExt)
    (hG2 : pExt ≤ finiteUniformProbability G2)
    (hsigma : ∀ h, G2 h → (∑ j : J, z h j ^ 2) = sigmaSq h)
    (hvarLower : ∀ h, G2 h → a * nPow ≤ sigmaSq h)
    (hvarUpper : ∀ h, G2 h → sigmaSq h ≤ A * nPow)
    (hthreshold : A * nPow ≤ t ^ 2)
    (hM : ∀ h, G2 h → ∀ j, |z h j| ≤ M)
    (hsmallScale : 8 * t * M ≤ a * nPow)
    (htsq : t ^ 2 = eps ^ 2 * nPow * logn) :
    pExt * ((1 / 2 : ℝ) * Real.exp (-(96 * eps ^ 2 * logn / a))) ≤
      finiteUniformProbability
        (fun x : H × (J → Bool) =>
          t ≤ |WeightedSignTilt.weightedSum (z x.1) x.2|) := by
  classical
  let q : ℝ := (1 / 2 : ℝ) * Real.exp (-(96 * eps ^ 2 * logn / a))
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hfiber : ∀ h, G2 h → q ≤ finiteUniformProbability
      (fun ε : J → Bool => t ≤ WeightedSignTilt.weightedSum (z h) ε) := by
    intro h hg
    dsimp [q]
    exact p3_component_tail_finite_uniform
      (z h) t (sigmaSq h) M a A nPow eps logn
      ha hnPow ht0 (hsigma h hg) (hvarLower h hg) (hvarUpper h hg)
      hthreshold (hM h hg) hsmallScale htsq
  have hjoint : pExt * q ≤
      finiteUniformProbability
        (fun x : H × (J → Bool) =>
          G2 x.1 ∧ t ≤ WeightedSignTilt.weightedSum (z x.1) x.2) :=
    p3_finiteUniformProbability_good_fiber_lower
      G2 (fun h ε => t ≤ WeightedSignTilt.weightedSum (z h) ε)
      pExt q hpExt0 hq0 hG2 hfiber
  calc
    pExt * ((1 / 2 : ℝ) * Real.exp (-(96 * eps ^ 2 * logn / a))) =
        pExt * q := rfl
    _ ≤ finiteUniformProbability
        (fun x : H × (J → Bool) =>
          G2 x.1 ∧ t ≤ WeightedSignTilt.weightedSum (z x.1) x.2) := hjoint
    _ ≤ finiteUniformProbability
        (fun x : H × (J → Bool) =>
          t ≤ |WeightedSignTilt.weightedSum (z x.1) x.2|) := by
      apply finiteUniformProbability_mono
      intro x hx
      exact hx.2.trans (le_abs_self _)

/-- With the value `a = α/4`, the exponent constant is exactly
`96/a = 384/α`. -/
theorem p3_exponent_constant_from_alpha
    (alpha : ℝ) (hα : alpha ≠ 0) :
    96 / (alpha / 4) = 384 / alpha := by
  field_simp [hα]
  ring

/-- With `pExt = 1/(8*3^h)`, multiplying by the tilt factor `1/2` gives the
single-component prefactor `1/(16*3^h)`. -/
theorem p3_prefactor_constant (h : ℕ) :
    (1 / ((8 : ℝ) * 3 ^ h)) * (1 / 2 : ℝ) =
      1 / ((16 : ℝ) * 3 ^ h) := by
  have h3 : (3 : ℝ) ^ h ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [h3]
  ring

/-- Combined constant rewrite used in the statement
`c_K * exp (-(C_K * eps^2 * log n))`, with
`c_K = 1/(16*3^h)` and `C_K = 384/alpha`. -/
theorem p3_component_constant_form
    (alpha eps logn : ℝ) (h : ℕ) (hα : alpha ≠ 0) :
    (1 / ((8 : ℝ) * 3 ^ h)) *
        ((1 / 2 : ℝ) *
          Real.exp (-(96 * eps ^ 2 * logn / (alpha / 4)))) =
      (1 / ((16 : ℝ) * 3 ^ h)) *
        Real.exp (-((384 / alpha) * eps ^ 2 * logn)) := by
  have hExpArg :
      96 * eps ^ 2 * logn / (alpha / 4) =
        (384 / alpha) * eps ^ 2 * logn := by
    field_simp [hα]
    ring
  rw [hExpArg]
  have h3 : (3 : ℝ) ^ h ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [h3]
  ring


end GraphMatrixReplica
