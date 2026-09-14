import GraphMatrix.Probability.MomentComparison.ExactPairInjection
import GraphMatrix.RademacherCharacterSum
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# X3a B: actual finite sign moments and standard Gaussian moments

This module uses a genuine finite uniform probability space for the signs and
Mathlib's `ProbabilityTheory.gaussianReal 0 1` for the Gaussian.  The finite
sign moment is obtained from the exact character sum.  The Gaussian moment is
obtained by differentiating its genuine moment-generating function; no CLT or
asymptotic replacement is used.
-/

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace GraphMatrixReplica.ScalarMomentComparison

/-- The finite sample space carrying the `m` independent Boolean signs. -/
abbrev ScalarSignSpace (m : ℕ) := Fin m → Bool

/-- Real-valued Rademacher sign. -/
def scalarRademacher (b : Bool) : ℝ := (GraphMatrixReplica.rademacherSign b : ℤ)

@[simp] theorem scalarRademacher_false : scalarRademacher false = 1 := by
  norm_num [scalarRademacher, GraphMatrixReplica.rademacherSign]

@[simp] theorem scalarRademacher_true : scalarRademacher true = -1 := by
  norm_num [scalarRademacher, GraphMatrixReplica.rademacherSign]

@[simp] theorem scalarRademacher_sq (b : Bool) : scalarRademacher b ^ 2 = 1 := by
  cases b <;> norm_num [scalarRademacher, GraphMatrixReplica.rademacherSign]

/-- Unnormalised finite sign sum. -/
def scalarSignRawSum (m : ℕ) (ε : ScalarSignSpace m) : ℝ :=
  ∑ j : Fin m, scalarRademacher (ε j)

/-- The normalized Rademacher sum `S_m`. -/
def scalarSignSum (m : ℕ) (ε : ScalarSignSpace m) : ℝ :=
  (Real.sqrt (m : ℝ))⁻¹ * scalarSignRawSum m ε

/-- The actual uniform probability mass function on all sign assignments. -/
def scalarSignSourcePMF (m : ℕ) : PMF (ScalarSignSpace m) :=
  PMF.uniformOfFintype (ScalarSignSpace m)

/-- The corresponding actual finite probability measure. -/
def scalarSignSourceLaw (m : ℕ) : Measure (ScalarSignSpace m) :=
  (scalarSignSourcePMF m).toMeasure

instance scalarSignSourceLaw_probability (m : ℕ) :
    IsProbabilityMeasure (scalarSignSourceLaw m) := by
  unfold scalarSignSourceLaw
  infer_instance

/-- Measurability of the finite sign sum. -/
theorem measurable_scalarSignSum (m : ℕ) : Measurable (scalarSignSum m) := by
  exact measurable_of_finite _

/-- The law on `ℝ` of the actual normalized finite sign sum. -/
def scalarSignLaw (m : ℕ) : Measure ℝ :=
  Measure.map (scalarSignSum m) (scalarSignSourceLaw m)

instance scalarSignLaw_probability (m : ℕ) : IsProbabilityMeasure (scalarSignLaw m) := by
  unfold scalarSignLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_scalarSignSum m).aemeasurable

/-- Every power of the finite sign sum is integrable. -/
theorem integrable_scalarSignSum_pow (m n : ℕ) :
    Integrable (fun ε : ScalarSignSpace m => scalarSignSum m ε ^ n)
      (scalarSignSourceLaw m) := by
  exact Integrable.of_finite

/-- Every power is integrable under the pushed-forward sign law. -/
theorem integrable_id_pow_scalarSignLaw (m n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (scalarSignLaw m) := by
  unfold scalarSignLaw
  refine (integrable_map_measure (by fun_prop)
    (measurable_scalarSignSum m).aemeasurable).2 ?_
  simpa [Function.comp_def] using integrable_scalarSignSum_pow m n

/-- Expectation under the finite uniform sign source is the normalized finite
sum. -/
theorem integral_scalarSignSourceLaw_eq_average
    (m : ℕ) (f : ScalarSignSpace m → ℝ) :
    (∫ ε, f ε ∂scalarSignSourceLaw m) =
      ((2 : ℝ) ^ m)⁻¹ * ∑ ε : ScalarSignSpace m, f ε := by
  classical
  unfold scalarSignSourceLaw scalarSignSourcePMF
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, smul_eq_mul, ← Finset.mul_sum]

/-- Real form of the exact finite Rademacher character average. -/
theorem real_rademacherCharacterAverage_eq_indicator
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K) :
    ((2 : ℝ) ^ Fintype.card K)⁻¹ *
        (∑ ε : K → Bool,
          ∏ a : A, scalarRademacher (ε (key a))) =
      if ∀ k : K, Even (GraphMatrixReplica.occurrenceMultiplicity key k)
      then 1 else 0 := by
  classical
  have hcast :
      (∑ ε : K → Bool,
        ∏ a : A, scalarRademacher (ε (key a))) =
        ((GraphMatrixReplica.rademacherCharacterSum key : ℤ) : ℝ) := by
    simp [GraphMatrixReplica.rademacherCharacterSum,
      GraphMatrixReplica.rademacherCharacter, scalarRademacher]
  rw [hcast, GraphMatrixReplica.rademacherCharacterSum_eq_indicator]
  by_cases h : ∀ k : K,
      Even (GraphMatrixReplica.occurrenceMultiplicity key k)
  · rw [if_pos h, if_pos h]
    norm_num [pow_ne_zero]
  · rw [if_neg h, if_neg h]
    simp

/-- Expansion of the unnormalised `n`-th sign moment as a sum over index
words, with the exact parity indicator on every word. -/
theorem integral_scalarSignRawSum_pow
    (m n : ℕ) :
    (∫ ε : ScalarSignSpace m, scalarSignRawSum m ε ^ n
      ∂scalarSignSourceLaw m) =
      ∑ w : Fin n → Fin m,
        if ∀ a : Fin m,
          Even (GraphMatrixReplica.occurrenceMultiplicity w a)
        then 1 else 0 := by
  classical
  rw [integral_scalarSignSourceLaw_eq_average]
  simp_rw [scalarSignRawSum, Fintype.sum_pow]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have hchar := real_rademacherCharacterAverage_eq_indicator w
  convert hchar using 1 <;>
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Exact count of even words in the actual finite `2k`-th raw sign moment. -/
theorem integral_scalarSignRawSum_even_pow (m k : ℕ) :
    (∫ ε : ScalarSignSpace m, scalarSignRawSum m ε ^ (2 * k)
      ∂scalarSignSourceLaw m) =
      Fintype.card (ScalarEvenWord m k) := by
  classical
  rw [show 2 * k = k * 2 by omega]
  rw [integral_scalarSignRawSum_pow]
  norm_cast
  simp [ScalarEvenWord, ScalarWord, scalarMultiplicity]
  have hsub : Fintype.card
        {w : ScalarWord m k //
          ∀ a : Fin m, Even (GraphMatrixReplica.occurrenceMultiplicity w a)} =
      (Finset.univ.filter fun w : ScalarWord m k =>
        ∀ a : Fin m,
          Even (GraphMatrixReplica.occurrenceMultiplicity w a)).card := by
    rw [Fintype.card_subtype]
  let e : {w : ScalarWord m k //
        ∀ a : Fin m,
          Even (GraphMatrixReplica.occurrenceMultiplicity w a)} ≃
      ScalarEvenWord m k := {
    toFun := fun w => ⟨w.1, w.2⟩
    invFun := fun w => ⟨w.1, w.2⟩
    left_inv := by intro w; rfl
    right_inv := by intro w; rfl
  }
  exact hsub.symm.trans (Fintype.card_congr e)

/-- If all fibers of a finite key are even, then the size of the domain is
even. -/
theorem even_card_of_all_occurrenceMultiplicity_even
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K)
    (hEven : ∀ k : K, Even (GraphMatrixReplica.occurrenceMultiplicity key k)) :
    Even (Fintype.card A) := by
  classical
  choose half hhalf using hEven
  refine ⟨∑ k : K, half k, ?_⟩
  have hsum := GraphMatrixReplica.ScalarMomentComparison.sum_occurrenceMultiplicity key
  calc
    Fintype.card A = ∑ k : K,
        GraphMatrixReplica.occurrenceMultiplicity key k := hsum.symm
    _ = ∑ k : K, (half k + half k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hhalf k
    _ = (∑ k : K, half k) + ∑ k : K, half k := by
      rw [Finset.sum_add_distrib]

/-- The unnormalised odd moments cancel exactly. -/
theorem integral_scalarSignRawSum_odd_pow (m k : ℕ) :
    (∫ ε : ScalarSignSpace m, scalarSignRawSum m ε ^ (2 * k + 1)
      ∂scalarSignSourceLaw m) = 0 := by
  classical
  rw [integral_scalarSignRawSum_pow]
  apply Finset.sum_eq_zero
  intro w _
  have hnot : ¬ ∀ a : Fin m,
      Even (GraphMatrixReplica.occurrenceMultiplicity w a) := by
    intro h
    have he := even_card_of_all_occurrenceMultiplicity_even w h
    have he' : Even (2 * k + 1) := by simpa using he
    rcases he' with ⟨q, hq⟩
    omega
  simp [hnot]

/-- Power of the positive square root appearing in the normalization. -/
theorem sqrt_nat_even_pow {m k : ℕ} (hm : 1 ≤ m) :
    Real.sqrt (m : ℝ) ^ (2 * k) = (m : ℝ) ^ k := by
  rw [pow_mul, Real.sq_sqrt (by positivity)]

/-- Exact actual finite-sign even moment. -/
theorem scalarSignSource_evenMoment {m k : ℕ} (hm : 1 ≤ m) :
    (∫ ε : ScalarSignSpace m, scalarSignSum m ε ^ (2 * k)
      ∂scalarSignSourceLaw m) =
      (Fintype.card (ScalarEvenWord m k) : ℝ) / (m : ℝ) ^ k := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp_rw [scalarSignSum, mul_pow]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_scalarSignRawSum_even_pow]
  rw [inv_pow, sqrt_nat_even_pow hm]
  field_simp

/-- Exact actual finite-sign odd moment. -/
theorem scalarSignSource_oddMoment {m k : ℕ} (hm : 1 ≤ m) :
    (∫ ε : ScalarSignSpace m, scalarSignSum m ε ^ (2 * k + 1)
      ∂scalarSignSourceLaw m) = 0 := by
  simp_rw [scalarSignSum, mul_pow]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_scalarSignRawSum_odd_pow]
  simp

/-- Zero-th moment of the finite sign source. -/
theorem scalarSignSource_zeroMoment (m : ℕ) :
    (∫ _ε : ScalarSignSpace m, (1 : ℝ) ∂scalarSignSourceLaw m) = 1 := by
  simp

/-- Moment transfer from the finite source to its law on `ℝ`. -/
theorem integral_pow_scalarSignLaw (m n : ℕ) :
    (∫ x : ℝ, x ^ n ∂scalarSignLaw m) =
      ∫ ε : ScalarSignSpace m, scalarSignSum m ε ^ n
        ∂scalarSignSourceLaw m := by
  unfold scalarSignLaw
  exact MeasureTheory.integral_map_of_stronglyMeasurable
    (measurable_scalarSignSum m) (continuous_pow n).stronglyMeasurable

/-- Exact even moment under the actual law on `ℝ`. -/
theorem scalarSign_evenMoment {m k : ℕ} (hm : 1 ≤ m) :
    (∫ x : ℝ, x ^ (2 * k) ∂scalarSignLaw m) =
      (Fintype.card (ScalarEvenWord m k) : ℝ) / (m : ℝ) ^ k := by
  rw [integral_pow_scalarSignLaw]
  exact scalarSignSource_evenMoment hm

/-- Every odd moment of the actual sign law vanishes. -/
theorem scalarSign_oddMoment {m k : ℕ} (hm : 1 ≤ m) :
    (∫ x : ℝ, x ^ (2 * k + 1) ∂scalarSignLaw m) = 0 := by
  rw [integral_pow_scalarSignLaw]
  exact scalarSignSource_oddMoment hm

/-- Zero-th moment of the actual sign law. -/
@[simp] theorem scalarSign_zeroMoment (m : ℕ) :
    (∫ _x : ℝ, (1 : ℝ) ∂scalarSignLaw m) = 1 := by
  simp

/-- The genuine standard real Gaussian law used by X3a. -/
def standardGaussianLaw : Measure ℝ := ProbabilityTheory.gaussianReal 0 1

instance standardGaussianLaw_probability : IsProbabilityMeasure standardGaussianLaw := by
  unfold standardGaussianLaw
  infer_instance

/-- All natural powers are integrable under the standard Gaussian law. -/
theorem standardGaussian_pow_integrable (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) standardGaussianLaw := by
  have hLp := ProbabilityTheory.memLp_id_gaussianReal'
    (μ := (0 : ℝ)) (v := (1 : NNReal)) (n : ENNReal) (by simp)
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [standardGaussianLaw, Function.comp_def, norm_pow] using
    hLp.integrable_norm_rpow'

/-- The standard Gaussian MGF is `exp(t^2/2)`. -/
theorem standardGaussian_mgf :
    ProbabilityTheory.mgf id standardGaussianLaw =
      fun t : ℝ => Real.exp (t ^ 2 / 2) := by
  simpa [standardGaussianLaw] using
    (ProbabilityTheory.mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)))

/-- The MGF's integrability interval is all of `ℝ`. -/
theorem zero_mem_standardGaussian_mgf_interior :
    (0 : ℝ) ∈ interior
      (ProbabilityTheory.integrableExpSet id standardGaussianLaw) := by
  simp [standardGaussianLaw]

/-- Gaussian moments are the derivatives at zero of the actual Gaussian MGF. -/
theorem standardGaussian_moment_eq_iteratedDeriv (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂standardGaussianLaw) =
      iteratedDeriv n (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  have h := ProbabilityTheory.iteratedDeriv_mgf_zero
    (X := id) (μ := standardGaussianLaw)
    zero_mem_standardGaussian_mgf_interior n
  rw [standardGaussian_mgf] at h
  simpa [Function.comp_def] using h.symm

/-- Derivative identity for the standard Gaussian MGF. -/
theorem deriv_standardGaussian_mgf_formula :
    deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t : ℝ => t * Real.exp (t ^ 2 / 2) := by
  funext t
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, deriv_fun_pow, Nat.add_one_sub_one,
    pow_one, deriv_id'', mul_one]
  ring

/-- Recurrence `M_{n+2}=(n+1)M_n` for derivatives at zero of `exp(t^2/2)`. -/
theorem standardGaussian_iteratedDeriv_recurrence (n : ℕ) :
    iteratedDeriv (n + 2) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
      (n + 1 : ℝ) *
        iteratedDeriv n (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  rw [show n + 2 = (n + 1) + 1 by omega, iteratedDeriv_succ']
  rw [deriv_standardGaussian_mgf_formula]
  have hid : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞) (fun x : ℝ => x) 0 :=
    contDiff_id.contDiffAt
  have hexp : ContDiffAt ℝ ((n + 1 : ℕ) : ℕ∞)
      (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
    fun_prop
  rw [iteratedDeriv_fun_mul hid hexp]
  simp only [iteratedDeriv_fun_id_zero]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b hb hb1
    by_cases hb0 : b = 0
    · subst b
      simp
    · have hbne1 : b ≠ 1 := by simpa using hb1
      simp [hbne1]
  · intro h
    simp at h

/-- Zero-th Gaussian moment. -/
@[simp] theorem standardGaussian_zeroMoment :
    (∫ _x : ℝ, (1 : ℝ) ∂standardGaussianLaw) = 1 := by
  simp

/-- First Gaussian moment. -/
@[simp] theorem standardGaussian_oneMoment :
    (∫ x : ℝ, x ∂standardGaussianLaw) = 0 := by
  simpa [standardGaussianLaw] using
    (ProbabilityTheory.integral_id_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : NNReal)))

/-- Exact odd Gaussian moments. -/
theorem standardGaussian_oddMoment (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k + 1) ∂standardGaussianLaw) = 0 := by
  induction k with
  | zero => simpa using standardGaussian_oneMoment
  | succ k ih =>
      rw [standardGaussian_moment_eq_iteratedDeriv]
      have hr := standardGaussian_iteratedDeriv_recurrence (2 * k + 1)
      have ih' := standardGaussian_moment_eq_iteratedDeriv (2 * k + 1)
      rw [← ih'] at hr
      rw [ih] at hr
      simpa [Nat.mul_add, Nat.add_mul] using hr

/-- Exact even Gaussian moment as the project's recursive odd double factorial. -/
theorem standardGaussian_evenMoment (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂standardGaussianLaw) =
      (GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ) := by
  induction k with
  | zero => simp [standardGaussianLaw, GraphMatrixReplica.rademacherPerfectMatchingCount]
  | succ k ih =>
      rw [standardGaussian_moment_eq_iteratedDeriv]
      have hr := standardGaussian_iteratedDeriv_recurrence (2 * k)
      have hk := standardGaussian_moment_eq_iteratedDeriv (2 * k)
      rw [← hk] at hr
      rw [ih] at hr
      rw [GraphMatrixReplica.rademacherPerfectMatchingCount]
      norm_num at hr ⊢
      exact_mod_cast hr

/-- Finite exact scalar lower/upper comparison before the exponential
simplification. -/
theorem scalarSign_evenMoment_twoSided
    {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ m) :
    (GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ) *
          (m.descFactorial k : ℝ) / (m : ℝ) ^ k ≤
      (∫ x : ℝ, x ^ (2 * k) ∂scalarSignLaw m) ∧
    (∫ x : ℝ, x ^ (2 * k) ∂scalarSignLaw m) ≤
      (GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ) := by
  have hmpos : 0 < (m : ℝ) ^ k := by positivity
  rw [scalarSign_evenMoment hm]
  constructor
  · apply (div_le_div_iff_of_pos_right hmpos).2
    exact_mod_cast card_scalarEvenWord_lower m k
  · have hcard := card_scalarEvenWord_le m k
    have hreal : (Fintype.card (ScalarEvenWord m k) : ℝ) ≤
        (GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ) *
          (m : ℝ) ^ k := by exact_mod_cast hcard
    have := (div_le_iff₀ hmpos).2 hreal
    simpa [mul_assoc] using this

/-- Elementary factor inequality used in the falling-factorial estimate. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hlin : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have hden : 0 < 1 + 2 * x := by linarith
  have hrec : Real.exp (-2 * x) ≤ (1 + 2 * x)⁻¹ := by
    rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
    exact inv_anti₀ hden hlin
  have hfrac : (1 + 2 * x)⁻¹ ≤ 1 - x := by
    rw [← mul_le_mul_iff_of_pos_left hden]
    field_simp
    nlinarith
  exact hrec.trans hfrac

/-- Sharp finite falling-factorial lower bound in the range `2k ≤ m`.
The real exponent is exactly `-k(k-1)/m`; no natural-number division occurs. -/
theorem descFactorial_div_pow_ge_exp
    {m k : ℕ} (hm : 1 ≤ m) (hkm : 2 * k ≤ m) :
    Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ))) ≤
      (m.descFactorial k : ℝ) / (m : ℝ) ^ k := by
  have hmR : 0 < (m : ℝ) := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
      have hkm' : 2 * k ≤ m := by omega
      have ih' := ih hkm'
      have hkhalf : (k : ℝ) / (m : ℝ) ≤ 1 / 2 := by
        apply (div_le_iff₀ hmR).2
        have hcast : (2 * k : ℕ) ≤ m := by omega
        have hcastR : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hcast
        nlinarith
      have hk0 : 0 ≤ (k : ℝ) / (m : ℝ) := by positivity
      have hfactor := exp_neg_two_mul_le_one_sub hk0 hkhalf
      have hksub : k ≤ m := by omega
      have hcastsub : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
        exact Nat.cast_sub hksub
      rw [Nat.descFactorial_succ, Nat.cast_mul, hcastsub, pow_succ]
      have hprod := mul_le_mul ih' hfactor (Real.exp_pos _).le
        (by positivity)
      have hpositive : 0 < (m : ℝ) ^ k := by positivity
      calc
        Real.exp (-(((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) - 1) /
            (m : ℝ))) =
            Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ))) *
              Real.exp (-2 * ((k : ℝ) / (m : ℝ))) := by
                rw [← Real.exp_add]
                congr 1
                field_simp
                push_cast
                ring
        _ ≤ ((m.descFactorial k : ℝ) / (m : ℝ) ^ k) *
              (1 - (k : ℝ) / (m : ℝ)) := hprod
        _ = (((m : ℝ) - (k : ℝ)) * (m.descFactorial k : ℝ)) /
              ((m : ℝ) * (m : ℝ) ^ k) := by
                field_simp
        _ = (((m : ℝ) - (k : ℝ)) * (m.descFactorial k : ℝ)) /
              ((m : ℝ) ^ k * (m : ℝ)) := by
                ring

/-- Final finite exact scalar comparison in the range needed by the trace
argument. -/
theorem scalarSign_gaussian_evenMoment_comparison
    {m k : ℕ} (hm : 1 ≤ m) (hkm : 2 * k ≤ m) :
    (∫ x : ℝ, x ^ (2 * k) ∂scalarSignLaw m) ≤
      (∫ x : ℝ, x ^ (2 * k) ∂standardGaussianLaw) ∧
    (∫ x : ℝ, x ^ (2 * k) ∂standardGaussianLaw) ≤
      Real.exp ((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ)) *
        (∫ x : ℝ, x ^ (2 * k) ∂scalarSignLaw m) := by
  have hk : k ≤ m := by omega
  have htwo := scalarSign_evenMoment_twoSided hm hk
  rw [standardGaussian_evenMoment]
  constructor
  · exact htwo.2
  · have hfall := descFactorial_div_pow_ge_exp hm hkm
    have hcount : 0 ≤ (GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ) := by
      positivity
    have hmomentLower := htwo.1
    have hmul := mul_le_mul_of_nonneg_left hfall hcount
    have hexppos : 0 < Real.exp ((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ)) :=
      Real.exp_pos _
    have hcancel :
        Real.exp ((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ)) *
          Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ))) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      (GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ) =
          Real.exp ((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ)) *
            (Real.exp (-((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ))) *
              (GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ)) := by
                rw [← mul_assoc, hcancel, one_mul]
      _ ≤ Real.exp ((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ)) *
            ((GraphMatrixReplica.rademacherPerfectMatchingCount k : ℝ) *
              (m.descFactorial k : ℝ) / (m : ℝ) ^ k) := by
                gcongr
                simpa [mul_div_assoc, mul_assoc, mul_comm, mul_left_comm] using hmul
      _ ≤ Real.exp ((k : ℝ) * ((k : ℝ) - 1) / (m : ℝ)) *
            (∫ x : ℝ, x ^ (2 * k) ∂scalarSignLaw m) := by
                gcongr

end GraphMatrixReplica.ScalarMomentComparison
