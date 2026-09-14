import GraphMatrix.Counting.IidTailIntegral
import GraphMatrix.GraphMatrixEntryMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # A finite-space Gaussian tail-to-moment lemma

This module starts from an assumed tail bound for a nonnegative random
variable on a finite measure space. It does not establish that tail bound for
the iid sign-matrix net. The layer-cake formula and the Gaussian Gamma kernel
give the exact even-moment estimate, followed by its `L^(2q)` root form.
-/

noncomputable section
open Set MeasureTheory Real

namespace GraphMatrixReplica

/-- The normalized counting measure on a finite discrete type agrees with
`paperMean`, including the empty type. -/
theorem c079_uniformIntegral_eq_paperMean
    {Ω : Type} [Fintype Ω] (f : Ω → ℝ) :
    (letI : MeasurableSpace Ω := ⊤
     ∫ ω, f ω ∂
       ((Fintype.card Ω : NNReal)⁻¹ • Measure.count)) =
      paperMean f := by
  letI : MeasurableSpace Ω := ⊤
  rw [integral_smul_nnreal_measure, integral_count]
  simp [paperMean, NNReal.smul_def, smul_eq_mul]

/-- For a finite-space nonnegative variable, change the threshold in the
layer-cake formula from `X^n` to `X`. -/
theorem c079_finite_moment_eq_tail_integral
    {α : Type*} [MeasurableSpace α] [Finite α]
    [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : ∀ a, 0 ≤ X a) (n : ℕ) (hn : 0 < n) :
    (∫ a, X a ^ n ∂μ) =
      ∫ t in Ioi 0, (n : ℝ) * t ^ ((n : ℝ) - 1) *
        μ.real {a | t < X a} := by
  have hLayer : (∫ a, X a ^ n ∂μ) =
      ∫ u in Ioi 0, μ.real {a | u < X a ^ n} :=
    (Integrable.of_finite : Integrable (fun a => X a ^ n) μ).integral_eq_integral_meas_lt
      (Filter.Eventually.of_forall (fun a => pow_nonneg (hX a) _))
  have hSub := integral_comp_rpow_Ioi_of_pos
    (g := fun u : ℝ => μ.real {a | u < X a ^ n})
    (p := (n : ℝ)) (by exact_mod_cast hn)
  calc
    (∫ a, X a ^ n ∂μ) =
        ∫ u in Ioi 0, μ.real {a | u < X a ^ n} := hLayer
    _ = ∫ t in Ioi 0, (n : ℝ) * t ^ ((n : ℝ) - 1) *
          μ.real {a | t ^ n < X a ^ n} := by
      simpa only [smul_eq_mul, Real.rpow_natCast] using hSub.symm
    _ = ∫ t in Ioi 0, (n : ℝ) * t ^ ((n : ℝ) - 1) *
          μ.real {a | t < X a} := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hset : {a | t ^ n < X a ^ n} = {a | t < X a} := by
        ext a
        have ht0 : 0 ≤ t := le_of_lt ht
        constructor
        · exact lt_of_pow_lt_pow_left₀ n (hX a)
        · intro h
          exact pow_lt_pow_left₀ h ht0 (by omega)
      dsimp only
      rw [hset]

/-- A Gaussian survival bound dominates the finite-space moment by the
corresponding Gaussian tail integral. -/
theorem c079_finite_moment_le_gaussian_kernel
    {α : Type*} [MeasurableSpace α] [Finite α]
    [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : ∀ a, 0 ≤ X a) (n : ℕ) (hn : 0 < n)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      μ.real {a | t < X a} ≤ Real.exp (-(t ^ 2 / 2))) :
    (∫ a, X a ^ n ∂μ) ≤
      ∫ t in Ioi 0, (n : ℝ) * t ^ ((n : ℝ) - 1) *
        Real.exp (-(t ^ 2 / 2)) := by
  let s : ℝ := (n : ℝ) - 1
  have hs : -1 < s := by
    change -1 < (n : ℝ) - 1
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hG0 : IntegrableOn (fun t : ℝ =>
      t ^ s * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) hs
  have hG : IntegrableOn (fun t : ℝ =>
      (n : ℝ) * t ^ s * Real.exp (-(t ^ 2 / 2))) (Ioi 0) := by
    change Integrable (fun t : ℝ =>
      (n : ℝ) * t ^ s * Real.exp (-(t ^ 2 / 2)))
        (volume.restrict (Ioi 0))
    have hh := hG0.const_mul (n : ℝ)
    change Integrable (fun t : ℝ =>
      (n : ℝ) * (t ^ s * Real.exp (-(1 / 2 : ℝ) * t ^ 2)))
        (volume.restrict (Ioi 0)) at hh
    have hEq : (fun t : ℝ =>
        (n : ℝ) * t ^ s * Real.exp (-(t ^ 2 / 2))) =
        (fun t : ℝ =>
          (n : ℝ) * (t ^ s * Real.exp (-(1 / 2 : ℝ) * t ^ 2))) := by
      funext t
      have he : -(t ^ 2 / 2) = -(1 / 2 : ℝ) * t ^ 2 := by ring
      rw [he]
      ring
    rw [hEq]
    exact hh
  have hmono : Antitone (fun t : ℝ => μ.real {a | t < X a}) := by
    intro t u htu
    exact measureReal_mono (by
      intro a ha
      exact lt_of_le_of_lt htu ha) (by finiteness)
  have hmeas : Measurable (fun t : ℝ =>
      (n : ℝ) * t ^ s * μ.real {a | t < X a}) := by
    fun_prop (disch := positivity)
  have hF : IntegrableOn (fun t : ℝ =>
      (n : ℝ) * t ^ s * μ.real {a | t < X a}) (Ioi 0) := by
    apply hG.mono' hmeas.aestronglyMeasurable
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hs0 : 0 ≤ t ^ s := Real.rpow_nonneg ht0 _
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hm0 : 0 ≤ μ.real {a | t < X a} := measureReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change (n : ℝ) * t ^ s * μ.real {a | t < X a} ≤
      (n : ℝ) * t ^ s * Real.exp (-(t ^ 2 / 2))
    gcongr
    exact hTail t ht0
  rw [c079_finite_moment_eq_tail_integral X hX n hn]
  exact setIntegral_mono_on hF hG measurableSet_Ioi (by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hs0 : 0 ≤ t ^ s := Real.rpow_nonneg ht0 _
    change (n : ℝ) * t ^ s * μ.real {a | t < X a} ≤
      (n : ℝ) * t ^ s * Real.exp (-(t ^ 2 / 2))
    gcongr
    exact hTail t ht0)

/-- The Gaussian tail integral at even order is exactly `2^q q!`. -/
theorem c079_gaussian_tail_kernel_exact (q : ℕ) (hq : 0 < q) :
    (∫ t : ℝ in Ioi 0,
      ((2 * q : ℕ) : ℝ) * t ^ (((2 * q : ℕ) : ℝ) - 1) *
        Real.exp (-(t ^ 2 / 2))) =
      (2 : ℝ) ^ q * (q.factorial : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have hKernel := integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := (((2 * (k + 1) : ℕ) : ℝ) - 1))
    (b := 1 / 2) (by norm_num) (by
      have hk : 0 < ((2 * (k + 1) : ℕ) : ℝ) := by positivity
      linarith) (by norm_num)
  simp only [Real.rpow_two, neg_div] at hKernel
  have hGamma : Real.Gamma (((((2 * (k + 1) : ℕ) : ℝ) - 1) + 1) / 2) =
      (k.factorial : ℝ) := by
    convert Real.Gamma_nat_eq_factorial k using 1
    norm_num
  have hRpow : (1 / 2 : ℝ) ^
      (-(((((2 * (k + 1) : ℕ) : ℝ) - 1) + 1) / 2)) =
      (2 : ℝ) ^ (k + 1) := by
    have hExp : -(((((2 * (k + 1) : ℕ) : ℝ) - 1) + 1) / 2) =
        -(((k + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [hExp, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num [one_div_pow]
  calc
    (∫ t : ℝ in Ioi 0,
        ((2 * (k + 1) : ℕ) : ℝ) *
          t ^ (((2 * (k + 1) : ℕ) : ℝ) - 1) *
          Real.exp (-(t ^ 2 / 2))) =
      ((2 * (k + 1) : ℕ) : ℝ) *
        ∫ t : ℝ in Ioi 0,
          t ^ (((2 * (k + 1) : ℕ) : ℝ) - 1) *
            Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      have he : -(t ^ 2 / 2) = -(1 / 2 : ℝ) * t ^ 2 := by ring
      rw [he]
      ring
    _ = ((2 * (k + 1) : ℕ) : ℝ) *
          ((1 / 2 : ℝ) ^
            (-(((((2 * (k + 1) : ℕ) : ℝ) - 1) + 1) / 2)) *
            (1 / 2 : ℝ) *
            Real.Gamma (((((2 * (k + 1) : ℕ) : ℝ) - 1) + 1) / 2)) := by
      exact congrArg
        (fun z : ℝ => (((2 * (k + 1) : ℕ) : ℝ) * z)) hKernel
    _ = (2 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) := by
      rw [hGamma, hRpow, Nat.factorial_succ]
      push_cast
      ring

/-- Exact factorial even-moment bound from an assumed Gaussian tail. -/
theorem c079_finite_gaussian_tail_even_moment
    {α : Type*} [MeasurableSpace α] [Finite α]
    [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : ∀ a, 0 ≤ X a) (q : ℕ) (hq : 0 < q)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      μ.real {a | t < X a} ≤ Real.exp (-(t ^ 2 / 2))) :
    (∫ a, X a ^ (2 * q) ∂μ) ≤
      (2 : ℝ) ^ q * (q.factorial : ℝ) := by
  exact (c079_finite_moment_le_gaussian_kernel X hX (2 * q)
    (by omega) hTail).trans_eq (c079_gaussian_tail_kernel_exact q hq)

/-- A simpler power bound, using `q! ≤ q^q`. -/
theorem c079_finite_gaussian_tail_even_moment_power
    {α : Type*} [MeasurableSpace α] [Finite α]
    [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : ∀ a, 0 ≤ X a) (q : ℕ) (hq : 0 < q)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      μ.real {a | t < X a} ≤ Real.exp (-(t ^ 2 / 2))) :
    (∫ a, X a ^ (2 * q) ∂μ) ≤
      (((2 * q : ℕ) : ℝ) ^ q) := by
  calc
    (∫ a, X a ^ (2 * q) ∂μ) ≤
        (2 : ℝ) ^ q * (q.factorial : ℝ) :=
      c079_finite_gaussian_tail_even_moment X hX q hq hTail
    _ ≤ (2 : ℝ) ^ q * (q : ℝ) ^ q := by
      gcongr
      exact_mod_cast Nat.factorial_le_pow q
    _ = (((2 * q : ℕ) : ℝ) ^ q) := by
      norm_cast
      rw [mul_pow]

/-- The `L^(2q)` norm bound required after a shifted Gaussian net tail.
The probability or net estimate itself is an explicit hypothesis. -/
theorem c079_finite_gaussian_tail_Lp_root
    {α : Type*} [MeasurableSpace α] [Finite α]
    [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : ∀ a, 0 ≤ X a) (q : ℕ) (hq : 0 < q)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      μ.real {a | t < X a} ≤ Real.exp (-(t ^ 2 / 2))) :
    (∫ a, X a ^ (2 * q) ∂μ) ^
        (1 / (((2 * q : ℕ) : ℝ))) ≤
      Real.sqrt (((2 * q : ℕ) : ℝ)) := by
  have hmean : 0 ≤ (∫ a, X a ^ (2 * q) ∂μ) :=
    integral_nonneg (fun a => pow_nonneg (hX a) _)
  have hq' : (0 : ℝ) < (((2 * q : ℕ) : ℝ)) := by positivity
  have hexp : 0 ≤ (1 / (((2 * q : ℕ) : ℝ))) := by positivity
  have hbound := c079_finite_gaussian_tail_even_moment_power X hX q hq hTail
  calc
    (∫ a, X a ^ (2 * q) ∂μ) ^
        (1 / (((2 * q : ℕ) : ℝ))) ≤
      (((((2 * q : ℕ) : ℝ)) ^ q) ^
        (1 / (((2 * q : ℕ) : ℝ)))) :=
      Real.rpow_le_rpow hmean hbound hexp
    _ = Real.sqrt (((2 * q : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (le_of_lt hq')]
      have he : (q : ℝ) * (1 / (((2 * q : ℕ) : ℝ))) = 1 / 2 := by
        push_cast
        field_simp
      rw [he, Real.sqrt_eq_rpow]


end GraphMatrixReplica

end
