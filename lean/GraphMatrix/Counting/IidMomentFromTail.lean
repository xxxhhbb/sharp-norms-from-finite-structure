import GraphMatrix.Counting.FiniteGaussianTailMoment
import GraphMatrix.Counting.IidSignMatrixHighMoment
import GraphMatrix.Counting.IidEvenWalkCountBound
import GraphMatrix.RademacherOpenWordContraction
import GraphMatrix.Counting.IidBilinearTail
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Conditional iid sign-matrix high moment from an explicit shifted net tail. -/

noncomputable section
open scoped Matrix.Norms.L2Operator
open MeasureTheory Set
namespace GraphMatrixReplica

theorem c079_uniform_measure_isProbability
    {Ω : Type} [Fintype Ω] [Nonempty Ω] :
    (letI : MeasurableSpace Ω := ⊤
     IsProbabilityMeasure
       ((Fintype.card Ω : NNReal)⁻¹ • (Measure.count : Measure Ω))) := by
  letI : MeasurableSpace Ω := ⊤
  constructor
  have hc : (Fintype.card Ω : NNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Ω› |>.ne'
  rw [Measure.smul_apply, Measure.count_apply (MeasurableSet.univ)]
  simp only [encard_univ, ENat.card_eq_coe_fintype_card]
  rw [ENNReal.smul_def, smul_eq_mul]
  change (((Fintype.card Ω : NNReal)⁻¹ : NNReal) : ENNReal) *
    ((Fintype.card Ω : NNReal) : ENNReal) = 1
  rw [← ENNReal.coe_mul]
  exact_mod_cast inv_mul_cancel₀ hc

theorem c079_uniform_measure_real_event_eq_probability
    {Ω : Type} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    (letI : MeasurableSpace Ω := ⊤
     (((Fintype.card Ω : NNReal)⁻¹ • (Measure.count : Measure Ω)).real
       {ω | P ω})) = finiteUniformProbability P := by
  letI : MeasurableSpace Ω := ⊤
  have hfun : (fun ω : Ω => if P ω then (1 : ℝ) else 0) =
      {ω | P ω}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : P ω <;> simp [h, Set.indicator]
  have h := c079_uniformIntegral_eq_paperMean
    (fun ω : Ω => if P ω then (1 : ℝ) else 0)
  change (∫ ω, (if P ω then (1 : ℝ) else 0) ∂
    ((Fintype.card Ω : NNReal)⁻¹ • Measure.count)) = _ at h
  have hIntegral : (∫ ω, (if P ω then (1 : ℝ) else 0) ∂
      ((Fintype.card Ω : NNReal)⁻¹ • Measure.count)) =
      (((Fintype.card Ω : NNReal)⁻¹ • (Measure.count : Measure Ω)).real
        {ω | P ω}) := by
    rw [hfun]
    exact integral_indicator_one (by exact MeasurableSet.of_discrete)
  exact hIntegral.symm.trans (by simpa [finiteUniformProbability] using h)

/-- A shifted Gaussian tail controls any pointwise dominated finite-space
variable by Minkowski's inequality. -/
theorem c079_shifted_gaussian_tail_lpNorm_bound
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Finite α] {μ : Measure α} [IsProbabilityMeasure μ]
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (R N : α → ℝ) (hR : ∀ a, 0 ≤ R a)
    (hN : ∀ a, ‖N a‖ ≤ C * (A + R a))
    (q : ℕ) (hq : 0 < q)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      μ.real {a | t < R a} ≤ Real.exp (-(t ^ 2 / 2))) :
    lpNorm N (ENNReal.ofReal (((2 * q : ℕ) : ℝ))) μ ≤
      C * (A + Real.sqrt (((2 * q : ℕ) : ℝ))) := by
  let r : ℝ := ((2 * q : ℕ) : ℝ)
  let p : ENNReal := ENNReal.ofReal r
  have hr : 0 < r := by dsimp [r]; positivity
  have hp0 : p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hpTop : p ≠ ⊤ := by simp [p]
  have hp1 : (1 : ENNReal) ≤ p := by
    change (1 : ENNReal) ≤ ENNReal.ofReal r
    have hr1 : (1 : ℝ) ≤ r := by dsimp [r]; exact_mod_cast (by omega : 1 ≤ 2 * q)
    simpa using (ENNReal.ofReal_le_ofReal hr1)
  have hto : p.toReal = r := by simp [p, le_of_lt hr]
  have hmemR : MemLp R p μ := MemLp.of_discrete
  have hmemAdd : MemLp (fun a => A + R a) p μ := MemLp.of_discrete
  have hmemScale : MemLp (fun a => C * (A + R a)) p μ := MemLp.of_discrete
  have hroot := c079_finite_gaussian_tail_Lp_root (μ := μ) R hR q hq hTail
  have hLpR : lpNorm R p μ ≤ Real.sqrt r := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpTop hmemR.aestronglyMeasurable]
    simp_rw [Real.norm_of_nonneg (hR _)]
    simp only [hto, inv_eq_one_div]
    simpa only [r, Real.rpow_natCast] using hroot
  have hLpA : lpNorm (fun _ : α => A) p μ = A := by
    rw [lpNorm_const' hp0 hpTop A]
    simp [probReal_univ, Real.norm_of_nonneg hA]
  have hLpAdd : lpNorm (fun a => A + R a) p μ ≤
      lpNorm (fun _ : α => A) p μ + lpNorm R p μ := by
    change lpNorm ((fun _ : α => A) + R) p μ ≤ _
    exact lpNorm_add_le (f := fun _ : α => A) (g := R)
      (μ := μ) (p := p) (MemLp.of_discrete) hp1
  calc
    lpNorm N p μ ≤ lpNorm (fun a => C * (A + R a)) p μ :=
      lpNorm_mono_real hmemScale hN
    _ = C * lpNorm (fun a => A + R a) p μ := by
      have hs := lpNorm_const_smul C (fun a : α => A + R a) μ (p := p)
      change lpNorm (C • (fun a : α => A + R a)) p μ =
        C * lpNorm (fun a => A + R a) p μ
      simpa [Real.norm_of_nonneg hC] using hs
    _ ≤ C * (lpNorm (fun _ : α => A) p μ + lpNorm R p μ) :=
      mul_le_mul_of_nonneg_left hLpAdd hC
    _ ≤ C * (A + Real.sqrt r) := by
      rw [hLpA]
      gcongr

private theorem c079_tail_matrix_one_norm_le (m : ℕ) :
    ‖(1 : Matrix (Fin m) (Fin m) ℝ)‖ ≤ 1 := by
  calc
    ‖(1 : Matrix (Fin m) (Fin m) ℝ)‖ =
        ‖Matrix.diagonal (fun _ : Fin m => (1 : ℝ))‖ := by simp
    _ = ‖(fun _ : Fin m => (1 : ℝ))‖ :=
      Matrix.l2_opNorm_diagonal _
    _ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).2
      intro i
      simp

private theorem c079_tail_matrix_pow_norm_le {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (q : ℕ) :
    ‖M ^ q‖ ≤ ‖M‖ ^ q := by
  induction q with
  | zero => simpa using c079_tail_matrix_one_norm_le m
  | succ q ih =>
      rw [pow_succ, pow_succ]
      exact (Matrix.l2_opNorm_mul (M ^ q) M).trans
        (mul_le_mul_of_nonneg_right ih (norm_nonneg M))

/-- Deterministic Gram-trace upper bound needed to recover the exact
even-walk count from an iid operator-norm moment. -/
theorem c079_iid_gramTrace_le_card_norm_pow {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (q : ℕ) :
    Matrix.trace ((M * M.transpose) ^ q) ≤
      (m : ℝ) * ‖M‖ ^ (2 * q) := by
  have hTranspose : ‖M.transpose‖ = ‖M‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose M
  have hGram : ‖M * M.transpose‖ ≤ ‖M‖ * ‖M.transpose‖ :=
    Matrix.l2_opNorm_mul M M.transpose
  have hPower : ‖(M * M.transpose) ^ q‖ ≤ ‖M‖ ^ (2 * q) := by
    calc
      _ ≤ ‖M * M.transpose‖ ^ q := c079_tail_matrix_pow_norm_le _ q
      _ ≤ (‖M‖ * ‖M.transpose‖) ^ q :=
        (pow_le_pow_left₀ (norm_nonneg _) hGram) q
      _ = ‖M‖ ^ (2 * q) := by
        rw [hTranspose, mul_pow, ← pow_add]
        congr 1
        omega
  calc
    Matrix.trace ((M * M.transpose) ^ q) ≤
        |Matrix.trace ((M * M.transpose) ^ q)| := le_abs_self _
    _ ≤ (m : ℝ) * ‖(M * M.transpose) ^ q‖ := by
      simpa using abs_matrix_trace_le_card_mul_l2_opNorm
        ((M * M.transpose) ^ q)
    _ ≤ (m : ℝ) * ‖M‖ ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg _)

/-- A root bound on the iid operator-norm moment pays for the trace factor
with the already verified dimension budget. This is a conditional theorem. -/
theorem c079_iid_evenWalkCount_le_of_root_bound (q : ℕ) (hq : 0 < q)
    (hRoot :
      (paperMean (fun w : Fin (2 * q ^ 2) × Fin (2 * q ^ 2) → Bool =>
        ‖c079IidSignMatrix (2 * q ^ 2) w‖ ^ (2 * q))) ^
          (1 / (((2 * q : ℕ) : ℝ))) ≤
        (20 / 3 : ℝ) * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) :
    c079IidEvenWalkCount (2 * q ^ 2) q ≤
      (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q) := by
  let m : ℕ := 2 * q ^ 2
  let B : ℝ := (20 / 3 : ℝ) * Real.sqrt (m : ℝ)
  have hmean : 0 ≤ paperMean (fun w : Fin m × Fin m → Bool =>
      ‖c079IidSignMatrix m w‖ ^ (2 * q)) := by
    have h := paperMean_mono (f := fun _ : Fin m × Fin m → Bool => (0 : ℝ))
      (g := fun w => ‖c079IidSignMatrix m w‖ ^ (2 * q))
      (fun w => pow_nonneg (norm_nonneg _) _)
    simpa [paperMean_zero] using h
  have hp : (0 : ℝ) < (((2 * q : ℕ) : ℝ)) := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hMoment : paperMean (fun w : Fin m × Fin m → Bool =>
      ‖c079IidSignMatrix m w‖ ^ (2 * q)) ≤ B ^ (2 * q) := by
    have hroot' :
        (paperMean (fun w : Fin m × Fin m → Bool =>
          ‖c079IidSignMatrix m w‖ ^ (2 * q))) ^
            (1 / (((2 * q : ℕ) : ℝ))) ≤ B := hRoot
    have h := Real.rpow_le_rpow
      (Real.rpow_nonneg hmean _) hroot' (le_of_lt hp)
    rw [← Real.rpow_mul hmean] at h
    have he : (1 / (((2 * q : ℕ) : ℝ))) *
        (((2 * q : ℕ) : ℝ)) = 1 := by
      field_simp
    rw [he, Real.rpow_one, Real.rpow_natCast] at h
    exact h
  calc
    c079IidEvenWalkCount m q =
        paperMean (fun w : Fin m × Fin m → Bool =>
          Matrix.trace ((c079IidSignMatrix m w *
            (c079IidSignMatrix m w).transpose) ^ q)) :=
      (c079IidSignMatrix_gramTrace_mean_eq_evenWalkCount m q hq).symm
    _ ≤ paperMean (fun w : Fin m × Fin m → Bool =>
        (m : ℝ) * ‖c079IidSignMatrix m w‖ ^ (2 * q)) := by
      apply paperMean_mono
      intro w
      exact c079_iid_gramTrace_le_card_norm_pow _ q
    _ = (m : ℝ) * paperMean (fun w : Fin m × Fin m → Bool =>
        ‖c079IidSignMatrix m w‖ ^ (2 * q)) :=
      paperMean_const_mul _ _
    _ ≤ (m : ℝ) * B ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hMoment (Nat.cast_nonneg _)
    _ ≤ (12 * Real.sqrt (m : ℝ)) ^ (2 * q) := by
      exact c079_targetDimension_numeric_budget q hq

/-- The exact shifted operator-norm tail needed for the iid even-walk count.
This theorem keeps that tail as an explicit premise. -/
theorem c079_iid_evenWalkCount_le_of_shifted_opNorm_tail
    (q : ℕ) (hq : 0 < q)
    (hTail : ∀ t : ℝ, 0 ≤ t →
      finiteUniformProbability
        (fun w : Fin (2 * q ^ 2) × Fin (2 * q ^ 2) → Bool =>
          (4 / 3 : ℝ) *
            (4 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ) + t) <
              ‖c079IidSignMatrix (2 * q ^ 2) w‖) ≤
        Real.exp (-(t ^ 2 / 2))) :
    c079IidEvenWalkCount (2 * q ^ 2) q ≤
      (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q) := by
  let m : ℕ := 2 * q ^ 2
  let Ω := Fin m × Fin m → Bool
  letI : Fintype Ω := inferInstance
  letI : Nonempty Ω := ⟨fun _ => false⟩
  letI : MeasurableSpace Ω := ⊤
  let μ : Measure Ω := (Fintype.card Ω : NNReal)⁻¹ • Measure.count
  haveI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure
      ((Fintype.card Ω : NNReal)⁻¹ • (Measure.count : Measure Ω))
    exact c079_uniform_measure_isProbability (Ω := Ω)
  let A : ℝ := 4 * Real.sqrt (m : ℝ)
  let R : Ω → ℝ := fun w =>
    max ((3 / 4 : ℝ) * ‖c079IidSignMatrix m w‖ - A) 0
  let N : Ω → ℝ := fun w => ‖c079IidSignMatrix m w‖
  have hR : ∀ w, 0 ≤ R w := by
    intro w
    dsimp [R]
    exact le_max_right _ _
  have hN : ∀ w, ‖N w‖ ≤ (4 / 3 : ℝ) * (A + R w) := by
    intro w
    have hmax : (3 / 4 : ℝ) * ‖c079IidSignMatrix m w‖ - A ≤ R w :=
      le_max_left _ _
    dsimp [N]
    rw [abs_of_nonneg (norm_nonneg _)]
    nlinarith
  have hRTail : ∀ t : ℝ, 0 ≤ t →
      μ.real {w | t < R w} ≤ Real.exp (-(t ^ 2 / 2)) := by
    intro t ht
    have hsub : {w : Ω | t < R w} ⊆
        {w : Ω | (4 / 3 : ℝ) * (A + t) < N w} := by
      intro w hw
      have hmax : t < max ((3 / 4 : ℝ) * N w - A) 0 := hw
      have hpos : t < (3 / 4 : ℝ) * N w - A := by
        rcases lt_max_iff.mp hmax with h | h
        · exact h
        · exact (not_lt_of_ge ht h).elim
      dsimp
      nlinarith
    calc
      μ.real {w | t < R w} ≤
          μ.real {w | (4 / 3 : ℝ) * (A + t) < N w} :=
        measureReal_mono hsub (by finiteness)
      _ = finiteUniformProbability
          (fun w : Ω => (4 / 3 : ℝ) * (A + t) < N w) := by
        exact c079_uniform_measure_real_event_eq_probability _
      _ ≤ Real.exp (-(t ^ 2 / 2)) := hTail t ht
  have hLp : lpNorm N (ENNReal.ofReal (((2 * q : ℕ) : ℝ))) μ ≤
      (4 / 3 : ℝ) * (A + Real.sqrt (((2 * q : ℕ) : ℝ))) := by
    exact c079_shifted_gaussian_tail_lpNorm_bound A (4 / 3)
      (by dsimp [A]; positivity) (by norm_num) R N hR hN q hq hRTail
  have hLpBudget : lpNorm N (ENNReal.ofReal (((2 * q : ℕ) : ℝ))) μ ≤
      (20 / 3 : ℝ) * Real.sqrt (m : ℝ) := by
    have hsqrt := c079_sqrt_twiceOrder_le_sqrt_targetDimension q hq
    dsimp [A] at hLp
    nlinarith
  have hr : (0 : ℝ) < (((2 * q : ℕ) : ℝ)) := by positivity
  have hp0 : ENNReal.ofReal (((2 * q : ℕ) : ℝ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hr
  have hpTop : ENNReal.ofReal (((2 * q : ℕ) : ℝ)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hMemN : MemLp N (ENNReal.ofReal (((2 * q : ℕ) : ℝ))) μ :=
    MemLp.of_discrete
  have hEq : lpNorm N (ENNReal.ofReal (((2 * q : ℕ) : ℝ))) μ =
      (paperMean (fun w : Ω => N w ^ (2 * q))) ^
        (1 / (((2 * q : ℕ) : ℝ))) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpTop
      hMemN.aestronglyMeasurable]
    simp only [N, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [ENNReal.toReal_ofReal (le_of_lt hr), Real.rpow_natCast,
      inv_eq_one_div]
    rw [c079_uniformIntegral_eq_paperMean]
  rw [hEq] at hLpBudget
  exact c079_iid_evenWalkCount_le_of_root_bound q hq
    (by simpa only [m, N] using hLpBudget)

theorem c079_iid_evenWalkCount_bound
    (q : ℕ) (hq : 0 < q) :
    c079IidEvenWalkCount (2 * q ^ 2) q ≤
      (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q) := by
  apply c079_iid_evenWalkCount_le_of_shifted_opNorm_tail q hq
  intro t ht
  simpa only [neg_div] using
    c079_iidSignMatrix_opNorm_tail (2 * q ^ 2) (by positivity) t ht

theorem c079_iidSignMatrix_highMoment
    (q : ℕ) (hq : 0 < q) :
    paperMean (fun w : Fin (2 * q ^ 2) × Fin (2 * q ^ 2) → Bool =>
      ‖c079IidSignMatrix (2 * q ^ 2) w‖ ^ (2 * q)) ≤
      (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q) :=
  c079IidSignMatrix_highMoment_of_evenWalkCount_bound q hq
    (c079_iid_evenWalkCount_bound q hq)

end GraphMatrixReplica
end
