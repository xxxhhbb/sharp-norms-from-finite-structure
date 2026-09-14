import GraphMatrix.Probability.Synchronization.SyncAmplification
import GraphMatrix.Main.ColorLowerAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped BigOperators
open Filter
namespace GraphMatrixReplica

def mainP3Tilt (r : ℕ) (cS : ℝ) : ℝ := p3SyncEpsilon (96 * (r : ℝ) / cS)
def mainP3TrialCoefficient (r : ℕ) (pExt : ℝ) : ℝ := (min (pExt / 2) 1) ^ r

theorem main_P3Tilt_pos (r : ℕ) (cS : ℝ) (hr : 0 < r) (hcS : 0 < cS) :
    0 < mainP3Tilt r cS := by
  apply p3SyncEpsilon_pos
  positivity

theorem main_P3Tilt_exponent (r : ℕ) (cS : ℝ) (hr : 0 < r) (hcS : 0 < cS) :
    (r : ℝ) * (96 * (mainP3Tilt r cS) ^ 2 / cS) = (1 / 4 : ℝ) := by
  have h := p3SyncEpsilon_exponent (96 * (r : ℝ) / cS) (by positivity)
  dsimp [mainP3Tilt]
  calc
    _ = (96 * (r : ℝ) / cS) * (p3SyncEpsilon (96 * (r : ℝ) / cS)) ^ 2 := by ring
    _ = _ := h

theorem main_P3TrialCoefficient_pos (r : ℕ) (pExt : ℝ) (hpExt : 0 < pExt) :
    0 < mainP3TrialCoefficient r pExt := by
  unfold mainP3TrialCoefficient
  positivity

/-- A graph-fixed tilt keeps the total cost of at most r component tails at
most n^(1/4), including the empty product. -/
theorem main_P3_component_tail_product_lower
    (r k n : ℕ) (pExt cS : ℝ) (hr : 0 < r) (hk : k ≤ r) (hn : 1 ≤ n)
    (hpExt : 0 < pExt) (hcS : 0 < cS) :
    mainP3TrialCoefficient r pExt * (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (pExt * ((1 / 2 : ℝ) *
        Real.exp (-(96 * (mainP3Tilt r cS) ^ 2 * Real.log (n : ℝ) / cS)))) ^ k := by
  let a : ℝ := min (pExt / 2) 1
  let d : ℝ := 96 * (mainP3Tilt r cS) ^ 2 / cS
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := min_le_right _ _
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
  have hkr : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk
  have hbudget : (r : ℝ) * d = (1 / 4 : ℝ) := main_P3Tilt_exponent r cS hr hcS
  have hDecay : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ((n : ℝ) ^ (-d)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    nlinarith
  have hSingle : a * (n : ℝ) ^ (-d) ≤
      pExt * ((1 / 2 : ℝ) *
        Real.exp (-(96 * (mainP3Tilt r cS) ^ 2 * Real.log (n : ℝ) / cS))) := by
    have hEq : (n : ℝ) ^ (-d) =
        Real.exp (-(96 * (mainP3Tilt r cS) ^ 2 * Real.log (n : ℝ) / cS)) := by
      rw [Real.rpow_def_of_pos hn0]
      congr 1
      dsimp [d]
      ring
    calc
      a * (n : ℝ) ^ (-d) ≤ (pExt / 2) * (n : ℝ) ^ (-d) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hn0.le _)
      _ = _ := by rw [hEq]; ring
  calc
    mainP3TrialCoefficient r pExt * (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
        a ^ k * ((n : ℝ) ^ (-d)) ^ k :=
      mul_le_mul (pow_le_pow_of_le_one ha0 ha1 hk) hDecay
        (Real.rpow_nonneg hn0.le _) (pow_nonneg ha0 _)
    _ = (a * (n : ℝ) ^ (-d)) ^ k := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg ha0 (Real.rpow_nonneg hn0.le _)) hSingle k

/-- The resulting one-trial lower-bound parameter is a legitimate probability. -/
theorem main_P3_trial_probability_bounds (r n : ℕ) (pExt : ℝ)
    (hpExt : 0 < pExt) (hn : 1 ≤ n) :
    0 ≤ mainP3TrialCoefficient r pExt * (n : ℝ) ^ (-(1 / 4 : ℝ)) ∧
      mainP3TrialCoefficient r pExt * (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
  have hc0 := (main_P3TrialCoefficient_pos r pExt hpExt).le
  have hc1 : mainP3TrialCoefficient r pExt ≤ 1 := by
    apply pow_le_one₀
    · positivity
    · exact min_le_right _ _
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  refine ⟨mul_nonneg hc0 (Real.rpow_nonneg hn0 _), ?_⟩
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num : -(1 / 4 : ℝ) ≤ 0)
  simpa using mul_le_mul hc1 hpow (Real.rpow_nonneg hn0 _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The actual floor number of disjoint separator trials eventually supplies
enough total probability mass to make the exponential failure bound <=1/2. -/
theorem main_P3_floor_trial_mass_eventually (r : ℕ) (hr : 0 < r)
    (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n ∧
      Real.log 2 ≤ (n / r : ℕ) * (c * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let a : ℝ := 1 / (2 * (r : ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hreal : ∀ᶠ x : ℝ in atTop, Real.log 2 ≤ (a * c) * x ^ (3 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).const_mul_atTop
      (mul_pos ha hc)).eventually_ge_atTop (Real.log 2)
  have hnat : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ (a * c) * (n : ℝ) ^ (3 / 4 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnat
  refine ⟨max N (2 * r), ?_⟩
  intro n hn
  have hn2 : 2 * r ≤ n := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hfloor := (main_uniformRoleDimension_bounds r n hr hn2).1
  have hpower : (n : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) = (n : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + -(1 / 4 : ℝ)) := (Real.rpow_add hn0 _ _).symm
      _ = _ := by norm_num
  refine ⟨hn1, ?_⟩
  calc
    Real.log 2 ≤ (a * c) * (n : ℝ) ^ (3 / 4 : ℝ) := hN n ((le_max_left _ _).trans hn)
    _ = (a * (n : ℝ)) * (c * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by rw [← hpower]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfloor (by positivity)

/-- The exact independent all-failure factor is <=1/2 once its trial mass is
at least log 2. No independence is asserted by this scalar lemma. -/
theorem main_P3_failure_factor_half (m : ℕ) (rho : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hmass : Real.log 2 ≤ (m : ℝ) * rho) :
    (1 - rho) ^ m ≤ (1 / 2 : ℝ) := by
  have hbase : 1 - rho ≤ Real.exp (-rho) := by
    have h := Real.add_one_le_exp (-rho)
    linarith
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - rho) hbase m
  have hExp : (Real.exp (-rho)) ^ m = Real.exp (-((m : ℝ) * rho)) := by
    clear hpow hmass
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring
  calc
    (1 - rho) ^ m ≤ Real.exp (-((m : ℝ) * rho)) := hpow.trans_eq hExp
    _ ≤ Real.exp (-(Real.log 2)) := Real.exp_le_exp.mpr (neg_le_neg hmass)
    _ = (1 / 2 : ℝ) := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

end GraphMatrixReplica
