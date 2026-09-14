import R6.FiniteConditionalTrials
import R6.P3FiniteProductLaw
import R6.P3UniformTail

/-!
# P3 synchronized-trial amplification

This module formalizes the finite-probability amplification after the actual
model has supplied a one-trial success lower bound for the SAME separator
tuple.  It does not replace that event by a product of separate maxima.

Execution status in this handoff: NOT EXECUTED.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A lower bound `ρ` on one-trial success gives the standard exponential
upper bound on failure of all `N` independent fresh trials. -/
theorem p3_all_fail_probability_le_exp
    {Ξ : Type} [Fintype Ξ] [Nonempty Ξ]
    (N : ℕ) (S : Ξ → Prop) [DecidablePred S]
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ρ ≤ finiteUniformProbability S) :
    finiteUniformProbability (fun v : Fin N → Ξ => ∀ i, ¬ S (v i)) ≤
      Real.exp (-((N : ℝ) * ρ)) := by
  rw [sync_all_fail_probability]
  have hp0 : 0 ≤ finiteUniformProbability S :=
    p3_finiteUniformProbability_nonneg S
  have hp1 : finiteUniformProbability S ≤ 1 :=
    p3_finiteUniformProbability_le_one S
  have hbase0 : 0 ≤ 1 - finiteUniformProbability S := by linarith
  have hbase : 1 - finiteUniformProbability S ≤ 1 - ρ := by linarith
  have hpow1 := pow_le_pow_left₀ hbase0 hbase N
  have hOneMinusRho0 : 0 ≤ 1 - ρ := by linarith
  have hbaseExp : 1 - ρ ≤ Real.exp (-ρ) := by
    have h := Real.add_one_le_exp (-ρ)
    nlinarith
  have hpow2 := pow_le_pow_left₀ hOneMinusRho0 hbaseExp N
  have hExpPow : (Real.exp (-ρ)) ^ N = Real.exp (-((N : ℝ) * ρ)) := by
    clear hpow1 hpow2
    induction N with
    | zero => simp
    | succ N ih =>
        rw [pow_succ, ih, ← Real.exp_add]
        congr 1
        push_cast
        ring
  exact hpow1.trans (hpow2.trans_eq hExpPow)

/-- The previous bound immediately gives an `exp (-c*sqrt n)` failure bound
once the deterministic trial-mass estimate `c*sqrt n ≤ N*ρ` is available. -/
theorem p3_all_fail_probability_le_exp_sqrt
    {Ξ : Type} [Fintype Ξ] [Nonempty Ξ]
    (N : ℕ) (S : Ξ → Prop) [DecidablePred S]
    (ρ c n : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ρ ≤ finiteUniformProbability S)
    (hmass : c * Real.sqrt n ≤ (N : ℝ) * ρ) :
    finiteUniformProbability (fun v : Fin N → Ξ => ∀ i, ¬ S (v i)) ≤
      Real.exp (-(c * Real.sqrt n)) := by
  calc
    finiteUniformProbability (fun v : Fin N → Ξ => ∀ i, ¬ S (v i)) ≤
        Real.exp (-((N : ℝ) * ρ)) :=
      p3_all_fail_probability_le_exp N S ρ hρ0 hρ1 hρ
    _ ≤ Real.exp (-(c * Real.sqrt n)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hmass)

/-- If the exact all-failure factor is at most `1/2`, the existing synchronized
expected-maximum theorem yields a clean factor `1/2` in front. -/
theorem p3_sync_expected_max_half
    {I Ξ : Type} [Fintype I] [Fintype Ξ] [Nonempty I] [Nonempty Ξ]
    (N : ℕ) (G : I → Prop) (S : I → Ξ → Prop)
    [DecidablePred G] [∀ ω, DecidablePred (S ω)]
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hsingle : ∀ ω, G ω → ρ ≤ finiteUniformProbability (S ω))
    (F : I × (Fin N → Ξ) → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hF0 : ∀ x, 0 ≤ F x)
    (hFsuccess : ∀ ω v, G ω → (∃ i, S ω (v i)) → T ≤ F (ω, v))
    (hfailHalf : (1 - ρ) ^ N ≤ (1 / 2 : ℝ)) :
    T * (finiteUniformProbability G / 2) ≤ paperMean F := by
  have hmain := sync_expected_max_lower_of_success
    N G S ρ hρ0 hρ1 hsingle F T hT hF0 hFsuccess
  have hG0 : 0 ≤ finiteUniformProbability G :=
    p3_finiteUniformProbability_nonneg G
  have hsuccessHalf : (1 / 2 : ℝ) ≤ 1 - (1 - ρ) ^ N := by
    linarith
  have hfactor : finiteUniformProbability G / 2 ≤
      finiteUniformProbability G * (1 - (1 - ρ) ^ N) := by
    have hm := mul_le_mul_of_nonneg_left hsuccessHalf hG0
    nlinarith
  calc
    T * (finiteUniformProbability G / 2) ≤
        T * (finiteUniformProbability G * (1 - (1 - ρ) ^ N)) :=
      mul_le_mul_of_nonneg_left hfactor hT
    _ ≤ paperMean F := hmain

/-- P3's fixed choice `ε = 1/(2*sqrt C)` gives exponent `C ε² = 1/4`. -/
def p3SyncEpsilon (C : ℝ) : ℝ := 1 / (2 * Real.sqrt C)

theorem p3SyncEpsilon_pos (C : ℝ) (hC : 0 < C) :
    0 < p3SyncEpsilon C := by
  unfold p3SyncEpsilon
  positivity

theorem p3SyncEpsilon_exponent (C : ℝ) (hC : 0 < C) :
    C * (p3SyncEpsilon C) ^ 2 = (1 / 4 : ℝ) := by
  have hs : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hs2 : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt (le_of_lt hC)
  unfold p3SyncEpsilon
  field_simp [ne_of_gt hs] <;> nlinarith [hs2]

#print axioms p3_all_fail_probability_le_exp
#print axioms p3_all_fail_probability_le_exp_sqrt
#print axioms p3_sync_expected_max_half
#print axioms p3SyncEpsilon_exponent

end GraphMatrixReplica
