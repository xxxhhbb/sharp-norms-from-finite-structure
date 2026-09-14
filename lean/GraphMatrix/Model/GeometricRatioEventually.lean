import GraphMatrix.Model.LogWindowArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # geometric ratio is eventually at most one half

The proof of `prop:core-upper` chooses a moment order in a fixed logarithmic
window, then uses `p^K/n ≤ 1/2` only for sufficiently large `n`.  This file
formalizes that eventual quantifier.  Neither a bound for all dimensions nor
an all-defect counting theorem is asserted here.
-/

noncomputable section

namespace GraphMatrixReplica

set_option maxHeartbeats 400000

/-- For each fixed defect exponent and fixed logarithmic moment window,
the exact trace order eventually satisfies the natural-number ratio
condition needed by the two-times-leading-scale geometric sum estimate. -/
theorem paperR16RealTraceOrder_geometricRatio_eventually
    (K : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ q : ℝ, 0 ≤ q →
        q ≤ C₀ * Real.log (2 * (n : ℝ)) →
          2 * (paperR16RealTraceOrder n q) ^ K ≤ n := by
  let D : ℝ := 2 + C₀
  let c : ℝ := (4 * D ^ K)⁻¹
  have hD : 0 < D := by dsimp [D]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hTendsto : Filter.Tendsto
      (fun n : ℕ => 2 * (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hLittle :
      (fun x : ℝ => Real.log x ^ (K : ℝ)) =o[Filter.atTop]
        (fun x : ℝ => x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (K : ℝ) (by norm_num)
  have hSmall : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log (2 * (n : ℝ)) ^ (K : ℝ)‖ ≤
        c * ‖(2 * (n : ℝ)) ^ (1 : ℝ)‖ :=
    hTendsto.eventually (hLittle.bound hc)
  have hLarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_ge_atTop 2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hLarge.and hSmall)
  refine ⟨N, ?_⟩
  intro n hn q hq hWindow
  obtain ⟨hnTwo, hSmallN⟩ := hN n hn
  let L : ℝ := Real.log (2 * (n : ℝ))
  have hL : 0 ≤ L := by
    have hOne := one_le_log_two_mul_nat_of_two_le n hnTwo
    dsimp [L]
    linarith
  have hOrder : (paperR16RealTraceOrder n q : ℝ) ≤ D * L := by
    simpa [D, L] using
      paperR16RealTraceOrder_le_log_window
        n q C₀ hnTwo hC₀ hq hWindow
  have hSmallReal : L ^ K ≤ c * (2 * (n : ℝ)) := by
    have hX : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
    simpa [L, Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg hL, abs_of_nonneg hX] using hSmallN
  have hOrderPow :
      (paperR16RealTraceOrder n q : ℝ) ^ K ≤ (D * L) ^ K := by
    gcongr
  have hReal :
      (2 : ℝ) * (paperR16RealTraceOrder n q : ℝ) ^ K ≤
        (n : ℝ) := by
    calc
      (2 : ℝ) * (paperR16RealTraceOrder n q : ℝ) ^ K ≤
          2 * (D * L) ^ K := by gcongr
      _ = 2 * D ^ K * L ^ K := by rw [mul_pow]; ring
      _ ≤ 2 * D ^ K * (c * (2 * (n : ℝ))) := by
        gcongr
      _ = (n : ℝ) := by
        dsimp [c]
        field_simp [ne_of_gt (pow_pos hD K)]
        ring
  exact_mod_cast hReal


end GraphMatrixReplica
