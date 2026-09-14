import GraphMatrix.PartialNCKIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Real half-exponent bookkeeping for partial NCK iteration

Natural-number division is not a correct notation for the square-root loss
when the number of iterations is odd.  This file uses `Real.rpow` and the
real exponent `(k : ℝ) / 2` throughout.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The exact real-half-power identity, valid for every natural `k`, including
odd `k`, and every nonnegative base. -/
theorem sqrt_natCast_pow_eq_rpow_half
    (p k : ℕ) :
    Real.sqrt ((p : ℝ) ^ k) =
      Real.rpow (p : ℝ) ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1
  ring

/-- Monotonicity of the true half exponent under an explicit logarithmic
upper bound on the moment parameter. -/
theorem rpow_half_le_const_mul_log_rpow_half
    (L : ℝ) (p k n : ℕ)
    (hL : 0 ≤ L) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ)) :
    Real.rpow (p : ℝ) ((k : ℝ) / 2) ≤
      Real.rpow L ((k : ℝ) / 2) *
        Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) := by
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hkHalf0 : 0 ≤ (k : ℝ) / 2 := by positivity
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnReal
  calc
    Real.rpow (p : ℝ) ((k : ℝ) / 2) ≤
        Real.rpow (L * Real.log (n : ℝ)) ((k : ℝ) / 2) :=
      Real.rpow_le_rpow hp0 hpLog hkHalf0
    _ = Real.rpow L ((k : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) :=
      Real.mul_rpow hL hlog0

/-- The same logarithmic transfer stated directly for the square-root factor
that appears in `PaperPartialNCKIteration`. -/
theorem sqrt_natCast_pow_le_const_mul_log_rpow_half
    (L : ℝ) (p k n : ℕ)
    (hL : 0 ≤ L) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ)) :
    Real.sqrt ((p : ℝ) ^ k) ≤
      Real.rpow L ((k : ℝ) / 2) *
        Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) := by
  rw [sqrt_natCast_pow_eq_rpow_half]
  exact rpow_half_le_const_mul_log_rpow_half L p k n hL hp hn hpLog

/-- The partial-NCK moment endpoint with the true half power transferred to
an explicit logarithmic scale.  `hMoment` is still the analytic input; this
result performs only the already-proved moment root and exponent arithmetic. -/
theorem paperMean_le_partialNCKLogScale_of_evenMoment
    {α : Type} [Fintype α]
    (f : α → ℝ) (C L : ℝ) (p k m n : ℕ) (D : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hm : 0 < m) (hf : ∀ a, 0 ≤ f a)
    (hMoment : paperMean (fun a => f a ^ (2 * m)) ≤
      partialNCKIteratedSquaredScale C p k D ^ m) :
    paperMean f ≤
      C ^ k * Real.rpow L ((k : ℝ) / 2) *
        Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) * D := by
  have hRoot := sqrt_natCast_pow_le_const_mul_log_rpow_half
    L p k n hL hp hn hpLog
  calc
    paperMean f ≤ C ^ k * Real.sqrt ((p : ℝ) ^ k) * D :=
      paperMean_le_partialNCKScale_of_evenMoment
        f C p k m D hC hD hm hf hMoment
    _ ≤ C ^ k *
          (Real.rpow L ((k : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2)) * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRoot (pow_nonneg hC k)) hD
    _ = C ^ k * Real.rpow L ((k : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) * D := by
      ring

/-- Operator-norm specialization of the real-half logarithmic endpoint. -/
theorem matrix_l2_opNorm_paperMean_le_partialNCKLogScale_of_evenMoment
    {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : α → Matrix ι κ ℝ) (C L : ℝ) (p k m n : ℕ) (D : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hm : 0 < m)
    (hMoment : paperMean (fun a => ‖A a‖ ^ (2 * m)) ≤
      partialNCKIteratedSquaredScale C p k D ^ m) :
    paperMean (fun a => ‖A a‖) ≤
      C ^ k * Real.rpow L ((k : ℝ) / 2) *
        Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) * D := by
  exact paperMean_le_partialNCKLogScale_of_evenMoment
    (fun a => ‖A a‖) C L p k m n D hC hL hD hp hn hpLog hm
    (fun a => norm_nonneg (A a)) hMoment


end GraphMatrixReplica
