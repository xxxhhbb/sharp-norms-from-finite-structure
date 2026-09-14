import R6.OperatorNormEndpoint
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # R16 logarithmic trace-order arithmetic

This is the parameter calculation in the proof of `prop:core-upper`:
`p = max(2, ceil(log(2n)), ceil(q/2))` for real `q`.  The explicit
large-dimension condition `2 ≤ n` is used only to deduce
`1 ≤ log(2n)`.  The geometric-ratio condition `(p^K)/n ≤ 1/2`
is a separate asymptotic input and is not asserted here.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The exact integer trace order selected in R16, `prop:core-upper`,
for a real requested `L^q` exponent. -/
def paperR16RealTraceOrder (n : ℕ) (q : ℝ) : ℕ :=
  max 2 (max (⌈Real.log (2 * (n : ℝ))⌉₊) (⌈q / 2⌉₊))

theorem paperR16RealTraceOrder_ge_two (n : ℕ) (q : ℝ) :
    2 ≤ paperR16RealTraceOrder n q := le_max_left _ _

theorem paperR16RealTraceOrder_covers_q (n : ℕ) (q : ℝ) :
    q ≤ 2 * (paperR16RealTraceOrder n q : ℝ) := by
  have hCeil : q / 2 ≤ (⌈q / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hMax : ⌈q / 2⌉₊ ≤ paperR16RealTraceOrder n q := by
    unfold paperR16RealTraceOrder
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hMaxR : (⌈q / 2⌉₊ : ℝ) ≤
      (paperR16RealTraceOrder n q : ℝ) := by exact_mod_cast hMax
  linarith

theorem paperR16RealTraceOrder_covers_log (n : ℕ) (q : ℝ) :
    Real.log (2 * (n : ℝ)) ≤ (paperR16RealTraceOrder n q : ℝ) := by
  have hCeil : Real.log (2 * (n : ℝ)) ≤
      (⌈Real.log (2 * (n : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
  have hMax : ⌈Real.log (2 * (n : ℝ))⌉₊ ≤
      paperR16RealTraceOrder n q := by
    unfold paperR16RealTraceOrder
    exact (le_max_left _ _).trans (le_max_right _ _)
  exact hCeil.trans (by exact_mod_cast hMax)

/-- A concrete lower threshold implying the logarithm can absorb ceilings
and the constant `2` in the paper's `max` choice. -/
theorem one_le_log_two_mul_nat_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hPos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  apply (Real.le_log_iff_exp_le hPos).2
  have hExp : Real.exp 1 < 3 := Real.exp_one_lt_three
  linarith

/-- For `2 ≤ n` and `q ≤ C₀ log(2n)`, the selected trace order stays in
a fixed logarithmic window.  The convenient constant `2+C₀` is not sharp;
it depends only on the fixed paper parameter `C₀`, not on `n` or `q`. -/
theorem paperR16RealTraceOrder_le_log_window
    (n : ℕ) (q C₀ : ℝ) (hn : 2 ≤ n) (hC₀ : 0 ≤ C₀)
    (hqNonneg : 0 ≤ q)
    (hqWindow : q ≤ C₀ * Real.log (2 * (n : ℝ))) :
    (paperR16RealTraceOrder n q : ℝ) ≤
      (2 + C₀) * Real.log (2 * (n : ℝ)) := by
  let L : ℝ := Real.log (2 * (n : ℝ))
  have hL : 1 ≤ L := one_le_log_two_mul_nat_of_two_le n hn
  have hC0L : 0 ≤ C₀ * (L - 1) := mul_nonneg hC₀ (by linarith)
  have hLogCeil : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hQCeil : (⌈q / 2⌉₊ : ℝ) < q / 2 + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hTwo : (2 : ℝ) ≤ (2 + C₀) * L := by nlinarith
  have hLog : (⌈L⌉₊ : ℝ) ≤ (2 + C₀) * L := by nlinarith
  have hQ : (⌈q / 2⌉₊ : ℝ) ≤ (2 + C₀) * L := by
    dsimp [L] at hqWindow ⊢
    nlinarith
  unfold paperR16RealTraceOrder
  rw [Nat.cast_max, Nat.cast_max]
  exact max_le hTwo (max_le hLog hQ)

#print axioms paperR16RealTraceOrder_covers_q
#print axioms paperR16RealTraceOrder_covers_log
#print axioms one_le_log_two_mul_nat_of_two_le
#print axioms paperR16RealTraceOrder_le_log_window

end GraphMatrixReplica
