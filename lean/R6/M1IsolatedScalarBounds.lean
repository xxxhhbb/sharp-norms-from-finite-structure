import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! Exact uniform bounds for the isolated-role injection multiplier.
These arithmetic lemmas do not assert the graph-matrix deletion identity. -/

namespace GraphMatrixReplica

/-- The exact extension count never exceeds the unrestricted choices. -/
theorem root_isolated_scalar_le_pow (n v h : ℕ) :
    (n - (v - h)).descFactorial h ≤ n ^ h := by
  exact (Nat.descFactorial_le_pow _ _).trans
    (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

/-- A uniform lower bound after the explicit threshold `n ≥ 2v`.
No positivity of `h` is required, so deletion of zero roles is included. -/
theorem root_pow_le_scaled_isolated_scalar (n v h : ℕ)
    (hh : h ≤ v) (hn : 2 * v ≤ n) :
    n ^ h ≤ 2 ^ h * (n - (v - h)).descFactorial h := by
  have hbase : n ≤ 2 * (n - (v - h) + 1 - h) := by omega
  calc
    n ^ h ≤ (2 * (n - (v - h) + 1 - h)) ^ h :=
      Nat.pow_le_pow_left hbase h
    _ = 2 ^ h * (n - (v - h) + 1 - h) ^ h := Nat.mul_pow _ _ _
    _ ≤ 2 ^ h * (n - (v - h)).descFactorial h :=
      Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial _ _)

/-- Real two-sided bound in the form needed for expectation/norm assembly. -/
theorem root_isolated_scalar_real_bounds (n v h : ℕ)
    (hh : h ≤ v) (hn : 2 * v ≤ n) :
    ((n : ℝ) / 2) ^ h ≤ ((n - (v - h)).descFactorial h : ℝ) ∧
      ((n - (v - h)).descFactorial h : ℝ) ≤ (n : ℝ) ^ h := by
  constructor
  · have hscaled : (n : ℝ) ^ h ≤
        (2 : ℝ) ^ h * ((n - (v - h)).descFactorial h : ℝ) := by
      exact_mod_cast root_pow_le_scaled_isolated_scalar n v h hh hn
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ h)).2
    simpa only [mul_comm] using hscaled
  · exact_mod_cast root_isolated_scalar_le_pow n v h

#print axioms root_isolated_scalar_le_pow
#print axioms root_pow_le_scaled_isolated_scalar
#print axioms root_isolated_scalar_real_bounds

end GraphMatrixReplica
