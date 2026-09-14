import R6.C079IidSignMatrixHighMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Numeric budget for a prospective iid sign-matrix net proof

The final even-walk count is not bounded here. The statements below only
verify the arithmetic needed to absorb a trace factor if an independent
operator-norm estimate is later established.
-/

noncomputable section
namespace GraphMatrixReplica

/-- The target dimension is at most `3^q`, allowing the trace factor to be
absorbed into the available exponential constant. -/
theorem c079_targetDimension_le_three_pow (q : ℕ) (hq : 0 < q) :
    2 * q ^ 2 ≤ 3 ^ q := by
  have htail : ∀ n : ℕ, 2 * (n + 2) ^ 2 ≤ 3 ^ (n + 2) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hratio : 2 * (n + 3) ^ 2 ≤
            3 * (2 * (n + 2) ^ 2) := by
          calc
            2 * (n + 3) ^ 2 = 2 * n ^ 2 + 12 * n + 18 := by ring
            _ ≤ 6 * n ^ 2 + 24 * n + 24 := by omega
            _ = 3 * (2 * (n + 2) ^ 2) := by ring
        calc
          2 * (n + 1 + 2) ^ 2 = 2 * (n + 3) ^ 2 := by
            congr 1
          _ ≤ 3 * (2 * (n + 2) ^ 2) := hratio
          _ ≤ 3 * 3 ^ (n + 2) := Nat.mul_le_mul_left 3 ih
          _ = 3 ^ (n + 1 + 2) := by
            rw [show n + 1 + 2 = n + 2 + 1 by omega, pow_succ]
            ring
  rcases q with _ | q
  · omega
  rcases q with _ | q
  · norm_num
  simpa [Nat.succ_eq_add_one, ← add_assoc] using htail q

/-- The fixed numerical inequality used to dominate the size of a pair of
`1/8`-nets by a Gaussian tail shifted by `4√m`. -/
theorem c079_exp_eight_gt_pairNetBase :
    (578 : ℝ) < Real.exp 8 := by
  have h : (5 / 2 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpow : (5 / 2 : ℝ) ^ 8 < (Real.exp 1) ^ 8 := by
    exact pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  calc
    (578 : ℝ) < (5 / 2 : ℝ) ^ 8 := by norm_num
    _ < (Real.exp 1) ^ 8 := hpow
    _ = Real.exp 8 := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- The finite cardinality factor from two nets is paid for by shifting the
scalar Hoeffding threshold by `4√m`. This is purely numeric; it does not
assert existence of a net or a probability estimate. -/
theorem c079_pairNetCardinality_exponential_budget
    (m : ℕ) (hm : 0 < m) :
    (2 : ℝ) * 289 ^ m ≤ Real.exp (8 * (m : ℝ)) := by
  have htwo : (2 : ℝ) ≤ 2 ^ m := by
    cases m with
    | zero => omega
    | succ n =>
        rw [pow_succ]
        have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        nlinarith
  calc
    (2 : ℝ) * 289 ^ m ≤ 2 ^ m * 289 ^ m := by
      exact mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = (578 : ℝ) ^ m := by
      rw [← mul_pow]
      norm_num
    _ ≤ (Real.exp 8) ^ m :=
      pow_le_pow_left₀ (by norm_num)
        (le_of_lt c079_exp_eight_gt_pairNetBase) _
    _ = Real.exp (8 * (m : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Algebraic tail prefactor reduction for a pair of cardinality-`17^m`
nets. The scalar Hoeffding tail and net construction are separate gates. -/
theorem c079_pairNet_shiftedTail_numeric
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    (2 : ℝ) * 289 ^ m *
      Real.exp (-((4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2)) ≤
      Real.exp (-(t ^ 2 / 2)) := by
  have hquad : (8 : ℝ) * m - (4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2 ≤
      -(t ^ 2 / 2) := by
    have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = m :=
      Real.sq_sqrt (by positivity)
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m : ℝ)) ht]
  calc
    (2 : ℝ) * 289 ^ m *
        Real.exp (-((4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2)) ≤
        Real.exp (8 * (m : ℝ)) *
          Real.exp (-((4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2)) := by
      exact mul_le_mul_of_nonneg_right
        (c079_pairNetCardinality_exponential_budget m hm)
        (Real.exp_nonneg _)
    _ = Real.exp ((8 : ℝ) * m -
          (4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2) := by
      simpa only [sub_eq_add_neg] using
        (Real.exp_add (8 * (m : ℝ))
          (-((4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2))).symm
    _ ≤ Real.exp (-(t ^ 2 / 2)) := Real.exp_le_exp.mpr hquad

/-- At `m=2q²`, the Gaussian fluctuation `√(2q)` is no larger than `√m`. -/
theorem c079_sqrt_twiceOrder_le_sqrt_targetDimension
    (q : ℕ) (hq : 0 < q) :
    Real.sqrt ((2 * q : ℕ) : ℝ) ≤
      Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ) := by
  apply Real.sqrt_le_sqrt
  have h : 2 * q ≤ 2 * q ^ 2 := by nlinarith
  exact_mod_cast h

/-- Pure arithmetic: an `L^(2q)` bound of `(20/3) sqrt(m)` is strong enough
to pay for the `m` eigenvalues in the trace, at `m = 2q²`. -/
theorem c079_targetDimension_numeric_budget (q : ℕ) (hq : 0 < q) :
    ((2 * q ^ 2 : ℕ) : ℝ) *
      ((20 / 3 : ℝ) * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q) ≤
      (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q) := by
  let m : ℕ := 2 * q ^ 2
  have hm : (0 : ℝ) ≤ m := by positivity
  have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = m := Real.sq_sqrt hm
  have hleft : ((20 / 3 : ℝ) * Real.sqrt (m : ℝ)) ^ (2 * q) =
      ((400 / 9 : ℝ) * (m : ℝ)) ^ q := by
    rw [pow_mul, mul_pow, hsqrt]
    norm_num
  have hright : (12 * Real.sqrt (m : ℝ)) ^ (2 * q) =
      (144 * (m : ℝ)) ^ q := by
    rw [pow_mul, mul_pow, hsqrt]
    norm_num
  have hdim : (m : ℝ) ≤ (3 : ℝ) ^ q := by
    exact_mod_cast c079_targetDimension_le_three_pow q hq
  change (m : ℝ) * ((20 / 3 : ℝ) * Real.sqrt (m : ℝ)) ^ (2 * q) ≤
    (12 * Real.sqrt (m : ℝ)) ^ (2 * q)
  rw [hleft, hright]
  calc
    (m : ℝ) * ((400 / 9 : ℝ) * m) ^ q ≤
        (3 : ℝ) ^ q * ((400 / 9 : ℝ) * m) ^ q := by
      gcongr
    _ = ((3 : ℝ) * ((400 / 9 : ℝ) * m)) ^ q :=
      (mul_pow _ _ _).symm
    _ ≤ (144 * (m : ℝ)) ^ q := by
      have hbase : (3 : ℝ) * ((400 / 9 : ℝ) * m) ≤
          144 * (m : ℝ) := by nlinarith [hm]
      exact pow_le_pow_left₀ (by positivity) hbase _

#print axioms c079_targetDimension_le_three_pow
#print axioms c079_exp_eight_gt_pairNetBase
#print axioms c079_pairNetCardinality_exponential_budget
#print axioms c079_pairNet_shiftedTail_numeric
#print axioms c079_sqrt_twiceOrder_le_sqrt_targetDimension
#print axioms c079_targetDimension_numeric_budget

end GraphMatrixReplica
