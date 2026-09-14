import R6.U3ForwardWordBudget
import R6.C079FreeSeedLedger

/-!
U3: exact arithmetic with m = p+1.  No cardinality bound is an assumption
in this module: it proves only identities/inequalities between explicit
natural-number budget expressions.
This module has not been executed in Lean in the return environment.
-/

noncomputable section
namespace GraphMatrixReplica.C079U3

/-- Exactly path * seed * (forward and reconstruction), at trace order m. -/
def fixedProfileBudget (r m a deltaOn D : ℕ) : ℕ :=
  (100 ^ (2 * m * r) * m ^ (2 * deltaOn)) *
    (2 ^ (r * m) * m ^ (a * m + r * deltaOn + 3 * r ^ 2 * D)) *
      ((2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D) *
        m ^ ((10 * r + 2) * D))

theorem fixedProfileBudget_eq (r m a deltaOn D : ℕ) :
    fixedProfileBudget r m a deltaOn D =
      (100 ^ (2 * m * r) * 2 ^ (r * m) *
        (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D)) *
      m ^ (a * m + (r + 2) * deltaOn + (3 * r ^ 2 + 10 * r + 2) * D) := by
  have he : 2 * deltaOn + (a * m + r * deltaOn + 3 * r ^ 2 * D) +
      (10 * r + 2) * D =
      a * m + (r + 2) * deltaOn + (3 * r ^ 2 + 10 * r + 2) * D := by ring
  calc
    fixedProfileBudget r m a deltaOn D =
      (100 ^ (2 * m * r) * 2 ^ (r * m) *
        (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D)) *
      m ^ (2 * deltaOn + (a * m + r * deltaOn + 3 * r ^ 2 * D) +
        (10 * r + 2) * D) := by
          simp only [fixedProfileBudget, pow_add]
          ring
    _ = _ := by rw [he]

/-- Multiplying by the full-role-profile count uses exactly the second
factor 2^(r*m), despite the shifted profile total s*p+delta. -/
theorem profileBudget_eq (r m a deltaOn D : ℕ) :
    2 ^ (r * m) * fixedProfileBudget r m a deltaOn D =
      (2 ^ (2 * r * m) * 100 ^ (2 * m * r) *
        (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D)) *
      m ^ (a * m + (r + 2) * deltaOn + (3 * r ^ 2 + 10 * r + 2) * D) := by
  rw [fixedProfileBudget_eq]
  have he : 2 * r * m = r * m + r * m := by ring
  rw [he, pow_add]
  ring

/-- Exact expansion of the requested C_r; no hidden enlarged constant. -/
theorem baseBudget_at_cap_eq (r m : ℕ) :
    2 ^ (2 * r * m) * 100 ^ (2 * m * r) *
      (2 * r) ^ (4 * r ^ 2 * m) * 4 ^ (2 * r ^ 2 * m) =
    c079C r ^ (2 * m) := by
  unfold c079C
  simp only [mul_pow, ← pow_mul]
  have h1 : r * (2 * m) = 2 * r * m := by ring
  have h2 : (2 * r ^ 2) * (2 * m) = 4 * r ^ 2 * m := by ring
  have h3 : r ^ 2 * (2 * m) = 2 * r ^ 2 * m := by ring
  have h4 : 2 * m * r = 2 * r * m := by ring
  rw [h1, h2, h3, h4]
  rw [show (200 : ℕ) = 2 * 100 by norm_num, mul_pow]

theorem baseBudget_le (r m D : ℕ) (hr : 1 ≤ r) (hD : D ≤ r * m) :
    2 ^ (2 * r * m) * 100 ^ (2 * m * r) *
      (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D) ≤
    c079C r ^ (2 * m) := by
  have h1 : 3 * r * D ≤ 4 * r ^ 2 * m := by
    have h := Nat.mul_le_mul_left (3 * r) hD
    nlinarith
  have h2 : 2 * r * D ≤ 2 * r ^ 2 * m := by
    have h := Nat.mul_le_mul_left (2 * r) hD
    nlinarith
  have hPow1 := Nat.pow_le_pow_right
    (show 0 < 2 * r by omega) h1
  have hPow2 := Nat.pow_le_pow_right
    (by norm_num : 0 < (4 : ℕ)) h2
  calc
    _ ≤ 2 ^ (2 * r * m) * 100 ^ (2 * m * r) *
        (2 * r) ^ (4 * r ^ 2 * m) * 4 ^ (2 * r ^ 2 * m) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hPow1) hPow2
    _ = _ := baseBudget_at_cap_eq r m

/-- The complete scalar budget after the exact split, with no graph count
or encoder injectivity introduced as a new hypothesis. -/
theorem profileBudget_le_requested
    (r m a deltaOn D : ℕ) (hr : 1 ≤ r) (hm : 0 < m) (hD : D ≤ r * m) :
    2 ^ (r * m) * fixedProfileBudget r m a deltaOn D ≤
      c079C r ^ (2 * m) *
        m ^ (a * m + c079K r * (deltaOn + D)) := by
  rw [profileBudget_eq]
  have hk : c079K r = 3 * r ^ 2 + 10 * r + 2 := by
    simp [c079K, show r ≠ 0 by omega]
  have hExp : a * m + (r + 2) * deltaOn +
      (3 * r ^ 2 + 10 * r + 2) * D ≤
      a * m + c079K r * (deltaOn + D) := by
    rw [← hk]
    exact c079_complete_exponent_bookkeeping r m a deltaOn D hr
  exact Nat.mul_le_mul (baseBudget_le r m D hr hD)
    (Nat.pow_le_pow_right hm hExp)

/-- Specialization to the actual Lean/paper parameter shift. -/
theorem profileBudget_le_requested_at_lean_order
    (r p a delta deltaOn D : ℕ) (hr : 1 ≤ r)
    (hSplit : delta = deltaOn + D) (hD : D ≤ r * p) :
    2 ^ (r * (p + 1)) * fixedProfileBudget r (p + 1) a deltaOn D ≤
      c079C r ^ (2 * (p + 1)) *
        (p + 1) ^ (a * (p + 1) + c079K r * delta) := by
  rw [hSplit]
  exact profileBudget_le_requested r (p + 1) a deltaOn D hr
    (Nat.succ_pos _) (hD.trans (Nat.mul_le_mul_left r (Nat.le_succ p)))

#print axioms fixedProfileBudget_eq
#print axioms profileBudget_eq
#print axioms baseBudget_at_cap_eq
#print axioms profileBudget_le_requested_at_lean_order
end GraphMatrixReplica.C079U3
