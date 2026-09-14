import Mathlib

/-! # C079 uniform defect-coefficient arithmetic

This module isolates the arithmetic endpoint of the C079 all-defect count.
It does not assert the combinatorial counting estimate itself.  Instead, it
proves that a coefficient loss `p^(K * delta)` is exactly absorbed by the
degree saving `n^delta` whenever `p^K <= n`, uniformly over every defect
layer `delta <= target`.

The result is intentionally independent of the paper and fully-partite state
types, so later C079 encoding modules can use it without importing either
operator-norm endpoint branch.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The polynomial loss attached to one defect layer is absorbed by the
corresponding loss of ambient-label degree. -/
theorem c079_defect_power_mul_degree_power_le_base
    (p a K n target delta : ℕ)
    (hdelta : delta ≤ target) (hscale : p ^ K ≤ n) :
    p ^ (a * p + K * delta) * n ^ (target - delta) ≤
      p ^ (a * p) * n ^ target := by
  calc
    p ^ (a * p + K * delta) * n ^ (target - delta) =
        p ^ (a * p) *
          (p ^ (K * delta) * n ^ (target - delta)) := by
      rw [pow_add, mul_assoc]
    _ ≤ p ^ (a * p) * n ^ target := by
      exact Nat.mul_le_mul_left _ <| by
        calc
          p ^ (K * delta) * n ^ (target - delta) =
              (p ^ K) ^ delta * n ^ (target - delta) := by
            rw [pow_mul]
          _ ≤ n ^ delta * n ^ (target - delta) := by
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hscale delta)
          _ = n ^ target := by
            rw [← pow_add, Nat.add_sub_of_le hdelta]

/-- One C079 coefficient bound implies a defect-uniform bound on its weighted
contribution.  `C^(2p)` is kept explicit because it survives the final
`2p`-th root as a shape-only constant. -/
theorem c079_one_defect_weighted_term_le
    (p a K C n target delta coefficient : ℕ)
    (hdelta : delta ≤ target) (hscale : p ^ K ≤ n)
    (hcoefficient :
      coefficient ≤ C ^ (2 * p) * p ^ (a * p + K * delta)) :
    coefficient * n ^ (target - delta) ≤
      C ^ (2 * p) * p ^ (a * p) * n ^ target := by
  calc
    coefficient * n ^ (target - delta) ≤
        (C ^ (2 * p) * p ^ (a * p + K * delta)) *
          n ^ (target - delta) :=
      Nat.mul_le_mul_right _ hcoefficient
    _ = C ^ (2 * p) *
          (p ^ (a * p + K * delta) * n ^ (target - delta)) := by
      ring
    _ ≤ C ^ (2 * p) * (p ^ (a * p) * n ^ target) := by
      exact Nat.mul_le_mul_left _
        (c079_defect_power_mul_degree_power_le_base
          p a K n target delta hdelta hscale)
    _ = C ^ (2 * p) * p ^ (a * p) * n ^ target := by
      ring

/-- Summing all possible defect layers costs only their number.  This theorem
is the precise uniform-coefficient output expected from a future formal proof
of the C079 combinatorial encoder. -/
theorem c079_all_defect_weighted_sum_le
    (p a K C n target : ℕ) (coefficient : Fin (target + 1) → ℕ)
    (hscale : p ^ K ≤ n)
    (hcoefficient : ∀ delta : Fin (target + 1),
      coefficient delta ≤
        C ^ (2 * p) * p ^ (a * p + K * delta.1)) :
    (∑ delta : Fin (target + 1),
        coefficient delta * n ^ (target - delta.1)) ≤
      (target + 1) *
        (C ^ (2 * p) * p ^ (a * p) * n ^ target) := by
  calc
    (∑ delta : Fin (target + 1),
        coefficient delta * n ^ (target - delta.1)) ≤
        ∑ _delta : Fin (target + 1),
          C ^ (2 * p) * p ^ (a * p) * n ^ target := by
      exact Finset.sum_le_sum fun delta _ =>
        c079_one_defect_weighted_term_le
          p a K C n target delta.1 (coefficient delta)
          (Nat.lt_succ_iff.mp delta.2) hscale (hcoefficient delta)
    _ = (target + 1) *
          (C ^ (2 * p) * p ^ (a * p) * n ^ target) := by
      simp


end GraphMatrixReplica
