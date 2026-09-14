import GraphMatrix.Counting.ForwardNormalization

/-! # C079 free-seed and combined exponent ledger

This module formalizes the arithmetic after the active-component incidence
bound in C079 Section 6.  The hypotheses expose both genuinely combinatorial
inputs:

* a seed fiber has size at most `(2*p)^width`;
* the total seed width obeys the crude and active-layer charges.

It does not define `theta_C`, prove the active-component incidence bound, or
construct the normalization decoder.  Thus its conclusions are conditional
arithmetic consequences, not a completed formalization of the C079 encoder.
-/

noncomputable section

namespace GraphMatrixReplica

/-- C079 equation (27), isolated as a consequence of the two width charges
and the normalized-defect estimate. -/
theorem c079_freeSeed_count_le_of_width_charges
    (p r a deltaOn D normalizedDefect width seedCount : ℕ)
    (hp : 1 ≤ p)
    (hSeed : seedCount ≤ (2 * p) ^ width)
    (hCrude : width ≤ r * (p - 1))
    (hActive : width ≤ a * (p - 1) + r * normalizedDefect)
    (hNormalized : normalizedDefect ≤ deltaOn + 3 * r * D) :
    seedCount ≤
      2 ^ (r * p) * p ^ (a * p + r * deltaOn + 3 * r ^ 2 * D) := by
  have hWidthCrude : width ≤ r * p := by
    calc
      width ≤ r * (p - 1) := hCrude
      _ ≤ r * p := Nat.mul_le_mul_left r (Nat.sub_le p 1)
  have hWidthActive :
      width ≤ a * p + r * deltaOn + 3 * r ^ 2 * D := by
    calc
      width ≤ a * (p - 1) + r * normalizedDefect := hActive
      _ ≤ a * p + r * (deltaOn + 3 * r * D) := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left a (Nat.sub_le p 1))
          (Nat.mul_le_mul_left r hNormalized)
      _ = a * p + r * deltaOn + 3 * r ^ 2 * D := by ring
  calc
    seedCount ≤ (2 * p) ^ width := hSeed
    _ = 2 ^ width * p ^ width := by rw [mul_pow]
    _ ≤ 2 ^ (r * p) *
        p ^ (a * p + r * deltaOn + 3 * r ^ 2 * D) := by
      exact Nat.mul_le_mul
        (Nat.pow_le_pow_right (by norm_num) hWidthCrude)
        (Nat.pow_le_pow_right (by omega) hWidthActive)

/-- Exact sum of the powers of `p` in C079 (13), (22), (23), and (27).
This is the detailed version of equation (28), before uniform domination by
one coefficient `K_r`. -/
theorem c079_combined_polynomialExponent_eq
    (r p a deltaOn D : ℕ) :
    2 * deltaOn + 6 * r * D + (4 * r + 2) * D +
        (a * p + r * deltaOn + 3 * r ^ 2 * D) =
      a * p + (r + 2) * deltaOn +
        (3 * r ^ 2 + 10 * r + 2) * D := by
  ring

/-- Multiplying the four polynomial factors from path states, forward
coarsening, reconstruction, and free seeds gives exactly the combined
exponent. -/
theorem c079_polynomialFactors_eq_combined
    (r p a deltaOn D : ℕ) :
    p ^ (2 * deltaOn) * p ^ (6 * r * D) *
        p ^ ((4 * r + 2) * D) *
          p ^ (a * p + r * deltaOn + 3 * r ^ 2 * D) =
      p ^ (a * p + (r + 2) * deltaOn +
        (3 * r ^ 2 + 10 * r + 2) * D) := by
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

/-- The combined exponent is absorbed by `a*p + K*delta` whenever `K`
dominates the on-backbone and off-backbone defect coefficients. -/
theorem c079_combined_polynomialExponent_le_uniform
    (r p a K deltaOn D : ℕ)
    (hOn : r + 2 ≤ K)
    (hOff : 3 * r ^ 2 + 10 * r + 2 ≤ K) :
    2 * deltaOn + 6 * r * D + (4 * r + 2) * D +
        (a * p + r * deltaOn + 3 * r ^ 2 * D) ≤
      a * p + K * (deltaOn + D) := by
  rw [c079_combined_polynomialExponent_eq]
  calc
    a * p + (r + 2) * deltaOn +
        (3 * r ^ 2 + 10 * r + 2) * D ≤
      a * p + K * deltaOn + K * D := by
        gcongr
    _ = a * p + K * (deltaOn + D) := by ring

/-- If the exact total defect is split as `deltaOn + D`, the preceding
uniform ledger has the statement form used by the all-defect coefficient
bound. -/
theorem c079_combined_polynomialExponent_le_of_split
    (r p a K delta deltaOn D : ℕ)
    (hSplit : delta = deltaOn + D)
    (hOn : r + 2 ≤ K)
    (hOff : 3 * r ^ 2 + 10 * r + 2 ≤ K) :
    2 * deltaOn + 6 * r * D + (4 * r + 2) * D +
        (a * p + r * deltaOn + 3 * r ^ 2 * D) ≤
      a * p + K * delta := by
  subst delta
  exact c079_combined_polynomialExponent_le_uniform
    r p a K deltaOn D hOn hOff

/-- Multiplicative form of the uniform exponent ledger. -/
theorem c079_polynomialFactors_le_uniform
    (r p a K deltaOn D : ℕ) (hp : 0 < p)
    (hOn : r + 2 ≤ K)
    (hOff : 3 * r ^ 2 + 10 * r + 2 ≤ K) :
    p ^ (2 * deltaOn) * p ^ (6 * r * D) *
        p ^ ((4 * r + 2) * D) *
          p ^ (a * p + r * deltaOn + 3 * r ^ 2 * D) ≤
      p ^ (a * p + K * (deltaOn + D)) := by
  rw [c079_polynomialFactors_eq_combined]
  apply Nat.pow_le_pow_right hp
  calc
    a * p + (r + 2) * deltaOn +
        (3 * r ^ 2 + 10 * r + 2) * D ≤
      a * p + K * deltaOn + K * D := by
        gcongr
    _ = a * p + K * (deltaOn + D) := by ring


end GraphMatrixReplica
