import Mathlib

/-! # C079 path-state counting: finite and arithmetic core

This file isolates the parts of C079 Lemma 3 that do not use probability or
matrix analysis.  The analytic input is exposed as two inequalities: a
uniform lower bound for the weight of every state in one degree fiber, and an
upper bound for the sum of those weights.  Everything after those inputs is a
finite-sum and natural-power calculation.

The constants follow the paper's choice `m = 2 * p^2`.  Replacing the paper's
factor `exp (ell + 1)` by `3^(ell+1)` is harmless because `Real.exp 1 < 3`;
formalizing that real-analytic comparison is deliberately not claimed here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- If every element of a finite type has weight at least `lower`, then the
cardinality times `lower` is at most the total weight. -/
theorem c079_card_mul_lower_le_weightSum
    {alpha : Type*} [Fintype alpha]
    (weight : alpha -> Nat) (lower : Nat)
    (hLower : forall x : alpha, lower <= weight x) :
    Fintype.card alpha * lower <= ∑ x : alpha, weight x := by
  calc
    Fintype.card alpha * lower = ∑ _x : alpha, lower := by simp
    _ <= ∑ x : alpha, weight x := by
      exact Finset.sum_le_sum fun x _ => hLower x

/-- Finite weighted-count extraction across a power gap.  This is the exact
algebra behind the passage from a degree-`B-t` lower weight and a degree-`B`
moment bound to a factor `m^t` in the state count. -/
theorem c079_card_le_of_scaled_power_weight_bounds
    {alpha : Type*} [Fintype alpha]
    (weight : alpha -> Nat) (m scale amplitude B t : Nat)
    (hm : 0 < m) (ht : t <= B)
    (hLower : forall x : alpha,
      m ^ (B - t) <= scale * weight x)
    (hUpper : (∑ x : alpha, weight x) <= amplitude * m ^ B) :
    Fintype.card alpha <= scale * amplitude * m ^ t := by
  have hPowerPos : 0 < m ^ (B - t) := pow_pos hm _
  have hScaledLower :
      Fintype.card alpha * m ^ (B - t) <=
        scale * ∑ x : alpha, weight x := by
    calc
      Fintype.card alpha * m ^ (B - t) <=
          (∑ x : alpha, scale * weight x) :=
        c079_card_mul_lower_le_weightSum
          (fun x : alpha => scale * weight x) (m ^ (B - t)) hLower
      _ = scale * ∑ x : alpha, weight x := by
        simp [Finset.mul_sum]
  have hPowSplit : m ^ B = m ^ t * m ^ (B - t) := by
    conv_lhs => rw [show B = t + (B - t) by omega]
    rw [pow_add]
  have hToUpper :
      Fintype.card alpha * m ^ (B - t) <=
        (scale * amplitude * m ^ t) * m ^ (B - t) := by
    calc
      Fintype.card alpha * m ^ (B - t) <=
          scale * ∑ x : alpha, weight x := hScaledLower
      _ <= scale * (amplitude * m ^ B) :=
        Nat.mul_le_mul_left scale hUpper
      _ = (scale * amplitude * m ^ t) * m ^ (B - t) := by
        rw [hPowSplit]
        ring
  exact Nat.le_of_mul_le_mul_right hToUpper hPowerPos

/-- The auxiliary dimension in Lemma 3 contributes exactly the desired
polynomial defect factor. -/
theorem c079_auxDimension_pow
    (p t : Nat) :
    (2 * p ^ 2) ^ t = 2 ^ t * p ^ (2 * t) := by
  rw [mul_pow, pow_mul]

/-- The fixed bases in the path argument are absorbed by the advertised
`100^(2*p*(ell+1))` envelope, uniformly in the path length. -/
theorem c079_path_fixedBases_le_hundred
    (ell p t : Nat) (hp : 2 <= p) (ht : t <= ell * (p - 1)) :
    3 ^ (ell + 1) * 12 ^ (2 * p * ell) * 2 ^ t <=
      100 ^ (2 * p * (ell + 1)) := by
  have hpOne : 1 <= p := by omega
  have hEll : ell <= p * ell := by
    nlinarith
  have ht' : t <= p * ell := by
    calc
      t <= ell * (p - 1) := ht
      _ <= ell * p := Nat.mul_le_mul_left ell (Nat.sub_le p 1)
      _ = p * ell := by ring
  have hTwo : 2 ^ t <= 2 ^ (p * ell) :=
    Nat.pow_le_pow_right (by omega) ht'
  have hThree : 3 ^ ell <= 3 ^ (p * ell) :=
    Nat.pow_le_pow_right (by omega) hEll
  have hBase : 864 ^ (p * ell) <= 10000 ^ (p * ell) :=
    Nat.pow_le_pow_left (by norm_num) _
  have hExtra : 3 <= 10000 ^ p := by
    calc
      3 <= 10000 := by norm_num
      _ <= 10000 ^ p := by
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < (10000 : Nat)) hpOne
  have hTwelveTwo :
      12 ^ (2 * p * ell) * 2 ^ (p * ell) = 288 ^ (p * ell) := by
    rw [show 2 * p * ell = 2 * (p * ell) by ring, pow_mul]
    rw [← mul_pow]
    norm_num
  have hThree288 :
      3 ^ (p * ell) * 288 ^ (p * ell) = 864 ^ (p * ell) := by
    rw [← mul_pow]
    norm_num
  calc
    3 ^ (ell + 1) * 12 ^ (2 * p * ell) * 2 ^ t <=
        3 ^ (ell + 1) * 12 ^ (2 * p * ell) * 2 ^ (p * ell) := by
      gcongr
    _ = 3 * 3 ^ ell *
          (12 ^ (2 * p * ell) * 2 ^ (p * ell)) := by
      rw [pow_add, pow_one]
      ring
    _ = 3 * (3 ^ ell * 288 ^ (p * ell)) := by
      rw [hTwelveTwo]
      ring
    _ <= 3 * (3 ^ (p * ell) * 288 ^ (p * ell)) := by
      gcongr
    _ = 3 * 864 ^ (p * ell) := by
      rw [hThree288]
    _ <= 10000 ^ p * 10000 ^ (p * ell) := by
      exact Nat.mul_le_mul hExtra hBase
    _ = 10000 ^ (p + p * ell) := by rw [pow_add]
    _ = 10000 ^ (p * (ell + 1)) := by
      congr 1
      ring
    _ = (100 ^ 2) ^ (p * (ell + 1)) := by
      congr 1
    _ = 100 ^ (2 * (p * (ell + 1))) := by
      exact (pow_mul 100 2 (p * (ell + 1))).symm
    _ = 100 ^ (2 * p * (ell + 1)) := by
      congr 1
      ring

/-- Conditional kernel of C079 Lemma 3.  The only hypotheses not discharged
here are precisely the per-state auxiliary-dimension lower bound and the
total auxiliary moment upper bound. -/
theorem c079_pathState_card_le_of_auxiliary_weight_bounds
    {alpha : Type*} [Fintype alpha]
    (weight : alpha -> Nat) (ell p t : Nat)
    (hp : 2 <= p) (ht : t <= ell * (p - 1))
    (hLower : forall x : alpha,
      (2 * p ^ 2) ^ (p * ell + 1 - t) <=
        3 ^ (ell + 1) * weight x)
    (hUpper : (∑ x : alpha, weight x) <=
      12 ^ (2 * p * ell) * (2 * p ^ 2) ^ (p * ell + 1)) :
    Fintype.card alpha <=
      100 ^ (2 * p * (ell + 1)) * p ^ (2 * t) := by
  have hm : 0 < 2 * p ^ 2 := by positivity
  have htDegree : t <= p * ell + 1 := by
    have ht' : t <= p * ell := by
      calc
        t <= ell * (p - 1) := ht
        _ <= ell * p := Nat.mul_le_mul_left ell (Nat.sub_le p 1)
        _ = p * ell := by ring
    omega
  have hCount := c079_card_le_of_scaled_power_weight_bounds
    weight (2 * p ^ 2) (3 ^ (ell + 1)) (12 ^ (2 * p * ell))
      (p * ell + 1) t hm htDegree hLower hUpper
  rw [c079_auxDimension_pow] at hCount
  calc
    Fintype.card alpha <=
        3 ^ (ell + 1) * 12 ^ (2 * p * ell) *
          (2 ^ t * p ^ (2 * t)) := hCount
    _ = (3 ^ (ell + 1) * 12 ^ (2 * p * ell) * 2 ^ t) *
          p ^ (2 * t) := by ring
    _ <= 100 ^ (2 * p * (ell + 1)) * p ^ (2 * t) := by
      exact Nat.mul_le_mul_right _
        (c079_path_fixedBases_le_hundred ell p t hp ht)


end GraphMatrixReplica
