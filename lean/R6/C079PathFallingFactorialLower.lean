import R6.C079PathStateCountInterface
import Mathlib.Data.Nat.Factorial.BigOperators

/-! # C079 path auxiliary falling-factorial lower bound

For trace order `q >= 2`, C079 evaluates the path state polynomial at the
auxiliary dimension `m = 2*q^2`.  This file proves a slightly stronger local
bound than the paper needs:

`m^b <= 2 * m.descFactorial b` whenever `b <= q`.

The proof is the elementary collision/union-bound estimate written as a
product inequality over the rationals.  It is uniform in `q` and `b`; no
finite enumeration is used.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Finite-product form of the elementary union bound
`prod (1-f_i) >= 1 - sum f_i`. -/
theorem c079_one_sub_sum_le_prod_one_sub
    (f : Nat -> Rat) (b : Nat)
    (hNonneg : forall i, i < b -> 0 <= f i)
    (hAtMostOne : forall i, i < b -> f i <= 1) :
    1 - (Finset.range b).sum f <=
      (Finset.range b).prod (fun i => 1 - f i) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      have hPrevNonneg : 0 <= (Finset.range b).sum f :=
        Finset.sum_nonneg fun i hi => hNonneg i (by
          exact Nat.lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self b))
      have hFactorNonneg : 0 <= 1 - f b := sub_nonneg.mpr <|
        hAtMostOne b (Nat.lt_succ_self b)
      have hInd := ih
        (fun i hi => hNonneg i (Nat.lt_trans hi (Nat.lt_succ_self b)))
        (fun i hi => hAtMostOne i (Nat.lt_trans hi (Nat.lt_succ_self b)))
      calc
        1 - ((Finset.range b).sum f + f b) <=
            (1 - f b) * (1 - (Finset.range b).sum f) := by
          have hfb := hNonneg b (Nat.lt_succ_self b)
          nlinarith
        _ <= (1 - f b) *
            (Finset.range b).prod (fun i => 1 - f i) :=
          mul_le_mul_of_nonneg_left hInd hFactorNonneg
        _ = (Finset.range b).prod (fun i => 1 - f i) *
            (1 - f b) := by ring

/-- Exact rational normalization of a descending factorial. -/
theorem c079_prod_one_sub_div_mul_pow_eq_descFactorial
    (m b : Nat) (hm : 0 < m) (hb : b <= m) :
    (Finset.range b).prod
        (fun i => (1 : Rat) - (i : Rat) / (m : Rat)) *
      (m : Rat) ^ b = (m.descFactorial b : Rat) := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hb' : b <= m := Nat.le_trans (Nat.le_succ b) hb
      have hmRat : (m : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      have hFactor :
          ((1 : Rat) - (b : Rat) / (m : Rat)) * (m : Rat) =
            (m - b : Nat) := by
        rw [Nat.cast_sub hb']
        field_simp
      rw [Finset.prod_range_succ, pow_succ, Nat.descFactorial_succ,
        Nat.cast_mul, Nat.cast_sub hb']
      calc
        ((Finset.range b).prod
              (fun i => (1 : Rat) - (i : Rat) / (m : Rat)) *
            ((1 : Rat) - (b : Rat) / (m : Rat))) *
            ((m : Rat) ^ b * (m : Rat)) =
            ((Finset.range b).prod
                (fun i => (1 : Rat) - (i : Rat) / (m : Rat)) *
              (m : Rat) ^ b) *
              (((1 : Rat) - (b : Rat) / (m : Rat)) * (m : Rat)) := by
          ring
        _ = (m.descFactorial b : Rat) * (m - b : Nat) := by
          rw [ih hb', hFactor]
        _ = (m - b : Rat) * (m.descFactorial b : Rat) := by
          rw [Nat.cast_sub hb']
          ring

/-- Uniform local falling-factorial lower bound at C079's auxiliary
dimension.  The factor `2` improves the paper's convenient factor `3`. -/
theorem c079_auxDimension_pow_le_two_mul_descFactorial
    (q b : Nat) (hq : 2 <= q) (hb : b <= q) :
    (2 * q ^ 2) ^ b <=
      2 * (2 * q ^ 2).descFactorial b := by
  let m : Nat := 2 * q ^ 2
  have hqPos : 0 < q := by omega
  have hm : 0 < m := by
    dsimp [m]
    positivity
  have hq_le_m : q <= m := by
    dsimp [m]
    nlinarith [sq_nonneg (q : Int)]
  have hb_m : b <= m := hb.trans hq_le_m
  let f : Nat -> Rat := fun i => (i : Rat) / (m : Rat)
  have hfNonneg : forall i, i < b -> 0 <= f i := by
    intro i hi
    dsimp [f]
    positivity
  have hfOne : forall i, i < b -> f i <= 1 := by
    intro i hi
    have hiq : i <= q := by omega
    have him : i <= m := hiq.trans hq_le_m
    dsimp [f]
    exact (div_le_one (by exact_mod_cast hm)).2 (by exact_mod_cast him)
  have hSumNat : (Finset.range b).sum (fun i => i) <= q ^ 2 := by
    calc
      (Finset.range b).sum (fun i => i) <=
          (Finset.range b).sum (fun _i => q) := by
        exact Finset.sum_le_sum fun i hi => by
          have hib : i < b := Finset.mem_range.mp hi
          omega
      _ = b * q := by simp
      _ <= q * q := Nat.mul_le_mul_right q hb
      _ = q ^ 2 := by ring
  have hSum : (Finset.range b).sum f <= (1 : Rat) / 2 := by
    have hmRatPos : (0 : Rat) < (m : Rat) := by exact_mod_cast hm
    calc
      (Finset.range b).sum f =
          ((Finset.range b).sum (fun i => (i : Rat))) / (m : Rat) := by
        simp [f, Finset.sum_div]
      _ <= (q ^ 2 : Nat) / (m : Rat) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hmRatPos)
        have hCastEq :
            (Finset.range b).sum (fun i => (i : Rat)) =
              ((Finset.range b).sum (fun i => i) : Nat) := by
          exact (Nat.cast_sum (s := Finset.range b) (f := fun i => i)).symm
        rw [hCastEq]
        exact_mod_cast hSumNat
      _ = (1 : Rat) / 2 := by
        dsimp [m]
        have hqRat : (q : Rat) ≠ 0 := by exact_mod_cast hqPos.ne'
        field_simp
        norm_cast
        ring
  have hProd :
      (1 : Rat) / 2 <=
        (Finset.range b).prod
          (fun i => (1 : Rat) - (i : Rat) / (m : Rat)) := by
    calc
      (1 : Rat) / 2 <= 1 - (Finset.range b).sum f := by linarith
      _ <= (Finset.range b).prod (fun i => 1 - f i) :=
        c079_one_sub_sum_le_prod_one_sub f b hfNonneg hfOne
      _ = (Finset.range b).prod
          (fun i => (1 : Rat) - (i : Rat) / (m : Rat)) := rfl
  have hMul := mul_le_mul_of_nonneg_right hProd
    (show (0 : Rat) <= (m : Rat) ^ b by positivity)
  have hNormalize :=
    c079_prod_one_sub_div_mul_pow_eq_descFactorial m b hm hb_m
  have hRat : ((m ^ b : Nat) : Rat) <=
      2 * (m.descFactorial b : Rat) := by
    rw [hNormalize] at hMul
    norm_num at hMul ⊢
    linarith
  exact_mod_cast hRat

/-- Rolewise product form.  `hCovered` is essential: without it, an isolated
unconstrained role can have more than `q` blocks and the local factorial
estimate above need not apply. -/
theorem c079_auxiliaryWeight_lower_of_covered
    (G : PartiteShape) (p : Nat)
    (hCovered : forall v : Fin G.roles, G.RoleCovered v)
    (hp : 1 <= p) (S : ReplicaState G p) :
    (2 * (p + 1) ^ 2) ^ S.totalBlockCount <=
      2 ^ G.roles *
        S.labelingWeight (fun _v : Fin G.roles => 2 * (p + 1) ^ 2) := by
  let m : Nat := 2 * (p + 1) ^ 2
  calc
    m ^ S.totalBlockCount =
        ∏ v : Fin G.roles,
          m ^ partitionBlockCount (S.partition v) := by
      simp [ReplicaState.totalBlockCount, Finset.prod_pow_eq_pow_sum]
    _ <= ∏ v : Fin G.roles,
          2 * m.descFactorial (partitionBlockCount (S.partition v)) := by
      exact Finset.prod_le_prod' fun v _ =>
        c079_auxDimension_pow_le_two_mul_descFactorial
          (p + 1) (partitionBlockCount (S.partition v))
          (by omega) (S.coveredRole_blockCount_le v (hCovered v))
    _ = 2 ^ G.roles * S.labelingWeight
          (fun _v : Fin G.roles => m) := by
      simp [ReplicaState.labelingWeight, Finset.prod_mul_distrib]

/-- The first analytic-looking input of C079 Lemma 3 is actually a finite
combinatorial inequality.  This directly discharges `hLower` from the path
degree-fiber interface for every covered path shape.  The conclusion uses
the paper's harmless base `3`, although the rolewise estimate uses `2`. -/
theorem c079PathAuxiliaryWeight_lower
    (G : PartiteShape) (p ell t : Nat)
    (hRoles : G.roles = ell + 1)
    (hCovered : forall v : Fin G.roles, G.RoleCovered v)
    (hp : 1 <= p) (T : C079PathStateDegreeFiber G p ell t) :
    (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1 - t) <=
      3 ^ (ell + 1) * c079PathAuxiliaryWeight T := by
  have hDegree :
      T.1.toReplicaState.totalBlockCount =
        (p + 1) * ell + 1 - t := T.2
  have hLocal := c079_auxiliaryWeight_lower_of_covered
    G p hCovered hp T.1.toReplicaState
  have hTwoThree : 2 ^ G.roles <= 3 ^ G.roles :=
    Nat.pow_le_pow_left (by norm_num) _
  calc
    (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1 - t) =
        (2 * (p + 1) ^ 2) ^ T.1.toReplicaState.totalBlockCount := by
      rw [hDegree]
    _ <= 2 ^ G.roles * c079PathAuxiliaryWeight T := hLocal
    _ <= 3 ^ G.roles * c079PathAuxiliaryWeight T :=
      Nat.mul_le_mul_right _ hTwoThree
    _ = 3 ^ (ell + 1) * c079PathAuxiliaryWeight T := by
      rw [hRoles]

/-- C079 path count with the local factorial lower hypothesis eliminated.
Only the auxiliary moment upper bound remains; it must be justified for a
canonical path shape by an independent sign-matrix product argument. -/
theorem c079_pathStateDegreeFiber_card_le_of_auxiliary_upper
    (G : PartiteShape) (p ell t : Nat)
    (hRoles : G.roles = ell + 1)
    (hCovered : forall v : Fin G.roles, G.RoleCovered v)
    (hp : 1 <= p) (ht : t <= ell * p)
    (hUpper :
      (∑ T : C079PathStateDegreeFiber G p ell t,
          c079PathAuxiliaryWeight T) <=
        12 ^ (2 * (p + 1) * ell) *
          (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1)) :
    Fintype.card (C079PathStateDegreeFiber G p ell t) <=
      100 ^ (2 * (p + 1) * (ell + 1)) * (p + 1) ^ (2 * t) := by
  exact c079_pathStateDegreeFiber_card_le_of_auxiliary_bounds
    G p ell t hRoles hp ht
    (c079PathAuxiliaryWeight_lower G p ell t hRoles hCovered hp)
    hUpper

#print axioms c079_one_sub_sum_le_prod_one_sub
#print axioms c079_prod_one_sub_div_mul_pow_eq_descFactorial
#print axioms c079_auxDimension_pow_le_two_mul_descFactorial
#print axioms c079_auxiliaryWeight_lower_of_covered
#print axioms c079PathAuxiliaryWeight_lower
#print axioms c079_pathStateDegreeFiber_card_le_of_auxiliary_upper

end GraphMatrixReplica
