import GraphMatrix.ReplicaPartitionState

/-! # Finite Rademacher character sums and replica edge parity

This file supplies the probability/algebra bridge missing from the initial R6
foundation.  The sum is kept over `ℤ`, so the cancellation statement is exact
and contains no analytic or measure-theoretic assumptions.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The two Rademacher signs, encoded by `Bool`. -/
def rademacherSign : Bool → ℤ
  | false => 1
  | true => -1

/-- Number of occurrences using a given sign coordinate. -/
def occurrenceMultiplicity {A K : Type*} [Fintype A] [Fintype K]
    [DecidableEq K] (key : A → K) (k : K) : ℕ :=
  (Finset.univ.filter fun a => key a = k).card

/-- The character produced by one assignment of independent signs. -/
def rademacherCharacter {A K : Type*} [Fintype A] [Fintype K]
    (key : A → K) (epsilon : K → Bool) : ℤ :=
  ∏ a : A, rademacherSign (epsilon (key a))

/-- The unnormalised expectation numerator over all sign assignments. -/
def rademacherCharacterSum {A K : Type*} [Fintype A] [Fintype K]
    [DecidableEq K]
    (key : A → K) : ℤ :=
  ∑ epsilon : K → Bool, rademacherCharacter key epsilon

theorem rademacherSign_pow_sum (m : ℕ) :
    (∑ b : Bool, rademacherSign b ^ m) = if Even m then 2 else 0 := by
  by_cases h : Even m
  · rw [if_pos h]
    simp [rademacherSign, h.neg_one_pow]
  · rw [if_neg h]
    have hm : Odd m := Nat.not_even_iff_odd.mp h
    simp [rademacherSign, hm.neg_one_pow]

theorem rademacherCharacter_fiberwise
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K) (epsilon : K → Bool) :
    rademacherCharacter key epsilon =
      ∏ k : K, rademacherSign (epsilon k) ^ occurrenceMultiplicity key k := by
  classical
  unfold rademacherCharacter occurrenceMultiplicity
  calc
    ∏ a : A, rademacherSign (epsilon (key a)) =
        ∏ k : K, ∏ _a ∈ (Finset.univ.filter fun a : A => key a = k),
          rademacherSign (epsilon k) := by
      exact (Finset.prod_fiberwise' Finset.univ key
        (fun k => rademacherSign (epsilon k))).symm
    _ = ∏ k : K,
        rademacherSign (epsilon k) ^
          (Finset.univ.filter fun a : A => key a = k).card := by
      simp

theorem rademacherCharacterSum_factorized
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K) :
    rademacherCharacterSum key =
      ∏ k : K, (∑ b : Bool, rademacherSign b ^ occurrenceMultiplicity key k) := by
  classical
  unfold rademacherCharacterSum
  simp_rw [rademacherCharacter_fiberwise key]
  exact (Fintype.prod_sum (fun k b =>
    rademacherSign b ^ occurrenceMultiplicity key k)).symm

/-- A finite Rademacher character has full mass exactly when every coordinate
occurs evenly, and otherwise cancels to zero. -/
theorem rademacherCharacterSum_eq_indicator
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K) :
    rademacherCharacterSum key =
      if ∀ k : K, Even (occurrenceMultiplicity key k)
      then (2 : ℤ) ^ Fintype.card K else 0 := by
  classical
  rw [rademacherCharacterSum_factorized]
  simp_rw [rademacherSign_pow_sum]
  by_cases h : ∀ k : K, Even (occurrenceMultiplicity key k)
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    push Not at h
    obtain ⟨k, hk⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- Uniform average of a finite Rademacher character. -/
def rademacherCharacterAverage
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K) : ℚ :=
  (rademacherCharacterSum key : ℚ) / (2 : ℚ) ^ Fintype.card K

/-- Normalized form: the finite Rademacher expectation is the parity
indicator. -/
theorem rademacherCharacterAverage_eq_indicator
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K) :
    rademacherCharacterAverage key =
      if ∀ k : K, Even (occurrenceMultiplicity key k) then 1 else 0 := by
  classical
  unfold rademacherCharacterAverage
  rw [rademacherCharacterSum_eq_indicator]
  by_cases h : ∀ k : K, Even (occurrenceMultiplicity key k)
  · rw [if_pos h, if_pos h]
    norm_num [pow_ne_zero]
  · rw [if_neg h, if_neg h]
    simp

theorem occurrenceMultiplicity_pair_eq_edgeMultiplicity
    {p : ℕ} {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (x : Replica p → alpha) (y : Replica p → beta) (a : Replica p) :
    occurrenceMultiplicity (fun b => (x b, y b)) (x a, y a) =
      edgeMultiplicity x y a := by
  classical
  unfold occurrenceMultiplicity edgeMultiplicity
  congr 1
  ext b
  simp

theorem all_pair_multiplicities_even_iff
    {p : ℕ} {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (x : Replica p → alpha) (y : Replica p → beta) :
    (∀ k : alpha × beta,
        Even (occurrenceMultiplicity (fun b => (x b, y b)) k)) ↔
      ∀ a : Replica p, Even (edgeMultiplicity x y a) := by
  classical
  constructor
  · intro h a
    rw [← occurrenceMultiplicity_pair_eq_edgeMultiplicity x y a]
    exact h (x a, y a)
  · intro h k
    by_cases hk : ∃ a : Replica p, (x a, y a) = k
    · obtain ⟨a, rfl⟩ := hk
      rw [occurrenceMultiplicity_pair_eq_edgeMultiplicity]
      exact h a
    · have hempty :
          (Finset.univ.filter fun a : Replica p => (x a, y a) = k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro a _ ha
        exact hk ⟨a, ha⟩
      unfold occurrenceMultiplicity
      rw [hempty]
      simp

/-- Exact finite sign-sum form of the Rademacher edge rule for concrete
replica labelings. -/
theorem replicaEdgeCharacterSum_eq_indicator
    {p : ℕ} {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (x : Replica p → alpha) (y : Replica p → beta)
    [Decidable (EdgeParityCompatible
      (equalityPartition x) (equalityPartition y))] :
    rademacherCharacterSum (fun a => (x a, y a)) =
      if EdgeParityCompatible (equalityPartition x) (equalityPartition y)
      then (2 : ℤ) ^ Fintype.card (alpha × beta) else 0 := by
  rw [rademacherCharacterSum_eq_indicator]
  by_cases h : EdgeParityCompatible
      (equalityPartition x) (equalityPartition y)
  · have hpairs : ∀ k : alpha × beta,
        Even (occurrenceMultiplicity (fun a => (x a, y a)) k) :=
      (all_pair_multiplicities_even_iff x y).2
        ((edgeParityCompatible_equalityPartitions_iff x y).1 h)
    rw [if_pos hpairs, if_pos h]
  · have hpairs : ¬ ∀ k : alpha × beta,
        Even (occurrenceMultiplicity (fun a => (x a, y a)) k) := by
      intro hpairs
      apply h
      exact (edgeParityCompatible_equalityPartitions_iff x y).2
        ((all_pair_multiplicities_even_iff x y).1 hpairs)
    rw [if_neg hpairs, if_neg h]

/-- Probability-normalized edge rule: the expectation is exactly one for a
parity-compatible replica labeling and zero otherwise. -/
theorem replicaEdgeCharacterAverage_eq_indicator
    {p : ℕ} {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (x : Replica p → alpha) (y : Replica p → beta)
    [Decidable (EdgeParityCompatible
      (equalityPartition x) (equalityPartition y))] :
    rademacherCharacterAverage (fun a => (x a, y a)) =
      if EdgeParityCompatible (equalityPartition x) (equalityPartition y)
      then 1 else 0 := by
  unfold rademacherCharacterAverage
  rw [replicaEdgeCharacterSum_eq_indicator]
  by_cases h : EdgeParityCompatible
      (equalityPartition x) (equalityPartition y)
  · rw [if_pos h, if_pos h]
    norm_num [pow_ne_zero]
  · rw [if_neg h, if_neg h]
    simp


end GraphMatrixReplica
