import GraphMatrix.ReplicaPartitionState

/-! # Block bound for even replica partitions

C078 uses the elementary consequence that an even partition of `2p` replicas
has at most `p` blocks.  This module proves that counting statement directly
for the typed quotient representation.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The block of `π` containing `a`, represented as a finite subset of the
replica type. -/
def partitionBlock {p : ℕ} (π : ReplicaPartition p) (a : Replica p) :
    Finset (Replica p) := by
  classical
  exact Finset.univ.filter fun b => π.r b a

/-- Every equality block has even cardinality. -/
def IsEvenPartition {p : ℕ} (π : ReplicaPartition p) : Prop :=
  ∀ a : Replica p, Even (partitionBlock π a).card

theorem mem_partitionBlock_self {p : ℕ} (π : ReplicaPartition p)
    (a : Replica p) : a ∈ partitionBlock π a := by
  classical
  simp [partitionBlock]

/-- A fiber of the quotient map is exactly the corresponding partition
block. -/
theorem quotientFiber_eq_partitionBlock {p : ℕ}
    (π : ReplicaPartition p) [DecidableEq (Quotient π)]
    (a : Replica p) :
    (Finset.univ.filter fun b : Replica p =>
      (Quotient.mk'' b : Quotient π) =
        (Quotient.mk'' a : Quotient π)) = partitionBlock π a := by
  classical
  ext b
  simp [partitionBlock, Quotient.eq]

/-- An even, nonempty block contains at least two replicas. -/
theorem two_le_card_partitionBlock_of_even {p : ℕ}
    (π : ReplicaPartition p) (hEven : IsEvenPartition π)
    (a : Replica p) : 2 ≤ (partitionBlock π a).card := by
  have hpos : 0 < (partitionBlock π a).card :=
    Finset.card_pos.mpr ⟨a, mem_partitionBlock_self π a⟩
  obtain ⟨k, hk⟩ := hEven a
  omega

/-- An even partition of `2(p+1)` replicas has at most `p+1` blocks. -/
theorem evenPartition_blockCount_le
    {p : ℕ} (π : ReplicaPartition (p + 1)) (hEven : IsEvenPartition π) :
    partitionBlockCount π ≤ p + 1 := by
  classical
  have hfiber : ∀ q : Quotient π,
      2 ≤ ((Finset.univ : Finset (Replica (p + 1))).filter
        fun a => Quotient.mk'' a = q).card := by
    intro q
    refine Quotient.inductionOn q fun a => ?_
    rw [quotientFiber_eq_partitionBlock]
    exact two_le_card_partitionBlock_of_even π hEven a
  have hsum :
      (Finset.univ : Finset (Replica (p + 1))).card =
        ∑ q : Quotient π,
          ((Finset.univ : Finset (Replica (p + 1))).filter
            fun a => Quotient.mk'' a = q).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (f := fun a : Replica (p + 1) => Quotient.mk'' a)
      (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  have hLower :
      2 * Fintype.card (Quotient π) ≤
        ∑ q : Quotient π,
          ((Finset.univ : Finset (Replica (p + 1))).filter
            fun a => Quotient.mk'' a = q).card := by
    calc
      2 * Fintype.card (Quotient π) = ∑ _q : Quotient π, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ q : Quotient π,
          ((Finset.univ : Finset (Replica (p + 1))).filter
            fun a => Quotient.mk'' a = q).card := by
        apply Finset.sum_le_sum
        intro q _
        exact hfiber q
  rw [← hsum] at hLower
  have hReplicaCard :
      (Finset.univ : Finset (Replica (p + 1))).card = 2 * (p + 1) := by
    simp [Replica, Nat.mul_comm]
  rw [hReplicaCard] at hLower
  unfold partitionBlockCount
  omega


end GraphMatrixReplica
