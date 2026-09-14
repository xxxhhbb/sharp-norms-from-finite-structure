import R6.C079PartitionMergeWord

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U2

theorem blockCount_le_of_coarsens {m : ℕ} {π σ : ReplicaPartition m}
    (h : PartitionCoarsens π σ) : partitionBlockCount π ≤ partitionBlockCount σ := by
  rw [← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) π,
    ← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) σ]
  exact Submodule.finrank_mono (partitionConstantSubspace_mono h)

/-- A fixed numbering of the current quotient blocks, recomputed after each merge.
The choice of numbering is part of the decoder, not an extra record. -/
def blockPoint {m : ℕ} (π : ReplicaPartition m) (i : Fin m) : Option (Replica m) := by
  classical
  exact if h : i.val < partitionBlockCount π then
    some (Quotient.out ((Fintype.equivFin (Quotient π)).symm ⟨i.val, h⟩))
  else none

def blockIndex {m : ℕ} (π : ReplicaPartition m)
    (hπ : partitionBlockCount π ≤ m) (a : Replica m) : Fin m := by
  classical
  exact ⟨(Fintype.equivFin (Quotient π) (Quotient.mk'' a)).val,
    lt_of_lt_of_le (Fintype.equivFin (Quotient π) (Quotient.mk'' a)).isLt hπ⟩

theorem blockPoint_index {m : ℕ} (π : ReplicaPartition m)
    (hπ : partitionBlockCount π ≤ m) (a : Replica m) :
    ∃ a', blockPoint π (blockIndex π hπ a) = some a' ∧ π.r a' a := by
  classical
  let q : Quotient π := Quotient.mk'' a
  refine ⟨Quotient.out q, ?_, ?_⟩
  · simp [blockPoint, blockIndex, q, partitionBlockCount]
  · exact Quotient.exact (Quotient.out_eq q)

def mergeBlock {m : ℕ} (π : ReplicaPartition m) (ij : Fin m × Fin m) :
    ReplicaPartition m :=
  match blockPoint π ij.1, blockPoint π ij.2 with
  | some a, some b => c079MergePoints π a b
  | _, _ => π

theorem mergePoints_eq_of_related {m : ℕ} (π : ReplicaPartition m)
    {a a' b b' : Replica m} (ha : π.r a' a) (hb : π.r b' b) :
    c079MergePoints π a' b' = c079MergePoints π a b := by
  apply Setoid.ext
  intro x y
  rw [mergePoints_rel_iff, mergePoints_rel_iff]
  have hxa : π.r x a' ↔ π.r x a :=
    ⟨fun h => π.iseqv.trans h ha, fun h => π.iseqv.trans h (π.iseqv.symm ha)⟩
  have hxb : π.r x b' ↔ π.r x b :=
    ⟨fun h => π.iseqv.trans h hb, fun h => π.iseqv.trans h (π.iseqv.symm hb)⟩
  have hya : π.r y a' ↔ π.r y a :=
    ⟨fun h => π.iseqv.trans h ha, fun h => π.iseqv.trans h (π.iseqv.symm ha)⟩
  have hyb : π.r y b' ↔ π.r y b :=
    ⟨fun h => π.iseqv.trans h hb, fun h => π.iseqv.trans h (π.iseqv.symm hb)⟩
  rw [hxa, hxb, hya, hyb]

theorem mergeBlock_index {m : ℕ} (π : ReplicaPartition m)
    (hπ : partitionBlockCount π ≤ m) (a b : Replica m) :
    mergeBlock π (blockIndex π hπ a, blockIndex π hπ b) = c079MergePoints π a b := by
  obtain ⟨a', ha', ha⟩ := blockPoint_index π hπ a
  obtain ⟨b', hb', hb⟩ := blockPoint_index π hπ b
  simp only [mergeBlock, ha', hb']
  exact mergePoints_eq_of_related π ha hb

theorem mergeBlock_coarsens {m : ℕ} (π : ReplicaPartition m) (ij : Fin m × Fin m) :
    PartitionCoarsens (mergeBlock π ij) π := by
  unfold mergeBlock
  split <;> try exact fun _ _ h => h
  exact mergePoints_coarsens _ _ _

theorem mergeBlock_self {m : ℕ} (π : ReplicaPartition m) (i : Fin m) :
    mergeBlock π (i, i) = π := by
  unfold mergeBlock
  cases h : blockPoint π i with
  | none => rfl
  | some a =>
    apply Setoid.ext
    intro x y
    rw [mergePoints_rel_iff]
    constructor
    · rintro (h | ⟨hxa, hya⟩ | ⟨hxa, hya⟩)
      · exact h
      · exact π.iseqv.trans hxa (π.iseqv.symm hya)
      · exact π.iseqv.trans hxa (π.iseqv.symm hya)
    · exact Or.inl

def decodeBlockWord {m : ℕ} (π : ReplicaPartition m) :
    List (Fin m × Fin m) → ReplicaPartition m
  | [] => π
  | ij :: rest => decodeBlockWord (mergeBlock π ij) rest

theorem recode_point_word {m : ℕ} (π : ReplicaPartition m)
    (hπ : partitionBlockCount π ≤ m) (word : List (Replica m × Replica m)) :
    ∃ code : List (Fin m × Fin m), code.length = word.length ∧
      decodeBlockWord π code = c079DecodeMergeWord π word := by
  induction word generalizing π with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons ab word ih =>
    have hnext : partitionBlockCount (c079MergePoints π ab.1 ab.2) ≤ m :=
      (blockCount_le_of_coarsens (mergePoints_coarsens π ab.1 ab.2)).trans hπ
    obtain ⟨code, hlen, hdec⟩ := ih (c079MergePoints π ab.1 ab.2) hnext
    refine ⟨(blockIndex π hπ ab.1, blockIndex π hπ ab.2) :: code, ?_, ?_⟩
    · simp only [List.length_cons, hlen]
    · simp only [decodeBlockWord, mergeBlock_index, c079DecodeMergeWord]
      exact hdec

theorem exists_block_word {m : ℕ} (π σ : ReplicaPartition m)
    (hσ : partitionBlockCount σ ≤ m) (h : PartitionCoarsens π σ) :
    ∃ code : List (Fin m × Fin m), decodeBlockWord σ code = π ∧
      code.length ≤ partitionBlockCount σ - partitionBlockCount π := by
  obtain ⟨word, hdec, hlen⟩ := exists_c079MergeWord π σ h
  obtain ⟨code, hc, hd⟩ := recode_point_word σ hσ word
  exact ⟨code, hd.trans hdec, hc.trans_le hlen⟩

#print axioms blockPoint_index
#print axioms mergeBlock_index
#print axioms exists_block_word
end GraphMatrixReplica.C079U2
