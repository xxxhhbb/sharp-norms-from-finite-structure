import R6.EvenPartitionBlockBound

/-! # Edge parity forces even endpoint partitions

For a nonisolated role, C078 obtains even equality blocks by decomposing a
role block into meet cells along any incident edge.  This file formalizes that
finite fiber decomposition.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Inside a fixed `π`-block, a fiber of the quotient map for `σ` is exactly
one `π ∧ σ` meet cell. -/
theorem quotientFiberInBlock_eq_meetCell
    {p : ℕ} (π σ : ReplicaPartition p) [DecidableEq (Quotient σ)]
    (a b : Replica p) (hb : b ∈ partitionBlock π a) :
    ((partitionBlock π a).filter fun x =>
      (Quotient.mk'' x : Quotient σ) = Quotient.mk'' b) =
        partitionMeetCell π σ b := by
  classical
  ext x
  simp only [Finset.mem_filter]
  have hba : π.r b a := by
    simpa only [partitionBlock, Finset.mem_filter, Finset.mem_univ,
      true_and] using hb
  constructor
  · rintro ⟨hxBlock, hxQuot⟩
    have hxa : π.r x a := by
      simpa only [partitionBlock, Finset.mem_filter, Finset.mem_univ,
        true_and] using hxBlock
    have hxb : π.r x b :=
      π.iseqv.trans hxa (π.iseqv.symm hba)
    have hsxb : σ.r x b := Quotient.eq''.mp hxQuot
    simpa only [partitionMeetCell, Finset.mem_filter, Finset.mem_univ,
      true_and] using And.intro hxb hsxb
  · intro hxCell
    have hpair : π.r x b ∧ σ.r x b := by
      simpa only [partitionMeetCell, Finset.mem_filter, Finset.mem_univ,
        true_and] using hxCell
    have hxa : π.r x a := π.iseqv.trans hpair.1 hba
    have hxBlock : x ∈ partitionBlock π a := by
      simpa only [partitionBlock, Finset.mem_filter, Finset.mem_univ,
        true_and]
    exact ⟨hxBlock, Quotient.sound hpair.2⟩

/-- Edge parity makes every block of the first endpoint partition even. -/
theorem edgeParityCompatible_even_left
    {p : ℕ} (π σ : ReplicaPartition p)
    (hEdge : EdgeParityCompatible π σ) : IsEvenPartition π := by
  classical
  intro a
  let fiber : Quotient σ → Finset (Replica p) := fun q =>
    (partitionBlock π a).filter fun x =>
      (Quotient.mk'' x : Quotient σ) = q
  have hFiberEven : ∀ q : Quotient σ, Even (fiber q).card := by
    intro q
    by_cases hq : (fiber q).Nonempty
    · obtain ⟨b, hb⟩ := hq
      have hbBlock : b ∈ partitionBlock π a := (Finset.mem_filter.mp hb).1
      have hbQuot : (Quotient.mk'' b : Quotient σ) = q :=
        (Finset.mem_filter.mp hb).2
      rw [← hbQuot]
      change Even
        (((partitionBlock π a).filter fun x =>
          (Quotient.mk'' x : Quotient σ) = Quotient.mk'' b).card)
      rw [quotientFiberInBlock_eq_meetCell π σ a b hbBlock]
      exact hEdge b
    · have hEmpty : fiber q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hq
      rw [hEmpty]
      exact Even.zero
  have hCard :
      (partitionBlock π a).card = ∑ q : Quotient σ, (fiber q).card := by
    simpa [fiber] using Finset.card_eq_sum_card_fiberwise
      (f := fun x : Replica p => (Quotient.mk'' x : Quotient σ))
      (s := partitionBlock π a) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  choose half hHalf using hFiberEven
  refine ⟨∑ q : Quotient σ, half q, ?_⟩
  rw [hCard]
  simp_rw [hHalf]
  rw [Finset.sum_add_distrib]

/-- Symmetric endpoint form. -/
theorem edgeParityCompatible_even_right
    {p : ℕ} (π σ : ReplicaPartition p)
    (hEdge : EdgeParityCompatible π σ) : IsEvenPartition σ := by
  exact edgeParityCompatible_even_left σ π
    ((edgeParityCompatible_comm π σ).mp hEdge)

/-- Each endpoint of a parity-compatible edge has at most `p+1` blocks at
moment order `p+1`. -/
theorem edgeParityCompatible_blockCount_le
    {p : ℕ} (π σ : ReplicaPartition (p + 1))
    (hEdge : EdgeParityCompatible π σ) :
    partitionBlockCount π ≤ p + 1 ∧ partitionBlockCount σ ≤ p + 1 := by
  exact ⟨evenPartition_blockCount_le π
      (edgeParityCompatible_even_left π σ hEdge),
    evenPartition_blockCount_le σ
      (edgeParityCompatible_even_right π σ hEdge)⟩

/-- In a replica state, both endpoints of every graph edge satisfy the block
bound used in the C078 degree argument. -/
theorem ReplicaState.edgeEndpoint_blockCount_le
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (e : Fin G.edges) :
    partitionBlockCount (S.partition (G.source e)) ≤ p + 1 ∧
      partitionBlockCount (S.partition (G.target e)) ≤ p + 1 :=
  edgeParityCompatible_blockCount_le _ _ (S.edgeParity e)

#print axioms quotientFiberInBlock_eq_meetCell
#print axioms edgeParityCompatible_even_left
#print axioms edgeParityCompatible_even_right
#print axioms edgeParityCompatible_blockCount_le
#print axioms ReplicaState.edgeEndpoint_blockCount_le

end GraphMatrixReplica
