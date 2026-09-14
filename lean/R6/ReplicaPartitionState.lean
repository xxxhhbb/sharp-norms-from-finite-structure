import Mathlib

/-! # Typed replica-partition states for fully-partite graph matrices

This file formalizes the model-independent state space used by C078/C079.
It is deliberately separate from the Gaussian RTN Wick-subset development:
here edge compatibility is Rademacher parity of intersections of equality
partitions.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The `2p` occurrences are represented as `p` adjacent pairs. -/
abbrev Replica (p : ℕ) := Fin p × Bool

/-- An equality pattern on the replicas. -/
abbrev ReplicaPartition (p : ℕ) := Setoid (Replica p)

/-- The equality partition induced by an actual replica labeling. -/
@[instance_reducible] def equalityPartition {p : ℕ} {α : Type*} (x : Replica p → α) :
    ReplicaPartition p where
  r a b := x a = x b
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

@[simp] theorem equalityPartition_rel_iff
    {p : ℕ} {α : Type*} (x : Replica p → α) (a b : Replica p) :
    (equalityPartition x).r a b ↔ x a = x b := by
  rfl

/-- Number of blocks of a finite replica partition. -/
def partitionBlockCount {p : ℕ} (π : ReplicaPartition p) : ℕ := by
  classical
  exact Fintype.card (Quotient π)

/-- The meet cell of two role partitions containing replica `a`. -/
def partitionMeetCell {p : ℕ} (π σ : ReplicaPartition p)
    (a : Replica p) : Finset (Replica p) := by
  classical
  exact Finset.univ.filter fun b => π.r b a ∧ σ.r b a

/-- Rademacher edge parity: every cell of the meet partition has even size. -/
def EdgeParityCompatible {p : ℕ} (π σ : ReplicaPartition p) : Prop :=
  ∀ a : Replica p, Even (partitionMeetCell π σ a).card

theorem edgeParityCompatible_comm {p : ℕ} (π σ : ReplicaPartition p) :
    EdgeParityCompatible π σ ↔ EdgeParityCompatible σ π := by
  constructor <;> intro h a
  · rw [show partitionMeetCell σ π a = partitionMeetCell π σ a by
      ext b
      simp only [partitionMeetCell, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩]
    exact h a
  · rw [show partitionMeetCell π σ a = partitionMeetCell σ π a by
      ext b
      simp only [partitionMeetCell, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₂, h₁⟩]
    exact h a

/-- Multiplicity of the edge-sign coordinate used at replica `a`. -/
def edgeMultiplicity {p : ℕ} {α β : Type*}
    (x : Replica p → α) (y : Replica p → β) (a : Replica p) : ℕ := by
  classical
  exact (Finset.univ.filter fun b => x b = x a ∧ y b = y a).card

/-- The abstract meet-cell condition is exactly the concrete even-frequency
condition for a pair of replica labelings. -/
theorem edgeParityCompatible_equalityPartitions_iff
    {p : ℕ} {α β : Type*}
    (x : Replica p → α) (y : Replica p → β) :
    EdgeParityCompatible (equalityPartition x) (equalityPartition y) ↔
      ∀ a : Replica p, Even (edgeMultiplicity x y a) := by
  classical
  constructor
  · intro h a
    have hcell :
        partitionMeetCell (equalityPartition x) (equalityPartition y) a =
          Finset.univ.filter (fun b => x b = x a ∧ y b = y a) := by
      ext b
      simp only [partitionMeetCell, Finset.mem_filter, Finset.mem_univ,
        true_and, equalityPartition_rel_iff]
    unfold edgeMultiplicity
    rw [← hcell]
    exact h a
  · intro h a
    have hcell :
        partitionMeetCell (equalityPartition x) (equalityPartition y) a =
          Finset.univ.filter (fun b => x b = x a ∧ y b = y a) := by
      ext b
      simp only [partitionMeetCell, Finset.mem_filter, Finset.mem_univ,
        true_and, equalityPartition_rel_iff]
    rw [hcell]
    exact h a

/-- Coarsening of the right trace gluing
`(0,1),(2,3),...,(2p-2,2p-1)`. -/
def RightTraceCoarsens {p : ℕ} (π : ReplicaPartition (p + 1)) : Prop :=
  ∀ k : Fin (p + 1), π.r (k, false) (k, true)

/-- Coarsening of the left cyclic trace gluing
`(1,2),(3,4),...,(2p-1,0)` for `p+1` adjacent pairs. -/
def LeftTraceCoarsens {p : ℕ} (π : ReplicaPartition (p + 1)) : Prop :=
  (∀ k : Fin p, π.r (k.castSucc, true) (k.succ, false)) ∧
    π.r (Fin.last p, true) (0, false)

/-- Simultaneously coarsening the two trace matchings forces the whole
alternating cycle into one equality block. -/
theorem common_trace_coarsening_universal
    {p : ℕ} (π : ReplicaPartition (p + 1))
    (hL : LeftTraceCoarsens π) (hR : RightTraceCoarsens π) :
    ∀ a b : Replica (p + 1), π.r a b := by
  have hzero : ∀ k : Fin (p + 1), π.r (0, false) (k, false) := by
    intro k
    induction k using Fin.induction with
    | zero => exact π.iseqv.refl _
    | succ k ih =>
        exact π.iseqv.trans (π.iseqv.trans ih (hR k.castSucc)) (hL.1 k)
  have htoZero : ∀ a : Replica (p + 1), π.r a (0, false) := by
    rintro ⟨k, b⟩
    cases b with
    | false => exact π.iseqv.symm (hzero k)
    | true =>
        exact π.iseqv.trans (π.iseqv.symm (hR k))
          (π.iseqv.symm (hzero k))
  intro a b
  exact π.iseqv.trans (htoZero a) (π.iseqv.symm (htoZero b))

/-- Consequently a common-boundary equality partition has one block. -/
theorem common_trace_coarsening_blockCount_eq_one
    {p : ℕ} (π : ReplicaPartition (p + 1))
    (hL : LeftTraceCoarsens π) (hR : RightTraceCoarsens π) :
    partitionBlockCount π = 1 := by
  classical
  unfold partitionBlockCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk'' ((0, false) : Replica (p + 1)), ?_⟩
  intro q
  refine Quotient.inductionOn q fun a => ?_
  exact Quotient.sound (common_trace_coarsening_universal π hL hR a (0, false))

/-- Finite fully-partite graph shape used by the replica state. -/
structure PartiteShape where
  roles : ℕ
  edges : ℕ
  source : Fin edges → Fin roles
  target : Fin edges → Fin roles
  leftBoundary : Finset (Fin roles)
  rightBoundary : Finset (Fin roles)

/-- Exact typed C078 state at positive moment order `p+1`. -/
structure ReplicaState (G : PartiteShape) (p : ℕ) where
  partition : Fin G.roles → ReplicaPartition (p + 1)
  edgeParity : ∀ e : Fin G.edges,
    EdgeParityCompatible (partition (G.source e)) (partition (G.target e))
  leftGlue : ∀ v : Fin G.roles, v ∈ G.leftBoundary →
    LeftTraceCoarsens (partition v)
  rightGlue : ∀ v : Fin G.roles, v ∈ G.rightBoundary →
    RightTraceCoarsens (partition v)

/-- Every common-boundary role in an exact replica state has the universal
partition. -/
theorem ReplicaState.commonBoundary_universal
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (v : Fin G.roles) (hL : v ∈ G.leftBoundary)
    (hR : v ∈ G.rightBoundary) :
    ∀ a b : Replica (p + 1), (S.partition v).r a b :=
  common_trace_coarsening_universal (S.partition v)
    (S.leftGlue v hL) (S.rightGlue v hR)

/-- Block-count form of the common-boundary constraint. -/
theorem ReplicaState.commonBoundary_blockCount_eq_one
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (v : Fin G.roles) (hL : v ∈ G.leftBoundary)
    (hR : v ∈ G.rightBoundary) :
    partitionBlockCount (S.partition v) = 1 :=
  common_trace_coarsening_blockCount_eq_one (S.partition v)
    (S.leftGlue v hL) (S.rightGlue v hR)

#print axioms edgeParityCompatible_comm
#print axioms edgeParityCompatible_equalityPartitions_iff
#print axioms common_trace_coarsening_universal
#print axioms common_trace_coarsening_blockCount_eq_one
#print axioms ReplicaState.commonBoundary_universal
#print axioms ReplicaState.commonBoundary_blockCount_eq_one

end GraphMatrixReplica
