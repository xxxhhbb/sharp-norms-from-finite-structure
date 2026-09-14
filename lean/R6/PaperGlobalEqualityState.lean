import R6.PaperToPartiteBridge
import R6.PaperTraceWordExpansion

/-! # Global equality states for the original paper model

Unlike the fully-partite surrogate, the original graph matrix uses one
global injection in every replica.  Its equality pattern therefore lives on
all `(role, replica)` occurrences at once; it is not a product of independent
per-role partitions.
-/

noncomputable section

namespace GraphMatrixReplica

/-- All role occurrences in the `2(p+1)` realizations of a Gram trace word. -/
abbrev PaperOccurrence (G : PaperShape) (p : ℕ) :=
  Fin G.roles × Replica (p + 1)

/-- The ambient label carried by a role occurrence. -/
def paperFamilyLabel (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    PaperOccurrence G p → Fin n :=
  fun z => phis z.2 z.1

/-- The single global equality partition induced by a realization family. -/
def paperFamilyEqualityPartition (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    Setoid (PaperOccurrence G p) where
  r a b := paperFamilyLabel G phis a = paperFamilyLabel G phis b
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

@[simp] theorem paperFamilyEqualityPartition_rel_iff
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n)
    (a b : PaperOccurrence G p) :
    (paperFamilyEqualityPartition G phis).r a b ↔
      paperFamilyLabel G phis a = paperFamilyLabel G phis b := by
  rfl

/-- Exact global state conditions forced by trace compatibility. -/
structure PaperTraceGlobalEqualityState (G : PaperShape) (p : ℕ) where
  partition : Setoid (PaperOccurrence G p)
  withinReplicaInjective : ∀ (x : Replica (p + 1))
      (v w : Fin G.roles), partition.r (v, x) (w, x) → v = w
  leftCyclicGlue : ∀ (v : Fin G.roles), v ∈ G.leftBoundaryFinset →
    ∀ i : Fin (p + 1),
      partition.r (v, (i, true))
        (v, (finRotate (p + 1) i, false))
  rightAdjacentGlue : ∀ (v : Fin G.roles), v ∈ G.rightBoundaryFinset →
    ∀ i : Fin (p + 1), partition.r (v, (i, false)) (v, (i, true))

/-- The number of blocks of a finite global equality state. -/
def PaperTraceGlobalEqualityState.blockCount
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) : ℕ := by
  classical
  exact Fintype.card (Quotient S.partition)

/-- Global injectivity of each realization becomes a same-replica rigidity
condition on the induced equality partition. -/
theorem paperFamilyEqualityPartition_withinReplicaInjective
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    ∀ (x : Replica (p + 1)) (v w : Fin G.roles),
      (paperFamilyEqualityPartition G phis).r (v, x) (w, x) → v = w := by
  intro x v w h
  exact (phis x).injective h

/-- Trace-compatible realization families induce admissible global equality
states.  No independence between roles or shape edges is assumed. -/
def paperTraceInducedGlobalState (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n)
    (hCompatible : paperTraceCompatible G n p phis rows cols) :
    PaperTraceGlobalEqualityState G p where
  partition := paperFamilyEqualityPartition G phis
  withinReplicaInjective :=
    paperFamilyEqualityPartition_withinReplicaInjective G phis
  leftCyclicGlue := by
    intro v hv i
    obtain ⟨j, hj⟩ := (G.mem_leftBoundaryFinset_iff v).1 hv
    subst v
    exact (hCompatible (i, true)).1 j |>.trans
      ((hCompatible (finRotate (p + 1) i, false)).1 j).symm
  rightAdjacentGlue := by
    intro v hv i
    obtain ⟨j, hj⟩ := (G.mem_rightBoundaryFinset_iff v).1 hv
    subst v
    exact (hCompatible (i, false)).2 j |>.trans
      ((hCompatible (i, true)).2 j).symm

#print axioms paperFamilyEqualityPartition_withinReplicaInjective
#print axioms paperTraceInducedGlobalState

end GraphMatrixReplica
