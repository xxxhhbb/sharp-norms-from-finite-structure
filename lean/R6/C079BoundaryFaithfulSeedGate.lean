import R6.C079ComponentSeedTreeProof

/-! # Boundary-faithful component seeds: a genuine obstruction

The component seed tree controls matching distance but does not prescribe a
trace matching at boundary components. One cut component can meet both
external boundaries under the current shape and path-family definitions.
For positive defect order, the two prescribed trace matchings differ.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A seed is boundary-faithful if every component meeting a left or right
boundary receives exactly the corresponding standard trace matching. -/
def ReplicaState.C079BoundaryFaithfulSeed
    {G : PartiteShape} {p s : ℕ} (_S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1)) : Prop :=
  (∀ c : G.C079CutComponent family.backboneRoles,
      (∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
        v ∈ G.leftBoundary) →
      seed c = (leftPerfectMatching p).toC079MatchingPartition) ∧
  (∀ c : G.C079CutComponent family.backboneRoles,
      (∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
        v ∈ G.rightBoundary) →
      seed c = (rightPerfectMatching (p + 1)).toC079MatchingPartition)

/-- At positive order the two standard trace matchings are different. -/
theorem c079_leftRightTraceMatching_ne {p : ℕ} (hp : 0 < p) :
    (leftPerfectMatching p).toC079MatchingPartition ≠
      (rightPerfectMatching (p + 1)).toC079MatchingPartition := by
  intro heq
  have hzero :=
    (c079MatchingPartitionDistance_eq_zero_iff_eq
      (rightPerfectMatching (p + 1)).toC079MatchingPartition
      (leftPerfectMatching p).toC079MatchingPartition).2 heq.symm
  rw [c079MatchingPartitionDistance_of_perfectMatching,
    right_left_matchingIntersectionDistance_eq] at hzero
  omega

/-- A genuine cut component touching both external boundaries cannot have
one seed satisfying both exact trace prescriptions. -/
theorem ReplicaState.no_boundaryFaithfulSeed_of_bothBoundaries
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) (hp : 0 < p)
    (c : G.C079CutComponent family.backboneRoles)
    (hL : ∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
      v ∈ G.leftBoundary)
    (hR : ∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
      v ∈ G.rightBoundary) :
    ¬ ∃ seed : G.C079CutComponent family.backboneRoles →
        C079MatchingPartition (p + 1),
      S.C079BoundaryFaithfulSeed family seed := by
  rintro ⟨seed, hSeed⟩
  have hleft := hSeed.1 c hL
  have hright := hSeed.2 c hR
  exact c079_leftRightTraceMatching_ne hp (hleft.symm.trans hright)

/-- One role belongs to both boundaries and has no edges. This shape is
covered; the empty path family leaves its one genuine cut component. -/
def c079DualBoundaryShape : PartiteShape where
  roles := 1
  edges := 0
  source := Fin.elim0
  target := Fin.elim0
  leftBoundary := Finset.univ
  rightBoundary := Finset.univ

def c079DualBoundaryEmptyFamily :
    c079DualBoundaryShape.VertexDisjointRightToLeftPaths 0 where
  start := Fin.elim0
  startRight := by intro i; exact Fin.elim0 i
  path := by intro i; exact Fin.elim0 i
  vertexAt_injective := by
    intro z
    exact Fin.elim0 z.1

/-- A valid exact state: the one-block partition coarsens both traces. -/
def c079DualBoundaryState : ReplicaState c079DualBoundaryShape 1 where
  partition := fun _ => universalReplicaPartition 2
  edgeParity := by intro e; exact Fin.elim0 e
  leftGlue := by
    intro v hv
    constructor
    · intro k
      trivial
    · trivial
  rightGlue := by
    intro v hv k
    trivial

def c079DualBoundaryRole : Fin c079DualBoundaryShape.roles :=
  ⟨0, by decide⟩

theorem c079DualBoundary_isBoundaryCore :
    c079DualBoundaryShape.IsBoundaryCore := by
  intro v
  exact ⟨PartiteShape.EdgeWalkToBoundary.finishLeft v
    (Finset.mem_univ v)⟩

def c079DualBoundaryComponent :
    c079DualBoundaryShape.C079CutComponent
      c079DualBoundaryEmptyFamily.backboneRoles :=
  (c079DualBoundaryShape.c079CutGraph
    c079DualBoundaryEmptyFamily.backboneRoles).connectedComponentMk
      ⟨c079DualBoundaryRole, by
        simp [c079DualBoundaryEmptyFamily,
          PartiteShape.VertexDisjointRightToLeftPaths.backboneRoles]⟩

theorem c079DualBoundaryRole_mem_component :
    c079DualBoundaryRole ∈
      c079DualBoundaryShape.c079ComponentRoles
        c079DualBoundaryEmptyFamily.backboneRoles
        c079DualBoundaryComponent := by
  apply (c079DualBoundaryShape.mem_c079ComponentRoles_iff
    c079DualBoundaryEmptyFamily.backboneRoles
    c079DualBoundaryComponent c079DualBoundaryRole).2
  refine ⟨?_, rfl⟩
  simp [c079DualBoundaryEmptyFamily,
    PartiteShape.VertexDisjointRightToLeftPaths.backboneRoles]

/-- This valid covered state has a genuine component meeting both
boundaries, so no boundary-faithful seed exists even though the covered
seed-tree and `3rD` merge-word theorems apply. -/
theorem c079DualBoundary_no_boundaryFaithfulSeed :
    ¬ ∃ seed : c079DualBoundaryShape.C079CutComponent
        c079DualBoundaryEmptyFamily.backboneRoles →
          C079MatchingPartition 2,
      c079DualBoundaryState.C079BoundaryFaithfulSeed
        c079DualBoundaryEmptyFamily seed := by
  apply c079DualBoundaryState.no_boundaryFaithfulSeed_of_bothBoundaries
    c079DualBoundaryEmptyFamily (by decide) c079DualBoundaryComponent
  · exact ⟨c079DualBoundaryRole, c079DualBoundaryRole_mem_component,
      Finset.mem_univ _⟩
  · exact ⟨c079DualBoundaryRole, c079DualBoundaryRole_mem_component,
      Finset.mem_univ _⟩

#print axioms c079_leftRightTraceMatching_ne
#print axioms ReplicaState.no_boundaryFaithfulSeed_of_bothBoundaries
#print axioms c079DualBoundary_isBoundaryCore
#print axioms c079DualBoundary_no_boundaryFaithfulSeed

end GraphMatrixReplica
