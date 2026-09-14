import R6.U3RolewiseProfiles

/-!
U3: actual reconstruction quantifier and boundary-seed semantics.
No seed cardinality or geometric incidence inequality is taken as an input.
This module has not been executed in Lean in the return environment.
-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U3
open C079U2

open Classical in
attribute [local instance] propDecidable

variable {G : PartiteShape} {p s : ℕ}

/-- A concrete inhabitant, including zero-radius and zero-defect cases. -/
def nullReconstructionCode (p radius defect : ℕ) :
    ReconstructionCode (p + 1) radius defect :=
  (⟨List.replicate radius
      (((0 : Fin (p + 1)), false), ((0 : Fin (p + 1)), false)), by simp⟩,
    fun _ => (0, 0))

def nullReconstructionFamily
    (family : G.VertexDisjointRightToLeftPaths s) (d : Fin G.roles → ℕ) :
    ReconstructionFamily (p + 1) family d :=
  fun y => nullReconstructionCode p
    (2 * componentDefect family d (G.c079OffBackboneComponent family y.1 y.2))
    (d y.1)

/-- Changing reconstruction does not change validity: this follows from
its actual definition, rather than an independence assumption. -/
theorem validRecord_reconstruction_iff
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : Backbone family → ReplicaPartition (p + 1))
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d))
    (seed : G.C079CutComponent family.backboneRoles → C079MatchingPartition (p + 1))
    (R R' : ReconstructionFamily (p + 1) family d) :
    ValidRecord (Record.mk B forward seed R) ↔
      ValidRecord (Record.mk B forward seed R') := by
  rfl

/-- The universal quantifier in SeedFiber is equivalent to validity at an
explicit reconstruction inhabitant, even when all word budgets vanish. -/
theorem seedFiber_predicate_iff
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d))
    (seed : G.C079CutComponent family.backboneRoles → C079MatchingPartition (p + 1)) :
    (∀ R : ReconstructionFamily (p + 1) family d,
      ValidRecord (Record.mk B.1 forward seed R)) ↔
    ValidRecord (Record.mk B.1 forward seed (nullReconstructionFamily family d)) := by
  constructor
  · intro h
    exact h _
  · intro h R
    exact (validRecord_reconstruction_iff B.1 forward seed
      (nullReconstructionFamily family d) R).mp h

def seedRecord
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) : Record p family d :=
  Record.mk B.1 forward seed.1 (nullReconstructionFamily family d)

theorem seedRecord_valid
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) : ValidRecord (seedRecord seed) :=
  seed.2 (nullReconstructionFamily family d)

theorem seedRecord_has_actual_state
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) :
    ∃ T : ReplicaState G p, T.partition = normalizedRecord (seedRecord seed) :=
  (seedRecord_valid seed).1

theorem seed_pinned_left
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) (c : G.C079CutComponent family.backboneRoles)
    (h : ∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.leftBoundary) :
    seed.1 c = (leftPerfectMatching p).toC079MatchingPartition :=
  (seedRecord_valid seed).2.1 c h

theorem seed_pinned_right
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) (c : G.C079CutComponent family.backboneRoles)
    (h : ∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.rightBoundary) :
    seed.1 c = (rightPerfectMatching (p + 1)).toC079MatchingPartition :=
  (seedRecord_valid seed).2.2 c h

abbrev FreeComponent (family : G.VertexDisjointRightToLeftPaths s) :=
  {c : G.C079CutComponent family.backboneRoles // c.IsBoundaryFree}

/-- Only the genuine boundary-free component coordinates need to be counted. -/
def freeSeedRestriction
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) :
    FreeComponent family → C079MatchingPartition (p + 1) :=
  fun c => seed.1 c.1

theorem freeSeedRestriction_injective
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) :
    Function.Injective (freeSeedRestriction (B := B) (forward := forward)) := by
  intro seed seed' h
  apply Subtype.ext
  funext c
  by_cases hL : ∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.leftBoundary
  · exact (seed_pinned_left seed c hL).trans (seed_pinned_left seed' c hL).symm
  by_cases hR : ∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.rightBoundary
  · exact (seed_pinned_right seed c hR).trans (seed_pinned_right seed' c hR).symm
  have hFree : c.IsBoundaryFree := by
    intro v hv
    exact ⟨fun h => hL ⟨v, hv, h⟩, fun h => hR ⟨v, hv, h⟩⟩
  exact congrFun h ⟨c, hFree⟩

/-- The repaired backbone is fixed by B and forward, not by the seed. -/
def repairedAt
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d))
    (x : Fin G.roles) : ReplicaPartition (p + 1) :=
  decodeForward (originalPrefix B.1) forward x

/-- Actual incident edge coordinates determine the backbone neighbors. -/
def backboneNeighbors
    (family : G.VertexDisjointRightToLeftPaths s)
    (c : G.C079CutComponent family.backboneRoles) : Finset (Fin G.roles) :=
  family.backboneRoles.filter fun x =>
    ∃ y ∈ G.c079ComponentRoles family.backboneRoles c,
      ∃ e : Fin G.edges, G.EdgeIncident e x ∧ G.EdgeIncident e y

/-- Meet of the repaired partitions at the ACTUAL neighbors. -/
def neighborMeet
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d))
    (c : G.C079CutComponent family.backboneRoles) : ReplicaPartition (p + 1) :=
  (backboneNeighbors family c).inf (repairedAt B forward)

/-- The boundary-core hypothesis is used precisely to make the meet's
neighbor index nonempty on free components. -/
theorem backboneNeighbors_nonempty
    (hCore : G.IsBoundaryCore)
    (family : G.VertexDisjointRightToLeftPaths s) (c : FreeComponent family) :
    (backboneNeighbors family c.1).Nonempty := by
  obtain ⟨y, hy, x, hx, e, hey, hex⟩ :=
    G.c079_boundaryFree_component_attached_of_boundaryCore
      hCore family.backboneRoles c.1 c.2
  refine ⟨x, ?_⟩
  exact Finset.mem_filter.mpr ⟨hx, y, hy, e, hex, hey⟩

theorem normalizedRecord_backbone
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) (x : Fin G.roles) (hx : x ∈ family.backboneRoles) :
    normalizedRecord (seedRecord seed) x = repairedAt B forward x := by
  simp only [normalizedRecord, dif_pos hx, seedRecord, repairedAt]

/-- Off-backbone matching partitions have exactly p+1 blocks. -/
theorem normalizedRecord_off_blockCount
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    {B : PathFiber p family d}
    {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}
    (seed : SeedFiber B forward) (x : Fin G.roles) (hx : x ∉ family.backboneRoles) :
    partitionBlockCount (normalizedRecord (seedRecord seed) x) = p + 1 := by
  simp only [normalizedRecord, dif_neg hx, seedRecord]
  exact C079MatchingPartition.blockCount_eq _

#print axioms seedFiber_predicate_iff
#print axioms seedRecord_has_actual_state
#print axioms freeSeedRestriction_injective
#print axioms backboneNeighbors_nonempty
#print axioms normalizedRecord_off_blockCount
end GraphMatrixReplica.C079U3
