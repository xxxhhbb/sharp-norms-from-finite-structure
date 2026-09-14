import GraphMatrix.StateBoundaryPathDefect
import GraphMatrix.CoveredRoleBlockBound

/-! # The no-detached-component scope of the C079 count

`RoleCovered` only excludes isolated middle roles.  The theorem applies
to a boundary core: every role belongs to a graph component meeting at least
one boundary.  This module records that stronger, graph-only condition by an
explicit finite edge walk, and proves its elementary consequences.  No
counting assertion is inferred from it.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A graph-only edge walk from a role to either external boundary.  The walk
may repeat vertices, which is enough to express membership in a component
meeting a boundary. -/
inductive PartiteShape.EdgeWalkToBoundary (G : PartiteShape) :
    Fin G.roles → Type
  | finishLeft (v : Fin G.roles) (h : v ∈ G.leftBoundary) :
      G.EdgeWalkToBoundary v
  | finishRight (v : Fin G.roles) (h : v ∈ G.rightBoundary) :
      G.EdgeWalkToBoundary v
  | step {v : Fin G.roles} (e : Fin G.edges) (w : Fin G.roles)
      (hStart : G.EdgeIncident e v) (hEnd : G.EdgeIncident e w)
      (tail : G.EdgeWalkToBoundary w) : G.EdgeWalkToBoundary v

/-- Every role reaches one of the external boundaries.  This is the local
form of the paper's exclusion of genuinely detached components. -/
def PartiteShape.IsBoundaryCore (G : PartiteShape) : Prop :=
  ∀ v : Fin G.roles, Nonempty (G.EdgeWalkToBoundary v)

/-- Every role in a boundary core is retained by the replica-state block
bound.  The converse is not assumed: an edge-bearing detached component has
covered roles but is not a boundary core. -/
theorem PartiteShape.roleCovered_of_isBoundaryCore
    (G : PartiteShape) (hCore : G.IsBoundaryCore)
    (v : Fin G.roles) : G.RoleCovered v := by
  obtain ⟨walk⟩ := hCore v
  cases walk with
  | finishLeft v h => exact Or.inr (Or.inl h)
  | finishRight v h => exact Or.inr (Or.inr h)
  | step e w hStart hEnd tail => exact Or.inl ⟨e, hStart⟩

/-- A set of roles that contains every other endpoint of an incident edge
whenever it contains one endpoint.  A connected component is edge-closed. -/
def PartiteShape.EdgeClosed (G : PartiteShape)
    (C : Finset (Fin G.roles)) : Prop :=
  ∀ v ∈ C, ∀ e : Fin G.edges, ∀ w : Fin G.roles,
    G.EdgeIncident e v → G.EdgeIncident e w → w ∈ C

/-- An edge walk starting inside an edge-closed set ends at a boundary role
inside that set. -/
theorem PartiteShape.EdgeWalkToBoundary.boundary_mem_of_edgeClosed
    {G : PartiteShape} {C : Finset (Fin G.roles)}
    (hClosed : G.EdgeClosed C)
    {v : Fin G.roles} (hMem : v ∈ C)
    (walk : G.EdgeWalkToBoundary v) :
    ∃ b : Fin G.roles,
      b ∈ C ∧ (b ∈ G.leftBoundary ∨ b ∈ G.rightBoundary) := by
  induction walk with
  | finishLeft v h => exact ⟨v, hMem, Or.inl h⟩
  | finishRight v h => exact ⟨v, hMem, Or.inr h⟩
  | @step v e w hStart hEnd tail ih =>
      exact ih (hClosed v hMem e w hStart hEnd)

/-- The no-detached-component consequence actually used by the free-seed
argument: a nonempty graph component cannot be boundary-free. -/
theorem PartiteShape.edgeClosed_nonempty_meets_boundary
    (G : PartiteShape) (hCore : G.IsBoundaryCore)
    (C : Finset (Fin G.roles)) (hClosed : G.EdgeClosed C)
    (hNonempty : C.Nonempty) :
    ∃ b : Fin G.roles,
      b ∈ C ∧ (b ∈ G.leftBoundary ∨ b ∈ G.rightBoundary) := by
  obtain ⟨v, hv⟩ := hNonempty
  obtain ⟨walk⟩ := hCore v
  exact walk.boundary_mem_of_edgeClosed hClosed hv


end GraphMatrixReplica
