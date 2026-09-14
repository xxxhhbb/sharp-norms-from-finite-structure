import GraphMatrix.Probability.Components.ActiveComponentCoefficients
import GraphMatrix.JointEdgeRademacherExpectation

/-!
# primitive crossing-array addresses

This file records the real typed crossing coordinates used to build the
`eta_z(j)` vectors.  In particular, a primitive address keeps

* the shape-edge identity,
* the source/target orientation,
* the role-dependent endpoint label types.

-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica

/-- Full original typed edge-array sample. -/
abbrev P1TypedSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ) :=
  JointEdgeSignSample (G := P.toPartiteShape) dimension

/-- Restrict a full typed sample to the internal arrays of one component. -/
def p1RestrictInternalSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (eps : P1TypedSample P dimension) :
    P1InternalSample P dimension cut c :=
  fun e ij => eps e.1 ij

/-- A typed separator labeling. -/
abbrev P1CutRole (P : PaperShape) (cut : Finset (Fin P.roles)) :=
  {x : Fin P.roles // x ∈ cut}

abbrev P1CutLabel
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) :=
  (x : P1CutRole P cut) → Fin (dimension x.1)

/-- One actual crossing edge from role `z` to the cut.  The disjunction stores
which endpoint is the component endpoint and hence preserves orientation. -/
structure P1CrossingEdgeAt
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (z : Fin P.roles) where
  edge : Fin P.edges
  cutRole : Fin P.roles
  cutRole_mem : cutRole ∈ cut
  oriented :
    (P.source edge = z ∧ P.target edge = cutRole) ∨
    (P.source edge = cutRole ∧ P.target edge = z)

noncomputable instance (P : PaperShape) (cut : Finset (Fin P.roles))
    (z : Fin P.roles) : Fintype (P1CrossingEdgeAt P cut z) := by
  classical
  apply Fintype.ofInjective (fun a => (a.edge, a.cutRole))
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- Membership in `B` really supplies at least one primitive crossing edge. -/
theorem p1CrossingEdgeAt_nonempty_of_mem_boundary
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z : Fin P.roles) (hzB : z ∈ p1BoundaryRoles P cut c) :
    Nonempty (P1CrossingEdgeAt P cut z) := by
  classical
  have hzK : z ∈ p1ComponentRoles P cut c :=
    p1BoundaryRoles_subset_component P cut c hzB
  obtain ⟨hzCut, _hzComp⟩ :=
    (P.toPartiteShape.mem_c079ComponentRoles_iff cut c z).1 hzK
  obtain ⟨_hzK', x, hxCut, e, hze, hxe⟩ :=
    (mem_p1BoundaryRoles_iff P cut c z).1 hzB
  have hzx : z ≠ x := by
    intro h
    exact hzCut (h ▸ hxCut)
  rcases hze with hsz | htz <;> rcases hxe with hsx | htx
  · exfalso
    apply hzx
    exact hsz.symm.trans hsx
  · exact ⟨⟨e, x, hxCut, Or.inl ⟨hsz, htx⟩⟩⟩
  · exact ⟨⟨e, x, hxCut, Or.inr ⟨hsx, htz⟩⟩⟩
  · exfalso
    apply hzx
    exact htz.symm.trans htx

/-- The exact source/target coordinate in an edge array used by a crossing
edge at component label `j` and separator labeling `tau`. -/
def p1CrossingCoordinate
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (z : Fin P.roles)
    (a : P1CrossingEdgeAt P cut z)
    (j : Fin (dimension z))
    (tau : P1CutLabel P dimension cut) :
    EdgeSignCoordinate (G := P.toPartiteShape) dimension a.edge := by
  classical
  by_cases h : P.source a.edge = z ∧ P.target a.edge = a.cutRole
  · exact
      (Fin.cast (congrArg dimension h.1.symm) j,
       Fin.cast (congrArg dimension h.2.symm)
         (tau ⟨a.cutRole, a.cutRole_mem⟩))
  · have h := a.oriented.resolve_left h
    exact
      (Fin.cast (congrArg dimension h.1.symm)
         (tau ⟨a.cutRole, a.cutRole_mem⟩),
       Fin.cast (congrArg dimension h.2.symm) j)

/-- Product of all primitive crossing signs incident to `z`, evaluated at
component label `j` and a fixed separator labeling. -/
def p1EtaSignZ
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (z : Fin P.roles)
    (eps : P1TypedSample P dimension)
    (tau : P1CutLabel P dimension cut)
    (j : Fin (dimension z)) : ℤ :=
  ∏ a : P1CrossingEdgeAt P cut z,
    rademacherSign
      (eps a.edge (p1CrossingCoordinate P dimension cut z a j tau))

/-- Primitive address with its edge id exposed explicitly. -/
structure P1CrossingPrimitiveAddress
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (z : Fin P.roles) where
  crossing : P1CrossingEdgeAt P cut z
  coordinate : EdgeSignCoordinate (G := P.toPartiteShape)
    dimension crossing.edge

/-- Address actually used by one factor in `p1EtaSignZ`. -/
def p1CrossingPrimitiveAddressOf
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (z : Fin P.roles)
    (a : P1CrossingEdgeAt P cut z)
    (j : Fin (dimension z))
    (tau : P1CutLabel P dimension cut) :
    P1CrossingPrimitiveAddress P dimension cut z :=
  ⟨a, p1CrossingCoordinate P dimension cut z a j tau⟩

end GraphMatrixReplica
