import GraphMatrix.Model.ColorAutomorphismCore

/-! # Finite parity-to-automorphism step in the color-lower argument

This module handles only the combinatorial implication once an auxiliary
Fourier extraction has supplied odd occurrence of every target edge color.
It does not construct that extraction or prove a matrix norm lower bound.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Data obtained from a surviving edge-color word. The `odd_edge_fiber`
field is the exact Walsh parity condition; it is not asserted for every
role-color map. -/
structure PaperShape.R16OddEdgeColorMap (G : PaperShape) where
  role : Fin G.roles → Fin G.roles
  edgeColor : Fin G.edges → Fin G.edges
  odd_edge_fiber : ∀ target : Fin G.edges,
    Odd ((Finset.univ.filter fun e : Fin G.edges => edgeColor e = target).card)
  endpoints : ∀ e : Fin G.edges,
    (role (G.source e) = G.source (edgeColor e) ∧
      role (G.target e) = G.target (edgeColor e)) ∨
    (role (G.source e) = G.target (edgeColor e) ∧
      role (G.target e) = G.source (edgeColor e))
  left_fixed : ∀ v ∈ G.leftBoundaryFinset, role v = v
  right_fixed : ∀ v ∈ G.rightBoundaryFinset, role v = v

/-- Every target edge color occurs in the extracted word. -/
theorem PaperShape.R16OddEdgeColorMap.edgeColor_surjective
    {G : PaperShape} (f : G.R16OddEdgeColorMap) :
    Function.Surjective f.edgeColor := by
  intro target
  obtain ⟨k, hk⟩ := f.odd_edge_fiber target
  have hpos : 0 <
      (Finset.univ.filter fun e : Fin G.edges => f.edgeColor e = target).card := by
    omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact ⟨e, (Finset.mem_filter.mp he).2⟩

/-- Equal source and target edge counts turn edge-color coverage into a
permutation, before any role-map bijectivity is assumed. -/
def PaperShape.R16OddEdgeColorMap.edgeEquiv
    {G : PaperShape} (f : G.R16OddEdgeColorMap) :
    Fin G.edges ≃ Fin G.edges :=
  Equiv.ofBijective f.edgeColor
    ⟨Finite.injective_iff_surjective.mpr f.edgeColor_surjective,
      f.edgeColor_surjective⟩

/-- The endpoint-pair condition supplies exactly the incidence-preimage
datum required by the existing no-isolated-middle surjectivity theorem. -/
def PaperShape.R16OddEdgeColorMap.toEdgeCoveringRoleMap
    {G : PaperShape} (f : G.R16OddEdgeColorMap) :
    G.R16EdgeCoveringRoleMap where
  role := f.role
  edge := f.edgeEquiv
  target_incidence_has_preimage := by
    intro e v hv
    change G.source (f.edgeEquiv e) = v ∨
      G.target (f.edgeEquiv e) = v at hv
    rcases f.endpoints e with h | h
    · rcases hv with hv | hv
      · exact ⟨G.source e, Or.inl rfl, h.1.trans hv⟩
      · exact ⟨G.target e, Or.inr rfl, h.2.trans hv⟩
    · rcases hv with hv | hv
      · exact ⟨G.target e, Or.inr rfl, h.2.trans hv⟩
      · exact ⟨G.source e, Or.inl rfl, h.1.trans hv⟩
  left_fixed := f.left_fixed
  right_fixed := f.right_fixed

/-- Thus an odd-surviving edge-color map is a role permutation when the
shape has no isolated middle roles. -/
def PaperShape.R16OddEdgeColorMap.roleEquiv
    {G : PaperShape} (f : G.R16OddEdgeColorMap)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    Fin G.roles ≃ Fin G.roles :=
  f.toEdgeCoveringRoleMap.roleEquiv hNoIsolated

/-- The finite boundary-fixing graph-automorphism data required to identify
every surviving Fourier monomial with a typed one. -/
structure PaperShape.R16BoundaryFixingAutomorphism (G : PaperShape) where
  role : Fin G.roles ≃ Fin G.roles
  edge : Fin G.edges ≃ Fin G.edges
  endpoints : ∀ e : Fin G.edges,
    (role (G.source e) = G.source (edge e) ∧
      role (G.target e) = G.target (edge e)) ∨
    (role (G.source e) = G.target (edge e) ∧
      role (G.target e) = G.source (edge e))
  left_fixed : ∀ v ∈ G.leftBoundaryFinset, role v = v
  right_fixed : ∀ v ∈ G.rightBoundaryFinset, role v = v

theorem PaperShape.R16BoundaryFixingAutomorphism.ext
    {G : PaperShape} {f g : G.R16BoundaryFixingAutomorphism}
    (hrole : f.role = g.role) (hedge : f.edge = g.edge) : f = g := by
  cases f with
  | mk fr fe fh fl frr =>
    cases g with
    | mk gr ge gh gl grr =>
      cases hrole
      cases hedge
      rfl

/-- The identity always belongs to the boundary-fixing automorphism set. -/
def PaperShape.R16BoundaryFixingAutomorphism.identity
    (G : PaperShape) : G.R16BoundaryFixingAutomorphism where
  role := Equiv.refl _
  edge := Equiv.refl _
  endpoints := by intro e; exact Or.inl ⟨rfl, rfl⟩
  left_fixed := by intro v _; rfl
  right_fixed := by intro v _; rfl

private def PaperShape.R16BoundaryFixingAutomorphism.code
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism) :
    (Fin G.roles ≃ Fin G.roles) × (Fin G.edges ≃ Fin G.edges) :=
  (f.role, f.edge)

private theorem PaperShape.R16BoundaryFixingAutomorphism.code_injective
    {G : PaperShape} :
    Function.Injective (PaperShape.R16BoundaryFixingAutomorphism.code (G := G)) := by
  intro f g h
  rcases f with ⟨fr, fe, fh, fl, fg⟩
  rcases g with ⟨gr, ge, gh, gl, gg⟩
  change (fr, fe) = (gr, ge) at h
  cases h
  rfl

instance PaperShape.R16BoundaryFixingAutomorphism.instFintype
    (G : PaperShape) : Fintype G.R16BoundaryFixingAutomorphism :=
  Fintype.ofInjective PaperShape.R16BoundaryFixingAutomorphism.code
    PaperShape.R16BoundaryFixingAutomorphism.code_injective

theorem PaperShape.R16BoundaryFixingAutomorphism.card_pos
    (G : PaperShape) :
    0 < Fintype.card G.R16BoundaryFixingAutomorphism := by
  exact Fintype.card_pos_iff.mpr
    ⟨PaperShape.R16BoundaryFixingAutomorphism.identity G⟩

/-- Every actual automorphism satisfies the parity condition: each target
edge color has exactly one preimage. This is the reverse direction of the
combinatorial extraction step. -/
def PaperShape.R16BoundaryFixingAutomorphism.toOddEdgeColorMap
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism) :
    G.R16OddEdgeColorMap where
  role := f.role
  edgeColor := f.edge
  odd_edge_fiber := by
    intro target
    have hfiber :
        (Finset.univ.filter fun e : Fin G.edges => f.edge e = target) =
          {f.edge.symm target} := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro he
        apply f.edge.injective
        simpa using he
      · intro he
        subst e
        exact f.edge.apply_symm_apply target
    rw [hfiber]
    simp
  endpoints := f.endpoints
  left_fixed := f.left_fixed
  right_fixed := f.right_fixed

/-- Parity on every target edge color, with endpoint and boundary
compatibility, yields an actual graph automorphism. -/
def PaperShape.R16OddEdgeColorMap.toAutomorphism
    {G : PaperShape} (f : G.R16OddEdgeColorMap)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    G.R16BoundaryFixingAutomorphism where
  role := f.roleEquiv hNoIsolated
  edge := f.edgeEquiv
  endpoints := f.endpoints
  left_fixed := f.left_fixed
  right_fixed := f.right_fixed

theorem PaperShape.R16OddEdgeColorMap.toAutomorphism_toOddEdgeColorMap
    {G : PaperShape} (f : G.R16OddEdgeColorMap)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    (f.toAutomorphism hNoIsolated).toOddEdgeColorMap = f := by
  cases f
  rfl

theorem PaperShape.R16BoundaryFixingAutomorphism.toOddEdgeColorMap_toAutomorphism
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    (f.toOddEdgeColorMap.toAutomorphism hNoIsolated) = f := by
  apply PaperShape.R16BoundaryFixingAutomorphism.ext
  · ext v
    rfl
  · ext e
    rfl

/-- For shapes with no isolated middle role, parity-compatible color maps
are counted exactly by boundary-fixing graph automorphisms. This is purely
combinatorial; the Fourier and matrix-coefficient identifications remain
separate obligations. -/
def PaperShape.R16OddEdgeColorMap.equivAutomorphism
    (G : PaperShape) (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    G.R16OddEdgeColorMap ≃ G.R16BoundaryFixingAutomorphism where
  toFun f := f.toAutomorphism hNoIsolated
  invFun f := f.toOddEdgeColorMap
  left_inv f := f.toAutomorphism_toOddEdgeColorMap hNoIsolated
  right_inv f := f.toOddEdgeColorMap_toAutomorphism hNoIsolated

theorem PaperShape.R16BoundaryFixingAutomorphism.left_fixed_symm
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    (v : Fin G.roles) (hv : v ∈ G.leftBoundaryFinset) :
    f.role.symm v = v := by
  apply f.role.injective
  simpa using (f.left_fixed v hv).symm

theorem PaperShape.R16BoundaryFixingAutomorphism.right_fixed_symm
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    (v : Fin G.roles) (hv : v ∈ G.rightBoundaryFinset) :
    f.role.symm v = v := by
  apply f.role.injective
  simpa using (f.right_fixed v hv).symm


end GraphMatrixReplica
