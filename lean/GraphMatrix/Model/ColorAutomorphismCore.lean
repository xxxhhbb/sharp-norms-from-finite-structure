import GraphMatrix.ToPartiteBridge

/-!
# Role-map surjectivity in the lower coloring transfer

The lower typed-to-global transfer extracts a Fourier coefficient. Its
surviving monomials induce an edge-bijective endomorphism of the shape. This
file formalizes the finite combinatorial argument that such a role map is
bijective when all isolated roles are fixed at the boundary and there are
no isolated middle roles. The Fourier extraction and norm inequality are
separate, unproved obligations here.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The exact part of an edge-bijective color endomorphism used to prove
surjectivity on roles. A target edge incident to `v` has a source edge and
one of its endpoint roles mapping to `v`. The lower Fourier extraction must
construct this datum; its existence is not assumed for arbitrary maps. -/
structure PaperShape.R16EdgeCoveringRoleMap (G : PaperShape) where
  role : Fin G.roles → Fin G.roles
  edge : Fin G.edges ≃ Fin G.edges
  target_incidence_has_preimage :
    ∀ e : Fin G.edges, ∀ v : Fin G.roles,
      G.toPartiteShape.EdgeIncident (edge e) v →
        ∃ w : Fin G.roles,
          G.toPartiteShape.EdgeIncident e w ∧ role w = v
  left_fixed : ∀ v ∈ G.leftBoundaryFinset, role v = v
  right_fixed : ∀ v ∈ G.rightBoundaryFinset, role v = v

/-- Every target role touching a target edge has a preimage role. -/
theorem PaperShape.R16EdgeCoveringRoleMap.incident_role_in_range
    {G : PaperShape} (f : G.R16EdgeCoveringRoleMap)
    (v : Fin G.roles)
    (hIncident : ∃ e : Fin G.edges,
      G.toPartiteShape.EdgeIncident e v) :
    v ∈ Set.range f.role := by
  obtain ⟨e, he⟩ := hIncident
  let e0 := f.edge.symm e
  have he0 : f.edge e0 = e := f.edge.apply_symm_apply e
  obtain ⟨w, _hwIncident, hwRole⟩ :=
    f.target_incidence_has_preimage e0 v (by simpa [he0] using he)
  exact ⟨w, hwRole⟩

/-- With no isolated middle role, the edge-covered map is surjective on
all roles. Boundary roles without edges are fixed, while every remaining
role is incident to an edge. -/
theorem PaperShape.R16EdgeCoveringRoleMap.role_surjective
    {G : PaperShape} (f : G.R16EdgeCoveringRoleMap)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    Function.Surjective f.role := by
  intro v
  by_cases hLeft : v ∈ G.leftBoundaryFinset
  · exact ⟨v, f.left_fixed v hLeft⟩
  by_cases hRight : v ∈ G.rightBoundaryFinset
  · exact ⟨v, f.right_fixed v hRight⟩
  have hIncident : ∃ e : Fin G.edges,
      G.toPartiteShape.EdgeIncident e v := by
    by_contra hNoIncident
    apply hNoIsolated v
    refine ⟨hLeft, hRight, ?_⟩
    intro e
    constructor
    · intro hSource
      apply hNoIncident
      exact ⟨e, Or.inl hSource⟩
    · intro hTarget
      apply hNoIncident
      exact ⟨e, Or.inr hTarget⟩
  exact f.incident_role_in_range v hIncident

/-- On a finite role set, the role map is therefore a permutation. -/
def PaperShape.R16EdgeCoveringRoleMap.roleEquiv
    {G : PaperShape} (f : G.R16EdgeCoveringRoleMap)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    Fin G.roles ≃ Fin G.roles :=
  Equiv.ofBijective f.role
    ⟨Finite.injective_iff_surjective.mpr
      (f.role_surjective hNoIsolated),
      f.role_surjective hNoIsolated⟩


end GraphMatrixReplica
