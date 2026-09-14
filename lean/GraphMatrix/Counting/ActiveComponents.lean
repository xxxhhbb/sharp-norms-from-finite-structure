import GraphMatrix.Counting.BoundaryCoreScope
import GraphMatrix.Counting.PartitionIntervalMonotonicity
import GraphMatrix.FiniteMengerCertificate

/-! # Genuine active components of a C079 separator layer

The graph `G - cut` is the induced simple graph on roles outside `cut`.
Its `ConnectedComponent` quotient, not an arbitrary edge-closed set, is used
for the active-component count. An active component meets neither boundary
and has an edge to `cut`. The maximum `aStar` ranges over the actual minimum
right-left separators already defined for `PartiteShape`.

The no-detached hypothesis is `G.IsBoundaryCore`: every role has an edge walk
to an external boundary. It is strictly stronger than `RoleCovered`.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Undirected adjacency obtained from a shape edge with two distinct
endpoints. Self-loop edges do not affect connected components. -/
def PartiteShape.c079RoleGraph (G : PartiteShape) :
    SimpleGraph (Fin G.roles) where
  Adj u v := u ≠ v ∧
    ∃ e : Fin G.edges, G.EdgeIncident e u ∧ G.EdgeIncident e v
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by
      obtain ⟨e, hu, hv⟩ := h.2
      exact ⟨e, hv, hu⟩⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

/-- The actual induced graph after deleting the roles in `cut`. -/
def PartiteShape.c079CutGraph (G : PartiteShape)
    (cut : Finset (Fin G.roles)) :
    SimpleGraph {v : Fin G.roles // v ∉ cut} :=
  G.c079RoleGraph.induce {v | v ∉ cut}

/-- Connected components of the induced graph `G - cut`. -/
abbrev PartiteShape.C079CutComponent (G : PartiteShape)
    (cut : Finset (Fin G.roles)) :=
  (G.c079CutGraph cut).ConnectedComponent

/-- Underlying roles of one genuine component of `G - cut`. -/
def PartiteShape.c079ComponentRoles (G : PartiteShape)
    (cut : Finset (Fin G.roles)) (c : G.C079CutComponent cut) :
    Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ hv : v ∉ cut,
      (G.c079CutGraph cut).connectedComponentMk ⟨v, hv⟩ = c

theorem PartiteShape.mem_c079ComponentRoles_iff
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (c : G.C079CutComponent cut) (v : Fin G.roles) :
    v ∈ G.c079ComponentRoles cut c ↔
      ∃ hv : v ∉ cut,
        (G.c079CutGraph cut).connectedComponentMk ⟨v, hv⟩ = c := by
  classical
  simp [c079ComponentRoles]

/-- Every connected component contains at least one surviving role. -/
theorem PartiteShape.c079ComponentRoles_nonempty
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (c : G.C079CutComponent cut) :
    (G.c079ComponentRoles cut c).Nonempty := by
  obtain ⟨v, hv⟩ := c.nonempty_supp
  refine ⟨v.1, ?_⟩
  exact (G.mem_c079ComponentRoles_iff cut c v.1).2
    ⟨v.2, hv⟩

/-- A surviving endpoint of a shape edge stays in the same component. -/
theorem PartiteShape.c079ComponentRoles_edge_closed_outside_cut
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (c : G.C079CutComponent cut)
    {v w : Fin G.roles} (hv : v ∈ G.c079ComponentRoles cut c)
    (e : Fin G.edges) (hve : G.EdgeIncident e v)
    (hwe : G.EdgeIncident e w) (hw : w ∉ cut) :
    w ∈ G.c079ComponentRoles cut c := by
  obtain ⟨hvCut, hvComp⟩ :=
    (G.mem_c079ComponentRoles_iff cut c v).1 hv
  by_cases hEq : v = w
  · simpa [hEq] using hv
  have hAdj : (G.c079CutGraph cut).Adj
      ⟨v, hvCut⟩ ⟨w, hw⟩ := by
    change (G.c079RoleGraph).Adj v w
    exact ⟨hEq, ⟨e, hve, hwe⟩⟩
  have hSame := SimpleGraph.ConnectedComponent.sound hAdj.reachable
  exact (G.mem_c079ComponentRoles_iff cut c w).2
    ⟨hw, hSame.symm.trans hvComp⟩

/-- A component is attached when some of its vertices has an edge into
the deleted cut. -/
def PartiteShape.C079CutComponent.IsAttached
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (c : G.C079CutComponent cut) : Prop :=
  ∃ v ∈ G.c079ComponentRoles cut c,
    ∃ x ∈ cut, ∃ e : Fin G.edges,
      G.EdgeIncident e v ∧ G.EdgeIncident e x

/-- Boundary-free means no surviving role in the component belongs to
either external boundary. -/
def PartiteShape.C079CutComponent.IsBoundaryFree
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (c : G.C079CutComponent cut) : Prop :=
  ∀ v ∈ G.c079ComponentRoles cut c,
    v ∉ G.leftBoundary ∧ v ∉ G.rightBoundary

/-- Exactly the active components counted by C079's `a(cut)`. -/
def PartiteShape.C079CutComponent.IsActive
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (c : G.C079CutComponent cut) : Prop :=
  c.IsBoundaryFree ∧ c.IsAttached

/-- The finite number `a(cut)` of boundary-free components of `G-cut`
attached to `cut`. -/
def PartiteShape.c079ActiveComponentCount (G : PartiteShape)
    (cut : Finset (Fin G.roles)) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : G.C079CutComponent cut => c.IsActive).card

/-- C079's `a_*`: maximum active-component count over all minimum
right-left separators. Existence of such separators was proved separately. -/
def PartiteShape.activeComponentMaximum (G : PartiteShape) : ℕ := by
  classical
  exact (Finset.univ.filter G.IsMinimumRightLeftSeparator).sup
    G.c079ActiveComponentCount

/-- A component count cannot exceed the number of surviving roles, hence
cannot exceed the shape size `r`. This is the crude nonminimum-layer charge
used in the paper. -/
theorem PartiteShape.c079ActiveComponentCount_le_roles
    (G : PartiteShape) (cut : Finset (Fin G.roles)) :
    G.c079ActiveComponentCount cut ≤ G.roles := by
  classical
  have hFilter : G.c079ActiveComponentCount cut ≤
      Fintype.card (G.C079CutComponent cut) := by
    unfold c079ActiveComponentCount
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hSurj : Function.Surjective
      (G.c079CutGraph cut).connectedComponentMk := by
    intro c
    obtain ⟨v, rfl⟩ := Quot.exists_rep c
    exact ⟨v, rfl⟩
  have hQuot : Fintype.card (G.C079CutComponent cut) ≤
      Fintype.card {v : Fin G.roles // v ∉ cut} :=
    Fintype.card_le_of_surjective _ hSurj
  have hSubtype : Fintype.card {v : Fin G.roles // v ∉ cut} ≤
      G.roles := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun v : {v : Fin G.roles // v ∉ cut} => v.1)
      Subtype.val_injective
  exact hFilter.trans (hQuot.trans hSubtype)

theorem PartiteShape.c079ActiveMaximum_le_roles
    (G : PartiteShape) : G.activeComponentMaximum ≤ G.roles := by
  classical
  unfold activeComponentMaximum
  exact Finset.sup_le fun cut _ => G.c079ActiveComponentCount_le_roles cut

/-- The maximum is attained by a genuine minimum separator, including when
one or both boundaries are empty. -/
theorem PartiteShape.exists_minimum_with_c079ActiveMaximum
    (G : PartiteShape) :
    ∃ cut : Finset (Fin G.roles),
      G.IsMinimumRightLeftSeparator cut ∧
        G.c079ActiveComponentCount cut = G.activeComponentMaximum := by
  classical
  let cuts : Finset (Finset (Fin G.roles)) :=
    Finset.univ.filter G.IsMinimumRightLeftSeparator
  have hNonempty : cuts.Nonempty := by
    obtain ⟨cut, hMinimum⟩ := G.exists_minimumRightLeftSeparator
    exact ⟨cut, by simp [cuts, hMinimum]⟩
  have hImage := Finset.sup_mem_of_nonempty
    (f := G.c079ActiveComponentCount) hNonempty
  obtain ⟨cut, hCut, hEq⟩ := hImage
  refine ⟨cut, ?_, ?_⟩
  · simpa [cuts] using hCut
  · change G.c079ActiveComponentCount cut =
      cuts.sup G.c079ActiveComponentCount
    exact hEq

/-- Each minimum separator's active count is bounded by the maximum. -/
theorem PartiteShape.c079ActiveComponentCount_le_maximum
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (hMinimum : G.IsMinimumRightLeftSeparator cut) :
    G.c079ActiveComponentCount cut ≤ G.activeComponentMaximum := by
  classical
  unfold activeComponentMaximum
  exact Finset.le_sup (by simp [hMinimum] :
    cut ∈ Finset.univ.filter G.IsMinimumRightLeftSeparator)

/-- The no-detached boundary-core hypothesis forces every boundary-free
component of `G-cut` to attach to `cut`. Unlike `RoleCovered`, the hypothesis
excludes edge-bearing components wholly detached from both boundaries. -/
theorem PartiteShape.c079_boundaryFree_component_attached_of_boundaryCore
    (G : PartiteShape) (hCore : G.IsBoundaryCore)
    (cut : Finset (Fin G.roles)) (c : G.C079CutComponent cut)
    (hFree : c.IsBoundaryFree) : c.IsAttached := by
  by_contra hNotAttached
  have hClosed : G.EdgeClosed (G.c079ComponentRoles cut c) := by
    intro v hv e w hve hwe
    by_cases hwCut : w ∈ cut
    · exact False.elim (hNotAttached ⟨v, hv, w, hwCut,
        e, hve, hwe⟩)
    · exact G.c079ComponentRoles_edge_closed_outside_cut
        cut c hv e hve hwe hwCut
  obtain ⟨b, hb, hBoundary⟩ :=
    G.edgeClosed_nonempty_meets_boundary hCore
      (G.c079ComponentRoles cut c) hClosed
      (G.c079ComponentRoles_nonempty cut c)
  exact (hBoundary.elim (hFree b hb).1 (hFree b hb).2)


end GraphMatrixReplica
