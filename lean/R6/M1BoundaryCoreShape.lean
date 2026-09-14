import R6.M1GraphRawFactorBridge
import Mathlib.Data.Finset.Sort

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

def rootCoreRoles (G : PaperShape) : Finset (Fin G.roles) :=
  Finset.univ.filter fun v => Nonempty (G.toPartiteShape.EdgeWalkToBoundary v)

@[simp] theorem root_mem_coreRoles (G : PaperShape) (v : Fin G.roles) :
    v ∈ rootCoreRoles G ↔ Nonempty (G.toPartiteShape.EdgeWalkToBoundary v) := by
  simp [rootCoreRoles]

theorem root_coreRoles_eq_rawCoreRoles (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    rootCoreRoles G = (rootGraphRawFactorShape G dimension).coreRoles := by
  ext v
  simp [root_raw_core_iff_boundaryWalk]

theorem root_coreRoles_edgeClosed (G : PaperShape) : G.toPartiteShape.EdgeClosed (rootCoreRoles G) := by
  intro v hv e w hve hwe
  obtain ⟨walk⟩ := (root_mem_coreRoles G v).mp hv
  exact (root_mem_coreRoles G w).mpr ⟨.step e v hwe hve walk⟩

theorem root_left_mem_coreRoles (G : PaperShape) (i : Fin G.leftSize) :
    G.left i ∈ rootCoreRoles G := by
  apply (root_mem_coreRoles G _).mpr
  exact ⟨PartiteShape.EdgeWalkToBoundary.finishLeft (G := G.toPartiteShape) (G.left i)
    ((G.mem_leftBoundaryFinset_iff _).mpr ⟨i, rfl⟩)⟩

theorem root_right_mem_coreRoles (G : PaperShape) (i : Fin G.rightSize) :
    G.right i ∈ rootCoreRoles G := by
  apply (root_mem_coreRoles G _).mpr
  exact ⟨PartiteShape.EdgeWalkToBoundary.finishRight (G := G.toPartiteShape) (G.right i)
    ((G.mem_rightBoundaryFinset_iff _).mpr ⟨i, rfl⟩)⟩

def rootCoreEdges (G : PaperShape) : Finset (Fin G.edges) :=
  Finset.univ.filter fun e => G.source e ∈ rootCoreRoles G

theorem root_coreEdge_source (G : PaperShape) (e : rootCoreEdges G) :
    G.source e.1 ∈ rootCoreRoles G := (Finset.mem_filter.mp e.2).2

theorem root_coreEdge_target (G : PaperShape) (e : rootCoreEdges G) :
    G.target e.1 ∈ rootCoreRoles G :=
  root_coreRoles_edgeClosed G _ (root_coreEdge_source G e) e.1 _ (Or.inl rfl) (Or.inr rfl)

theorem root_incident_coreEdge (G : PaperShape) (e : Fin G.edges) {v : Fin G.roles}
    (hv : v ∈ rootCoreRoles G) (he : G.toPartiteShape.EdgeIncident e v) : e ∈ rootCoreEdges G := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, root_coreRoles_edgeClosed G v hv e _ he (Or.inl rfl)⟩

def rootCoreRoleIso (G : PaperShape) : Fin (rootCoreRoles G).card ≃o rootCoreRoles G :=
  (rootCoreRoles G).orderIsoOfFin rfl

def rootCoreEdgeIso (G : PaperShape) : Fin (rootCoreEdges G).card ≃o rootCoreEdges G :=
  (rootCoreEdges G).orderIsoOfFin rfl

/-- The concrete original simple graph induced by all boundary-reaching components. -/
def rootBoundaryCoreShape (G : PaperShape) : PaperShape where
  roles := (rootCoreRoles G).card
  edges := (rootCoreEdges G).card
  source e := (rootCoreRoleIso G).symm ⟨G.source ((rootCoreEdgeIso G) e).1,
    root_coreEdge_source G ((rootCoreEdgeIso G) e)⟩
  target e := (rootCoreRoleIso G).symm ⟨G.target ((rootCoreEdgeIso G) e).1,
    root_coreEdge_target G ((rootCoreEdgeIso G) e)⟩
  edge_order e := (rootCoreRoleIso G).symm.strictMono (G.edge_order ((rootCoreEdgeIso G) e).1)
  edge_injective := by
    intro e f h
    apply (rootCoreEdgeIso G).injective
    apply Subtype.ext
    apply G.edge_injective
    apply Prod.ext
    · have hh := congrArg (fun z => ((rootCoreRoleIso G) z.1).1) h
      simpa using hh
    · have hh := congrArg (fun z => ((rootCoreRoleIso G) z.2).1) h
      simpa using hh
  leftSize := G.leftSize
  rightSize := G.rightSize
  left := ⟨fun i => (rootCoreRoleIso G).symm ⟨G.left i, root_left_mem_coreRoles G i⟩, by
    intro i j h
    apply G.left.injective
    have hh := congrArg (fun z => ((rootCoreRoleIso G) z).1) h
    simpa using hh⟩
  right := ⟨fun i => (rootCoreRoleIso G).symm ⟨G.right i, root_right_mem_coreRoles G i⟩, by
    intro i j h
    apply G.right.injective
    have hh := congrArg (fun z => ((rootCoreRoleIso G) z).1) h
    simpa using hh⟩

def rootCoreInclude (G : PaperShape) : Fin (rootBoundaryCoreShape G).roles ↪ Fin G.roles where
  toFun v := ((rootCoreRoleIso G) v).1
  inj' := fun _ _ h => (rootCoreRoleIso G).injective (Subtype.ext h)

def rootCoreIndex (G : PaperShape) (v : Fin G.roles) (hv : v ∈ rootCoreRoles G) :
    Fin (rootBoundaryCoreShape G).roles := (rootCoreRoleIso G).symm ⟨v, hv⟩

@[simp] theorem root_coreInclude_index (G : PaperShape) (v : Fin G.roles) (hv : v ∈ rootCoreRoles G) :
    rootCoreInclude G (rootCoreIndex G v hv) = v := by
  simp [rootCoreInclude, rootCoreIndex]

theorem root_core_left_iff (G : PaperShape) (v : Fin (rootBoundaryCoreShape G).roles) :
    v ∈ (rootBoundaryCoreShape G).toPartiteShape.leftBoundary ↔
      rootCoreInclude G v ∈ G.toPartiteShape.leftBoundary := by
  change v ∈ (rootBoundaryCoreShape G).leftBoundaryFinset ↔ rootCoreInclude G v ∈ G.leftBoundaryFinset
  rw [(rootBoundaryCoreShape G).mem_leftBoundaryFinset_iff v,
    G.mem_leftBoundaryFinset_iff (rootCoreInclude G v)]
  change (∃ i, (rootCoreRoleIso G).symm ⟨G.left i, _⟩ = v) ↔
    ∃ i, G.left i = ((rootCoreRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem root_core_right_iff (G : PaperShape) (v : Fin (rootBoundaryCoreShape G).roles) :
    v ∈ (rootBoundaryCoreShape G).toPartiteShape.rightBoundary ↔
      rootCoreInclude G v ∈ G.toPartiteShape.rightBoundary := by
  change v ∈ (rootBoundaryCoreShape G).rightBoundaryFinset ↔ rootCoreInclude G v ∈ G.rightBoundaryFinset
  rw [(rootBoundaryCoreShape G).mem_rightBoundaryFinset_iff v,
    G.mem_rightBoundaryFinset_iff (rootCoreInclude G v)]
  change (∃ i, (rootCoreRoleIso G).symm ⟨G.right i, _⟩ = v) ↔
    ∃ i, G.right i = ((rootCoreRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem root_core_incident_iff (G : PaperShape) (e : Fin (rootBoundaryCoreShape G).edges)
    (v : Fin (rootBoundaryCoreShape G).roles) :
    (rootBoundaryCoreShape G).toPartiteShape.EdgeIncident e v ↔
      G.toPartiteShape.EdgeIncident ((rootCoreEdgeIso G) e).1 (rootCoreInclude G v) := by
  change ((rootCoreRoleIso G).symm ⟨G.source ((rootCoreEdgeIso G) e).1, _⟩ = v ∨
    (rootCoreRoleIso G).symm ⟨G.target ((rootCoreEdgeIso G) e).1, _⟩ = v) ↔
      G.source ((rootCoreEdgeIso G) e).1 = ((rootCoreRoleIso G) v).1 ∨
      G.target ((rootCoreEdgeIso G) e).1 = ((rootCoreRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

def rootCoreReduceWalk (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (walk : G.toPartiteShape.EdgeWalkToBoundary v) : ∀ hv : v ∈ rootCoreRoles G,
      (rootBoundaryCoreShape G).toPartiteShape.EdgeWalkToBoundary (rootCoreIndex G v hv) := by
  induction walk with
  | finishLeft v hl =>
    intro hv
    exact .finishLeft _ ((root_core_left_iff G _).mpr (by simpa using hl))
  | finishRight v hr =>
    intro hv
    exact .finishRight _ ((root_core_right_iff G _).mpr (by simpa using hr))
  | @step v e w hStart hEnd tail ih =>
    intro hv
    have he := root_incident_coreEdge G e hv hStart
    have hw := root_coreRoles_edgeClosed G v hv e w hStart hEnd
    let en := (rootCoreEdgeIso G).symm ⟨e, he⟩
    apply PartiteShape.EdgeWalkToBoundary.step en (rootCoreIndex G w hw)
    · apply (root_core_incident_iff G en _).mpr
      simpa [en] using hStart
    · apply (root_core_incident_iff G en _).mpr
      simpa [en] using hEnd
    · exact ih hw

theorem root_boundaryCoreShape_isBoundaryCore (G : PaperShape) :
    (rootBoundaryCoreShape G).toPartiteShape.IsBoundaryCore := by
  intro v
  obtain ⟨walk⟩ := (root_mem_coreRoles G _).mp ((rootCoreRoleIso G) v).2
  have h := rootCoreReduceWalk G walk ((rootCoreRoleIso G) v).2
  simpa [rootCoreIndex] using (Nonempty.intro h)

#print axioms rootBoundaryCoreShape
#print axioms root_coreRoles_eq_rawCoreRoles
#print axioms rootCoreReduceWalk
#print axioms root_boundaryCoreShape_isBoundaryCore
end GraphMatrixReplica
