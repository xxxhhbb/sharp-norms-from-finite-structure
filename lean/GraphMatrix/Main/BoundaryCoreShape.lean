import GraphMatrix.Main.GraphRawFactorBridge
import Mathlib.Data.Finset.Sort

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

def mainCoreRoles (G : PaperShape) : Finset (Fin G.roles) :=
  Finset.univ.filter fun v => Nonempty (G.toPartiteShape.EdgeWalkToBoundary v)

@[simp] theorem main_mem_coreRoles (G : PaperShape) (v : Fin G.roles) :
    v ∈ mainCoreRoles G ↔ Nonempty (G.toPartiteShape.EdgeWalkToBoundary v) := by
  simp [mainCoreRoles]

theorem main_coreRoles_eq_rawCoreRoles (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    mainCoreRoles G = (mainGraphRawFactorShape G dimension).coreRoles := by
  ext v
  simp [main_raw_core_iff_boundaryWalk]

theorem main_coreRoles_edgeClosed (G : PaperShape) : G.toPartiteShape.EdgeClosed (mainCoreRoles G) := by
  intro v hv e w hve hwe
  obtain ⟨walk⟩ := (main_mem_coreRoles G v).mp hv
  exact (main_mem_coreRoles G w).mpr ⟨.step e v hwe hve walk⟩

theorem main_left_mem_coreRoles (G : PaperShape) (i : Fin G.leftSize) :
    G.left i ∈ mainCoreRoles G := by
  apply (main_mem_coreRoles G _).mpr
  exact ⟨PartiteShape.EdgeWalkToBoundary.finishLeft (G := G.toPartiteShape) (G.left i)
    ((G.mem_leftBoundaryFinset_iff _).mpr ⟨i, rfl⟩)⟩

theorem main_right_mem_coreRoles (G : PaperShape) (i : Fin G.rightSize) :
    G.right i ∈ mainCoreRoles G := by
  apply (main_mem_coreRoles G _).mpr
  exact ⟨PartiteShape.EdgeWalkToBoundary.finishRight (G := G.toPartiteShape) (G.right i)
    ((G.mem_rightBoundaryFinset_iff _).mpr ⟨i, rfl⟩)⟩

def mainCoreEdges (G : PaperShape) : Finset (Fin G.edges) :=
  Finset.univ.filter fun e => G.source e ∈ mainCoreRoles G

theorem main_coreEdge_source (G : PaperShape) (e : mainCoreEdges G) :
    G.source e.1 ∈ mainCoreRoles G := (Finset.mem_filter.mp e.2).2

theorem main_coreEdge_target (G : PaperShape) (e : mainCoreEdges G) :
    G.target e.1 ∈ mainCoreRoles G :=
  main_coreRoles_edgeClosed G _ (main_coreEdge_source G e) e.1 _ (Or.inl rfl) (Or.inr rfl)

theorem main_incident_coreEdge (G : PaperShape) (e : Fin G.edges) {v : Fin G.roles}
    (hv : v ∈ mainCoreRoles G) (he : G.toPartiteShape.EdgeIncident e v) : e ∈ mainCoreEdges G := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, main_coreRoles_edgeClosed G v hv e _ he (Or.inl rfl)⟩

def mainCoreRoleIso (G : PaperShape) : Fin (mainCoreRoles G).card ≃o mainCoreRoles G :=
  (mainCoreRoles G).orderIsoOfFin rfl

def mainCoreEdgeIso (G : PaperShape) : Fin (mainCoreEdges G).card ≃o mainCoreEdges G :=
  (mainCoreEdges G).orderIsoOfFin rfl

/-- The concrete original simple graph induced by all boundary-reaching components. -/
def mainBoundaryCoreShape (G : PaperShape) : PaperShape where
  roles := (mainCoreRoles G).card
  edges := (mainCoreEdges G).card
  source e := (mainCoreRoleIso G).symm ⟨G.source ((mainCoreEdgeIso G) e).1,
    main_coreEdge_source G ((mainCoreEdgeIso G) e)⟩
  target e := (mainCoreRoleIso G).symm ⟨G.target ((mainCoreEdgeIso G) e).1,
    main_coreEdge_target G ((mainCoreEdgeIso G) e)⟩
  edge_order e := (mainCoreRoleIso G).symm.strictMono (G.edge_order ((mainCoreEdgeIso G) e).1)
  edge_injective := by
    intro e f h
    apply (mainCoreEdgeIso G).injective
    apply Subtype.ext
    apply G.edge_injective
    apply Prod.ext
    · have hh := congrArg (fun z => ((mainCoreRoleIso G) z.1).1) h
      simpa using hh
    · have hh := congrArg (fun z => ((mainCoreRoleIso G) z.2).1) h
      simpa using hh
  leftSize := G.leftSize
  rightSize := G.rightSize
  left := ⟨fun i => (mainCoreRoleIso G).symm ⟨G.left i, main_left_mem_coreRoles G i⟩, by
    intro i j h
    apply G.left.injective
    have hh := congrArg (fun z => ((mainCoreRoleIso G) z).1) h
    simpa using hh⟩
  right := ⟨fun i => (mainCoreRoleIso G).symm ⟨G.right i, main_right_mem_coreRoles G i⟩, by
    intro i j h
    apply G.right.injective
    have hh := congrArg (fun z => ((mainCoreRoleIso G) z).1) h
    simpa using hh⟩

def mainCoreInclude (G : PaperShape) : Fin (mainBoundaryCoreShape G).roles ↪ Fin G.roles where
  toFun v := ((mainCoreRoleIso G) v).1
  inj' := fun _ _ h => (mainCoreRoleIso G).injective (Subtype.ext h)

def mainCoreIndex (G : PaperShape) (v : Fin G.roles) (hv : v ∈ mainCoreRoles G) :
    Fin (mainBoundaryCoreShape G).roles := (mainCoreRoleIso G).symm ⟨v, hv⟩

@[simp] theorem main_coreInclude_index (G : PaperShape) (v : Fin G.roles) (hv : v ∈ mainCoreRoles G) :
    mainCoreInclude G (mainCoreIndex G v hv) = v := by
  simp [mainCoreInclude, mainCoreIndex]

theorem main_core_left_iff (G : PaperShape) (v : Fin (mainBoundaryCoreShape G).roles) :
    v ∈ (mainBoundaryCoreShape G).toPartiteShape.leftBoundary ↔
      mainCoreInclude G v ∈ G.toPartiteShape.leftBoundary := by
  change v ∈ (mainBoundaryCoreShape G).leftBoundaryFinset ↔ mainCoreInclude G v ∈ G.leftBoundaryFinset
  rw [(mainBoundaryCoreShape G).mem_leftBoundaryFinset_iff v,
    G.mem_leftBoundaryFinset_iff (mainCoreInclude G v)]
  change (∃ i, (mainCoreRoleIso G).symm ⟨G.left i, _⟩ = v) ↔
    ∃ i, G.left i = ((mainCoreRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem main_core_right_iff (G : PaperShape) (v : Fin (mainBoundaryCoreShape G).roles) :
    v ∈ (mainBoundaryCoreShape G).toPartiteShape.rightBoundary ↔
      mainCoreInclude G v ∈ G.toPartiteShape.rightBoundary := by
  change v ∈ (mainBoundaryCoreShape G).rightBoundaryFinset ↔ mainCoreInclude G v ∈ G.rightBoundaryFinset
  rw [(mainBoundaryCoreShape G).mem_rightBoundaryFinset_iff v,
    G.mem_rightBoundaryFinset_iff (mainCoreInclude G v)]
  change (∃ i, (mainCoreRoleIso G).symm ⟨G.right i, _⟩ = v) ↔
    ∃ i, G.right i = ((mainCoreRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem main_core_incident_iff (G : PaperShape) (e : Fin (mainBoundaryCoreShape G).edges)
    (v : Fin (mainBoundaryCoreShape G).roles) :
    (mainBoundaryCoreShape G).toPartiteShape.EdgeIncident e v ↔
      G.toPartiteShape.EdgeIncident ((mainCoreEdgeIso G) e).1 (mainCoreInclude G v) := by
  change ((mainCoreRoleIso G).symm ⟨G.source ((mainCoreEdgeIso G) e).1, _⟩ = v ∨
    (mainCoreRoleIso G).symm ⟨G.target ((mainCoreEdgeIso G) e).1, _⟩ = v) ↔
      G.source ((mainCoreEdgeIso G) e).1 = ((mainCoreRoleIso G) v).1 ∨
      G.target ((mainCoreEdgeIso G) e).1 = ((mainCoreRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

def mainCoreReduceWalk (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (walk : G.toPartiteShape.EdgeWalkToBoundary v) : ∀ hv : v ∈ mainCoreRoles G,
      (mainBoundaryCoreShape G).toPartiteShape.EdgeWalkToBoundary (mainCoreIndex G v hv) := by
  induction walk with
  | finishLeft v hl =>
    intro hv
    exact .finishLeft _ ((main_core_left_iff G _).mpr (by simpa using hl))
  | finishRight v hr =>
    intro hv
    exact .finishRight _ ((main_core_right_iff G _).mpr (by simpa using hr))
  | @step v e w hStart hEnd tail ih =>
    intro hv
    have he := main_incident_coreEdge G e hv hStart
    have hw := main_coreRoles_edgeClosed G v hv e w hStart hEnd
    let en := (mainCoreEdgeIso G).symm ⟨e, he⟩
    apply PartiteShape.EdgeWalkToBoundary.step en (mainCoreIndex G w hw)
    · apply (main_core_incident_iff G en _).mpr
      simpa [en] using hStart
    · apply (main_core_incident_iff G en _).mpr
      simpa [en] using hEnd
    · exact ih hw

theorem main_boundaryCoreShape_isBoundaryCore (G : PaperShape) :
    (mainBoundaryCoreShape G).toPartiteShape.IsBoundaryCore := by
  intro v
  obtain ⟨walk⟩ := (main_mem_coreRoles G _).mp ((mainCoreRoleIso G) v).2
  have h := mainCoreReduceWalk G walk ((mainCoreRoleIso G) v).2
  simpa [mainCoreIndex] using (Nonempty.intro h)

end GraphMatrixReplica
