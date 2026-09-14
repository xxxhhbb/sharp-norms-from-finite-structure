import GraphMatrix.Main.BoundaryCoreShape
import GraphMatrix.Probability.Factorization.RealLpFactorization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

def mainCoreCanonicalRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fin (mainBoundaryCoreShape G).roles ≃ (mainGraphRawFactorShape G dimension).CanonicalCore :=
  (mainCoreRoleIso G).toEquiv.trans (Equiv.subtypeEquivRight fun v =>
    (main_mem_coreRoles G v).trans (main_raw_core_iff_boundaryWalk G dimension v).symm)

@[simp] theorem main_coreCanonicalRole_val (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (v : Fin (mainBoundaryCoreShape G).roles) :
    (mainCoreCanonicalRoleEquiv G dimension v).1 = mainCoreInclude G v := rfl

theorem main_coreEdges_iff_rawCoreOccurrence (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin G.edges) : e ∈ mainCoreEdges G ↔
      (mainGraphRawFactorShape G dimension).CoreOccurrence e := by
  constructor
  · intro he v hv
    apply (main_raw_core_iff_boundaryWalk G dimension v).mpr
    apply (main_mem_coreRoles G v).mp
    exact main_coreRoles_edgeClosed G _ (main_coreEdge_source G ⟨e, he⟩) e v
      (Or.inl rfl) ((main_raw_scope_iff_incident G dimension e v).mp hv)
  · intro he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (main_mem_coreRoles G _).mpr
    exact (main_raw_core_iff_boundaryWalk G dimension _).mp
      (he (G.source e) (by simp [mainGraphRawFactorShape]))

def mainCoreOccurrenceEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fin (mainBoundaryCoreShape G).edges ≃ (mainGraphRawFactorShape G dimension).CanonicalCoreOccurrence :=
  (mainCoreEdgeIso G).toEquiv.trans (Equiv.subtypeEquivRight fun e =>
    main_coreEdges_iff_rawCoreOccurrence G dimension e)

@[simp] theorem main_coreOccurrence_val (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (mainBoundaryCoreShape G).edges) :
    (mainCoreOccurrenceEquiv G dimension e).1 = ((mainCoreEdgeIso G) e).1 := rfl

def mainCoreDimension (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fin (mainBoundaryCoreShape G).roles → ℕ := fun v => dimension (mainCoreInclude G v)

def mainCoreAssignmentEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    PartiteRoleAssignment (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension) ≃
      (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.CoreTuple :=
  Equiv.piCongrLeft (fun c : (mainGraphRawFactorShape G dimension).CanonicalCore => Fin (dimension c.1))
    (mainCoreCanonicalRoleEquiv G dimension)

@[simp] theorem main_coreAssignment_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (a : PartiteRoleAssignment (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension))
    (v : Fin (mainBoundaryCoreShape G).roles) :
    mainCoreAssignmentEquiv G dimension a (mainCoreCanonicalRoleEquiv G dimension v) = a v := by
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

def mainCoreLeftRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    {v : Fin (mainBoundaryCoreShape G).roles // v ∈ (mainBoundaryCoreShape G).toPartiteShape.leftBoundary} ≃
      {c : (mainGraphRawFactorShape G dimension).CanonicalCore //
        c ∈ (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary} :=
  (mainCoreCanonicalRoleEquiv G dimension).subtypeEquiv (by
    intro v
    simp only [Model.RawFactorShape.canonicalPreprocessedShape, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change v ∈ (mainBoundaryCoreShape G).toPartiteShape.leftBoundary ↔
      mainCoreInclude G v ∈ G.toPartiteShape.leftBoundary
    exact main_core_left_iff G v)

def mainCoreRightRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    {v : Fin (mainBoundaryCoreShape G).roles // v ∈ (mainBoundaryCoreShape G).toPartiteShape.rightBoundary} ≃
      {c : (mainGraphRawFactorShape G dimension).CanonicalCore //
        c ∈ (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary} :=
  (mainCoreCanonicalRoleEquiv G dimension).subtypeEquiv (by
    intro v
    simp only [Model.RawFactorShape.canonicalPreprocessedShape, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change v ∈ (mainBoundaryCoreShape G).toPartiteShape.rightBoundary ↔
      mainCoreInclude G v ∈ G.toPartiteShape.rightBoundary
    exact main_core_right_iff G v)

def mainCoreRowEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    PartiteBoundaryRow (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension) ≃
      (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.BoundaryTuple
        (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary :=
  Equiv.piCongrLeft (fun c : {c : (mainGraphRawFactorShape G dimension).CanonicalCore //
      c ∈ (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary} =>
    Fin (dimension c.1.1)) (mainCoreLeftRoleEquiv G dimension)

def mainCoreColEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    PartiteBoundaryCol (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension) ≃
      (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.BoundaryTuple
        (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary :=
  Equiv.piCongrLeft (fun c : {c : (mainGraphRawFactorShape G dimension).CanonicalCore //
      c ∈ (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary} =>
    Fin (dimension c.1.1)) (mainCoreRightRoleEquiv G dimension)

@[simp] theorem main_coreRow_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (row : PartiteBoundaryRow (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension))
    (v : {v : Fin (mainBoundaryCoreShape G).roles // v ∈ (mainBoundaryCoreShape G).toPartiteShape.leftBoundary}) :
    mainCoreRowEquiv G dimension row (mainCoreLeftRoleEquiv G dimension v) = row v :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

@[simp] theorem main_coreCol_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (col : PartiteBoundaryCol (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension))
    (v : {v : Fin (mainBoundaryCoreShape G).roles // v ∈ (mainBoundaryCoreShape G).toPartiteShape.rightBoundary}) :
    mainCoreColEquiv G dimension col (mainCoreRightRoleEquiv G dimension v) = col v :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

def mainCoreCellRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (mainBoundaryCoreShape G).edges) :
    {v : Fin (mainBoundaryCoreShape G).roles //
      v ∈ (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).scope e} ≃
    {w : Fin G.roles // w ∈ (mainGraphRawFactorShape G dimension).scope (mainCoreOccurrenceEquiv G dimension e).1} where
  toFun v := ⟨mainCoreInclude G v.1, (main_raw_scope_iff_incident G dimension _ _).mpr
    ((main_core_incident_iff G e v.1).mp
      ((main_raw_scope_iff_incident (mainBoundaryCoreShape G) (mainCoreDimension G dimension) e v.1).mp v.2))⟩
  invFun w :=
    have hw : w.1 ∈ mainCoreRoles G := (main_mem_coreRoles G w.1).mpr
      ((main_raw_core_iff_boundaryWalk G dimension w.1).mp ((mainCoreOccurrenceEquiv G dimension e).2 w.1 w.2))
    ⟨mainCoreIndex G w.1 hw,
      (main_raw_scope_iff_incident (mainBoundaryCoreShape G) (mainCoreDimension G dimension) e _).mpr
        ((main_core_incident_iff G e _).mpr (by
          simpa using (main_raw_scope_iff_incident G dimension _ _).mp w.2))⟩
  left_inv v := by
    apply Subtype.ext
    apply (mainCoreInclude G).injective
    simp
  right_inv w := by
    apply Subtype.ext
    simp

@[simp] theorem main_coreCellRole_val (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (mainBoundaryCoreShape G).edges)
    (v : {v : Fin (mainBoundaryCoreShape G).roles //
      v ∈ (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).scope e}) :
    (mainCoreCellRoleEquiv G dimension e v).1 = mainCoreInclude G v.1 := rfl

def mainCoreCellEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (mainBoundaryCoreShape G).edges) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).RawCell e ≃
      (mainGraphRawFactorShape G dimension).RawCell (mainCoreOccurrenceEquiv G dimension e).1 :=
  Equiv.piCongrLeft (fun w : {w : Fin G.roles //
      w ∈ (mainGraphRawFactorShape G dimension).scope (mainCoreOccurrenceEquiv G dimension e).1} =>
    Fin (dimension w.1)) (mainCoreCellRoleEquiv G dimension e)

@[simp] theorem main_coreCell_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (mainBoundaryCoreShape G).edges)
    (a : (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).RawCell e)
    (v : {v : Fin (mainBoundaryCoreShape G).roles //
      v ∈ (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).scope e}) :
    mainCoreCellEquiv G dimension e a (mainCoreCellRoleEquiv G dimension e v) = a v :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

end GraphMatrixReplica
