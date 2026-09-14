import R6.M1BoundaryCoreShape
import R6.F1aRealLpFactorization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

def rootCoreCanonicalRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fin (rootBoundaryCoreShape G).roles ≃ (rootGraphRawFactorShape G dimension).CanonicalCore :=
  (rootCoreRoleIso G).toEquiv.trans (Equiv.subtypeEquivRight fun v =>
    (root_mem_coreRoles G v).trans (root_raw_core_iff_boundaryWalk G dimension v).symm)

@[simp] theorem root_coreCanonicalRole_val (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (v : Fin (rootBoundaryCoreShape G).roles) :
    (rootCoreCanonicalRoleEquiv G dimension v).1 = rootCoreInclude G v := rfl

theorem root_coreEdges_iff_rawCoreOccurrence (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin G.edges) : e ∈ rootCoreEdges G ↔
      (rootGraphRawFactorShape G dimension).CoreOccurrence e := by
  constructor
  · intro he v hv
    apply (root_raw_core_iff_boundaryWalk G dimension v).mpr
    apply (root_mem_coreRoles G v).mp
    exact root_coreRoles_edgeClosed G _ (root_coreEdge_source G ⟨e, he⟩) e v
      (Or.inl rfl) ((root_raw_scope_iff_incident G dimension e v).mp hv)
  · intro he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (root_mem_coreRoles G _).mpr
    exact (root_raw_core_iff_boundaryWalk G dimension _).mp
      (he (G.source e) (by simp [rootGraphRawFactorShape]))

def rootCoreOccurrenceEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fin (rootBoundaryCoreShape G).edges ≃ (rootGraphRawFactorShape G dimension).CanonicalCoreOccurrence :=
  (rootCoreEdgeIso G).toEquiv.trans (Equiv.subtypeEquivRight fun e =>
    root_coreEdges_iff_rawCoreOccurrence G dimension e)

@[simp] theorem root_coreOccurrence_val (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (rootBoundaryCoreShape G).edges) :
    (rootCoreOccurrenceEquiv G dimension e).1 = ((rootCoreEdgeIso G) e).1 := rfl

def rootCoreDimension (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fin (rootBoundaryCoreShape G).roles → ℕ := fun v => dimension (rootCoreInclude G v)

def rootCoreAssignmentEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    PartiteRoleAssignment (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension) ≃
      (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.CoreTuple :=
  Equiv.piCongrLeft (fun c : (rootGraphRawFactorShape G dimension).CanonicalCore => Fin (dimension c.1))
    (rootCoreCanonicalRoleEquiv G dimension)

@[simp] theorem root_coreAssignment_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (a : PartiteRoleAssignment (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension))
    (v : Fin (rootBoundaryCoreShape G).roles) :
    rootCoreAssignmentEquiv G dimension a (rootCoreCanonicalRoleEquiv G dimension v) = a v := by
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

def rootCoreLeftRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    {v : Fin (rootBoundaryCoreShape G).roles // v ∈ (rootBoundaryCoreShape G).toPartiteShape.leftBoundary} ≃
      {c : (rootGraphRawFactorShape G dimension).CanonicalCore //
        c ∈ (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary} :=
  (rootCoreCanonicalRoleEquiv G dimension).subtypeEquiv (by
    intro v
    simp only [PaperR16.RawFactorShape.canonicalPreprocessedShape, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change v ∈ (rootBoundaryCoreShape G).toPartiteShape.leftBoundary ↔
      rootCoreInclude G v ∈ G.toPartiteShape.leftBoundary
    exact root_core_left_iff G v)

def rootCoreRightRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    {v : Fin (rootBoundaryCoreShape G).roles // v ∈ (rootBoundaryCoreShape G).toPartiteShape.rightBoundary} ≃
      {c : (rootGraphRawFactorShape G dimension).CanonicalCore //
        c ∈ (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary} :=
  (rootCoreCanonicalRoleEquiv G dimension).subtypeEquiv (by
    intro v
    simp only [PaperR16.RawFactorShape.canonicalPreprocessedShape, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change v ∈ (rootBoundaryCoreShape G).toPartiteShape.rightBoundary ↔
      rootCoreInclude G v ∈ G.toPartiteShape.rightBoundary
    exact root_core_right_iff G v)

def rootCoreRowEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    PartiteBoundaryRow (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension) ≃
      (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.BoundaryTuple
        (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary :=
  Equiv.piCongrLeft (fun c : {c : (rootGraphRawFactorShape G dimension).CanonicalCore //
      c ∈ (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary} =>
    Fin (dimension c.1.1)) (rootCoreLeftRoleEquiv G dimension)

def rootCoreColEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    PartiteBoundaryCol (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension) ≃
      (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.BoundaryTuple
        (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary :=
  Equiv.piCongrLeft (fun c : {c : (rootGraphRawFactorShape G dimension).CanonicalCore //
      c ∈ (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary} =>
    Fin (dimension c.1.1)) (rootCoreRightRoleEquiv G dimension)

@[simp] theorem root_coreRow_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (row : PartiteBoundaryRow (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension))
    (v : {v : Fin (rootBoundaryCoreShape G).roles // v ∈ (rootBoundaryCoreShape G).toPartiteShape.leftBoundary}) :
    rootCoreRowEquiv G dimension row (rootCoreLeftRoleEquiv G dimension v) = row v :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

@[simp] theorem root_coreCol_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (col : PartiteBoundaryCol (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension))
    (v : {v : Fin (rootBoundaryCoreShape G).roles // v ∈ (rootBoundaryCoreShape G).toPartiteShape.rightBoundary}) :
    rootCoreColEquiv G dimension col (rootCoreRightRoleEquiv G dimension v) = col v :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

def rootCoreCellRoleEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (rootBoundaryCoreShape G).edges) :
    {v : Fin (rootBoundaryCoreShape G).roles //
      v ∈ (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).scope e} ≃
    {w : Fin G.roles // w ∈ (rootGraphRawFactorShape G dimension).scope (rootCoreOccurrenceEquiv G dimension e).1} where
  toFun v := ⟨rootCoreInclude G v.1, (root_raw_scope_iff_incident G dimension _ _).mpr
    ((root_core_incident_iff G e v.1).mp
      ((root_raw_scope_iff_incident (rootBoundaryCoreShape G) (rootCoreDimension G dimension) e v.1).mp v.2))⟩
  invFun w :=
    have hw : w.1 ∈ rootCoreRoles G := (root_mem_coreRoles G w.1).mpr
      ((root_raw_core_iff_boundaryWalk G dimension w.1).mp ((rootCoreOccurrenceEquiv G dimension e).2 w.1 w.2))
    ⟨rootCoreIndex G w.1 hw,
      (root_raw_scope_iff_incident (rootBoundaryCoreShape G) (rootCoreDimension G dimension) e _).mpr
        ((root_core_incident_iff G e _).mpr (by
          simpa using (root_raw_scope_iff_incident G dimension _ _).mp w.2))⟩
  left_inv v := by
    apply Subtype.ext
    apply (rootCoreInclude G).injective
    simp
  right_inv w := by
    apply Subtype.ext
    simp

@[simp] theorem root_coreCellRole_val (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (rootBoundaryCoreShape G).edges)
    (v : {v : Fin (rootBoundaryCoreShape G).roles //
      v ∈ (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).scope e}) :
    (rootCoreCellRoleEquiv G dimension e v).1 = rootCoreInclude G v.1 := rfl

def rootCoreCellEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (rootBoundaryCoreShape G).edges) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).RawCell e ≃
      (rootGraphRawFactorShape G dimension).RawCell (rootCoreOccurrenceEquiv G dimension e).1 :=
  Equiv.piCongrLeft (fun w : {w : Fin G.roles //
      w ∈ (rootGraphRawFactorShape G dimension).scope (rootCoreOccurrenceEquiv G dimension e).1} =>
    Fin (dimension w.1)) (rootCoreCellRoleEquiv G dimension e)

@[simp] theorem root_coreCell_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (rootBoundaryCoreShape G).edges)
    (a : (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).RawCell e)
    (v : {v : Fin (rootBoundaryCoreShape G).roles //
      v ∈ (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).scope e}) :
    rootCoreCellEquiv G dimension e a (rootCoreCellRoleEquiv G dimension e v) = a v :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

#print axioms rootCoreCanonicalRoleEquiv
#print axioms rootCoreOccurrenceEquiv
#print axioms rootCoreAssignmentEquiv
#print axioms rootCoreRowEquiv
#print axioms rootCoreColEquiv
#print axioms rootCoreCellEquiv
end GraphMatrixReplica
