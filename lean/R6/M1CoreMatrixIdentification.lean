import R6.M1CoreMatrixIndices

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica

def rootCoreRawSampleFromBlock (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).RawSample where
  array e a := x ⟨⟨(rootCoreOccurrenceEquiv G dimension e).1, rootCoreCellEquiv G dimension e a⟩,
    (rootCoreOccurrenceEquiv G dimension e).2⟩

theorem root_core_cell_assignment_eq (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (rootBoundaryCoreShape G).edges)
    (a : PartiteRoleAssignment (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension)) :
    rootCoreCellEquiv G dimension e (fun v => a v.1) =
      fun w : {w : Fin G.roles //
        w ∈ (rootGraphRawFactorShape G dimension).scope (rootCoreOccurrenceEquiv G dimension e).1} =>
        rootCoreAssignmentEquiv G dimension a
        ⟨w.1, (rootCoreOccurrenceEquiv G dimension e).2 w.1 w.2⟩ := by
  funext w
  obtain ⟨v, rfl⟩ := (rootCoreCellRoleEquiv G dimension e).surjective w
  rw [root_coreCell_apply]
  change a v.1 = rootCoreAssignmentEquiv G dimension a (rootCoreCanonicalRoleEquiv G dimension v.1)
  rw [root_coreAssignment_apply]

theorem root_core_block_amplitude_eq (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ)
    (a : PartiteRoleAssignment (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension)) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).rawAmplitude
      (rootCoreRawSampleFromBlock G dimension x) a =
      (rootGraphRawFactorShape G dimension).coreAmplitudeFromBlock x (rootCoreAssignmentEquiv G dimension a) := by
  unfold PaperR16.RawFactorShape.rawAmplitude PaperR16.RawFactorShape.coreAmplitudeFromBlock
  apply Fintype.prod_equiv (rootCoreOccurrenceEquiv G dimension)
  intro e
  change x ⟨⟨(rootCoreOccurrenceEquiv G dimension e).1,
      rootCoreCellEquiv G dimension e (fun v => a v.1)⟩, _⟩ = _
  rw [root_core_cell_assignment_eq]

theorem root_core_entryCompatible_iff (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (a : PartiteRoleAssignment (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension))
    (row : PartiteBoundaryRow (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension))
    (col : PartiteBoundaryCol (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension)) :
    partiteBoundaryEntryCompatible a row col ↔
      (∀ c : {c : (rootGraphRawFactorShape G dimension).CanonicalCore //
          c ∈ (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary},
        rootCoreAssignmentEquiv G dimension a c.1 = rootCoreRowEquiv G dimension row c) ∧
      (∀ c : {c : (rootGraphRawFactorShape G dimension).CanonicalCore //
          c ∈ (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary},
        rootCoreAssignmentEquiv G dimension a c.1 = rootCoreColEquiv G dimension col c) := by
  constructor
  · intro h
    constructor
    · intro c
      obtain ⟨v, rfl⟩ := (rootCoreLeftRoleEquiv G dimension).surjective c
      change rootCoreAssignmentEquiv G dimension a (rootCoreCanonicalRoleEquiv G dimension v.1) =
        rootCoreRowEquiv G dimension row (rootCoreLeftRoleEquiv G dimension v)
      simpa only [root_coreAssignment_apply, root_coreRow_apply] using h.1 v
    · intro c
      obtain ⟨v, rfl⟩ := (rootCoreRightRoleEquiv G dimension).surjective c
      change rootCoreAssignmentEquiv G dimension a (rootCoreCanonicalRoleEquiv G dimension v.1) =
        rootCoreColEquiv G dimension col (rootCoreRightRoleEquiv G dimension v)
      simpa only [root_coreAssignment_apply, root_coreCol_apply] using h.2 v
  · intro h
    constructor
    · intro v
      have hh := h.1 (rootCoreLeftRoleEquiv G dimension v)
      change rootCoreAssignmentEquiv G dimension a (rootCoreCanonicalRoleEquiv G dimension v.1) =
        rootCoreRowEquiv G dimension row (rootCoreLeftRoleEquiv G dimension v) at hh
      simpa only [root_coreAssignment_apply, root_coreRow_apply] using hh
    · intro v
      have hh := h.2 (rootCoreRightRoleEquiv G dimension v)
      change rootCoreAssignmentEquiv G dimension a (rootCoreCanonicalRoleEquiv G dimension v.1) =
        rootCoreColEquiv G dimension col (rootCoreRightRoleEquiv G dimension v) at hh
      simpa only [root_coreAssignment_apply, root_coreCol_apply] using hh

theorem root_core_rawEntry_eq_nativeCore (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ)
    (row : PartiteBoundaryRow (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension))
    (col : PartiteBoundaryCol (G := (rootBoundaryCoreShape G).toPartiteShape) (rootCoreDimension G dimension)) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).rawMatrix
      (rootCoreRawSampleFromBlock G dimension x) row col =
      (rootGraphRawFactorShape G dimension).coreMatrixFromBlock x
        (rootCoreRowEquiv G dimension row) (rootCoreColEquiv G dimension col) := by
  classical
  unfold PaperR16.RawFactorShape.rawMatrix PaperR16.RawFactorShape.coreMatrixFromBlock
  apply Fintype.sum_equiv (rootCoreAssignmentEquiv G dimension)
  intro a
  unfold PaperR16.RawFactorShape.coreEntryFromBlock
  change (if partiteBoundaryEntryCompatible a row col then
      (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).rawAmplitude
        (rootCoreRawSampleFromBlock G dimension x) a else 0) = _
  simp only [root_core_entryCompatible_iff, root_core_block_amplitude_eq]

/-- The concrete core graph matrix is exactly the native factor core after
the explicit boundary reindexing; arbitrary real block values are permitted. -/
theorem root_core_rawOperatorMatrix_eq_reindex_native (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).rawOperatorMatrix
      (rootCoreRawSampleFromBlock G dimension x) =
      Matrix.reindex (rootCoreRowEquiv G dimension).symm (rootCoreColEquiv G dimension).symm
        ((rootGraphRawFactorShape G dimension).coreMatrixFromBlock x) := by
  ext row col
  exact root_core_rawEntry_eq_nativeCore G dimension x row col

theorem root_core_rawOperatorNorm_eq_native (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    ‖(rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).rawOperatorMatrix
      (rootCoreRawSampleFromBlock G dimension x)‖ =
      ‖(rootGraphRawFactorShape G dimension).coreMatrixFromBlock x‖ := by
  rw [root_core_rawOperatorMatrix_eq_reindex_native, paper_l2_opNorm_reindex]

#print axioms root_core_block_amplitude_eq
#print axioms root_core_rawEntry_eq_nativeCore
#print axioms root_core_rawOperatorMatrix_eq_reindex_native
#print axioms root_core_rawOperatorNorm_eq_native
end GraphMatrixReplica
