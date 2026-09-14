import GraphMatrix.Main.CoreMatrixIndices

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica

def mainCoreRawSampleFromBlock (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).RawSample where
  array e a := x ⟨⟨(mainCoreOccurrenceEquiv G dimension e).1, mainCoreCellEquiv G dimension e a⟩,
    (mainCoreOccurrenceEquiv G dimension e).2⟩

theorem main_core_cell_assignment_eq (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin (mainBoundaryCoreShape G).edges)
    (a : PartiteRoleAssignment (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension)) :
    mainCoreCellEquiv G dimension e (fun v => a v.1) =
      fun w : {w : Fin G.roles //
        w ∈ (mainGraphRawFactorShape G dimension).scope (mainCoreOccurrenceEquiv G dimension e).1} =>
        mainCoreAssignmentEquiv G dimension a
        ⟨w.1, (mainCoreOccurrenceEquiv G dimension e).2 w.1 w.2⟩ := by
  funext w
  obtain ⟨v, rfl⟩ := (mainCoreCellRoleEquiv G dimension e).surjective w
  rw [main_coreCell_apply]
  change a v.1 = mainCoreAssignmentEquiv G dimension a (mainCoreCanonicalRoleEquiv G dimension v.1)
  rw [main_coreAssignment_apply]

theorem main_core_block_amplitude_eq (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ)
    (a : PartiteRoleAssignment (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension)) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).rawAmplitude
      (mainCoreRawSampleFromBlock G dimension x) a =
      (mainGraphRawFactorShape G dimension).coreAmplitudeFromBlock x (mainCoreAssignmentEquiv G dimension a) := by
  unfold Model.RawFactorShape.rawAmplitude Model.RawFactorShape.coreAmplitudeFromBlock
  apply Fintype.prod_equiv (mainCoreOccurrenceEquiv G dimension)
  intro e
  change x ⟨⟨(mainCoreOccurrenceEquiv G dimension e).1,
      mainCoreCellEquiv G dimension e (fun v => a v.1)⟩, _⟩ = _
  rw [main_core_cell_assignment_eq]

theorem main_core_entryCompatible_iff (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (a : PartiteRoleAssignment (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension))
    (row : PartiteBoundaryRow (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension))
    (col : PartiteBoundaryCol (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension)) :
    partiteBoundaryEntryCompatible a row col ↔
      (∀ c : {c : (mainGraphRawFactorShape G dimension).CanonicalCore //
          c ∈ (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.leftBoundary},
        mainCoreAssignmentEquiv G dimension a c.1 = mainCoreRowEquiv G dimension row c) ∧
      (∀ c : {c : (mainGraphRawFactorShape G dimension).CanonicalCore //
          c ∈ (mainGraphRawFactorShape G dimension).canonicalPreprocessedShape.rightBoundary},
        mainCoreAssignmentEquiv G dimension a c.1 = mainCoreColEquiv G dimension col c) := by
  constructor
  · intro h
    constructor
    · intro c
      obtain ⟨v, rfl⟩ := (mainCoreLeftRoleEquiv G dimension).surjective c
      change mainCoreAssignmentEquiv G dimension a (mainCoreCanonicalRoleEquiv G dimension v.1) =
        mainCoreRowEquiv G dimension row (mainCoreLeftRoleEquiv G dimension v)
      simpa only [main_coreAssignment_apply, main_coreRow_apply] using h.1 v
    · intro c
      obtain ⟨v, rfl⟩ := (mainCoreRightRoleEquiv G dimension).surjective c
      change mainCoreAssignmentEquiv G dimension a (mainCoreCanonicalRoleEquiv G dimension v.1) =
        mainCoreColEquiv G dimension col (mainCoreRightRoleEquiv G dimension v)
      simpa only [main_coreAssignment_apply, main_coreCol_apply] using h.2 v
  · intro h
    constructor
    · intro v
      have hh := h.1 (mainCoreLeftRoleEquiv G dimension v)
      change mainCoreAssignmentEquiv G dimension a (mainCoreCanonicalRoleEquiv G dimension v.1) =
        mainCoreRowEquiv G dimension row (mainCoreLeftRoleEquiv G dimension v) at hh
      simpa only [main_coreAssignment_apply, main_coreRow_apply] using hh
    · intro v
      have hh := h.2 (mainCoreRightRoleEquiv G dimension v)
      change mainCoreAssignmentEquiv G dimension a (mainCoreCanonicalRoleEquiv G dimension v.1) =
        mainCoreColEquiv G dimension col (mainCoreRightRoleEquiv G dimension v) at hh
      simpa only [main_coreAssignment_apply, main_coreCol_apply] using hh

theorem main_core_rawEntry_eq_nativeCore (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ)
    (row : PartiteBoundaryRow (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension))
    (col : PartiteBoundaryCol (G := (mainBoundaryCoreShape G).toPartiteShape) (mainCoreDimension G dimension)) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).rawMatrix
      (mainCoreRawSampleFromBlock G dimension x) row col =
      (mainGraphRawFactorShape G dimension).coreMatrixFromBlock x
        (mainCoreRowEquiv G dimension row) (mainCoreColEquiv G dimension col) := by
  classical
  unfold Model.RawFactorShape.rawMatrix Model.RawFactorShape.coreMatrixFromBlock
  apply Fintype.sum_equiv (mainCoreAssignmentEquiv G dimension)
  intro a
  unfold Model.RawFactorShape.coreEntryFromBlock
  change (if partiteBoundaryEntryCompatible a row col then
      (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).rawAmplitude
        (mainCoreRawSampleFromBlock G dimension x) a else 0) = _
  simp only [main_core_entryCompatible_iff, main_core_block_amplitude_eq]

/-- The concrete core graph matrix is exactly the native factor core after
the explicit boundary reindexing; arbitrary real block values are permitted. -/
theorem main_core_rawOperatorMatrix_eq_reindex_native (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).rawOperatorMatrix
      (mainCoreRawSampleFromBlock G dimension x) =
      Matrix.reindex (mainCoreRowEquiv G dimension).symm (mainCoreColEquiv G dimension).symm
        ((mainGraphRawFactorShape G dimension).coreMatrixFromBlock x) := by
  ext row col
  exact main_core_rawEntry_eq_nativeCore G dimension x row col

theorem main_core_rawOperatorNorm_eq_native (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    ‖(mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).rawOperatorMatrix
      (mainCoreRawSampleFromBlock G dimension x)‖ =
      ‖(mainGraphRawFactorShape G dimension).coreMatrixFromBlock x‖ := by
  rw [main_core_rawOperatorMatrix_eq_reindex_native, paper_l2_opNorm_reindex]

end GraphMatrixReplica
