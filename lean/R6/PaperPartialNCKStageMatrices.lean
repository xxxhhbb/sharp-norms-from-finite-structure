import R6.PaperPartialNCKConcreteLedger

/-! # Concrete partial-NCK stage matrices

Equation (10) of BLNvH v2 retains an independent noise copy for every
coordinate in `Z`, while coordinates moved to `R` or `C` become matrix
indices.  This file records the corresponding assignment-sum matrix without
asserting independence through the old shared-noise model.

There is one small but important bookkeeping distinction.  The previously
defined `paperIntermediateMarginalizedOrientedMatrix` keeps the signs of all
shape edges in its entries.  The raw terminal `Y_[Z|R|C]` does not keep the
signs of the edges already moved to `R` or `C`.  On a fixed orientation those
missing unit signs are row/column gauge factors.  We therefore expose both
the raw paper matrix and its gauge-twisted version, and prove the exact
endpoint identities rather than identifying the two definitions silently.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- One independent copy of the ambient unordered-edge noise for each shape
edge.  Independence is represented by the product type itself. -/
abbrev PaperDecoupledNoise (G : PaperShape) (n : ℕ) :=
  Fin G.edges → PaperNoise n

/-- The diagonal embedding of the coupled noise into the decoupled product
space.  This is an exact specialization, not a probabilistic decoupling
claim. -/
def paperDiagonalDecoupledNoise
    (G : PaperShape) {n : ℕ} (w : PaperNoise n) :
    PaperDecoupledNoise G n :=
  fun _ => w

/-- Product of the independent edge-coordinate signs indexed by `Z`. -/
def paperDecoupledNoiseProductOn
    (G : PaperShape) {n : ℕ}
    (Z : Finset (Fin G.edges)) (w : PaperDecoupledNoise G n)
    (assignment : PaperAssignment G n) : ℝ :=
  ∏ e ∈ Z, paperEdgeSign (w e)
    (assignment (G.source e)) (assignment (G.target e))

/-- The paper's `Y_[Z|R|C]` assignment sum through arbitrary concrete row
and column coordinate maps.  `rowMap` and `colMap` encode the tensor-basis
coordinates moved to `R` and `C`; the only random scalar factors left are
those indexed by `Z`. -/
def paperYThroughCoordinates
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (w : PaperDecoupledNoise G n)
    {rows cols : Type*}
    (rowMap : PaperAssignment G n → rows)
    (colMap : PaperAssignment G n → cols) : Matrix rows cols ℝ := by
  classical
  exact fun row col =>
    ∑ assignment : PaperAssignment G n,
      if rowMap assignment = row ∧ colMap assignment = col then
        paperOrientedAssignmentWeight G orientation assignment *
          paperDecoupledNoiseProductOn G Z w assignment
      else 0

/-! ## Literal formula-(10) coordinate packaging -/

/-- Row basis of `Y_[Z|R|C]`: the original ordered row boundary together
with one ordered ambient pair for every edge coordinate moved to `R`.
Using ordered pairs is equivalent to the unordered ambient coordinate on a
fixed orientation piece. -/
abbrev PaperYRowIndex (G : PaperShape) (n : ℕ)
    (R : Finset (Fin G.edges)) :=
  PaperRow G n × ({e : Fin G.edges // e ∈ R} → Fin n × Fin n)

/-- Column basis of `Y_[Z|R|C]`. -/
abbrev PaperYColIndex (G : PaperShape) (n : ℕ)
    (C : Finset (Fin G.edges)) :=
  PaperCol G n × ({e : Fin G.edges // e ∈ C} → Fin n × Fin n)

/-- The concrete row tensor coordinate of one assignment. -/
def paperYRowCoordinate
    (G : PaperShape) {n : ℕ} (R : Finset (Fin G.edges))
    (assignment : PaperAssignment G n) : PaperYRowIndex G n R :=
  (paperAssignmentLeftTuple G assignment,
    fun e => paperAssignmentEdgeCoordinate G assignment e.1)

/-- The concrete column tensor coordinate of one assignment. -/
def paperYColCoordinate
    (G : PaperShape) {n : ℕ} (C : Finset (Fin G.edges))
    (assignment : PaperAssignment G n) : PaperYColIndex G n C :=
  (paperAssignmentRightTuple G assignment,
    fun e => paperAssignmentEdgeCoordinate G assignment e.1)

/-- Literal paper-style intermediate stage.  Edges in `R` and `C` are
matrix coordinates, while precisely the complementary edges in `Z` remain
decoupled random variables. -/
def paperYMatrix
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool)
    (R C : Finset (Fin G.edges))
    (w : PaperDecoupledNoise G n) :
    Matrix (PaperYRowIndex G n R) (PaperYColIndex G n C) ℝ :=
  paperYThroughCoordinates G n orientation
    (Finset.univ \ (R ∪ C)) w
    (paperYRowCoordinate G R) (paperYColCoordinate G C)

/-- The order-zero decoupled oriented chaos, using the original ordered
boundary coordinates.  It is the canonical compression of
`paperYMatrix G n orientation ∅ ∅ w`, whose two additional function blocks
have empty domains. -/
def paperDecoupledOrientedGraphMatrix
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ :=
  paperYThroughCoordinates G n orientation Finset.univ w
    (paperAssignmentLeftTuple G) (paperAssignmentRightTuple G)

/-- Elimination from the subtype of an empty finite set. -/
def paperEmptyEdgeElim
    (G : PaperShape) {β : Sort*}
    (e : {e : Fin G.edges // e ∈ (∅ : Finset (Fin G.edges))}) : β := by
  have hCard : Fintype.card
      {e : Fin G.edges // e ∈ (∅ : Finset (Fin G.edges))} = 0 := by
    simp
  exact (Fintype.card_eq_zero_iff.mp hCard).elim e

/-- Canonical removal of the empty row edge-coordinate block. -/
def paperYEmptyRowEquiv (G : PaperShape) (n : ℕ) :
    PaperYRowIndex G n ∅ ≃ PaperRow G n where
  toFun x := x.1
  invFun row := (row, fun e => paperEmptyEdgeElim G e)
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext e
      exact paperEmptyEdgeElim G e
  right_inv _ := rfl

/-- Canonical removal of the empty column edge-coordinate block. -/
def paperYEmptyColEquiv (G : PaperShape) (n : ℕ) :
    PaperYColIndex G n ∅ ≃ PaperCol G n where
  toFun x := x.1
  invFun col := (col, fun e => paperEmptyEdgeElim G e)
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext e
      exact paperEmptyEdgeElim G e
  right_inv _ := rfl

/-- Literal formula (10) at `R=C=∅`, reindexed by deleting the two empty
edge-coordinate blocks. -/
theorem paperYMatrix_empty_reindex_eq_decoupled
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    Matrix.reindex (paperYEmptyRowEquiv G n) (paperYEmptyColEquiv G n)
        (paperYMatrix G n orientation ∅ ∅ w) =
      paperDecoupledOrientedGraphMatrix G n orientation w := by
  classical
  ext row col
  unfold paperYMatrix paperDecoupledOrientedGraphMatrix
    paperYThroughCoordinates
  apply Finset.sum_congr rfl
  intro assignment _
  have hRow :
      paperYRowCoordinate G (∅ : Finset (Fin G.edges)) assignment =
          (paperYEmptyRowEquiv G n).symm row ↔
        paperAssignmentLeftTuple G assignment = row := by
    constructor
    · exact fun h => congrArg Prod.fst h
    · intro h
      apply Prod.ext h
      funext e
      exact paperEmptyEdgeElim G e
  have hCol :
      paperYColCoordinate G (∅ : Finset (Fin G.edges)) assignment =
          (paperYEmptyColEquiv G n).symm col ↔
        paperAssignmentRightTuple G assignment = col := by
    constructor
    · exact fun h => congrArg Prod.fst h
    · intro h
      apply Prod.ext h
      funext e
      exact paperEmptyEdgeElim G e
  simp only [Finset.union_empty, Finset.sdiff_empty, hRow, hCol]
  by_cases hEntry : paperAssignmentLeftTuple G assignment = row ∧
      paperAssignmentRightTuple G assignment = col <;>
    simp [hEntry]

/-! ## The fixed distinguished edge ordering -/

/-- The selected ordering edges transported from the underlying partite
shape back to the paper edge type. -/
def paperSelectedOrderingEdges
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate) :
    Finset (Fin G.edges) :=
  certificate.paths.orderingEdges

/-- The canonical increasing enumeration of the selected ordering-edge
set.  The paper only needs a fixed order, so the ambient `Fin` order is a
concrete deterministic choice. -/
def paperOrderingEdgeAt
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (i : Fin (paperSelectedOrderingEdges G certificate).card) : Fin G.edges :=
  ((Finset.orderIsoOfFin (paperSelectedOrderingEdges G certificate) rfl) i).1

/-- First `i` selected edges in the fixed ordering. -/
def paperOrderingEdgePrefix
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (i : ℕ) : Finset (Fin G.edges) := by
  classical
  exact (Finset.univ.filter fun j :
      Fin (paperSelectedOrderingEdges G certificate).card => j.val < i).image
    (paperOrderingEdgeAt G certificate)

@[simp] theorem paperOrderingEdgePrefix_zero
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate) :
    paperOrderingEdgePrefix G certificate 0 = ∅ := by
  classical
  simp [paperOrderingEdgePrefix]

theorem paperOrderingEdgePrefix_card_eq_all
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate) :
    paperOrderingEdgePrefix G certificate
        (paperSelectedOrderingEdges G certificate).card =
      paperSelectedOrderingEdges G certificate := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.orderIsoOfFin
      (paperSelectedOrderingEdges G certificate) rfl i).2
  · intro he
    let i := (Finset.orderIsoOfFin
      (paperSelectedOrderingEdges G certificate) rfl).symm ⟨e, he⟩
    apply Finset.mem_image.2
    refine ⟨i, ?_, ?_⟩
    · simp [i]
    · exact congrArg Subtype.val
        ((Finset.orderIsoOfFin
          (paperSelectedOrderingEdges G certificate) rfl).apply_symm_apply
            ⟨e, he⟩)

/-- The side assigned by `D` to a selected edge. -/
def paperSelectedEdgeSide
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (e : {e : Fin G.edges // e ∈ paperSelectedOrderingEdges G certificate}) :
    Bool :=
  D.edgeSide ⟨e.1, e.2⟩

/-- Among the first `i` selected edges, those moved to the row side. -/
def paperPartialNCKStageRowEdges
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (i : ℕ) : Finset (Fin G.edges) := by
  classical
  exact (paperOrderingEdgePrefix G certificate i).filter fun e =>
    ∃ he : e ∈ paperSelectedOrderingEdges G certificate,
      paperSelectedEdgeSide G certificate D ⟨e, he⟩ = false

/-- Among the first `i` selected edges, those moved to the column side. -/
def paperPartialNCKStageColEdges
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (i : ℕ) : Finset (Fin G.edges) := by
  classical
  exact (paperOrderingEdgePrefix G certificate i).filter fun e =>
    ∃ he : e ∈ paperSelectedOrderingEdges G certificate,
      paperSelectedEdgeSide G certificate D ⟨e, he⟩ = true

@[simp] theorem paperPartialNCKStageRowEdges_zero
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths) :
    paperPartialNCKStageRowEdges G certificate D 0 = ∅ := by
  simp [paperPartialNCKStageRowEdges]

@[simp] theorem paperPartialNCKStageColEdges_zero
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths) :
    paperPartialNCKStageColEdges G certificate D 0 = ∅ := by
  simp [paperPartialNCKStageColEdges]

/-- At the final selected-edge stage, every distinguished edge has moved to
exactly one matrix side. -/
theorem paperPartialNCKStage_edges_union_at_card
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths) :
    paperPartialNCKStageRowEdges G certificate D
          (paperSelectedOrderingEdges G certificate).card ∪
        paperPartialNCKStageColEdges G certificate D
          (paperSelectedOrderingEdges G certificate).card =
      paperSelectedOrderingEdges G certificate := by
  classical
  rw [paperPartialNCKStageRowEdges, paperPartialNCKStageColEdges,
    paperOrderingEdgePrefix_card_eq_all]
  ext e
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hRow | hCol
    · exact (Finset.mem_filter.mp hRow).1
    · exact (Finset.mem_filter.mp hCol).1
  · intro he
    cases hSide : paperSelectedEdgeSide G certificate D ⟨e, he⟩ with
    | false =>
        apply Finset.mem_union_left
        exact Finset.mem_filter.2 ⟨he, ⟨he, hSide⟩⟩
    | true =>
        apply Finset.mem_union_right
        exact Finset.mem_filter.2 ⟨he, ⟨he, hSide⟩⟩

/-- The concrete sequence of literal formula-(10) stages.  Stage `i` moves
the first `i` selected edges to the side prescribed by `D`; all other shape
edges remain in the decoupled chaos set `Z`. -/
def paperPartialNCKStageMatrix
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) (w : PaperDecoupledNoise G n) :
    Matrix
      (PaperYRowIndex G n
        (paperPartialNCKStageRowEdges G certificate D i))
      (PaperYColIndex G n
        (paperPartialNCKStageColEdges G certificate D i)) ℝ :=
  paperYMatrix G n orientation
    (paperPartialNCKStageRowEdges G certificate D i)
    (paperPartialNCKStageColEdges G certificate D i) w

/-- The actual L2 operator norm of the `i`th literal paper stage. -/
def paperPartialNCKRawStageNorm
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) (i : ℕ) : ℝ :=
  ‖paperPartialNCKStageMatrix G certificate D n orientation i w‖

theorem paperPartialNCKRawStageNorm_nonneg
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) (i : ℕ) :
    0 ≤ paperPartialNCKRawStageNorm
      G certificate D n orientation w i :=
  norm_nonneg _

@[simp] theorem paperDecoupledNoiseProductOn_diagonal_univ
    (G : PaperShape) {n : ℕ} (w : PaperNoise n)
    (assignment : PaperAssignment G n) :
    paperDecoupledNoiseProductOn G Finset.univ
        (paperDiagonalDecoupledNoise G w) assignment =
      paperAssignmentNoiseProduct G w assignment := by
  rfl

/-- On the diagonal copy of the noise, the order-zero decoupled chaos is
exactly the existing oriented graph matrix.  This is the concrete coupled
endpoint map; no norm comparison is used. -/
theorem paperDecoupledOrientedGraphMatrix_diagonal_eq
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    paperDecoupledOrientedGraphMatrix G n orientation
        (paperDiagonalDecoupledNoise G w) =
      paperOrientedGraphMatrix G n orientation w := by
  classical
  rw [paperOrientedGraphMatrix_eq_nearlyCombinatorial]
  ext row col
  unfold paperDecoupledOrientedGraphMatrix paperYThroughCoordinates
    paperNearlyCombinatorialOrientedMatrix
  apply Finset.sum_congr rfl
  intro assignment _
  by_cases hEntry :
      paperAssignmentLeftTuple G assignment = row ∧
        paperAssignmentRightTuple G assignment = col
  · simp [hEntry, paperAssignmentEntryCompatible,
      paperDecoupledNoiseProductOn_diagonal_univ]
  · simp [hEntry, paperAssignmentEntryCompatible]

/-- The deterministic product of the unit signs belonging to coordinates
already moved out of `Z`.  In the paper tensor indexing this product splits
between row and column coordinates. -/
def paperFlattenedGaugeProductOn
    (G : PaperShape) {n : ℕ}
    (flattened : Finset (Fin G.edges)) (w : PaperNoise n)
    (assignment : PaperAssignment G n) : ℝ :=
  ∏ e ∈ flattened, paperEdgeSign w
    (assignment (G.source e)) (assignment (G.target e))

/-- Gauge-twisted `Y_[Z|R|C]`.  This keeps the raw decoupled factors on `Z`
and restores the unit signs of already flattened coordinates.  It is useful
because the older intermediate-matrix API retained those harmless signs. -/
def paperGaugeTwistedYThroughCoordinates
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool)
    (Z flattened : Finset (Fin G.edges))
    (decoupled : PaperDecoupledNoise G n) (coupled : PaperNoise n)
    {rows cols : Type*}
    (rowMap : PaperAssignment G n → rows)
    (colMap : PaperAssignment G n → cols) : Matrix rows cols ℝ := by
  classical
  exact fun row col =>
    ∑ assignment : PaperAssignment G n,
      if rowMap assignment = row ∧ colMap assignment = col then
        paperOrientedAssignmentWeight G orientation assignment *
          (paperDecoupledNoiseProductOn G Z decoupled assignment *
            paperFlattenedGaugeProductOn G flattened coupled assignment)
      else 0

theorem paper_complement_mul_flattenedGauge_eq_fullNoise
    (G : PaperShape) {n : ℕ}
    (flattened : Finset (Fin G.edges)) (w : PaperNoise n)
    (assignment : PaperAssignment G n) :
    paperDecoupledNoiseProductOn G (Finset.univ \ flattened)
        (paperDiagonalDecoupledNoise G w) assignment *
      paperFlattenedGaugeProductOn G flattened w assignment =
        paperAssignmentNoiseProduct G w assignment := by
  classical
  let f : Fin G.edges → ℝ := fun e => paperEdgeSign w
    (assignment (G.source e)) (assignment (G.target e))
  change (∏ e ∈ Finset.univ \ flattened, f e) *
      (∏ e ∈ flattened, f e) = ∏ e : Fin G.edges, f e
  rw [Finset.prod_sdiff (Finset.subset_univ flattened)]

/-- The exact terminal coordinate maps already used by the marginalized
intermediate flattening. -/
def paperIntermediateCoveredRowMap
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    {n : ℕ} (assignment : PaperAssignment G n) :
    PaperVisibleTuple n D.coveredRowRoles :=
  paperAssignmentRestriction D.coveredRowRoles
    (paperAssignmentRestriction
      (coveredRoles G.isolatedMiddleRoles) assignment)

def paperIntermediateCoveredColMap
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    {n : ℕ} (assignment : PaperAssignment G n) :
    PaperVisibleTuple n D.coveredColRoles :=
  paperAssignmentRestriction D.coveredColRoles
    (paperAssignmentRestriction
      (coveredRoles G.isolatedMiddleRoles) assignment)

/-- The selected ordering edges, transported across the definitional equality
between the paper shape and its underlying partite shape. -/
def paperCertificateOrderingEdges
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate) :
    Finset (Fin G.edges) :=
  certificate.paths.orderingEdges

/-- The raw paper terminal stage after the distinguished ordering edges have
been moved to row/column coordinates.  Only the complementary shape edges
remain random. -/
def paperPartialNCKRawTerminalMatrix
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    Matrix (PaperVisibleTuple n D.coveredRowRoles)
      (PaperVisibleTuple n D.coveredColRoles) ℝ :=
  paperYThroughCoordinates G n orientation
    (Finset.univ \ paperCertificateOrderingEdges G certificate) w
    (paperIntermediateCoveredRowMap G certificate D)
    (paperIntermediateCoveredColMap G certificate D)

/-- The terminal stage with the flattened-coordinate gauge factors restored.
This has the same concrete coordinate maps as the raw paper terminal stage. -/
def paperPartialNCKGaugeTerminalMatrix
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) (coupled : PaperNoise n) :
    Matrix (PaperVisibleTuple n D.coveredRowRoles)
      (PaperVisibleTuple n D.coveredColRoles) ℝ :=
  paperGaugeTwistedYThroughCoordinates G n orientation
    (Finset.univ \ paperCertificateOrderingEdges G certificate)
    (paperCertificateOrderingEdges G certificate) decoupled coupled
    (paperIntermediateCoveredRowMap G certificate D)
    (paperIntermediateCoveredColMap G certificate D)

/-- The diagonal gauge-twisted terminal stage is definitionally the older
full-noise marginalized intermediate matrix, entry by entry. -/
theorem paperPartialNCKGaugeTerminalMatrix_diagonal_eq_intermediate
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
        (paperDiagonalDecoupledNoise G w) w =
      paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w := by
  classical
  ext row col
  unfold paperPartialNCKGaugeTerminalMatrix
    paperGaugeTwistedYThroughCoordinates
    paperIntermediateMarginalizedOrientedMatrix
    paperOrientedMatrixThroughCoveredCoordinates
    paperIntermediateCoveredRowMap paperIntermediateCoveredColMap
  apply Finset.sum_congr rfl
  intro assignment _
  by_cases hEntry :
      paperAssignmentRestriction D.coveredRowRoles
            (paperAssignmentRestriction
              (coveredRoles G.isolatedMiddleRoles) assignment) = row ∧
        paperAssignmentRestriction D.coveredColRoles
            (paperAssignmentRestriction
              (coveredRoles G.isolatedMiddleRoles) assignment) = col
  · simp only [if_pos hEntry]
    rw [paper_complement_mul_flattenedGauge_eq_fullNoise]
    rfl
  · simp only [if_neg hEntry]

/-- Norm form of the coupled order-zero endpoint identity. -/
theorem norm_paperDecoupledOrientedGraphMatrix_diagonal
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖paperDecoupledOrientedGraphMatrix G n orientation
        (paperDiagonalDecoupledNoise G w)‖ =
      ‖paperOrientedGraphMatrix G n orientation w‖ := by
  rw [paperDecoupledOrientedGraphMatrix_diagonal_eq]

/-- The literal empty-edge-coordinate stage, after its explicit reindexing,
has exactly the coupled oriented endpoint norm on diagonal noise. -/
theorem norm_reindex_paperYMatrix_empty_diagonal
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖Matrix.reindex (paperYEmptyRowEquiv G n) (paperYEmptyColEquiv G n)
        (paperYMatrix G n orientation ∅ ∅
          (paperDiagonalDecoupledNoise G w))‖ =
      ‖paperOrientedGraphMatrix G n orientation w‖ := by
  rw [paperYMatrix_empty_reindex_eq_decoupled,
    paperDecoupledOrientedGraphMatrix_diagonal_eq]

/-- Norm form of the terminal gauge endpoint identity. -/
theorem norm_paperPartialNCKGaugeTerminalMatrix_diagonal
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
        (paperDiagonalDecoupledNoise G w) w‖ =
      ‖paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w‖ := by
  rw [paperPartialNCKGaugeTerminalMatrix_diagonal_eq_intermediate]

#print axioms paperDecoupledOrientedGraphMatrix_diagonal_eq
#print axioms paperYMatrix_empty_reindex_eq_decoupled
#print axioms paperOrderingEdgePrefix_card_eq_all
#print axioms paperPartialNCKStage_edges_union_at_card
#print axioms paperPartialNCKRawStageNorm_nonneg
#print axioms paper_complement_mul_flattenedGauge_eq_fullNoise
#print axioms paperPartialNCKGaugeTerminalMatrix_diagonal_eq_intermediate
#print axioms norm_paperDecoupledOrientedGraphMatrix_diagonal
#print axioms norm_reindex_paperYMatrix_empty_diagonal
#print axioms norm_paperPartialNCKGaugeTerminalMatrix_diagonal

end GraphMatrixReplica
