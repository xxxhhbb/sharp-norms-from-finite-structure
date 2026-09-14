import R6.PaperPartialNCKRawTerminalBound

/-! # Final literal-stage coordinate compression

The literal formula-(10) coordinates repeat a role whenever it occurs in
several selected edges.  The raw terminal coordinates carry every visible
role once.  This file identifies the former with a zero-padded copy of the
latter and obtains the required operator-norm comparison.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-! ## A generic finite zero-padding lemma for embeddings -/

/-- Complete an embedding of finite coordinate types by the complement of
its range. -/
def paperEmbeddingSumComplEquiv {α β : Type*} (e : α ↪ β) :
    α ⊕ {b : β // b ∉ Set.range e} ≃ β := by
  classical
  letI : DecidablePred (Set.range e) := Classical.decPred _
  exact
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
      (Equiv.sumCompl (Set.range e))

@[simp] theorem paperEmbeddingSumComplEquiv_apply_inl
    {α β : Type*} (e : α ↪ β) (a : α) :
    paperEmbeddingSumComplEquiv e (Sum.inl a) = e a := by
  classical
  simp [paperEmbeddingSumComplEquiv, Equiv.sumCompl]

@[simp] theorem paperEmbeddingSumComplEquiv_apply_inr
    {α β : Type*} (e : α ↪ β) (b : {b : β // b ∉ Set.range e}) :
    paperEmbeddingSumComplEquiv e (Sum.inr b) = b.1 := by
  classical
  simp [paperEmbeddingSumComplEquiv, Equiv.sumCompl]

/-- A matrix supported on the ranges of two embeddings is a finite
zero-padding of its compressed matrix, hence its L2 operator norm cannot be
larger. -/
theorem paper_l2_opNorm_le_of_embedded_support
    {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    (er : m ↪ m') (ec : n ↪ n')
    (A : Matrix m n ℝ) (B : Matrix m' n' ℝ)
    (hmain : ∀ i j, B (er i) (ec j) = A i j)
    (hrow : ∀ i, i ∉ Set.range er → ∀ j, B i j = 0)
    (hcol : ∀ j, j ∉ Set.range ec → ∀ i, B i j = 0) :
    ‖B‖ ≤ ‖A‖ := by
  classical
  let rowEquiv := paperEmbeddingSumComplEquiv er
  let colEquiv := paperEmbeddingSumComplEquiv ec
  have hMatrix :
      Matrix.reindex rowEquiv.symm colEquiv.symm B =
        Matrix.fromBlocks A 0 0 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simpa [rowEquiv, colEquiv, Matrix.reindex, Matrix.fromBlocks] using
        hmain i j
    · simpa [rowEquiv, colEquiv, Matrix.reindex, Matrix.fromBlocks] using
        hcol j.1 j.2 (er i)
    · simpa [rowEquiv, colEquiv, Matrix.reindex, Matrix.fromBlocks] using
        hrow i.1 i.2 (ec j)
    · simpa [rowEquiv, colEquiv, Matrix.reindex, Matrix.fromBlocks] using
        hrow i.1 i.2 j.1
  have hReindex := paper_l2_opNorm_reindex rowEquiv.symm colEquiv.symm B
  rw [hMatrix] at hReindex
  rw [← hReindex]
  exact paper_l2_opNorm_fromBlocks_zero_le A

/-! ## Canonical terminal coordinate embeddings -/

variable (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)

abbrev PaperFinalStageRowEdges : Finset (Fin G.edges) :=
  paperPartialNCKStageRowEdges G certificate D
    (paperSelectedOrderingEdges G certificate).card

abbrev PaperFinalStageColEdges : Finset (Fin G.edges) :=
  paperPartialNCKStageColEdges G certificate D
    (paperSelectedOrderingEdges G certificate).card

theorem mem_intermediateRowRoles_iff (v : Fin G.toPartiteShape.roles) :
    v ∈ D.rowRoles ↔
      v ∈ G.toPartiteShape.leftBoundary ∨
        ∃ (e : Fin G.toPartiteShape.edges),
          (∃ he : e ∈ certificate.paths.orderingEdges,
            D.edgeSide ⟨e, he⟩ = false) ∧
          G.toPartiteShape.EdgeIncident e v := by
  classical
  unfold PartiteShape.IntermediateFlatteningRoleSides.rowRoles
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  aesop

theorem mem_intermediateColRoles_iff (v : Fin G.toPartiteShape.roles) :
    v ∈ D.colRoles ↔
      v ∈ G.toPartiteShape.rightBoundary ∨
        ∃ (e : Fin G.toPartiteShape.edges),
          (∃ he : e ∈ certificate.paths.orderingEdges,
            D.edgeSide ⟨e, he⟩ = true) ∧
          G.toPartiteShape.EdgeIncident e v := by
  classical
  unfold PartiteShape.IntermediateFlatteningRoleSides.colRoles
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  aesop

theorem mem_paperFinalStageRowEdges_iff (e : Fin G.edges) :
    e ∈ PaperFinalStageRowEdges G certificate D ↔
      ∃ he : e ∈ paperSelectedOrderingEdges G certificate,
        paperSelectedEdgeSide G certificate D ⟨e, he⟩ = false := by
  classical
  simp only [PaperFinalStageRowEdges, paperPartialNCKStageRowEdges,
    paperOrderingEdgePrefix_card_eq_all, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    rcases h with ⟨he, hSide⟩
    exact ⟨he, ⟨he, hSide⟩⟩

theorem mem_paperFinalStageColEdges_iff (e : Fin G.edges) :
    e ∈ PaperFinalStageColEdges G certificate D ↔
      ∃ he : e ∈ paperSelectedOrderingEdges G certificate,
        paperSelectedEdgeSide G certificate D ⟨e, he⟩ = true := by
  classical
  simp only [PaperFinalStageColEdges, paperPartialNCKStageColEdges,
    paperOrderingEdgePrefix_card_eq_all, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    rcases h with ⟨he, hSide⟩
    exact ⟨he, ⟨he, hSide⟩⟩

/-- A left-boundary occurrence regarded as a covered row-role coordinate. -/
def paperTerminalLeftBoundaryIndex (i : Fin G.leftSize) :
    {v : PaperCoveredRole G // v ∈ D.coveredRowRoles} := by
  classical
  have hLeft : G.left i ∈ G.toPartiteShape.leftBoundary := by
    exact (G.mem_leftBoundaryFinset_iff (G.left i)).2 ⟨i, rfl⟩
  have hRow : G.left i ∈ D.rowRoles := D.leftBoundary_subset_rowRoles hLeft
  refine ⟨⟨G.left i, D.rowRoles_subset_coveredRoles hRow⟩, ?_⟩
  unfold PartiteShape.IntermediateFlatteningRoleSides.coveredRowRoles
  apply Finset.mem_map.2
  exact ⟨⟨G.left i, hRow⟩, Finset.mem_attach _ _, rfl⟩

/-- A right-boundary occurrence regarded as a covered column-role
coordinate. -/
def paperTerminalRightBoundaryIndex (i : Fin G.rightSize) :
    {v : PaperCoveredRole G // v ∈ D.coveredColRoles} := by
  classical
  have hRight : G.right i ∈ G.toPartiteShape.rightBoundary := by
    exact (G.mem_rightBoundaryFinset_iff (G.right i)).2 ⟨i, rfl⟩
  have hCol : G.right i ∈ D.colRoles := D.rightBoundary_subset_colRoles hRight
  refine ⟨⟨G.right i, D.colRoles_subset_coveredRoles hCol⟩, ?_⟩
  unfold PartiteShape.IntermediateFlatteningRoleSides.coveredColRoles
  apply Finset.mem_map.2
  exact ⟨⟨G.right i, hCol⟩, Finset.mem_attach _ _, rfl⟩

/-- Encode a duplicate-free covered row tuple in the literal terminal row
coordinates.  Repeated edge endpoints read the same tuple coordinate. -/
def paperFinalRawRowIndex {n : ℕ}
    (row : PaperVisibleTuple n D.coveredRowRoles) :
    PaperYRowIndex G n (PaperFinalStageRowEdges G certificate D) :=
  (fun i => row (paperTerminalLeftBoundaryIndex G certificate D i),
    fun e => by
      let h := (mem_paperFinalStageRowEdges_iff G certificate D e.1).1 e.2
      exact
        (row (paperTerminalRowSourceIndex G certificate D
            ⟨e.1, h.choose⟩ h.choose_spec),
          row (paperTerminalRowTargetIndex G certificate D
            ⟨e.1, h.choose⟩ h.choose_spec)))

/-- Encode a duplicate-free covered column tuple in the literal terminal
column coordinates. -/
def paperFinalRawColIndex {n : ℕ}
    (col : PaperVisibleTuple n D.coveredColRoles) :
    PaperYColIndex G n (PaperFinalStageColEdges G certificate D) :=
  (fun i => col (paperTerminalRightBoundaryIndex G certificate D i),
    fun e => by
      let h := (mem_paperFinalStageColEdges_iff G certificate D e.1).1 e.2
      exact
        (col (paperTerminalColSourceIndex G certificate D
            ⟨e.1, h.choose⟩ h.choose_spec),
          col (paperTerminalColTargetIndex G certificate D
            ⟨e.1, h.choose⟩ h.choose_spec)))

/-- Every assignment's literal final row coordinate is its covered row tuple
encoded with the preceding consistency map. -/
theorem paperFinalRawRowIndex_intermediateMap {n : ℕ}
    (assignment : PaperAssignment G n) :
    paperFinalRawRowIndex G certificate D
        (paperIntermediateCoveredRowMap G certificate D assignment) =
      paperYRowCoordinate G (PaperFinalStageRowEdges G certificate D)
        assignment := by
  classical
  apply Prod.ext
  · funext i
    rfl
  · funext e
    apply Prod.ext <;> rfl

/-- Column counterpart of `paperFinalRawRowIndex_intermediateMap`. -/
theorem paperFinalRawColIndex_intermediateMap {n : ℕ}
    (assignment : PaperAssignment G n) :
    paperFinalRawColIndex G certificate D
        (paperIntermediateCoveredColMap G certificate D assignment) =
      paperYColCoordinate G (PaperFinalStageColEdges G certificate D)
        assignment := by
  classical
  apply Prod.ext
  · funext i
    rfl
  · funext e
    apply Prod.ext <;> rfl

theorem paperFinalRawRowIndex_injective {n : ℕ} :
    Function.Injective (paperFinalRawRowIndex G certificate D (n := n)) := by
  classical
  intro row₁ row₂ h
  funext x
  have hRow : x.1.1 ∈ D.rowRoles := by
    unfold PartiteShape.IntermediateFlatteningRoleSides.coveredRowRoles at x
    obtain ⟨v, _hv, hvx⟩ := Finset.mem_map.1 x.2
    have hval : v.1 = x.1.1 := by
      exact congrArg (fun z : PaperCoveredRole G => z.1) hvx
    simpa [hval] using v.2
  have hRow' : x.1.1 ∈ G.toPartiteShape.leftBoundary ∨
      ∃ (e : Fin G.edges),
        (∃ he : e ∈ certificate.paths.orderingEdges,
          D.edgeSide ⟨e, he⟩ = false) ∧
        G.toPartiteShape.EdgeIncident e x.1.1 :=
    (mem_intermediateRowRoles_iff G certificate D x.1.1).1 hRow
  clear hRow
  rcases hRow' with hLeft | ⟨e, ⟨he, hSide⟩, hIncident⟩
  · obtain ⟨i, hi⟩ := (G.mem_leftBoundaryFinset_iff x.1.1).1 hLeft
    have hx : paperTerminalLeftBoundaryIndex G certificate D i = x := by
      apply Subtype.ext
      apply Subtype.ext
      exact hi
    have hAt := congrArg (fun z => z.1 i) h
    change row₁ (paperTerminalLeftBoundaryIndex G certificate D i) =
      row₂ (paperTerminalLeftBoundaryIndex G certificate D i) at hAt
    simpa [hx] using hAt
  · have heFinal : e ∈ PaperFinalStageRowEdges G certificate D :=
      (mem_paperFinalStageRowEdges_iff G certificate D e).2 ⟨he, hSide⟩
    let ef : {e : Fin G.edges //
        e ∈ PaperFinalStageRowEdges G certificate D} := ⟨e, heFinal⟩
    have hAt := congrArg (fun z => z.2 ef) h
    let hs := (mem_paperFinalStageRowEdges_iff G certificate D e).1 heFinal
    change
      (row₁ (paperTerminalRowSourceIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec),
        row₁ (paperTerminalRowTargetIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec)) =
      (row₂ (paperTerminalRowSourceIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec),
        row₂ (paperTerminalRowTargetIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec)) at hAt
    rcases hIncident with hSource | hTarget
    · have hx : paperTerminalRowSourceIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec = x := by
        apply Subtype.ext
        apply Subtype.ext
        exact hSource
      simpa [hx] using congrArg Prod.fst hAt
    · have hx : paperTerminalRowTargetIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec = x := by
        apply Subtype.ext
        apply Subtype.ext
        exact hTarget
      simpa [hx] using congrArg Prod.snd hAt

theorem paperFinalRawColIndex_injective {n : ℕ} :
    Function.Injective (paperFinalRawColIndex G certificate D (n := n)) := by
  classical
  intro col₁ col₂ h
  funext x
  have hCol : x.1.1 ∈ D.colRoles := by
    unfold PartiteShape.IntermediateFlatteningRoleSides.coveredColRoles at x
    obtain ⟨v, _hv, hvx⟩ := Finset.mem_map.1 x.2
    have hval : v.1 = x.1.1 := by
      exact congrArg (fun z : PaperCoveredRole G => z.1) hvx
    simpa [hval] using v.2
  have hCol' : x.1.1 ∈ G.toPartiteShape.rightBoundary ∨
      ∃ (e : Fin G.edges),
        (∃ he : e ∈ certificate.paths.orderingEdges,
          D.edgeSide ⟨e, he⟩ = true) ∧
        G.toPartiteShape.EdgeIncident e x.1.1 :=
    (mem_intermediateColRoles_iff G certificate D x.1.1).1 hCol
  clear hCol
  rcases hCol' with hRight | ⟨e, ⟨he, hSide⟩, hIncident⟩
  · obtain ⟨i, hi⟩ := (G.mem_rightBoundaryFinset_iff x.1.1).1 hRight
    have hx : paperTerminalRightBoundaryIndex G certificate D i = x := by
      apply Subtype.ext
      apply Subtype.ext
      exact hi
    have hAt := congrArg (fun z => z.1 i) h
    change col₁ (paperTerminalRightBoundaryIndex G certificate D i) =
      col₂ (paperTerminalRightBoundaryIndex G certificate D i) at hAt
    simpa [hx] using hAt
  · have heFinal : e ∈ PaperFinalStageColEdges G certificate D :=
      (mem_paperFinalStageColEdges_iff G certificate D e).2 ⟨he, hSide⟩
    let ef : {e : Fin G.edges //
        e ∈ PaperFinalStageColEdges G certificate D} := ⟨e, heFinal⟩
    have hAt := congrArg (fun z => z.2 ef) h
    let hs := (mem_paperFinalStageColEdges_iff G certificate D e).1 heFinal
    change
      (col₁ (paperTerminalColSourceIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec),
        col₁ (paperTerminalColTargetIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec)) =
      (col₂ (paperTerminalColSourceIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec),
        col₂ (paperTerminalColTargetIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec)) at hAt
    rcases hIncident with hSource | hTarget
    · have hx : paperTerminalColSourceIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec = x := by
        apply Subtype.ext
        apply Subtype.ext
        exact hSource
      simpa [hx] using congrArg Prod.fst hAt
    · have hx : paperTerminalColTargetIndex G certificate D
          ⟨e, hs.choose⟩ hs.choose_spec = x := by
        apply Subtype.ext
        apply Subtype.ext
        exact hTarget
      simpa [hx] using congrArg Prod.snd hAt

def paperFinalRawRowEmbedding {n : ℕ} :
    PaperVisibleTuple n D.coveredRowRoles ↪
      PaperYRowIndex G n (PaperFinalStageRowEdges G certificate D) where
  toFun := paperFinalRawRowIndex G certificate D
  inj' := paperFinalRawRowIndex_injective G certificate D

def paperFinalRawColEmbedding {n : ℕ} :
    PaperVisibleTuple n D.coveredColRoles ↪
      PaperYColIndex G n (PaperFinalStageColEdges G certificate D) where
  toFun := paperFinalRawColIndex G certificate D
  inj' := paperFinalRawColIndex_injective G certificate D

@[simp] theorem paperFinalRawRowEmbedding_apply {n : ℕ}
    (row : PaperVisibleTuple n D.coveredRowRoles) :
    paperFinalRawRowEmbedding G certificate D row =
      paperFinalRawRowIndex G certificate D row := rfl

@[simp] theorem paperFinalRawColEmbedding_apply {n : ℕ}
    (col : PaperVisibleTuple n D.coveredColRoles) :
    paperFinalRawColEmbedding G certificate D col =
      paperFinalRawColIndex G certificate D col := rfl

/-! ## The literal matrix is supported on the consistent coordinates -/

theorem paperFinalLiteral_apply_rawEmbeddings
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n)
    (row : PaperVisibleTuple n D.coveredRowRoles)
    (col : PaperVisibleTuple n D.coveredColRoles) :
    paperPartialNCKStageMatrix G certificate D n orientation
        (paperSelectedOrderingEdges G certificate).card w
        (paperFinalRawRowEmbedding G certificate D row)
        (paperFinalRawColEmbedding G certificate D col) =
      paperPartialNCKRawTerminalMatrix G certificate D n orientation w
        row col := by
  classical
  unfold paperPartialNCKStageMatrix paperYMatrix
    paperPartialNCKRawTerminalMatrix paperYThroughCoordinates
  rw [paperPartialNCKStage_edges_union_at_card]
  apply Finset.sum_congr rfl
  intro assignment _ha
  have hRow :
      paperYRowCoordinate G (PaperFinalStageRowEdges G certificate D)
          assignment = paperFinalRawRowIndex G certificate D row ↔
        paperIntermediateCoveredRowMap G certificate D assignment = row := by
    rw [← paperFinalRawRowIndex_intermediateMap G certificate D assignment]
    exact (paperFinalRawRowIndex_injective G certificate D).eq_iff
  have hCol :
      paperYColCoordinate G (PaperFinalStageColEdges G certificate D)
          assignment = paperFinalRawColIndex G certificate D col ↔
        paperIntermediateCoveredColMap G certificate D assignment = col := by
    rw [← paperFinalRawColIndex_intermediateMap G certificate D assignment]
    exact (paperFinalRawColIndex_injective G certificate D).eq_iff
  rw [paperFinalRawRowEmbedding_apply, paperFinalRawColEmbedding_apply]
  have hRowActual :
      paperYRowCoordinate G
            (paperPartialNCKStageRowEdges G certificate D
              (paperSelectedOrderingEdges G certificate).card) assignment =
          paperFinalRawRowIndex G certificate D row ↔
        paperIntermediateCoveredRowMap G certificate D assignment = row := hRow
  have hColActual :
      paperYColCoordinate G
            (paperPartialNCKStageColEdges G certificate D
              (paperSelectedOrderingEdges G certificate).card) assignment =
          paperFinalRawColIndex G certificate D col ↔
        paperIntermediateCoveredColMap G certificate D assignment = col := hCol
  by_cases hLiteral :
      paperYRowCoordinate G
            (paperPartialNCKStageRowEdges G certificate D
              (paperSelectedOrderingEdges G certificate).card) assignment =
          paperFinalRawRowIndex G certificate D row ∧
        paperYColCoordinate G
            (paperPartialNCKStageColEdges G certificate D
              (paperSelectedOrderingEdges G certificate).card) assignment =
          paperFinalRawColIndex G certificate D col
  · have hRaw :
        paperIntermediateCoveredRowMap G certificate D assignment = row ∧
          paperIntermediateCoveredColMap G certificate D assignment = col :=
      ⟨hRowActual.1 hLiteral.1, hColActual.1 hLiteral.2⟩
    rw [if_pos hLiteral, if_pos hRaw]
    rfl
  · have hRaw : ¬
        (paperIntermediateCoveredRowMap G certificate D assignment = row ∧
          paperIntermediateCoveredColMap G certificate D assignment = col) := by
      intro hRaw
      exact hLiteral ⟨hRowActual.2 hRaw.1, hColActual.2 hRaw.2⟩
    rw [if_neg hLiteral, if_neg hRaw]

theorem paperFinalLiteral_zero_off_rowRange
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n)
    (row : PaperYRowIndex G n (PaperFinalStageRowEdges G certificate D))
    (hrow : row ∉ Set.range (paperFinalRawRowEmbedding G certificate D))
    (col : PaperYColIndex G n (PaperFinalStageColEdges G certificate D)) :
    paperPartialNCKStageMatrix G certificate D n orientation
        (paperSelectedOrderingEdges G certificate).card w row col = 0 := by
  classical
  unfold paperPartialNCKStageMatrix paperYMatrix paperYThroughCoordinates
  apply Finset.sum_eq_zero
  intro assignment _ha
  by_cases hCoordinates :
      paperYRowCoordinate G (PaperFinalStageRowEdges G certificate D)
            assignment = row ∧
        paperYColCoordinate G (PaperFinalStageColEdges G certificate D)
            assignment = col
  · exfalso
    apply hrow
    refine ⟨paperIntermediateCoveredRowMap G certificate D assignment, ?_⟩
    exact (paperFinalRawRowIndex_intermediateMap G certificate D assignment).trans
      hCoordinates.1
  · simp [hCoordinates]

theorem paperFinalLiteral_zero_off_colRange
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n)
    (col : PaperYColIndex G n (PaperFinalStageColEdges G certificate D))
    (hcol : col ∉ Set.range (paperFinalRawColEmbedding G certificate D))
    (row : PaperYRowIndex G n (PaperFinalStageRowEdges G certificate D)) :
    paperPartialNCKStageMatrix G certificate D n orientation
        (paperSelectedOrderingEdges G certificate).card w row col = 0 := by
  classical
  unfold paperPartialNCKStageMatrix paperYMatrix paperYThroughCoordinates
  apply Finset.sum_eq_zero
  intro assignment _ha
  by_cases hCoordinates :
      paperYRowCoordinate G (PaperFinalStageRowEdges G certificate D)
            assignment = row ∧
        paperYColCoordinate G (PaperFinalStageColEdges G certificate D)
            assignment = col
  · exfalso
    apply hcol
    refine ⟨paperIntermediateCoveredColMap G certificate D assignment, ?_⟩
    exact (paperFinalRawColIndex_intermediateMap G certificate D assignment).trans
      hCoordinates.2
  · simp [hCoordinates]

/-- The literal final stage is exactly a zero-padding of the raw terminal
matrix, in the norm direction needed by the moment iteration. -/
theorem paperPartialNCKFinalLiteralNorm_le_rawTerminal
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    paperPartialNCKRawStageNorm G certificate D n orientation w
        (paperSelectedOrderingEdges G certificate).card ≤
      ‖paperPartialNCKRawTerminalMatrix G certificate D n orientation w‖ := by
  unfold paperPartialNCKRawStageNorm
  apply paper_l2_opNorm_le_of_embedded_support
    (paperFinalRawRowEmbedding G certificate D)
    (paperFinalRawColEmbedding G certificate D)
  · exact paperFinalLiteral_apply_rawEmbeddings G certificate D orientation w
  · exact paperFinalLiteral_zero_off_rowRange G certificate D orientation w
  · exact paperFinalLiteral_zero_off_colRange G certificate D orientation w

/-! ## Unconditional canonical endpoint -/

/-- The terminal-coordinate compression interface is realized internally for
every paper shape and ambient dimension. -/
theorem paperFinalLiteralToRawTerminalNorm_unconditional
    (G : PaperShape) (n : ℕ) :
    PaperFinalLiteralToRawTerminalNorm G n := by
  intro orientation decoupled
  exact paperPartialNCKFinalLiteralNorm_le_rawTerminal G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) orientation decoupled

/-- Pointwise literal-final-stage formula-(21) bound, with the Menger
certificate, role sides, and coordinate compression all constructed
internally. -/
theorem paperUnconditionalFinalLiteralStage_squaredNorm_le_canonicalPower
    (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) :
    paperUnconditionalPartialNCKRawStageNorm G n orientation decoupled
        (paperUnconditionalOrderingLength G) ^ 2 ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
  calc
    paperUnconditionalPartialNCKRawStageNorm G n orientation decoupled
          (paperUnconditionalOrderingLength G) ^ 2 ≤
        ‖paperPartialNCKRawTerminalMatrix G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation)
          n orientation decoupled‖ ^ 2 := by
      exact pow_le_pow_left₀
        (paperUnconditionalPartialNCKRawStageNorm_nonneg G n orientation
          decoupled (paperUnconditionalOrderingLength G))
        (paperFinalLiteralToRawTerminalNorm_unconditional G n orientation
          decoupled) 2
    _ ≤ (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G :=
      paperUnconditionalRawTerminal_squaredNorm_le_canonicalPower
        G n hn orientation decoupled

/-- Mean literal-final-stage bound required to terminate the partial-NCK
iteration, now with no external coordinate-compression premise. -/
theorem paperUnconditionalFinalLiteralStage_mean_le_canonicalPower_unconditional
    (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) :
    paperUnconditionalDecoupledSquaredStageMean G n orientation
        (paperUnconditionalOrderingLength G) ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G :=
  paperUnconditionalFinalLiteralStage_mean_le_canonicalPower G n hn
    (paperFinalLiteralToRawTerminalNorm_unconditional G n) orientation

#print axioms paperEmbeddingSumComplEquiv
#print axioms paper_l2_opNorm_le_of_embedded_support
#print axioms paperFinalRawRowIndex_injective
#print axioms paperFinalRawColIndex_injective
#print axioms paperFinalLiteral_apply_rawEmbeddings
#print axioms paperPartialNCKFinalLiteralNorm_le_rawTerminal
#print axioms paperFinalLiteralToRawTerminalNorm_unconditional
#print axioms paperUnconditionalFinalLiteralStage_mean_le_canonicalPower_unconditional

end GraphMatrixReplica
