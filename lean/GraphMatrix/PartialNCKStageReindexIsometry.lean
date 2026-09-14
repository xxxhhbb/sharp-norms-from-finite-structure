import GraphMatrix.PartialNCKAlgebraicReindexProof

/-! # Literal successor-stage reindexing

The new edge coordinate at a partial-NCK successor stage is split off from
the finite function block in the row or column index.  This file makes that
finite equivalence explicit and proves that the resulting matrix reindexing
preserves the `ℓ₂` operator norm.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-! ## Operator norm under finite reindexing -/

/-- Reindexing both axes by finite equivalences preserves the matrix
`ℓ₂` operator norm. -/
theorem paper_l2_opNorm_reindex
    {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    (er : m ≃ m') (ec : n ≃ n') (A : Matrix m n ℝ) :
    ‖Matrix.reindex er ec A‖ = ‖A‖ := by
  classical
  let rowIso : EuclideanSpace ℝ m ≃ₗᵢ[ℝ] EuclideanSpace ℝ m' :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ er
  let colIso : EuclideanSpace ℝ n' ≃ₗᵢ[ℝ] EuclideanSpace ℝ n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ec.symm
  let TA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := m) (n := n)).trans
      LinearMap.toContinuousLinearMap) A
  let TR : EuclideanSpace ℝ n' →L[ℝ] EuclideanSpace ℝ m' :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := m') (n := n')).trans
      LinearMap.toContinuousLinearMap) (Matrix.reindex er ec A)
  have hmap : TR = (rowIso : EuclideanSpace ℝ m →L[ℝ] EuclideanSpace ℝ m').comp
      (TA.comp (colIso : EuclideanSpace ℝ n' →L[ℝ] EuclideanSpace ℝ n)) := by
    ext x i
    simp only [TR, TA, rowIso, colIso, ContinuousLinearMap.comp_apply]
    change (∑ j, A (er.symm i) (ec.symm j) * x j) =
      ∑ j, A (er.symm i) j * x (ec j)
    exact Fintype.sum_equiv ec.symm _ _ (fun _ => by simp)
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  change ‖TR‖ = ‖TA‖
  rw [hmap, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-! ## Splitting one inserted coordinate -/

/-- A function on `insert e S` is a function on `S`, together with its
distinguished value at `e`. -/
def paperPiInsertEquiv
    {α β : Type*} [DecidableEq α]
    (S : Finset α) (e : α) (he : e ∉ S) :
    ({x : α // x ∈ insert e S} → β) ≃
      (({x : α // x ∈ S} → β) × β) where
  toFun f :=
    (fun x => f ⟨x.1, Finset.mem_insert_of_mem x.2⟩,
      f ⟨e, Finset.mem_insert_self e S⟩)
  invFun g x := if hx : x.1 = e then g.2 else
    g.1 ⟨x.1, (Finset.mem_insert.mp x.2).resolve_left hx⟩
  left_inv f := by
    funext x
    by_cases hx : x.1 = e
    · simp only [hx, ↓reduceDIte]
      congr 1
      exact Subtype.ext hx.symm
    · simp [hx]
  right_inv g := by
    apply Prod.ext
    · funext x
      have hx : x.1 ≠ e := fun h => he (h ▸ x.2)
      simp [hx]
    · simp

/-- The literal row index after inserting one edge, written as the old row
index times the new ordered-pair coordinate. -/
def paperYRowInsertEquiv
    (G : PaperShape) (n : ℕ) (R : Finset (Fin G.edges))
    (e : Fin G.edges) (he : e ∉ R) :
    PaperYRowIndex G n (insert e R) ≃
      PaperYRowIndex G n R × (Fin n × Fin n) :=
  (Equiv.prodCongr (Equiv.refl (PaperRow G n))
      (paperPiInsertEquiv R e he)).trans
    (Equiv.prodAssoc (PaperRow G n)
      ({x : Fin G.edges // x ∈ R} → Fin n × Fin n)
      (Fin n × Fin n)).symm

/-- Column analogue of `paperYRowInsertEquiv`. -/
def paperYColInsertEquiv
    (G : PaperShape) (n : ℕ) (C : Finset (Fin G.edges))
    (e : Fin G.edges) (he : e ∉ C) :
    PaperYColIndex G n (insert e C) ≃
      PaperYColIndex G n C × (Fin n × Fin n) :=
  (Equiv.prodCongr (Equiv.refl (PaperCol G n))
      (paperPiInsertEquiv C e he)).trans
    (Equiv.prodAssoc (PaperCol G n)
      ({x : Fin G.edges // x ∈ C} → Fin n × Fin n)
      (Fin n × Fin n)).symm

@[simp]
theorem paperYRowInsertEquiv_coordinate
    (G : PaperShape) (n : ℕ) (R : Finset (Fin G.edges))
    (e : Fin G.edges) (he : e ∉ R) (a : PaperAssignment G n) :
    paperYRowInsertEquiv G n R e he
        (paperYRowCoordinate G (insert e R) a) =
      (paperYRowCoordinate G R a, paperAssignmentEdgeCoordinate G a e) := by
  rfl

@[simp]
theorem paperYColInsertEquiv_coordinate
    (G : PaperShape) (n : ℕ) (C : Finset (Fin G.edges))
    (e : Fin G.edges) (he : e ∉ C) (a : PaperAssignment G n) :
    paperYColInsertEquiv G n C e he
        (paperYColCoordinate G (insert e C) a) =
      (paperYColCoordinate G C a, paperAssignmentEdgeCoordinate G a e) := by
  rfl

/-! ## Entrywise successor identities -/

/-- The coefficient block attached to an arbitrary edge outside the old
row/column coordinate sets. -/
def paperStageCoefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (R C : Finset (Fin G.edges)) (e : Fin G.edges)
    (w : PaperDecoupledNoise G n) (a b : Fin n) :
    Matrix (PaperYRowIndex G n R) (PaperYColIndex G n C) ℝ := by
  classical
  exact fun row col =>
    ∑ assignment : PaperAssignment G n,
      if paperYRowCoordinate G R assignment = row ∧
          paperYColCoordinate G C assignment = col ∧
          assignment (G.source e) = a ∧ assignment (G.target e) = b then
        paperOrientedAssignmentWeight G orientation assignment *
          paperDecoupledNoiseProductOn G
            ((Finset.univ \ (R ∪ C)).erase e) w assignment
      else 0

/-- Moving `e` into the row-coordinate set is exactly row flattening of its
coefficient family, after the explicit finite reindexing above. -/
theorem paperYMatrix_insertRow_reindex
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (R C : Finset (Fin G.edges)) (e : Fin G.edges)
    (heR : e ∉ R) (_heC : e ∉ C) (w : PaperDecoupledNoise G n) :
    Matrix.reindex (paperYRowInsertEquiv G n R e heR)
        (Equiv.refl (PaperYColIndex G n C))
        (paperYMatrix G n orientation (insert e R) C w) =
      paperMatrixRademacherRowFlattening
        (paperStageCoefficient G n orientation R C e) w := by
  classical
  have hNoise :
      Finset.univ \ (insert e R ∪ C) =
        (Finset.univ \ (R ∪ C)).erase e := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    tauto
  ext row col
  simp only [Matrix.reindex_apply, Equiv.refl_symm]
  unfold paperYMatrix paperYThroughCoordinates
    paperMatrixRademacherRowFlattening paperStageCoefficient
  rw [hNoise]
  apply Finset.sum_congr rfl
  intro assignment _ha
  have hRow :
      paperYRowCoordinate G (insert e R) assignment =
          (paperYRowInsertEquiv G n R e heR).symm row ↔
        paperYRowCoordinate G R assignment = row.1 ∧
          paperAssignmentEdgeCoordinate G assignment e = row.2 := by
    rw [← (paperYRowInsertEquiv G n R e heR).apply_eq_iff_eq]
    simp only [Equiv.apply_symm_apply, paperYRowInsertEquiv_coordinate,
      Prod.ext_iff]
  simp only [hRow, paperAssignmentEdgeCoordinate, Prod.ext_iff,
    Equiv.refl_apply]
  congr 1
  apply propext
  tauto

/-- Column counterpart of `paperYMatrix_insertRow_reindex`. -/
theorem paperYMatrix_insertCol_reindex
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (R C : Finset (Fin G.edges)) (e : Fin G.edges)
    (_heR : e ∉ R) (heC : e ∉ C) (w : PaperDecoupledNoise G n) :
    Matrix.reindex (Equiv.refl (PaperYRowIndex G n R))
        (paperYColInsertEquiv G n C e heC)
        (paperYMatrix G n orientation R (insert e C) w) =
      paperMatrixRademacherColFlattening
        (paperStageCoefficient G n orientation R C e) w := by
  classical
  have hNoise :
      Finset.univ \ (R ∪ insert e C) =
        (Finset.univ \ (R ∪ C)).erase e := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    tauto
  ext row col
  simp only [Matrix.reindex_apply, Equiv.refl_symm]
  unfold paperYMatrix paperYThroughCoordinates
    paperMatrixRademacherColFlattening paperStageCoefficient
  rw [hNoise]
  apply Finset.sum_congr rfl
  intro assignment _ha
  have hCol :
      paperYColCoordinate G (insert e C) assignment =
          (paperYColInsertEquiv G n C e heC).symm col ↔
        paperYColCoordinate G C assignment = col.1 ∧
          paperAssignmentEdgeCoordinate G assignment e = col.2 := by
    rw [← (paperYColInsertEquiv G n C e heC).apply_eq_iff_eq]
    simp only [Equiv.apply_symm_apply, paperYColInsertEquiv_coordinate,
      Prod.ext_iff]
  simp only [hCol, paperAssignmentEdgeCoordinate, Prod.ext_iff,
    Equiv.refl_apply]

/-! ## The concrete unconditional stages -/

/-- The generic coefficient just defined specializes definitionally to the
coefficient used by the unconditional stage decomposition. -/
theorem paperUnconditionalStageRademacherCoefficient_eq_stageCoefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G) :
    paperUnconditionalStageRademacherCoefficient G n orientation i hi =
      paperStageCoefficient G n orientation
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i)
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i)
        (paperUnconditionalOrderingEdgeAt G i hi) := by
  rfl

/-- The previously isolated successor-stage norm reindex is unconditional:
the literal new coordinate and the NCK coefficient block differ only by a
finite row or column equivalence. -/
theorem paperPartialNCKStageFlatteningNormReindex_unconditional
    (G : PaperShape) (n : ℕ) :
    PaperPartialNCKStageFlatteningNormReindex G n := by
  classical
  intro orientation i hi
  let R := paperPartialNCKStageRowEdges G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) i
  let C := paperPartialNCKStageColEdges G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) i
  let e := paperUnconditionalOrderingEdgeAt G i hi
  have heNoise : e ∈ paperUnconditionalStageNoiseEdges G orientation i := by
    exact paperUnconditionalOrderingEdgeAt_mem_stageNoiseEdges G orientation i hi
  have heR : e ∉ R := by
    intro he
    have : e ∈ R ∪ C := Finset.mem_union_left C he
    exact (Finset.mem_sdiff.mp heNoise).2 this
  have heC : e ∉ C := by
    intro he
    have : e ∈ R ∪ C := Finset.mem_union_right R he
    exact (Finset.mem_sdiff.mp heNoise).2 this
  constructor
  · intro hSide w
    unfold paperUnconditionalPartialNCKStageMatrix paperPartialNCKStageMatrix
    rw [paperUnconditionalStageRowEdges_succ_of_side_false
      G orientation i hi hSide,
      paperUnconditionalStageColEdges_succ_of_side_false
      G orientation i hi hSide]
    change ‖paperYMatrix G n orientation (insert e R) C w‖ = _
    have hMatrix := paperYMatrix_insertRow_reindex
      G n orientation R C e heR heC w
    have hNorm := paper_l2_opNorm_reindex
      (paperYRowInsertEquiv G n R e heR)
      (Equiv.refl (PaperYColIndex G n C))
      (paperYMatrix G n orientation (insert e R) C w)
    calc
      ‖paperYMatrix G n orientation (insert e R) C w‖ =
          ‖Matrix.reindex (paperYRowInsertEquiv G n R e heR)
            (Equiv.refl (PaperYColIndex G n C))
            (paperYMatrix G n orientation (insert e R) C w)‖ := hNorm.symm
      _ = ‖paperMatrixRademacherRowFlattening
          (paperStageCoefficient G n orientation R C e) w‖ :=
        congrArg norm hMatrix
      _ = ‖paperMatrixRademacherRowFlattening
          (paperUnconditionalStageRademacherCoefficient
            G n orientation i hi) w‖ := by
        rw [paperUnconditionalStageRademacherCoefficient_eq_stageCoefficient]
  · intro hSide w
    unfold paperUnconditionalPartialNCKStageMatrix paperPartialNCKStageMatrix
    rw [paperUnconditionalStageRowEdges_succ_of_side_true
      G orientation i hi hSide,
      paperUnconditionalStageColEdges_succ_of_side_true
      G orientation i hi hSide]
    change ‖paperYMatrix G n orientation R (insert e C) w‖ = _
    have hMatrix := paperYMatrix_insertCol_reindex
      G n orientation R C e heR heC w
    have hNorm := paper_l2_opNorm_reindex
      (Equiv.refl (PaperYRowIndex G n R))
      (paperYColInsertEquiv G n C e heC)
      (paperYMatrix G n orientation R (insert e C) w)
    calc
      ‖paperYMatrix G n orientation R (insert e C) w‖ =
          ‖Matrix.reindex (Equiv.refl (PaperYRowIndex G n R))
            (paperYColInsertEquiv G n C e heC)
            (paperYMatrix G n orientation R (insert e C) w)‖ := hNorm.symm
      _ = ‖paperMatrixRademacherColFlattening
          (paperStageCoefficient G n orientation R C e) w‖ :=
        congrArg norm hMatrix
      _ = ‖paperMatrixRademacherColFlattening
          (paperUnconditionalStageRademacherCoefficient
            G n orientation i hi) w‖ := by
        rw [paperUnconditionalStageRademacherCoefficient_eq_stageCoefficient]

/-- Canonical short name for the unconditional witness. -/
theorem paperPartialNCKStageFlatteningNormReindex
    (G : PaperShape) (n : ℕ) :
    PaperPartialNCKStageFlatteningNormReindex G n :=
  paperPartialNCKStageFlatteningNormReindex_unconditional G n


end GraphMatrixReplica
