import GraphMatrix.PartialNCKOneStepReduction
import GraphMatrix.PartialNCKGaugeIsometry

/-! # Algebraic reindexing facts for the concrete partial-NCK stages

This file proves the pointwise diagonal terminal identity and constructs the
coefficient matrices for the actual edge exposed at a successor stage.  It
also records why the full terminal field of
`PaperPartialNCKAlgebraicReindex` is not merely a finite-product reindex in
the current model: its left side averages independent noise copies for the
unselected edges, whereas its right side uses one shared copy.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Rotate three finite sums.  Kept explicit to avoid asking the simplifier
to orient the symmetric `Finset.sum_comm` lemma. -/
private theorem paper_sum_rotate_three
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-- Collapse the unique ordered-pair summand selected by two equalities. -/
private theorem paper_sum_pair_indicator
    {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (a₀ : α) (b₀ : β) (f : α → β → ℝ) :
    (∑ a, ∑ b, if a₀ = a ∧ b₀ = b then f a b else 0) = f a₀ b₀ := by
  classical
  rw [Finset.sum_eq_single a₀]
  · rw [Finset.sum_eq_single b₀]
    · simp
    · intro b _hb hne
      rw [if_neg (fun h => hne h.2.symm)]
    · simp
  · intro a _ha hne
    apply Finset.sum_eq_zero
    intro b _hb
    rw [if_neg (fun h => hne h.1.symm)]
  · simp

/-! ## What the completed gauge isometry proves at the terminal endpoint -/

/-- On diagonal noise, the raw terminal matrix has exactly the norm of the
coupled marginalized terminal matrix.  This is the strongest pointwise
terminal equality furnished by the gauge isometry. -/
theorem norm_paperUnconditionalRawTerminal_diagonal_eq_intermediate
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperNoise n) :
    ‖paperPartialNCKRawTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation
        (paperDiagonalDecoupledNoise G w)‖ =
      ‖paperIntermediateMarginalizedOrientedMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation w‖ := by
  calc
    ‖paperPartialNCKRawTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation
        (paperDiagonalDecoupledNoise G w)‖ =
      ‖paperPartialNCKGaugeTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation
        (paperDiagonalDecoupledNoise G w) w‖ := by
          symm
          exact norm_paperPartialNCKGaugeTerminalMatrix_eq_raw G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation) orientation
            (paperDiagonalDecoupledNoise G w) w
    _ = ‖paperIntermediateMarginalizedOrientedMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation w‖ :=
      norm_paperUnconditionalGaugeTerminal_diagonal G n orientation w

/-- Mean form of the diagonal terminal identity.  Notice that the domain on
the left is still `PaperNoise n`, not the larger independent product
`PaperDecoupledNoise G n`. -/
theorem paperMean_norm_paperUnconditionalRawTerminal_diagonal_sq
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperMean (fun w : PaperNoise n =>
      ‖paperPartialNCKRawTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation
        (paperDiagonalDecoupledNoise G w)‖ ^ 2) =
      paperTheorem48AnalyticLedger G n orientation 0 := by
  rw [paperTheorem48AnalyticLedger_zero]
  apply congrArg paperMean
  funext w
  rw [norm_paperUnconditionalRawTerminal_diagonal_eq_intermediate]

/-! ## The actual coefficient family exposed at a successor stage -/

/-- The current unflattened noise set at canonical stage `i`. -/
def paperUnconditionalStageNoiseEdges
    (G : PaperShape) (orientation : Fin G.edges → Bool) (i : ℕ) :
    Finset (Fin G.edges) :=
  Finset.univ \ (paperPartialNCKStageRowEdges G
      G.unconditionalBoundaryCleanMengerCertificate
      (G.unconditionalIntermediateSides orientation) i ∪
    paperPartialNCKStageColEdges G
      G.unconditionalBoundaryCleanMengerCertificate
      (G.unconditionalIntermediateSides orientation) i)

/-- The edge added at stage `i+1` is genuinely present in the old random set
`Z`. -/
theorem paperUnconditionalOrderingEdgeAt_mem_stageNoiseEdges
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G) :
    paperUnconditionalOrderingEdgeAt G i hi ∈
      paperUnconditionalStageNoiseEdges G orientation i := by
  classical
  have hPrefix := paperUnconditionalOrderingEdgeAt_not_mem_prefix G i hi
  have hRow : paperUnconditionalOrderingEdgeAt G i hi ∉
      paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) i := by
    intro h
    exact hPrefix (Finset.mem_filter.mp h).1
  have hCol : paperUnconditionalOrderingEdgeAt G i hi ∉
      paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) i := by
    intro h
    exact hPrefix (Finset.mem_filter.mp h).1
  simp [paperUnconditionalStageNoiseEdges, hRow, hCol]

/-- Coefficient of the sign indexed by the ordered ambient pair `(a,b)` for
the actual new edge.  Its random product has that edge erased, so the family
is independent of the distinguished edge-noise coordinate. -/
def paperUnconditionalStageRademacherCoefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (a b : Fin n) :
    Matrix
      (PaperYRowIndex G n
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i))
      (PaperYColIndex G n
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i)) ℝ := by
  classical
  let R := paperPartialNCKStageRowEdges G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) i
  let C := paperPartialNCKStageColEdges G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) i
  let e := paperUnconditionalOrderingEdgeAt G i hi
  exact fun row col =>
    ∑ assignment : PaperAssignment G n,
      if paperYRowCoordinate G R assignment = row ∧
          paperYColCoordinate G C assignment = col ∧
          assignment (G.source e) = a ∧ assignment (G.target e) = b then
        paperOrientedAssignmentWeight G orientation assignment *
          paperDecoupledNoiseProductOn G
            ((Finset.univ \ (R ∪ C)).erase e) w assignment
      else 0

/-- The constructed coefficient family does not depend on the noise copy of
the edge being exposed. -/
theorem paperUnconditionalStageRademacherCoefficient_independent
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (ξ : PaperNoise n) (a b : Fin n) :
    paperUnconditionalStageRademacherCoefficient G n orientation i hi
        (Function.update w (paperUnconditionalOrderingEdgeAt G i hi) ξ) a b =
      paperUnconditionalStageRademacherCoefficient G n orientation i hi
        w a b := by
  classical
  ext row col
  unfold paperUnconditionalStageRademacherCoefficient
  apply Finset.sum_congr rfl
  intro assignment _ha
  split_ifs with hEntry
  · apply congrArg (fun x : ℝ =>
      paperOrientedAssignmentWeight G orientation assignment * x)
    unfold paperDecoupledNoiseProductOn
    apply Finset.prod_congr rfl
    intro e he
    have hne : e ≠ paperUnconditionalOrderingEdgeAt G i hi :=
      Finset.ne_of_mem_erase he
    rw [Function.update_of_ne hne]
  · rfl

/-- Erasing the exposed edge factors the old noise product into its sign and
the coefficient product. -/
theorem paperUnconditionalStageNoiseProduct_eq_sign_mul_erase
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (assignment : PaperAssignment G n) :
    paperDecoupledNoiseProductOn G
        (paperUnconditionalStageNoiseEdges G orientation i) w assignment =
      paperEdgeSign (w (paperUnconditionalOrderingEdgeAt G i hi))
          (assignment (G.source (paperUnconditionalOrderingEdgeAt G i hi)))
          (assignment (G.target (paperUnconditionalOrderingEdgeAt G i hi))) *
        paperDecoupledNoiseProductOn G
          ((paperUnconditionalStageNoiseEdges G orientation i).erase
            (paperUnconditionalOrderingEdgeAt G i hi)) w assignment := by
  classical
  unfold paperDecoupledNoiseProductOn
  rw [← Finset.mul_prod_erase _ _
    (paperUnconditionalOrderingEdgeAt_mem_stageNoiseEdges
      G orientation i hi)]

/-- Entrywise expansion of the actual old stage as the Rademacher sum of the
coefficient family obtained by erasing the newly exposed edge. -/
theorem paperUnconditionalPartialNCKStageMatrix_eq_rademacherSum
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    paperUnconditionalPartialNCKStageMatrix G n orientation i w =
      paperMatrixRademacherSum
        (paperUnconditionalOrderingEdgeAt G i hi)
        (paperUnconditionalStageRademacherCoefficient
          G n orientation i hi) w := by
  classical
  ext row col
  unfold paperUnconditionalPartialNCKStageMatrix
    paperPartialNCKStageMatrix paperYMatrix paperYThroughCoordinates
    paperMatrixRademacherSum
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  unfold paperUnconditionalStageRademacherCoefficient
  simp_rw [Finset.mul_sum]
  rw [paper_sum_rotate_three]
  apply Finset.sum_congr rfl
  intro assignment _hassignment
  by_cases hEntry :
      paperYRowCoordinate G
          (paperPartialNCKStageRowEdges G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation) i)
          assignment = row ∧
        paperYColCoordinate G
          (paperPartialNCKStageColEdges G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation) i)
          assignment = col
  · rw [if_pos hEntry]
    simp only [hEntry.1, hEntry.2, true_and]
    have hprod := paperUnconditionalStageNoiseProduct_eq_sign_mul_erase
      G n orientation i hi w assignment
    unfold paperUnconditionalStageNoiseEdges at hprod
    rw [hprod]
    simp_rw [mul_ite, mul_zero]
    rw [paper_sum_pair_indicator]
    ring
  · rw [if_neg hEntry]
    symm
    apply Finset.sum_eq_zero
    intro a _ha
    apply Finset.sum_eq_zero
    intro b _hb
    rw [if_neg]
    · simp
    · intro h
      exact hEntry ⟨h.1, h.2.1⟩

/-! ## The single remaining stage-index isometry -/

/-- The one still-unproved algebraic statement for successor stages.  The
four finite-set update lemmas in `PaperPartialNCKOneStepReduction` show that
the next index type is obtained by inserting precisely the displayed ambient
pair.  What remains is the norm-preserving removal of inconsistent/duplicate
edge-coordinate rows or columns in the literal `PaperY` indexing. -/
def PaperPartialNCKStageFlatteningNormReindex
    (G : PaperShape) (n : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (i : ℕ)
      (hi : i < paperUnconditionalOrderingLength G),
    (paperUnconditionalOrderingEdgeSide G orientation i hi = false →
      ∀ w : PaperDecoupledNoise G n,
        ‖paperUnconditionalPartialNCKStageMatrix G n orientation (i + 1) w‖ =
          ‖paperMatrixRademacherRowFlattening
            (paperUnconditionalStageRademacherCoefficient
              G n orientation i hi) w‖) ∧
    (paperUnconditionalOrderingEdgeSide G orientation i hi = true →
      ∀ w : PaperDecoupledNoise G n,
        ‖paperUnconditionalPartialNCKStageMatrix G n orientation (i + 1) w‖ =
          ‖paperMatrixRademacherColFlattening
            (paperUnconditionalStageRademacherCoefficient
              G n orientation i hi) w‖)

/-- Once the single norm-reindex statement is available, all actual raw
successor stages supply the equality witnesses required by the generic NCK
reduction. -/
theorem paperPartialNCK_stageDecomposition_of_flatteningNormReindex
    (G : PaperShape) (n : ℕ)
    (hReindex : PaperPartialNCKStageFlatteningNormReindex G n) :
    ∀ (orientation : Fin G.edges → Bool) (i : ℕ),
      ∀ hi : i < paperUnconditionalOrderingLength G,
        (∃ hRow : PaperRowStageRademacherWitness G n orientation i,
          hRow.edge = paperUnconditionalOrderingEdgeAt G i hi) ∨
        (∃ hCol : PaperColStageRademacherWitness G n orientation i,
          hCol.edge = paperUnconditionalOrderingEdgeAt G i hi) := by
  intro orientation i hi
  cases hSide : paperUnconditionalOrderingEdgeSide G orientation i hi with
  | false =>
      left
      refine ⟨{
        edge := paperUnconditionalOrderingEdgeAt G i hi
        coefficients := paperUnconditionalStageRademacherCoefficient
          G n orientation i hi
        independent := ?_
        before_eq := ?_
        after_norm_eq := ?_ }, rfl⟩
      · exact fun w ξ a b =>
          paperUnconditionalStageRademacherCoefficient_independent
            G n orientation i hi w ξ a b
      · exact fun w =>
          paperUnconditionalPartialNCKStageMatrix_eq_rademacherSum
            G n orientation i hi w
      · exact hReindex orientation i hi |>.1 hSide
  | true =>
      right
      refine ⟨{
        edge := paperUnconditionalOrderingEdgeAt G i hi
        coefficients := paperUnconditionalStageRademacherCoefficient
          G n orientation i hi
        independent := ?_
        before_eq := ?_
        after_norm_eq := ?_ }, rfl⟩
      · exact fun w ξ a b =>
          paperUnconditionalStageRademacherCoefficient_independent
            G n orientation i hi w ξ a b
      · exact fun w =>
          paperUnconditionalPartialNCKStageMatrix_eq_rademacherSum
            G n orientation i hi w
      · exact hReindex orientation i hi |>.2 hSide

/-- The requested terminal field stated separately.  Unlike the successor
reindex above, this compares an average over one noise copy per shape edge
with an average over the diagonal shared-noise copy.  It is therefore an
additional decoupling assertion unless the residual noise set is empty or a
separate invariance theorem is supplied. -/
def PaperTerminalStageMeanIdentification
    (G : PaperShape) (n : ℕ) : Prop :=
  ∀ orientation : Fin G.edges → Bool,
    paperUnconditionalDecoupledSquaredStageMean G n orientation
        (paperUnconditionalOrderingLength G) =
      paperTheorem48AnalyticLedger G n orientation 0

/-- Exact constructor for the old algebraic package from its two logically
distinct remaining components. -/
theorem paperPartialNCKAlgebraicReindex_of_terminal_and_stageReindex
    (G : PaperShape) (n : ℕ)
    (hTerminal : PaperTerminalStageMeanIdentification G n)
    (hReindex : PaperPartialNCKStageFlatteningNormReindex G n) :
    PaperPartialNCKAlgebraicReindex G n where
  terminal_mean_eq := hTerminal
  stage_decomposition :=
    paperPartialNCK_stageDecomposition_of_flatteningNormReindex G n hReindex

/-! ## Corrected raw-stage reduction (no terminal equality) -/

/-- The corrected ledger is raw and decoupled at every index, including the
terminal index zero. -/
def paperTheorem48RawAnalyticLedger
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) : ℝ :=
  paperUnconditionalDecoupledSquaredStageMean G n orientation
    (paperUnconditionalOrderingLength G -
      min i (paperUnconditionalOrderingLength G))

/-- Generic matrix NCK plus the pure successor reindex gives a raw forward
stage inequality.  No terminal shared/decoupled identification occurs. -/
theorem paperUnconditionalRawStage_step_of_pureStageReindex
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hNCK : MatrixRademacherNCKSquared C p)
    (hReindex : PaperPartialNCKStageFlatteningNormReindex G n)
    (orientation : Fin G.edges → Bool) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    paperUnconditionalDecoupledSquaredStageMean G n orientation i ≤
      partialNCKSquaredStepFactor C p *
        paperUnconditionalDecoupledSquaredStageMean G n orientation (i + 1) := by
  have hStages := paperPartialNCK_stageDecomposition_of_flatteningNormReindex
    G n hReindex orientation i hi
  rcases hStages with hRow | hCol
  · obtain ⟨hRow, _hEdge⟩ := hRow
    have h := hNCK.1
      (ι := Fin G.edges)
      (rows := PaperYRowIndex G n
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i))
      (cols := PaperYColIndex G n
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i))
      n hRow.edge hRow.coefficients hRow.independent
    calc
      paperUnconditionalDecoupledSquaredStageMean G n orientation i =
          paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperMatrixRademacherSum hRow.edge hRow.coefficients w‖ ^ 2) := by
        unfold paperUnconditionalDecoupledSquaredStageMean
          paperUnconditionalPartialNCKRawStageNorm
        congr 1
        funext w
        have hb := congrArg (fun M => ‖M‖ ^ 2) (hRow.before_eq w)
        simpa [paperPartialNCKRawStageNorm,
          paperUnconditionalPartialNCKStageMatrix] using hb
      _ ≤ partialNCKSquaredStepFactor C p *
          paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperMatrixRademacherRowFlattening hRow.coefficients w‖ ^ 2) := h
      _ = partialNCKSquaredStepFactor C p *
          paperUnconditionalDecoupledSquaredStageMean G n orientation (i + 1) := by
        congr 1
        unfold paperUnconditionalDecoupledSquaredStageMean
          paperUnconditionalPartialNCKRawStageNorm
        congr 1
        funext w
        have ha := congrArg (fun x : ℝ => x ^ 2) (hRow.after_norm_eq w)
        simpa [paperPartialNCKRawStageNorm,
          paperUnconditionalPartialNCKStageMatrix] using ha.symm
  · obtain ⟨hCol, _hEdge⟩ := hCol
    have h := hNCK.2
      (ι := Fin G.edges)
      (rows := PaperYRowIndex G n
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i))
      (cols := PaperYColIndex G n
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i))
      n hCol.edge hCol.coefficients hCol.independent
    calc
      paperUnconditionalDecoupledSquaredStageMean G n orientation i =
          paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperMatrixRademacherSum hCol.edge hCol.coefficients w‖ ^ 2) := by
        unfold paperUnconditionalDecoupledSquaredStageMean
          paperUnconditionalPartialNCKRawStageNorm
        congr 1
        funext w
        have hb := congrArg (fun M => ‖M‖ ^ 2) (hCol.before_eq w)
        simpa [paperPartialNCKRawStageNorm,
          paperUnconditionalPartialNCKStageMatrix] using hb
      _ ≤ partialNCKSquaredStepFactor C p *
          paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperMatrixRademacherColFlattening hCol.coefficients w‖ ^ 2) := h
      _ = partialNCKSquaredStepFactor C p *
          paperUnconditionalDecoupledSquaredStageMean G n orientation (i + 1) := by
        congr 1
        unfold paperUnconditionalDecoupledSquaredStageMean
          paperUnconditionalPartialNCKRawStageNorm
        congr 1
        funext w
        have ha := congrArg (fun x : ℝ => x ^ 2) (hCol.after_norm_eq w)
        simpa [paperPartialNCKRawStageNorm,
          paperUnconditionalPartialNCKStageMatrix] using ha.symm

/-- Corrected reverse-ledger recurrence.  Its first step is the genuine raw
terminal-to-preterminal NCK move, not a false equality between shared and
fully decoupled terminal averages. -/
theorem paperTheorem48RawAnalyticLedger_step
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hNCK : MatrixRademacherNCKSquared C p)
    (hReindex : PaperPartialNCKStageFlatteningNormReindex G n)
    (orientation : Fin G.edges → Bool) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    paperTheorem48RawAnalyticLedger G n orientation (i + 1) ≤
      partialNCKSquaredStepFactor C p *
        paperTheorem48RawAnalyticLedger G n orientation i := by
  let k := paperUnconditionalOrderingLength G
  let j := k - (i + 1)
  have hjlt : j < k := by
    dsimp [j]
    omega
  have h := paperUnconditionalRawStage_step_of_pureStageReindex
    G C p n hNCK hReindex orientation j hjlt
  have hsucc : j + 1 = k - i := by
    dsimp [j]
    omega
  rw [hsucc] at h
  simpa [paperTheorem48RawAnalyticLedger, k,
    Nat.min_eq_left (Nat.le_of_lt hi),
    Nat.min_eq_left (by omega : i + 1 ≤ k), j] using h


end GraphMatrixReplica
