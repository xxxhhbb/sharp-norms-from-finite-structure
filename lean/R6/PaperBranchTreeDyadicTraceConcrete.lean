import R6.PaperTheorem48BranchingAssembly
import R6.PaperPartialNCKStageReindexIsometry

/-! # Concrete coefficients at every node of the NCK branch tree

This file exposes the distinguished sign at an arbitrary orientation/stage/
side-assignment node.  The actual independent sign coordinate is
`Sym2 (Fin n)`, not the redundant ordered pair used by the literal `PaperY`
edge-coordinate block.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

set_option maxHeartbeats 800000

/-- Rotate three finite sums so that the assignment sum is outermost. -/
private theorem paperBranch_sum_rotate_three
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-- Collapse the unique ordered endpoint-pair summand. -/
private theorem paperBranch_sum_pair_indicator
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

/-! ## The exposed edge and its ordered coefficient blocks -/

def paperBranchStageNoiseEdges
    (G : PaperShape) (D : PaperCanonicalNCKSides G) (stage : ℕ) :
    Finset (Fin G.edges) :=
  Finset.univ \ (paperPartialNCKStageRowEdges G
      G.unconditionalBoundaryCleanMengerCertificate D stage ∪
    paperPartialNCKStageColEdges G
      G.unconditionalBoundaryCleanMengerCertificate D stage)

theorem paperUnconditionalOrderingEdgeAt_mem_branchStageNoiseEdges
    (G : PaperShape) (D : PaperCanonicalNCKSides G)
    (stage : ℕ) (hstage : stage < paperUnconditionalOrderingLength G) :
    paperUnconditionalOrderingEdgeAt G stage hstage ∈
      paperBranchStageNoiseEdges G D stage := by
  classical
  have hPrefix := paperUnconditionalOrderingEdgeAt_not_mem_prefix
    G stage hstage
  have hRow : paperUnconditionalOrderingEdgeAt G stage hstage ∉
      paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage := by
    intro h
    exact hPrefix (Finset.mem_filter.mp h).1
  have hCol : paperUnconditionalOrderingEdgeAt G stage hstage ∉
      paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage := by
    intro h
    exact hPrefix (Finset.mem_filter.mp h).1
  simp [paperBranchStageNoiseEdges, hRow, hCol]

/-- Ordered endpoint coefficient blocks.  This is a convenient literal
intermediate representation; it is not yet the independent sign index. -/
def paperBranchStageOrderedCoefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (a b : Fin n) :
    Matrix
      (PaperYRowIndex G n (paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage))
      (PaperYColIndex G n (paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage)) ℝ := by
  classical
  let R := paperPartialNCKStageRowEdges G
    G.unconditionalBoundaryCleanMengerCertificate D stage
  let C := paperPartialNCKStageColEdges G
    G.unconditionalBoundaryCleanMengerCertificate D stage
  let e := paperUnconditionalOrderingEdgeAt G stage hstage
  exact fun row col =>
    ∑ assignment : PaperAssignment G n,
      if paperYRowCoordinate G R assignment = row ∧
          paperYColCoordinate G C assignment = col ∧
          assignment (G.source e) = a ∧ assignment (G.target e) = b then
        paperOrientedAssignmentWeight G orientation assignment *
          paperDecoupledNoiseProductOn G
            ((Finset.univ \ (R ∪ C)).erase e) w assignment
      else 0

theorem paperBranchStageOrderedCoefficient_independent
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (ξ : PaperNoise n) (a b : Fin n) :
    paperBranchStageOrderedCoefficient G n orientation D stage hstage
        (Function.update w (paperUnconditionalOrderingEdgeAt G stage hstage) ξ)
        a b =
      paperBranchStageOrderedCoefficient G n orientation D stage hstage
        w a b := by
  classical
  ext row col
  unfold paperBranchStageOrderedCoefficient
  apply Finset.sum_congr rfl
  intro assignment _ha
  split_ifs with hEntry
  · apply congrArg (fun x : ℝ =>
      paperOrientedAssignmentWeight G orientation assignment * x)
    unfold paperDecoupledNoiseProductOn
    apply Finset.prod_congr rfl
    intro e he
    have hne : e ≠ paperUnconditionalOrderingEdgeAt G stage hstage :=
      Finset.ne_of_mem_erase he
    rw [Function.update_of_ne hne]
  · rfl

theorem paperBranchStageNoiseProduct_eq_sign_mul_erase
    (G : PaperShape) (n : ℕ) (D : PaperCanonicalNCKSides G)
    (stage : ℕ) (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (assignment : PaperAssignment G n) :
    paperDecoupledNoiseProductOn G (paperBranchStageNoiseEdges G D stage)
        w assignment =
      paperEdgeSign (w (paperUnconditionalOrderingEdgeAt G stage hstage))
          (assignment (G.source
            (paperUnconditionalOrderingEdgeAt G stage hstage)))
          (assignment (G.target
            (paperUnconditionalOrderingEdgeAt G stage hstage))) *
        paperDecoupledNoiseProductOn G
          ((paperBranchStageNoiseEdges G D stage).erase
            (paperUnconditionalOrderingEdgeAt G stage hstage)) w assignment := by
  classical
  unfold paperDecoupledNoiseProductOn
  rw [← Finset.mul_prod_erase _ _
    (paperUnconditionalOrderingEdgeAt_mem_branchStageNoiseEdges
      G D stage hstage)]

/-- Exact parent-stage expansion over the redundant ordered endpoint blocks. -/
theorem paperPartialNCKStageMatrix_eq_orderedRademacherSum
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    paperPartialNCKStageMatrix G
        G.unconditionalBoundaryCleanMengerCertificate D
        n orientation stage w =
      paperMatrixRademacherSum
        (paperUnconditionalOrderingEdgeAt G stage hstage)
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w := by
  classical
  ext row col
  unfold paperPartialNCKStageMatrix paperYMatrix paperYThroughCoordinates
    paperMatrixRademacherSum
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  unfold paperBranchStageOrderedCoefficient
  simp_rw [Finset.mul_sum]
  rw [paperBranch_sum_rotate_three]
  apply Finset.sum_congr rfl
  intro assignment _hassignment
  by_cases hEntry :
      paperYRowCoordinate G
          (paperPartialNCKStageRowEdges G
            G.unconditionalBoundaryCleanMengerCertificate D stage)
          assignment = row ∧
        paperYColCoordinate G
          (paperPartialNCKStageColEdges G
            G.unconditionalBoundaryCleanMengerCertificate D stage)
          assignment = col
  · rw [if_pos hEntry]
    simp only [hEntry.1, hEntry.2, true_and]
    have hprod := paperBranchStageNoiseProduct_eq_sign_mul_erase
      G n D stage hstage w assignment
    unfold paperBranchStageNoiseEdges at hprod
    rw [hprod]
    simp_rw [mul_ite, mul_zero]
    rw [paperBranch_sum_pair_indicator]
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

/-! ## Aggregation to the true `Sym2` coordinate -/

/-- The actual independent coefficient family at an arbitrary branch node. -/
def paperBranchStageSym2Coefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    Sym2 (Fin n) →
      Matrix
        (PaperYRowIndex G n (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate D stage))
        (PaperYColIndex G n (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate D stage)) ℝ :=
  paperSym2AggregatedCoefficientFamily
    (paperBranchStageOrderedCoefficient G n orientation D stage hstage w)

/-- A matrix Rademacher sum using the true unordered coordinate of one
distinguished paper-noise copy. -/
def paperSym2NoiseMatrixRademacherSum
    {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
    [DecidableEq ι] {n : ℕ}
    (e : ι)
    (A : (ι → PaperNoise n) → Sym2 (Fin n) → Matrix rows cols ℝ)
    (w : ι → PaperNoise n) : Matrix rows cols ℝ :=
  paperRademacherMatrixSum (A w) (paperNoiseSym2Projection (w e))

theorem paperSign_noiseSym2Projection
    {n : ℕ} (w : PaperNoise n) (a b : Fin n) :
    paperSign (paperNoiseSym2Projection w s(a, b)) =
      paperEdgeSign w a b := by
  simp [paperNoiseSym2Projection, paperCanonicalAmbientEdge_mk,
    paperSign, paperEdgeSign]

theorem paperMatrixRademacherSum_eq_sym2NoiseSum
    {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
    [DecidableEq ι] {n : ℕ}
    (e : ι)
    (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ)
    (w : ι → PaperNoise n) :
    paperMatrixRademacherSum e A w =
      paperSym2NoiseMatrixRademacherSum e
        (fun w' => paperSym2AggregatedCoefficientFamily (A w')) w := by
  classical
  unfold paperSym2NoiseMatrixRademacherSum
  rw [paperRademacherMatrixSum_sym2_aggregate]
  ext row col
  unfold paperMatrixRademacherSum
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [paperSign_noiseSym2Projection]

/-- Exact expansion of the literal parent stage over independent `Sym2`
signs. -/
theorem paperPartialNCKStageMatrix_eq_sym2RademacherSum
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    paperPartialNCKStageMatrix G
        G.unconditionalBoundaryCleanMengerCertificate D
        n orientation stage w =
      paperSym2NoiseMatrixRademacherSum
        (paperUnconditionalOrderingEdgeAt G stage hstage)
        (paperBranchStageSym2Coefficient
          G n orientation D stage hstage) w := by
  rw [paperPartialNCKStageMatrix_eq_orderedRademacherSum]
  exact paperMatrixRademacherSum_eq_sym2NoiseSum
    (paperUnconditionalOrderingEdgeAt G stage hstage)
    (paperBranchStageOrderedCoefficient
      G n orientation D stage hstage) w

theorem paperBranchStageSym2Coefficient_independent
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (ξ : PaperNoise n) :
    paperBranchStageSym2Coefficient G n orientation D stage hstage
        (Function.update w (paperUnconditionalOrderingEdgeAt G stage hstage) ξ) =
      paperBranchStageSym2Coefficient G n orientation D stage hstage w := by
  funext z
  unfold paperBranchStageSym2Coefficient
    paperSym2AggregatedCoefficientFamily
  funext row col
  apply Finset.sum_congr rfl
  intro x _hx
  split_ifs
  · rw [paperBranchStageOrderedCoefficient_independent]
  · rfl

/-! ## Ordered child flattenings

The existing literal successor is indexed by an ordered endpoint pair.  The
following equalities therefore apply to the ordered coefficient family.  A
further support-orthogonality/compression lemma is required to identify these
with the variance blocks of the aggregated `Sym2` family; there is no type
equivalence `Fin n × Fin n ≃ Sym2 (Fin n)` in general.
-/

theorem paperBranchStage_edge_not_mem_row
    (G : PaperShape) (D : PaperCanonicalNCKSides G)
    (stage : ℕ) (hstage : stage < paperUnconditionalOrderingLength G) :
    paperUnconditionalOrderingEdgeAt G stage hstage ∉
      paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage := by
  intro h
  exact paperUnconditionalOrderingEdgeAt_not_mem_prefix G stage hstage
    (Finset.mem_filter.mp h).1

theorem paperBranchStage_edge_not_mem_col
    (G : PaperShape) (D : PaperCanonicalNCKSides G)
    (stage : ℕ) (hstage : stage < paperUnconditionalOrderingLength G) :
    paperUnconditionalOrderingEdgeAt G stage hstage ∉
      paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage := by
  intro h
  exact paperUnconditionalOrderingEdgeAt_not_mem_prefix G stage hstage
    (Finset.mem_filter.mp h).1

/-- Row-child matrix with the newly inserted literal coordinate, reindexed
to the ordered coefficient row flattening. -/
theorem paperBranchOrderedRowChild_reindex
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    let R := paperPartialNCKStageRowEdges G
      G.unconditionalBoundaryCleanMengerCertificate D stage
    let C := paperPartialNCKStageColEdges G
      G.unconditionalBoundaryCleanMengerCertificate D stage
    let e := paperUnconditionalOrderingEdgeAt G stage hstage
    Matrix.reindex
        (paperYRowInsertEquiv G n R e
          (paperBranchStage_edge_not_mem_row G D stage hstage))
        (Equiv.refl (PaperYColIndex G n C))
        (paperYMatrix G n orientation (insert e R) C w) =
      paperMatrixRademacherRowFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w := by
  dsimp only
  exact paperYMatrix_insertRow_reindex G n orientation _ _ _
    (paperBranchStage_edge_not_mem_row G D stage hstage)
    (paperBranchStage_edge_not_mem_col G D stage hstage) w

/-- Along an actual list-history row child, the literal successor matrix is
the ordered coefficient row flattening after the explicit inserted-coordinate
equivalence. -/
theorem paperNCKBranchRowChildMatrix_reindex_orderedCoefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (history : List Bool)
    (hstage : history.length < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    let D := paperNCKBranchSides G history
    ‖paperNCKBranchStageMatrix G n orientation
        (paperNCKBranchChild false history) w‖ =
      ‖paperMatrixRademacherRowFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D history.length hstage) w‖ := by
  dsimp only
  let R := paperPartialNCKStageRowEdges G
    G.unconditionalBoundaryCleanMengerCertificate
      (paperNCKBranchSides G history) history.length
  let C := paperPartialNCKStageColEdges G
    G.unconditionalBoundaryCleanMengerCertificate
      (paperNCKBranchSides G history) history.length
  let e := paperUnconditionalOrderingEdgeAt G history.length hstage
  have heR : e ∉ R :=
    paperBranchStage_edge_not_mem_row G (paperNCKBranchSides G history)
      history.length hstage
  have heC : e ∉ C :=
    paperBranchStage_edge_not_mem_col G (paperNCKBranchSides G history)
      history.length hstage
  have hRow :
      paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild false history))
          (paperNCKBranchChild false history).length = insert e R := by
    rw [paperNCKBranchChild_length]
    exact paperNCKBranch_rowChild_rowEdges G history hstage
  have hCol :
      paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild false history))
          (paperNCKBranchChild false history).length = C := by
    rw [paperNCKBranchChild_length]
    exact paperNCKBranch_rowChild_colEdges G history hstage
  unfold paperNCKBranchStageMatrix paperPartialNCKStageMatrix
  have hMatrix := paperBranchOrderedRowChild_reindex
    G n orientation (paperNCKBranchSides G history) history.length hstage w
  have hNorm := paper_l2_opNorm_reindex
    (paperYRowInsertEquiv G n R e heR)
    (Equiv.refl (PaperYColIndex G n C))
    (paperYMatrix G n orientation (insert e R) C w)
  calc
    ‖paperYMatrix G n orientation
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild false history))
          (paperNCKBranchChild false history).length)
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild false history))
          (paperNCKBranchChild false history).length) w‖ =
        ‖paperYMatrix G n orientation (insert e R) C w‖ :=
      norm_paperYMatrix_congr_edges G n orientation w hRow hCol
    _ =
        ‖Matrix.reindex (paperYRowInsertEquiv G n R e heR)
          (Equiv.refl (PaperYColIndex G n C))
          (paperYMatrix G n orientation (insert e R) C w)‖ := hNorm.symm
    _ = _ := congrArg norm hMatrix

/-- Column-child analogue of the preceding ordered-block reindex. -/
theorem paperBranchOrderedColChild_reindex
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    let R := paperPartialNCKStageRowEdges G
      G.unconditionalBoundaryCleanMengerCertificate D stage
    let C := paperPartialNCKStageColEdges G
      G.unconditionalBoundaryCleanMengerCertificate D stage
    let e := paperUnconditionalOrderingEdgeAt G stage hstage
    Matrix.reindex
        (Equiv.refl (PaperYRowIndex G n R))
        (paperYColInsertEquiv G n C e
          (paperBranchStage_edge_not_mem_col G D stage hstage))
        (paperYMatrix G n orientation R (insert e C) w) =
      paperMatrixRademacherColFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w := by
  dsimp only
  exact paperYMatrix_insertCol_reindex G n orientation _ _ _
    (paperBranchStage_edge_not_mem_row G D stage hstage)
    (paperBranchStage_edge_not_mem_col G D stage hstage) w

/-- Along an actual list-history column child, the literal successor matrix
is the ordered coefficient column flattening. -/
theorem paperNCKBranchColChildMatrix_reindex_orderedCoefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (history : List Bool)
    (hstage : history.length < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    let D := paperNCKBranchSides G history
    ‖paperNCKBranchStageMatrix G n orientation
        (paperNCKBranchChild true history) w‖ =
      ‖paperMatrixRademacherColFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D history.length hstage) w‖ := by
  dsimp only
  let R := paperPartialNCKStageRowEdges G
    G.unconditionalBoundaryCleanMengerCertificate
      (paperNCKBranchSides G history) history.length
  let C := paperPartialNCKStageColEdges G
    G.unconditionalBoundaryCleanMengerCertificate
      (paperNCKBranchSides G history) history.length
  let e := paperUnconditionalOrderingEdgeAt G history.length hstage
  have heR : e ∉ R :=
    paperBranchStage_edge_not_mem_row G (paperNCKBranchSides G history)
      history.length hstage
  have heC : e ∉ C :=
    paperBranchStage_edge_not_mem_col G (paperNCKBranchSides G history)
      history.length hstage
  have hRow :
      paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild true history))
          (paperNCKBranchChild true history).length = R := by
    rw [paperNCKBranchChild_length]
    exact paperNCKBranch_colChild_rowEdges G history hstage
  have hCol :
      paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild true history))
          (paperNCKBranchChild true history).length = insert e C := by
    rw [paperNCKBranchChild_length]
    exact paperNCKBranch_colChild_colEdges G history hstage
  unfold paperNCKBranchStageMatrix paperPartialNCKStageMatrix
  have hMatrix := paperBranchOrderedColChild_reindex
    G n orientation (paperNCKBranchSides G history) history.length hstage w
  have hNorm := paper_l2_opNorm_reindex
    (Equiv.refl (PaperYRowIndex G n R))
    (paperYColInsertEquiv G n C e heC)
    (paperYMatrix G n orientation R (insert e C) w)
  calc
    ‖paperYMatrix G n orientation
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild true history))
          (paperNCKBranchChild true history).length)
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G (paperNCKBranchChild true history))
          (paperNCKBranchChild true history).length) w‖ =
        ‖paperYMatrix G n orientation R (insert e C) w‖ :=
      norm_paperYMatrix_congr_edges G n orientation w hRow hCol
    _ =
        ‖Matrix.reindex (Equiv.refl (PaperYRowIndex G n R))
          (paperYColInsertEquiv G n C e heC)
          (paperYMatrix G n orientation R (insert e C) w)‖ := hNorm.symm
    _ = _ := congrArg norm hMatrix

/-! ## Coefficient-level dyadic trace obligation -/

/-- The trace obligation after replacing the parent matrix by its concrete
independent `Sym2` coefficient sum.  Unlike the raw-stage formulation, this
is directly in the input language of the even-word/Catalan development. -/
def PaperBranchSym2CoefficientDyadicTraceBound
    (G : PaperShape) (C : ℝ) (p n q : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (stage : ℕ)
      (hstage : stage < paperUnconditionalOrderingLength G)
      (D : PaperCanonicalNCKSides G),
    paperMean (fun w : PaperDecoupledNoise G n =>
      Matrix.trace
        ((paperSym2NoiseMatrixRademacherSum
              (paperUnconditionalOrderingEdgeAt G stage hstage)
              (paperBranchStageSym2Coefficient
                G n orientation D stage hstage) w *
            (paperSym2NoiseMatrixRademacherSum
              (paperUnconditionalOrderingEdgeAt G stage hstage)
              (paperBranchStageSym2Coefficient
                G n orientation D stage hstage) w).transpose) ^ (2 ^ q))) ≤
      (partialNCKSquaredStepFactor C p *
        (paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate D stage hstage false) (stage + 1) +
          paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate D stage hstage true) (stage + 1))) ^
        (2 ^ q)

/-- The concrete `Sym2` expansion transports the coefficient-level trace
estimate back to the literal branch-tree stage. -/
theorem paperBranchTreeDyadicTraceBound_of_sym2Coefficient
    (G : PaperShape) (C : ℝ) (p n q : ℕ)
    (hCoeff : PaperBranchSym2CoefficientDyadicTraceBound G C p n q) :
    PaperBranchTreeDyadicTraceBound G C p n q := by
  intro orientation stage hstage D
  calc
    paperMean (fun w : PaperDecoupledNoise G n =>
        Matrix.trace
          ((paperPartialNCKStageMatrix G
                G.unconditionalBoundaryCleanMengerCertificate D
                n orientation stage w *
              (paperPartialNCKStageMatrix G
                G.unconditionalBoundaryCleanMengerCertificate D
                n orientation stage w).transpose) ^ (2 ^ q))) =
      paperMean (fun w : PaperDecoupledNoise G n =>
        Matrix.trace
          ((paperSym2NoiseMatrixRademacherSum
                (paperUnconditionalOrderingEdgeAt G stage hstage)
                (paperBranchStageSym2Coefficient
                  G n orientation D stage hstage) w *
              (paperSym2NoiseMatrixRademacherSum
                (paperUnconditionalOrderingEdgeAt G stage hstage)
                (paperBranchStageSym2Coefficient
                  G n orientation D stage hstage) w).transpose) ^ (2 ^ q))) := by
        apply congrArg paperMean
        funext w
        rw [paperPartialNCKStageMatrix_eq_sym2RademacherSum]
    _ ≤ _ := hCoeff orientation stage hstage D

#print axioms paperPartialNCKStageMatrix_eq_orderedRademacherSum
#print axioms paperPartialNCKStageMatrix_eq_sym2RademacherSum
#print axioms paperBranchStageSym2Coefficient_independent
#print axioms paperNCKBranchRowChildMatrix_reindex_orderedCoefficient
#print axioms paperNCKBranchColChildMatrix_reindex_orderedCoefficient
#print axioms paperBranchTreeDyadicTraceBound_of_sym2Coefficient

#print axioms paperBranchStageOrderedCoefficient_independent
#print axioms paperPartialNCKStageMatrix_eq_orderedRademacherSum
#print axioms paperMatrixRademacherSum_eq_sym2NoiseSum
#print axioms paperPartialNCKStageMatrix_eq_sym2RademacherSum
#print axioms paperBranchStageSym2Coefficient_independent
#print axioms paperBranchOrderedRowChild_reindex
#print axioms paperBranchOrderedColChild_reindex

end GraphMatrixReplica
