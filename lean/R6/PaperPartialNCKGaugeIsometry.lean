import R6.PaperPartialNCKStageMatrices

/-! # The terminal partial-NCK gauge is an isometry

At the terminal stage every selected shape edge has been assigned to exactly
one matrix side.  Its missing sign is consequently a function of that side's
visible role tuple.  This file packages the two products as diagonal sign
matrices and proves that the gauge-twisted terminal matrix is obtained from
the raw terminal matrix by left and right diagonal multiplication.

No edge-disjointness is needed: repeated role coordinates merely make several
unit-sign factors read the same tuple entries.  Every selected edge is still
assigned to exactly one side, so the product splits without conflict.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

variable (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)

/-- A role incident to a row-selected edge, regarded as a visible covered
row coordinate. -/
def paperTerminalRowRoleIndex
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = false)
    (v : Fin G.roles) (hv : G.toPartiteShape.EdgeIncident e.1 v) :
    {v : PaperCoveredRole G // v ∈ D.coveredRowRoles} := by
  classical
  have hRow : v ∈ D.rowRoles :=
    D.incident_mem_rowRoles_of_side_false e.2 hSide hv
  refine ⟨⟨v, D.rowRoles_subset_coveredRoles hRow⟩, ?_⟩
  unfold PartiteShape.IntermediateFlatteningRoleSides.coveredRowRoles
  apply Finset.mem_map.2
  refine ⟨⟨v, hRow⟩, Finset.mem_attach _ _, ?_⟩
  rfl

/-- A role incident to a column-selected edge, regarded as a visible covered
column coordinate. -/
def paperTerminalColRoleIndex
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = true)
    (v : Fin G.roles) (hv : G.toPartiteShape.EdgeIncident e.1 v) :
    {v : PaperCoveredRole G // v ∈ D.coveredColRoles} := by
  classical
  have hCol : v ∈ D.colRoles :=
    D.incident_mem_colRoles_of_side_true e.2 hSide hv
  refine ⟨⟨v, D.colRoles_subset_coveredRoles hCol⟩, ?_⟩
  unfold PartiteShape.IntermediateFlatteningRoleSides.coveredColRoles
  apply Finset.mem_map.2
  refine ⟨⟨v, hCol⟩, Finset.mem_attach _ _, ?_⟩
  rfl

def paperTerminalRowSourceIndex
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = false) :
    {v : PaperCoveredRole G // v ∈ D.coveredRowRoles} :=
  paperTerminalRowRoleIndex G certificate D e hSide (G.source e.1) (Or.inl rfl)

def paperTerminalRowTargetIndex
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = false) :
    {v : PaperCoveredRole G // v ∈ D.coveredRowRoles} :=
  paperTerminalRowRoleIndex G certificate D e hSide (G.target e.1) (Or.inr rfl)

def paperTerminalColSourceIndex
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = true) :
    {v : PaperCoveredRole G // v ∈ D.coveredColRoles} :=
  paperTerminalColRoleIndex G certificate D e hSide (G.source e.1) (Or.inl rfl)

def paperTerminalColTargetIndex
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = true) :
    {v : PaperCoveredRole G // v ∈ D.coveredColRoles} :=
  paperTerminalColRoleIndex G certificate D e hSide (G.target e.1) (Or.inr rfl)

/-- Product of the terminal signs assigned to the row side. -/
def paperTerminalRowGauge {n : ℕ} (w : PaperNoise n)
    (row : PaperVisibleTuple n D.coveredRowRoles) : ℝ := by
  classical
  exact ∏ e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate},
    if h : paperSelectedEdgeSide G certificate D e = false then
      paperEdgeSign w
        (row (paperTerminalRowSourceIndex G certificate D e h))
        (row (paperTerminalRowTargetIndex G certificate D e h))
    else 1

/-- Product of the terminal signs assigned to the column side. -/
def paperTerminalColGauge {n : ℕ} (w : PaperNoise n)
    (col : PaperVisibleTuple n D.coveredColRoles) : ℝ := by
  classical
  exact ∏ e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate},
    if h : paperSelectedEdgeSide G certificate D e = true then
      paperEdgeSign w
        (col (paperTerminalColSourceIndex G certificate D e h))
        (col (paperTerminalColTargetIndex G certificate D e h))
    else 1

/-- The left diagonal sign matrix. -/
def paperTerminalRowGaugeMatrix {n : ℕ} (w : PaperNoise n) :
    Matrix (PaperVisibleTuple n D.coveredRowRoles)
      (PaperVisibleTuple n D.coveredRowRoles) ℝ :=
  Matrix.diagonal (paperTerminalRowGauge G certificate D w)

/-- The right diagonal sign matrix. -/
def paperTerminalColGaugeMatrix {n : ℕ} (w : PaperNoise n) :
    Matrix (PaperVisibleTuple n D.coveredColRoles)
      (PaperVisibleTuple n D.coveredColRoles) ℝ :=
  Matrix.diagonal (paperTerminalColGauge G certificate D w)

@[simp] theorem paperIntermediateCoveredRowMap_apply_terminalSourceIndex
    {n : ℕ} (assignment : PaperAssignment G n)
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = false) :
    paperIntermediateCoveredRowMap G certificate D assignment
        (paperTerminalRowSourceIndex G certificate D e hSide) =
      assignment (G.source e.1) := by
  rfl

@[simp] theorem paperIntermediateCoveredRowMap_apply_terminalTargetIndex
    {n : ℕ} (assignment : PaperAssignment G n)
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = false) :
    paperIntermediateCoveredRowMap G certificate D assignment
        (paperTerminalRowTargetIndex G certificate D e hSide) =
      assignment (G.target e.1) := by
  rfl

@[simp] theorem paperIntermediateCoveredColMap_apply_terminalSourceIndex
    {n : ℕ} (assignment : PaperAssignment G n)
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = true) :
    paperIntermediateCoveredColMap G certificate D assignment
        (paperTerminalColSourceIndex G certificate D e hSide) =
      assignment (G.source e.1) := by
  rfl

@[simp] theorem paperIntermediateCoveredColMap_apply_terminalTargetIndex
    {n : ℕ} (assignment : PaperAssignment G n)
    (e : {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G certificate})
    (hSide : paperSelectedEdgeSide G certificate D e = true) :
    paperIntermediateCoveredColMap G certificate D assignment
        (paperTerminalColTargetIndex G certificate D e hSide) =
      assignment (G.target e.1) := by
  rfl

/-- The selected-edge product splits between the two visible tuple blocks.
This remains true when distinct edges share endpoints: the proof is a
pointwise partition of edge factors, not a disjointness argument on roles. -/
theorem paperFlattenedGaugeProductOn_eq_row_mul_col
    {n : ℕ} (w : PaperNoise n) (assignment : PaperAssignment G n) :
    paperFlattenedGaugeProductOn G
        (paperSelectedOrderingEdges G certificate) w assignment =
      paperTerminalRowGauge G certificate D w
          (paperIntermediateCoveredRowMap G certificate D assignment) *
        paperTerminalColGauge G certificate D w
          (paperIntermediateCoveredColMap G certificate D assignment) := by
  classical
  unfold paperFlattenedGaugeProductOn paperTerminalRowGauge
    paperTerminalColGauge
  rw [← Finset.prod_attach]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _he
  by_cases hSide : paperSelectedEdgeSide G certificate D e = false
  · have hNotTrue : paperSelectedEdgeSide G certificate D e ≠ true := by
      simp [hSide]
    rw [dif_pos hSide, dif_neg hNotTrue, mul_one,
      paperIntermediateCoveredRowMap_apply_terminalSourceIndex,
      paperIntermediateCoveredRowMap_apply_terminalTargetIndex]
  · have hTrue : paperSelectedEdgeSide G certificate D e = true :=
      Bool.eq_true_of_not_eq_false hSide
    rw [dif_neg hSide, dif_pos hTrue, one_mul,
      paperIntermediateCoveredColMap_apply_terminalSourceIndex,
      paperIntermediateCoveredColMap_apply_terminalTargetIndex]

/-- Entrywise factorization of the gauge terminal through its raw terminal.
The statement is valid for arbitrary decoupled residual noise. -/
theorem paperPartialNCKGaugeTerminalMatrix_apply_eq
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) (coupled : PaperNoise n)
    (row : PaperVisibleTuple n D.coveredRowRoles)
    (col : PaperVisibleTuple n D.coveredColRoles) :
    paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
        decoupled coupled row col =
      paperTerminalRowGauge G certificate D coupled row *
        paperPartialNCKRawTerminalMatrix G certificate D n orientation
          decoupled row col *
        paperTerminalColGauge G certificate D coupled col := by
  classical
  unfold paperPartialNCKGaugeTerminalMatrix
    paperGaugeTwistedYThroughCoordinates
    paperPartialNCKRawTerminalMatrix paperYThroughCoordinates
  rw [show paperCertificateOrderingEdges G certificate =
      paperSelectedOrderingEdges G certificate from rfl]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro assignment _
  by_cases hEntry :
      paperIntermediateCoveredRowMap G certificate D assignment = row ∧
        paperIntermediateCoveredColMap G certificate D assignment = col
  · simp only [if_pos hEntry]
    rw [paperFlattenedGaugeProductOn_eq_row_mul_col G certificate D]
    rw [hEntry.1, hEntry.2]
    ring
  · simp [hEntry]

/-- Exact matrix factorization by the two diagonal gauges. -/
theorem paperTerminalRow_mul_raw_mul_col_eq_gauge
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) (coupled : PaperNoise n) :
    paperTerminalRowGaugeMatrix G certificate D coupled *
          paperPartialNCKRawTerminalMatrix G certificate D n orientation decoupled *
        paperTerminalColGaugeMatrix G certificate D coupled =
      paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
        decoupled coupled := by
  classical
  ext row col
  unfold paperTerminalRowGaugeMatrix paperTerminalColGaugeMatrix
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (paperPartialNCKGaugeTerminalMatrix_apply_eq G certificate D
    orientation decoupled coupled row col).symm

@[simp] theorem paperEdgeSign_mul_self_terminal
    {n : ℕ} (w : PaperNoise n) (i j : Fin n) :
    paperEdgeSign w i j * paperEdgeSign w i j = 1 := by
  unfold paperEdgeSign
  split <;> norm_num

@[simp] theorem paperTerminalRowGauge_mul_self
    {n : ℕ} (w : PaperNoise n)
    (row : PaperVisibleTuple n D.coveredRowRoles) :
    paperTerminalRowGauge G certificate D w row *
        paperTerminalRowGauge G certificate D w row = 1 := by
  classical
  unfold paperTerminalRowGauge
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro e _he
  by_cases hSide : paperSelectedEdgeSide G certificate D e = false
  · rw [dif_pos hSide]
    exact paperEdgeSign_mul_self_terminal _ _ _
  · rw [dif_neg hSide]
    norm_num

@[simp] theorem paperTerminalColGauge_mul_self
    {n : ℕ} (w : PaperNoise n)
    (col : PaperVisibleTuple n D.coveredColRoles) :
    paperTerminalColGauge G certificate D w col *
        paperTerminalColGauge G certificate D w col = 1 := by
  classical
  unfold paperTerminalColGauge
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro e _he
  by_cases hSide : paperSelectedEdgeSide G certificate D e = true
  · rw [dif_pos hSide]
    exact paperEdgeSign_mul_self_terminal _ _ _
  · rw [dif_neg hSide]
    norm_num

@[simp] theorem star_paperTerminalRowGaugeMatrix
    {n : ℕ} (w : PaperNoise n) :
    star (paperTerminalRowGaugeMatrix G certificate D w) =
      paperTerminalRowGaugeMatrix G certificate D w := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    rfl
  · simp [paperTerminalRowGaugeMatrix, Matrix.diagonal, h, Ne.symm h]

@[simp] theorem star_paperTerminalColGaugeMatrix
    {n : ℕ} (w : PaperNoise n) :
    star (paperTerminalColGaugeMatrix G certificate D w) =
      paperTerminalColGaugeMatrix G certificate D w := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    rfl
  · simp [paperTerminalColGaugeMatrix, Matrix.diagonal, h, Ne.symm h]

theorem paperTerminalRowGaugeMatrix_mul_self
    {n : ℕ} (w : PaperNoise n) :
    paperTerminalRowGaugeMatrix G certificate D w *
        paperTerminalRowGaugeMatrix G certificate D w = 1 := by
  classical
  unfold paperTerminalRowGaugeMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.diagonal, h]

theorem paperTerminalColGaugeMatrix_mul_self
    {n : ℕ} (w : PaperNoise n) :
    paperTerminalColGaugeMatrix G certificate D w *
        paperTerminalColGaugeMatrix G certificate D w = 1 := by
  classical
  unfold paperTerminalColGaugeMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [Matrix.diagonal, h]

theorem paperTerminalRowGaugeMatrix_mem_unitary
    {n : ℕ} (w : PaperNoise n) :
    paperTerminalRowGaugeMatrix G certificate D w ∈
      unitary (Matrix (PaperVisibleTuple n D.coveredRowRoles)
        (PaperVisibleTuple n D.coveredRowRoles) ℝ) := by
  rw [Unitary.mem_iff, star_paperTerminalRowGaugeMatrix]
  exact ⟨paperTerminalRowGaugeMatrix_mul_self G certificate D w,
    paperTerminalRowGaugeMatrix_mul_self G certificate D w⟩

theorem paperTerminalColGaugeMatrix_mem_unitary
    {n : ℕ} (w : PaperNoise n) :
    paperTerminalColGaugeMatrix G certificate D w ∈
      unitary (Matrix (PaperVisibleTuple n D.coveredColRoles)
        (PaperVisibleTuple n D.coveredColRoles) ℝ) := by
  rw [Unitary.mem_iff, star_paperTerminalColGaugeMatrix]
  exact ⟨paperTerminalColGaugeMatrix_mul_self G certificate D w,
    paperTerminalColGaugeMatrix_mul_self G certificate D w⟩

@[simp] theorem abs_paperTerminalRowGauge
    {n : ℕ} (w : PaperNoise n)
    (row : PaperVisibleTuple n D.coveredRowRoles) :
    |paperTerminalRowGauge G certificate D w row| = 1 := by
  have h := congrArg abs
    (paperTerminalRowGauge_mul_self G certificate D w row)
  rw [abs_mul, abs_one] at h
  nlinarith [abs_nonneg (paperTerminalRowGauge G certificate D w row)]

@[simp] theorem abs_paperTerminalColGauge
    {n : ℕ} (w : PaperNoise n)
    (col : PaperVisibleTuple n D.coveredColRoles) :
    |paperTerminalColGauge G certificate D w col| = 1 := by
  have h := congrArg abs
    (paperTerminalColGauge_mul_self G certificate D w col)
  rw [abs_mul, abs_one] at h
  nlinarith [abs_nonneg (paperTerminalColGauge G certificate D w col)]

theorem norm_paperTerminalRowGaugeMatrix_le_one
    {n : ℕ} (w : PaperNoise n) :
    ‖paperTerminalRowGaugeMatrix G certificate D w‖ ≤ 1 := by
  unfold paperTerminalRowGaugeMatrix
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro row
  rw [Real.norm_eq_abs, abs_paperTerminalRowGauge]

theorem norm_paperTerminalColGaugeMatrix_le_one
    {n : ℕ} (w : PaperNoise n) :
    ‖paperTerminalColGaugeMatrix G certificate D w‖ ≤ 1 := by
  unfold paperTerminalColGaugeMatrix
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro col
  rw [Real.norm_eq_abs, abs_paperTerminalColGauge]

/-- The inverse factorization.  Both gauge matrices are their own inverse. -/
theorem paperTerminalRow_mul_gauge_mul_col_eq_raw
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) (coupled : PaperNoise n) :
    paperTerminalRowGaugeMatrix G certificate D coupled *
          paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
            decoupled coupled *
        paperTerminalColGaugeMatrix G certificate D coupled =
      paperPartialNCKRawTerminalMatrix G certificate D n orientation
        decoupled := by
  classical
  ext row col
  unfold paperTerminalRowGaugeMatrix paperTerminalColGaugeMatrix
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
    paperPartialNCKGaugeTerminalMatrix_apply_eq G certificate D]
  let r := paperTerminalRowGauge G certificate D coupled row
  let c := paperTerminalColGauge G certificate D coupled col
  let x := paperPartialNCKRawTerminalMatrix G certificate D n orientation
    decoupled row col
  change r * (r * x * c) * c = x
  have hr : r * r = 1 :=
    paperTerminalRowGauge_mul_self G certificate D coupled row
  have hc : c * c = 1 :=
    paperTerminalColGauge_mul_self G certificate D coupled col
  calc
    r * (r * x * c) * c = (r * r) * x * (c * c) := by ring
    _ = x := by rw [hr, hc]; ring

/-- A two-sided diagonal sign gauge leaves the rectangular L2 operator norm
unchanged.  This is the exact raw/gauge terminal norm identification needed
by the partial-NCK ledger. -/
theorem norm_paperPartialNCKGaugeTerminalMatrix_eq_raw
    {n : ℕ} (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) (coupled : PaperNoise n) :
    ‖paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
        decoupled coupled‖ =
      ‖paperPartialNCKRawTerminalMatrix G certificate D n orientation
        decoupled‖ := by
  apply le_antisymm
  · rw [← paperTerminalRow_mul_raw_mul_col_eq_gauge G certificate D]
    calc
      ‖paperTerminalRowGaugeMatrix G certificate D coupled *
            paperPartialNCKRawTerminalMatrix G certificate D n orientation
              decoupled *
          paperTerminalColGaugeMatrix G certificate D coupled‖
          ≤ ‖paperTerminalRowGaugeMatrix G certificate D coupled *
                paperPartialNCKRawTerminalMatrix G certificate D n orientation
                  decoupled‖ *
              ‖paperTerminalColGaugeMatrix G certificate D coupled‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖paperTerminalRowGaugeMatrix G certificate D coupled‖ *
              ‖paperPartialNCKRawTerminalMatrix G certificate D n orientation
                decoupled‖) *
            ‖paperTerminalColGaugeMatrix G certificate D coupled‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * ‖paperPartialNCKRawTerminalMatrix G certificate D n orientation
              decoupled‖) * 1 := by
        gcongr
        · exact norm_paperTerminalRowGaugeMatrix_le_one G certificate D coupled
        · exact norm_paperTerminalColGaugeMatrix_le_one G certificate D coupled
      _ = ‖paperPartialNCKRawTerminalMatrix G certificate D n orientation
              decoupled‖ := by ring
  · rw [← paperTerminalRow_mul_gauge_mul_col_eq_raw G certificate D]
    calc
      ‖paperTerminalRowGaugeMatrix G certificate D coupled *
            paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
              decoupled coupled *
          paperTerminalColGaugeMatrix G certificate D coupled‖
          ≤ ‖paperTerminalRowGaugeMatrix G certificate D coupled *
                paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
                  decoupled coupled‖ *
              ‖paperTerminalColGaugeMatrix G certificate D coupled‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖paperTerminalRowGaugeMatrix G certificate D coupled‖ *
              ‖paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
                decoupled coupled‖) *
            ‖paperTerminalColGaugeMatrix G certificate D coupled‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * ‖paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
              decoupled coupled‖) * 1 := by
        gcongr
        · exact norm_paperTerminalRowGaugeMatrix_le_one G certificate D coupled
        · exact norm_paperTerminalColGaugeMatrix_le_one G certificate D coupled
      _ = ‖paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
              decoupled coupled‖ := by ring

/-- On diagonal noise the raw terminal norm is therefore exactly the norm of
the already formalized marginalized intermediate matrix.  This removes the
former raw/gauge endpoint-identification premise. -/
theorem norm_paperPartialNCKRawTerminalMatrix_diagonal_eq_intermediate
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖paperPartialNCKRawTerminalMatrix G certificate D n orientation
        (paperDiagonalDecoupledNoise G w)‖ =
      ‖paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w‖ := by
  calc
    ‖paperPartialNCKRawTerminalMatrix G certificate D n orientation
        (paperDiagonalDecoupledNoise G w)‖ =
        ‖paperPartialNCKGaugeTerminalMatrix G certificate D n orientation
          (paperDiagonalDecoupledNoise G w) w‖ :=
      (norm_paperPartialNCKGaugeTerminalMatrix_eq_raw G certificate D
        orientation (paperDiagonalDecoupledNoise G w) w).symm
    _ = ‖paperIntermediateMarginalizedOrientedMatrix
          G certificate D n orientation w‖ :=
      norm_paperPartialNCKGaugeTerminalMatrix_diagonal G certificate D
        n orientation w

#print axioms paperFlattenedGaugeProductOn_eq_row_mul_col
#print axioms paperTerminalRow_mul_raw_mul_col_eq_gauge
#print axioms paperTerminalRowGaugeMatrix_mem_unitary
#print axioms paperTerminalColGaugeMatrix_mem_unitary
#print axioms paperTerminalRow_mul_gauge_mul_col_eq_raw
#print axioms norm_paperPartialNCKGaugeTerminalMatrix_eq_raw
#print axioms norm_paperPartialNCKRawTerminalMatrix_diagonal_eq_intermediate

end GraphMatrixReplica
