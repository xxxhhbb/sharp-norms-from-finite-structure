import R6.PaperTheorem48AnalyticReduction

/-! # Reduction of a concrete partial-NCK step

This file separates the analytic noncommutative Khintchine input from the
finite reindexing needed by the literal paper stages.  The generic input is an
inequality for a matrix Rademacher sum and either its row or column
flattening.  Everything in `PaperPartialNCKAlgebraicReindex` is equality data:
it says that the next selected edge gives exactly such a sum, and records the
terminal finite-product change of variables.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-! ## A generic matrix Rademacher/NCK interface -/

/-- A matrix-valued Rademacher sum using one distinguished coordinate of a
finite product of paper-noise spaces. -/
def paperMatrixRademacherSum
    {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
    [DecidableEq ι] {n : ℕ}
    (e : ι)
    (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ)
    (w : ι → PaperNoise n) : Matrix rows cols ℝ :=
  ∑ a : Fin n, ∑ b : Fin n,
    paperEdgeSign (w e) a b • A w a b

/-- Move the ordered ambient pair indexing the coefficients to the row
space. -/
def paperMatrixRademacherRowFlattening
    {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
    {n : ℕ}
    (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ)
    (w : ι → PaperNoise n) :
    Matrix (rows × (Fin n × Fin n)) cols ℝ :=
  fun r c => A w r.2.1 r.2.2 r.1 c

/-- Move the ordered ambient pair indexing the coefficients to the column
space. -/
def paperMatrixRademacherColFlattening
    {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
    {n : ℕ}
    (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ)
    (w : ι → PaperNoise n) :
    Matrix rows (cols × (Fin n × Fin n)) ℝ :=
  fun r c => A w c.2.1 c.2.2 r c.1

/-- The reusable analytic statement needed by a partial-NCK move.  The
coefficient family may depend on every other noise coordinate but must be
unchanged when the distinguished coordinate is replaced.  Both possible
flattening sides are included because the geometric orientation chooses the
side edge by edge. -/
def MatrixRademacherNCKSquared (C : ℝ) (p : ℕ) : Prop :=
  (∀ {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
      [DecidableEq ι] [DecidableEq rows] [DecidableEq cols]
      (n : ℕ) (e : ι)
      (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ),
      (∀ (w : ι → PaperNoise n) (ξ : PaperNoise n) (a b : Fin n),
        A (Function.update w e ξ) a b = A w a b) →
      paperMean (fun w : ι → PaperNoise n =>
        ‖paperMatrixRademacherSum e A w‖ ^ 2) ≤
        partialNCKSquaredStepFactor C p *
          paperMean (fun w : ι → PaperNoise n =>
            ‖paperMatrixRademacherRowFlattening A w‖ ^ 2)) ∧
  (∀ {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
      [DecidableEq ι] [DecidableEq rows] [DecidableEq cols]
      (n : ℕ) (e : ι)
      (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ),
      (∀ (w : ι → PaperNoise n) (ξ : PaperNoise n) (a b : Fin n),
        A (Function.update w e ξ) a b = A w a b) →
      paperMean (fun w : ι → PaperNoise n =>
        ‖paperMatrixRademacherSum e A w‖ ^ 2) ≤
        partialNCKSquaredStepFactor C p *
          paperMean (fun w : ι → PaperNoise n =>
            ‖paperMatrixRademacherColFlattening A w‖ ^ 2))

/-! ## The exact edge added by a stage -/

/-- The selected edge added between stages `i` and `i+1`. -/
def paperUnconditionalOrderingEdgeAt
    (G : PaperShape) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) : Fin G.edges :=
  paperOrderingEdgeAt G G.unconditionalBoundaryCleanMengerCertificate
    ⟨i, hi⟩

/-- The canonical prefix really adds exactly its `i`th ordering edge. -/
theorem paperUnconditionalOrderingPrefix_succ
    (G : PaperShape) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    paperOrderingEdgePrefix G
        G.unconditionalBoundaryCleanMengerCertificate (i + 1) =
      insert (paperUnconditionalOrderingEdgeAt G i hi)
        (paperOrderingEdgePrefix G
          G.unconditionalBoundaryCleanMengerCertificate i) := by
  classical
  unfold paperOrderingEdgePrefix paperUnconditionalOrderingEdgeAt
  let S := paperSelectedOrderingEdges G
    G.unconditionalBoundaryCleanMengerCertificate
  let q : Fin S.card := ⟨i, hi⟩
  have hFilter :
      (Finset.univ.filter fun j : Fin S.card => j.val < i + 1) =
        insert q (Finset.univ.filter fun j : Fin S.card => j.val < i) := by
    ext j
    dsimp [q]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j.val = i
      · left
        exact Fin.ext hji
      · right
        omega
    · intro hj
      rcases hj with rfl | hj
      · exact Nat.lt_succ_self i
      · omega
  rw [hFilter, Finset.image_insert]

/-- The added ordering edge was not present in the preceding prefix. -/
theorem paperUnconditionalOrderingEdgeAt_not_mem_prefix
    (G : PaperShape) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    paperUnconditionalOrderingEdgeAt G i hi ∉
      paperOrderingEdgePrefix G
        G.unconditionalBoundaryCleanMengerCertificate i := by
  classical
  intro hmem
  unfold paperOrderingEdgePrefix at hmem
  obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hmem
  have hjlt : j.val < i := by simpa using hj
  have hIndex : j = (⟨i, hi⟩ : Fin
      (paperSelectedOrderingEdges G
        G.unconditionalBoundaryCleanMengerCertificate).card) := by
    apply (Finset.orderIsoOfFin
      (paperSelectedOrderingEdges G
        G.unconditionalBoundaryCleanMengerCertificate) rfl).injective
    exact Subtype.ext hEq
  have : j.val = i := congrArg Fin.val hIndex
  omega

/-- The added edge belongs to the canonical selected ordering set. -/
theorem paperUnconditionalOrderingEdgeAt_mem_selected
    (G : PaperShape) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    paperUnconditionalOrderingEdgeAt G i hi ∈
      paperSelectedOrderingEdges G
        G.unconditionalBoundaryCleanMengerCertificate := by
  unfold paperUnconditionalOrderingEdgeAt
  exact (Finset.orderIsoOfFin
    (paperSelectedOrderingEdges G
      G.unconditionalBoundaryCleanMengerCertificate) rfl ⟨i, hi⟩).2

/-- The side of the unique edge added at this canonical stage. -/
def paperUnconditionalOrderingEdgeSide
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G) : Bool :=
  paperSelectedEdgeSide G G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation)
    ⟨paperUnconditionalOrderingEdgeAt G i hi,
      paperUnconditionalOrderingEdgeAt_mem_selected G i hi⟩

/-- On a row move, the row-edge set inserts exactly the newly ordered edge. -/
theorem paperUnconditionalStageRowEdges_succ_of_side_false
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (hSide : paperUnconditionalOrderingEdgeSide G orientation i hi = false) :
    paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) (i + 1) =
      insert (paperUnconditionalOrderingEdgeAt G i hi)
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i) := by
  classical
  unfold paperPartialNCKStageRowEdges
  rw [paperUnconditionalOrderingPrefix_succ G i hi]
  simp only [Finset.filter_insert]
  rw [if_pos]
  exact ⟨paperUnconditionalOrderingEdgeAt_mem_selected G i hi, hSide⟩

/-- On a row move, the column-edge set is unchanged. -/
theorem paperUnconditionalStageColEdges_succ_of_side_false
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (hSide : paperUnconditionalOrderingEdgeSide G orientation i hi = false) :
    paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) (i + 1) =
      paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) i := by
  classical
  unfold paperPartialNCKStageColEdges
  rw [paperUnconditionalOrderingPrefix_succ G i hi]
  simp only [Finset.filter_insert]
  rw [if_neg]
  intro h
  exact Bool.false_ne_true (hSide.symm.trans h.2)

/-- On a column move, the column-edge set inserts exactly the newly ordered
edge. -/
theorem paperUnconditionalStageColEdges_succ_of_side_true
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (hSide : paperUnconditionalOrderingEdgeSide G orientation i hi = true) :
    paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) (i + 1) =
      insert (paperUnconditionalOrderingEdgeAt G i hi)
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) i) := by
  classical
  unfold paperPartialNCKStageColEdges
  rw [paperUnconditionalOrderingPrefix_succ G i hi]
  simp only [Finset.filter_insert]
  rw [if_pos]
  exact ⟨paperUnconditionalOrderingEdgeAt_mem_selected G i hi, hSide⟩

/-- On a column move, the row-edge set is unchanged. -/
theorem paperUnconditionalStageRowEdges_succ_of_side_true
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (hSide : paperUnconditionalOrderingEdgeSide G orientation i hi = true) :
    paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) (i + 1) =
      paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) i := by
  classical
  unfold paperPartialNCKStageRowEdges
  rw [paperUnconditionalOrderingPrefix_succ G i hi]
  simp only [Finset.filter_insert]
  rw [if_neg]
  intro h
  have hBad : true = false := hSide.symm.trans h.2
  exact Bool.noConfusion hBad

/-! ## Equality-only stage witnesses -/

/-- Row-side realization of one raw stage as a Rademacher sum.  The last
field records the norm-preserving finite reindex from the next literal stage
to the row-flattened coefficient matrix. -/
structure PaperRowStageRademacherWitness
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) where
  edge : Fin G.edges
  coefficients :
    PaperDecoupledNoise G n → Fin n → Fin n →
      Matrix
        (PaperYRowIndex G n
          (paperPartialNCKStageRowEdges G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation) i))
        (PaperYColIndex G n
          (paperPartialNCKStageColEdges G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation) i)) ℝ
  independent : ∀ w ξ a b,
    coefficients (Function.update w edge ξ) a b = coefficients w a b
  before_eq : ∀ w,
    paperUnconditionalPartialNCKStageMatrix G n orientation i w =
      paperMatrixRademacherSum edge coefficients w
  after_norm_eq : ∀ w,
    ‖paperUnconditionalPartialNCKStageMatrix G n orientation (i + 1) w‖ =
      ‖paperMatrixRademacherRowFlattening coefficients w‖

/-- Column-side counterpart of `PaperRowStageRademacherWitness`. -/
structure PaperColStageRademacherWitness
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) where
  edge : Fin G.edges
  coefficients :
    PaperDecoupledNoise G n → Fin n → Fin n →
      Matrix
        (PaperYRowIndex G n
          (paperPartialNCKStageRowEdges G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation) i))
        (PaperYColIndex G n
          (paperPartialNCKStageColEdges G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation) i)) ℝ
  independent : ∀ w ξ a b,
    coefficients (Function.update w edge ξ) a b = coefficients w a b
  before_eq : ∀ w,
    paperUnconditionalPartialNCKStageMatrix G n orientation i w =
      paperMatrixRademacherSum edge coefficients w
  after_norm_eq : ∀ w,
    ‖paperUnconditionalPartialNCKStageMatrix G n orientation (i + 1) w‖ =
      ‖paperMatrixRademacherColFlattening coefficients w‖

/-- The sole remaining finite-algebraic reindex package.  It contains no
inequality.  The first field is the uniform finite-product change of variables
identifying the raw terminal mean with the coupled marginalized terminal
mean.  The second field is the row/column Rademacher decomposition of each
actual successor stage. -/
structure PaperPartialNCKAlgebraicReindex (G : PaperShape) (n : ℕ) : Prop where
  terminal_mean_eq : ∀ orientation : Fin G.edges → Bool,
    paperUnconditionalDecoupledSquaredStageMean G n orientation
        (paperUnconditionalOrderingLength G) =
      paperTheorem48AnalyticLedger G n orientation 0
  stage_decomposition : ∀ (orientation : Fin G.edges → Bool) (i : ℕ),
    ∀ hi : i < paperUnconditionalOrderingLength G,
      (∃ hRow : PaperRowStageRademacherWitness G n orientation i,
        hRow.edge = paperUnconditionalOrderingEdgeAt G i hi) ∨
      (∃ hCol : PaperColStageRademacherWitness G n orientation i,
        hCol.edge = paperUnconditionalOrderingEdgeAt G i hi)

/-! ## Applying the generic NCK input -/

/-- A generic matrix Rademacher/NCK inequality immediately gives every raw
forward stage estimate once the equality-only stage reindex is supplied. -/
theorem paperUnconditionalRawStage_step_of_matrixRademacherNCK
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hNCK : MatrixRademacherNCKSquared C p)
    (hAlg : PaperPartialNCKAlgebraicReindex G n)
    (orientation : Fin G.edges → Bool) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    paperUnconditionalDecoupledSquaredStageMean G n orientation i ≤
      partialNCKSquaredStepFactor C p *
        paperUnconditionalDecoupledSquaredStageMean G n orientation (i + 1) := by
  rcases hAlg.stage_decomposition orientation i hi with hRow | hCol
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

/-- The precise reduction theorem: the generic matrix NCK inequality plus the
single equality-only reindex package proves the concrete unconditional
one-step input used by Theorem 4.8. -/
theorem paperUnconditionalPartialNCKOneStep_of_matrixRademacherNCK
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hNCK : MatrixRademacherNCKSquared C p)
    (hAlg : PaperPartialNCKAlgebraicReindex G n) :
    PaperUnconditionalPartialNCKOneStep G n p C := by
  intro orientation i hi
  let k := paperUnconditionalOrderingLength G
  have hik : i + 1 ≤ k := by omega
  by_cases hi0 : i = 0
  · subst i
    by_cases hk : k = 0
    · omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hraw := paperUnconditionalRawStage_step_of_matrixRademacherNCK
        G C p n hNCK hAlg orientation (k - 1) (by omega)
      have hsucc : k - 1 + 1 = k := by omega
      have hmin1 : min 1 k = 1 := Nat.min_eq_left hkpos
      rw [hsucc, hAlg.terminal_mean_eq orientation] at hraw
      simpa [paperTheorem48AnalyticLedger, k, hk, hmin1] using hraw
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    let j := k - (i + 1)
    have hjlt : j < k := by
      dsimp [j]
      omega
    have hraw := paperUnconditionalRawStage_step_of_matrixRademacherNCK
      G C p n hNCK hAlg orientation j hjlt
    have hj : j = k - (i + 1) := rfl
    have hji : j + 1 = k - i := by
      dsimp [j]
      omega
    rw [hji] at hraw
    simpa [paperTheorem48AnalyticLedger, k, Nat.min_eq_left hik,
      Nat.min_eq_left (Nat.le_of_lt hi), hi0, Nat.ne_of_gt hiPos,
      hj] using hraw

/-- Direct upper-bound assembly from the generic matrix NCK statement.  The
only non-analytic argument is `hAlg`, whose fields are finite equalities and
coordinate-independence facts rather than estimates. -/
theorem paperTheorem48_upper_of_matrixRademacherNCK
    (G : PaperShape)
    (C L : ℝ) (p m n : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hm : 0 < m)
    (hShared : PaperSharedCoupledToDecoupledComparison G n m)
    (hNCK : MatrixRademacherNCKSquared C p)
    (hAlg : PaperPartialNCKAlgebraicReindex G n) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) *
        (C ^ paperTheorem48CanonicalOrderingBudget G *
          Real.rpow L
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ))
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (n : ℝ)
            ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2)) := by
  exact paperTheorem48_upper_of_two_analytic_inputs G C L p m n
    hC hL hp hn hlog hpLog hm hShared
    (paperUnconditionalPartialNCKOneStep_of_matrixRademacherNCK
      G C p n hNCK hAlg)

#print axioms paperUnconditionalOrderingPrefix_succ
#print axioms paperUnconditionalRawStage_step_of_matrixRademacherNCK
#print axioms paperUnconditionalPartialNCKOneStep_of_matrixRademacherNCK
#print axioms paperTheorem48_upper_of_matrixRademacherNCK

end GraphMatrixReplica
