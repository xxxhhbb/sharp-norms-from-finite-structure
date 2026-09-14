import R6.PaperTheorem48StageSpecificAssembly
import R6.PaperRademacherMatrixDyadicMoment
import R6.PaperRademacherCatalanTraceBridge

/-! # Honest branch-tree reduction for the paper's partial NCK step

The graph orientation and the row/column choice in formula (28) are two
different pieces of data.  In particular, the canonical object
`unconditionalIntermediateSides orientation` follows only one branch of the
binary row/column tree.  This file therefore introduces an independent side
assignment `D`, exposes both children `D[e := false]` and `D[e := true]`, and
states the dyadic trace obligation sufficient for the resulting sum
recurrence.

The coefficient noise coordinate is the unordered ambient edge
`Sym2 (Fin n)`.  Ordered endpoint pairs may be used internally to construct a
coefficient, but they must be aggregated over the corresponding `Sym2` fiber
before applying an independent-sign trace expansion.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

set_option maxHeartbeats 800000

/-! ## Independent branch data -/

/-- The row/column branch assignment for the canonical Menger ordering.  It
is deliberately not a graph orientation. -/
abbrev PaperCanonicalNCKSides (G : PaperShape) :=
  G.UnconditionalIntermediateRoleSides

/-- The selected edge at a branch-tree level, bundled with its membership in
the canonical ordering set. -/
def paperCanonicalOrderingEdgeSubtype
    (G : PaperShape) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    {e : Fin G.edges // e ∈ paperSelectedOrderingEdges G
      G.unconditionalBoundaryCleanMengerCertificate} :=
  ⟨paperUnconditionalOrderingEdgeAt G i hi,
    paperUnconditionalOrderingEdgeAt_mem_selected G i hi⟩

/-- Replace the row/column decision at the current selected edge. -/
def paperCanonicalNCKSideUpdate
    {G : PaperShape} (D : PaperCanonicalNCKSides G)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (side : Bool) : PaperCanonicalNCKSides G where
  edgeSide := Function.update D.edgeSide
    (paperCanonicalOrderingEdgeSubtype G i hi) side

@[simp] theorem paperCanonicalNCKSideUpdate_self
    {G : PaperShape} (D : PaperCanonicalNCKSides G)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (side : Bool) :
    (paperCanonicalNCKSideUpdate D i hi side).edgeSide
        (paperCanonicalOrderingEdgeSubtype G i hi) = side := by
  exact Function.update_self _ _ _

/-- Extensionality for the one-field branch-assignment structure. -/
theorem paperCanonicalNCKSides_ext
    {G : PaperShape} {D E : PaperCanonicalNCKSides G}
    (h : D.edgeSide = E.edgeSide) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- Updating the current edge with its existing value leaves the assignment
unchanged. -/
theorem paperCanonicalNCKSideUpdate_eq_self
    {G : PaperShape} (D : PaperCanonicalNCKSides G)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G) :
    paperCanonicalNCKSideUpdate D i hi
        (D.edgeSide (paperCanonicalOrderingEdgeSubtype G i hi)) = D := by
  apply paperCanonicalNCKSides_ext
  funext e
  by_cases he : e = paperCanonicalOrderingEdgeSubtype G i hi
  · subst e
    exact Function.update_self _ _ _
  · exact Function.update_of_ne he _ _

/-- The two children at every genuine level are different assignments. -/
theorem paperCanonicalNCKSideUpdate_false_ne_true
    {G : PaperShape} (D : PaperCanonicalNCKSides G)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G) :
    paperCanonicalNCKSideUpdate D i hi false ≠
      paperCanonicalNCKSideUpdate D i hi true := by
  intro h
  have hAt := congrArg
    (fun E : PaperCanonicalNCKSides G =>
      E.edgeSide (paperCanonicalOrderingEdgeSubtype G i hi)) h
  simpa using hAt

/-! ## Audit of the former one-branch interface -/

/-- The old canonical side assignment is definitionally the restriction of
the graph orientation.  Hence it cannot represent the independent branch
variable required by the binary formula-(28) iteration. -/
@[simp] theorem paperUnconditionalIntermediateSides_edgeSide
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (e : {e : Fin G.edges // e ∈ paperSelectedOrderingEdges G
      G.unconditionalBoundaryCleanMengerCertificate}) :
    (G.unconditionalIntermediateSides orientation).edgeSide e =
      orientation e.1 := rfl

/-- At a fixed orientation the old assignment chooses exactly one of the two
children at the current level.  The other child is not represented by the
same side assignment. -/
theorem paperOrientationSelectedBranch_eq_one_child
    (G : PaperShape) (orientation : Fin G.edges → Bool)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G) :
    paperCanonicalNCKSideUpdate
        (G.unconditionalIntermediateSides orientation) i hi
        (orientation (paperUnconditionalOrderingEdgeAt G i hi)) =
      G.unconditionalIntermediateSides orientation := by
  exact paperCanonicalNCKSideUpdate_eq_self
    (G.unconditionalIntermediateSides orientation) i hi

/-! ## `Sym2` is the independent sign coordinate -/

/-- Aggregate an ordered-pair coefficient family over unordered ambient-edge
fibers.  This is the coefficient family seen by the independent paper sign. -/
def paperSym2AggregatedCoefficientFamily
    {n : ℕ} {rows cols : Type}
    (A : Fin n → Fin n → Matrix rows cols ℝ) :
    Sym2 (Fin n) → Matrix rows cols ℝ :=
  fun z row col => ∑ x : Fin n × Fin n,
    if s(x.1, x.2) = z then A x.1 x.2 row col else 0

/-- Regrouping ordered endpoint coefficients by their true unordered noise
coordinate. -/
theorem paperRademacherMatrixSum_sym2_aggregate
    {n : ℕ} {rows cols : Type}
    [Fintype rows] [Fintype cols]
    (A : Fin n → Fin n → Matrix rows cols ℝ)
    (ξ : Sym2 (Fin n) → Bool) :
    paperRademacherMatrixSum
        (paperSym2AggregatedCoefficientFamily A) ξ =
      ∑ a : Fin n, ∑ b : Fin n,
        paperSign (ξ s(a, b)) • A a b := by
  classical
  ext row col
  unfold paperRademacherMatrixSum paperSym2AggregatedCoefficientFamily
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-! ## The honest branch-tree squared recurrence -/

/-- Mean squared norm at a node `D` of the independent row/column branch
tree.  The graph orientation remains a separate parameter. -/
def paperBranchSquaredStageMean
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ) : ℝ :=
  paperMean (fun w : PaperDecoupledNoise G n =>
    paperPartialNCKRawStageNorm G
      G.unconditionalBoundaryCleanMengerCertificate D n orientation w stage ^ 2)

theorem paperBranchSquaredStageMean_nonneg
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ) :
    0 ≤ paperBranchSquaredStageMean G n orientation D stage := by
  unfold paperBranchSquaredStageMean paperMean
  positivity

/-- Formula-(28)-shaped input: every branch node is bounded using the sum of
both row and column children.  This is strictly richer than the former
orientation-selected, one-child recurrence. -/
def PaperBranchTreeRawNCKSquared
    (G : PaperShape) (C : ℝ) (p n : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (stage : ℕ)
      (hstage : stage < paperUnconditionalOrderingLength G)
      (D : PaperCanonicalNCKSides G),
    paperBranchSquaredStageMean G n orientation D stage ≤
      partialNCKSquaredStepFactor C p *
        (paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate D stage hstage false) (stage + 1) +
          paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate D stage hstage true) (stage + 1))

/-- The dimension hypothesis which accompanies the trace/Catalan estimate at
every node.  It is explicit rather than hidden in a universal matrix-NCK
assumption. -/
def PaperBranchTreeDimensionLogCondition
    (G : PaperShape) (p n : ℕ) : Prop :=
  ∀ (_orientation : Fin G.edges → Bool) (stage : ℕ)
      (_hstage : stage < paperUnconditionalOrderingLength G)
      (D : PaperCanonicalNCKSides G),
    Real.log
        ((max
          (Fintype.card (PaperYRowIndex G n
            (paperPartialNCKStageRowEdges G
              G.unconditionalBoundaryCleanMengerCertificate D stage)))
          (Fintype.card (PaperYColIndex G n
            (paperPartialNCKStageColEdges G
              G.unconditionalBoundaryCleanMengerCertificate D stage))) : ℕ) : ℝ) ≤
      (p : ℝ)

/-- Honest analytic ledger: orientation and branch assignment are independent,
the current node is the literal raw stage mean, and both children occur in
the one-step inequality. -/
structure PaperBranchTreeRawLedger
    (G : PaperShape) (C : ℝ) (p n : ℕ) : Prop where
  dimensionLog : PaperBranchTreeDimensionLogCondition G p n
  branchStep : PaperBranchTreeRawNCKSquared G C p n

/-! ## Dyadic trace reduction at every branch node -/

/-- The remaining explicit dyadic trace obligation.  Its right side contains
the sum of the two independently updated children.  Catalan/even-word
estimates should be used to establish precisely this statement. -/
def PaperBranchTreeDyadicTraceBound
    (G : PaperShape) (C : ℝ) (p n q : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (stage : ℕ)
      (hstage : stage < paperUnconditionalOrderingLength G)
      (D : PaperCanonicalNCKSides G),
    paperMean (fun w : PaperDecoupledNoise G n =>
      Matrix.trace
        ((paperPartialNCKStageMatrix G
              G.unconditionalBoundaryCleanMengerCertificate D
              n orientation stage w *
            (paperPartialNCKStageMatrix G
              G.unconditionalBoundaryCleanMengerCertificate D
              n orientation stage w).transpose) ^ (2 ^ q))) ≤
      (partialNCKSquaredStepFactor C p *
        (paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate D stage hstage false) (stage + 1) +
          paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate D stage hstage true) (stage + 1))) ^
        (2 ^ q)

/-- Jensen plus the deterministic norm-to-Gram-trace inequality turn the
explicit dyadic trace estimate into the honest two-child squared recurrence. -/
theorem paperBranchTreeRawNCKSquared_of_dyadicTraceBound
    (G : PaperShape) (C : ℝ) (p n q : ℕ)
    (hTrace : PaperBranchTreeDyadicTraceBound G C p n q) :
    PaperBranchTreeRawNCKSquared G C p n := by
  intro orientation stage hstage D
  let B := partialNCKSquaredStepFactor C p *
    (paperBranchSquaredStageMean G n orientation
        (paperCanonicalNCKSideUpdate D stage hstage false) (stage + 1) +
      paperBranchSquaredStageMean G n orientation
        (paperCanonicalNCKSideUpdate D stage hstage true) (stage + 1))
  have hB : 0 ≤ B := mul_nonneg
    (partialNCKSquaredStepFactor_nonneg C p)
    (add_nonneg
      (paperBranchSquaredStageMean_nonneg G n orientation
        (paperCanonicalNCKSideUpdate D stage hstage false) (stage + 1))
      (paperBranchSquaredStageMean_nonneg G n orientation
        (paperCanonicalNCKSideUpdate D stage hstage true) (stage + 1)))
  apply paperMean_le_of_mean_pow_le_pow
    (fun w : PaperDecoupledNoise G n =>
      paperPartialNCKRawStageNorm G
        G.unconditionalBoundaryCleanMengerCertificate D
        n orientation w stage ^ 2)
    (2 ^ q) B (by positivity) (fun w => sq_nonneg _) hB
  calc
    paperMean (fun w : PaperDecoupledNoise G n =>
        (paperPartialNCKRawStageNorm G
          G.unconditionalBoundaryCleanMengerCertificate D
          n orientation w stage ^ 2) ^ (2 ^ q)) ≤
      paperMean (fun w : PaperDecoupledNoise G n =>
        Matrix.trace
          ((paperPartialNCKStageMatrix G
                G.unconditionalBoundaryCleanMengerCertificate D
                n orientation stage w *
              (paperPartialNCKStageMatrix G
                G.unconditionalBoundaryCleanMengerCertificate D
                n orientation stage w).transpose) ^ (2 ^ q))) := by
        apply paperMean_mono
        intro w
        simpa [paperPartialNCKRawStageNorm, pow_mul] using
          (matrix_l2_opNorm_pow_dyadic_le_gramTrace
            (paperPartialNCKStageMatrix G
              G.unconditionalBoundaryCleanMengerCertificate D
              n orientation stage w) q)
    _ ≤ B ^ (2 ^ q) := hTrace orientation stage hstage D

/-- Bundle the explicit dimension condition with the trace-derived branch
recurrence. -/
theorem paperBranchTreeRawLedger_of_dyadicTraceBound
    (G : PaperShape) (C : ℝ) (p n q : ℕ)
    (hDim : PaperBranchTreeDimensionLogCondition G p n)
    (hTrace : PaperBranchTreeDyadicTraceBound G C p n q) :
    PaperBranchTreeRawLedger G C p n :=
  ⟨hDim, paperBranchTreeRawNCKSquared_of_dyadicTraceBound
    G C p n q hTrace⟩

#print axioms paperCanonicalNCKSideUpdate_false_ne_true
#print axioms paperOrientationSelectedBranch_eq_one_child
#print axioms paperRademacherMatrixSum_sym2_aggregate
#print axioms paperBranchTreeRawNCKSquared_of_dyadicTraceBound
#print axioms paperBranchTreeRawLedger_of_dyadicTraceBound

end GraphMatrixReplica
