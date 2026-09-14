import GraphMatrix.UnconditionalMengerFlattening
import GraphMatrix.Theorem48UpperAssembly
import GraphMatrix.PartialNCKStageMatrices

/-! # Theorem 4.8 with canonical finite geometry

The Menger certificate, minimum cut, clean path family, selected edges, and
row/column sides are fixed internally.  The remaining hypotheses are exactly
the numerical partial-NCK ledger inputs (or, for the literal stage interface,
the coupled/decoupled noise arguments).
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The deterministic R/C assignment obtained by restricting an orientation
to the canonically selected ordering edges. -/
def PaperShape.unconditionalIntermediateSides
    (G : PaperShape) (orientation : Fin G.edges → Bool) :
    G.UnconditionalIntermediateRoleSides where
  edgeSide e := orientation e.1

/-- Number of edges in the canonical geometric partial-NCK chain. -/
def paperUnconditionalOrderingLength (G : PaperShape) : ℕ :=
  G.unconditionalBoundaryCleanMengerCertificate.paths.orderingEdges.card

/-- Canonical internal form of the paper's `f(α)` ordering budget. -/
def paperTheorem48CanonicalOrderingBudget (G : PaperShape) : ℕ :=
  G.toPartiteShape.intermediateOrderingBudget
    G.toPartiteShape.rightLeftSeparatorNumber

/-- Canonical internal polynomial-size exponent. -/
def paperTheorem48CanonicalSizeExponent (G : PaperShape) : ℕ :=
  G.roles - G.toPartiteShape.rightLeftSeparatorNumber +
    G.isolatedMiddleRoles.card

/-- The canonical ordering length is bounded by the internally computed
`f(α)`, with no certificate or path-family argument. -/
theorem paperUnconditionalOrderingLength_le_canonicalBudget
    (G : PaperShape) :
    paperUnconditionalOrderingLength G ≤
      paperTheorem48CanonicalOrderingBudget G := by
  have h := G.unconditionalOrderingEdges_card_le
  simpa [paperUnconditionalOrderingLength,
    paperTheorem48CanonicalOrderingBudget,
    PartiteShape.intermediateOrderingBudget] using h

/-- The old certificate-indexed budget is definitionally the canonical
separator budget after finite strong duality. -/
theorem paperTheorem48_certificateBudget_eq_canonicalBudget
    (G : PaperShape) :
    G.toPartiteShape.intermediateOrderingBudget
        G.unconditionalBoundaryCleanMengerCertificate.cut.card =
      paperTheorem48CanonicalOrderingBudget G := by
  unfold paperTheorem48CanonicalOrderingBudget
  congr 1
  exact G.unconditionalMengerCut_card_eq_separatorNumber

/-- The old certificate-indexed polynomial exponent is the canonical
separator exponent. -/
theorem paperTheorem48_certificateSizeExponent_eq_canonical
    (G : PaperShape) :
    paperTheorem48SizeExponent
        G G.unconditionalBoundaryCleanMengerCertificate =
      paperTheorem48CanonicalSizeExponent G := by
  unfold paperTheorem48SizeExponent paperTheorem48CanonicalSizeExponent
  have hCut := G.unconditionalMengerCut_card_eq_separatorNumber
  omega

/-! ## Literal stage-matrix interface without geometric parameters -/

def paperUnconditionalPartialNCKStageMatrix
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) (w : PaperDecoupledNoise G n) :=
  paperPartialNCKStageMatrix G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) n orientation i w

def paperUnconditionalPartialNCKRawStageNorm
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) (i : ℕ) : ℝ :=
  paperPartialNCKRawStageNorm G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) n orientation w i

theorem paperUnconditionalPartialNCKRawStageNorm_nonneg
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) (i : ℕ) :
    0 ≤ paperUnconditionalPartialNCKRawStageNorm G n orientation w i :=
  paperPartialNCKRawStageNorm_nonneg G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) n orientation w i

/-- At the terminal index, the canonical R/C edge sets exhaust the canonical
selected ordering prefix. -/
theorem paperUnconditionalPartialNCKStage_edges_union_terminal
    (G : PaperShape) (orientation : Fin G.edges → Bool) :
    paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation)
          (paperUnconditionalOrderingLength G) ∪
        paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation)
          (paperUnconditionalOrderingLength G) =
      paperSelectedOrderingEdges G
        G.unconditionalBoundaryCleanMengerCertificate := by
  exact paperPartialNCKStage_edges_union_at_card G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation)

/-- The canonical terminal gauge matrix is exactly the unconditional
marginalized intermediate flattening on diagonal noise. -/
theorem paperUnconditionalGaugeTerminal_diagonal_eq_intermediate
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperNoise n) :
    paperPartialNCKGaugeTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation
        (paperDiagonalDecoupledNoise G w) w =
      paperIntermediateMarginalizedOrientedMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation w :=
  paperPartialNCKGaugeTerminalMatrix_diagonal_eq_intermediate G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) n orientation w

theorem norm_paperUnconditionalGaugeTerminal_diagonal
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperNoise n) :
    ‖paperPartialNCKGaugeTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation
        (paperDiagonalDecoupledNoise G w) w‖ =
      ‖paperIntermediateMarginalizedOrientedMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation) n orientation w‖ :=
  norm_paperPartialNCKGaugeTerminalMatrix_diagonal G
    G.unconditionalBoundaryCleanMengerCertificate
    (G.unconditionalIntermediateSides orientation) n orientation w

/-! ## Upper assembly with canonical geometry -/

/-- The Theorem 4.8 upper assembly after eliminating every external finite
geometric parameter.  `B`, `hStep`, and `hMomentAtEnd` are the remaining
analytic partial-NCK/decoupling inputs. -/
theorem paperTheorem48_upper_of_unconditionalPartialNCKLedger
    (G : PaperShape)
    (B : (Fin G.edges → Bool) → ℕ → ℝ)
    (C L : ℝ) (p m n : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hm : 0 < m)
    (hLedgerNonneg : ∀ orientation i, 0 ≤ B orientation i)
    (hTerminal : ∀ orientation,
      B orientation 0 =
        paperMean (fun w : PaperNoise n =>
          ‖paperIntermediateMarginalizedOrientedMatrix G
            G.unconditionalBoundaryCleanMengerCertificate
            (G.unconditionalIntermediateSides orientation)
              n orientation w‖ ^ 2))
    (hStep : ∀ orientation i,
      B orientation (i + 1) ≤
        partialNCKSquaredStepFactor C p * B orientation i)
    (hMomentAtEnd : ∀ orientation,
      paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) ≤
      B orientation (paperUnconditionalOrderingLength G) ^ m) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) *
        (C ^ paperTheorem48CanonicalOrderingBudget G *
          Real.rpow L
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ))
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (n : ℝ)
            ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2)) := by
  have h := paperTheorem48_upper_of_partialNCKLedger G
    G.unconditionalBoundaryCleanMengerCertificate
    G.unconditionalIntermediateSides B C L p m n
    hC hL hp hn hlog hpLog hm hLedgerNonneg hTerminal hStep hMomentAtEnd
  rw [paperTheorem48_certificateBudget_eq_canonicalBudget G,
    paperTheorem48_certificateSizeExponent_eq_canonical G] at h
  exact h


end GraphMatrixReplica
