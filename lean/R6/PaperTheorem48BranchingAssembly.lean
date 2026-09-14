import R6.PaperStageSpecificNCKTraceReduction
import R6.PaperPartialNCKBranchingStages
import R6.PaperRademacherDecoupledStageZeroGlue

/-! # Theorem 4.8 assembled through the full NCK branch tree

This assembly keeps graph orientation and row/column NCK branching
independent.  Every level contributes both children, every terminal branch is
bounded by the arbitrary-side formula-(21) compression theorem, and the
resulting exact binary loss is retained through the square-root endpoint.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

set_option maxHeartbeats 800000

/-! ## Connecting total side updates to list histories -/

theorem paperCanonicalOrderingEdgeSubtype_eq_paperNCKBranchEdge
    (G : PaperShape) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    paperCanonicalOrderingEdgeSubtype G i hi =
      paperNCKBranchEdge G i hi := by
  apply Subtype.ext
  rfl

theorem paperCanonicalNCKSideUpdate_branchSides
    (G : PaperShape) (history : List Bool)
    (hi : history.length < paperUnconditionalOrderingLength G)
    (side : Bool) :
    paperCanonicalNCKSideUpdate (paperNCKBranchSides G history)
        history.length hi side =
      paperNCKBranchSides G (paperNCKBranchChild side history) := by
  rw [paperNCKBranchSides_child G history hi side]
  apply paperCanonicalNCKSides_ext
  unfold paperCanonicalNCKSideUpdate paperNCKUpdateSide
  rw [paperCanonicalOrderingEdgeSubtype_eq_paperNCKBranchEdge G
    history.length hi]

theorem paperBranchSquaredStageMean_branchSides
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (history : List Bool) :
    paperBranchSquaredStageMean G n orientation
        (paperNCKBranchSides G history) history.length =
      paperNCKBranchSquaredStageMean G n orientation history := by
  rfl

/-- The total-assignment two-child premise restricts to the concrete
newest-first history tree used by the finite branching ledger. -/
theorem paperPartialNCKBranchingSumSquared_of_branchTree
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hBranch : PaperBranchTreeRawNCKSquared G C p n) :
    PaperPartialNCKBranchingSumSquared G C p n := by
  intro orientation history hi
  have h := hBranch orientation history.length hi
    (paperNCKBranchSides G history)
  calc
    paperNCKBranchSquaredStageMean G n orientation history =
        paperBranchSquaredStageMean G n orientation
          (paperNCKBranchSides G history) history.length :=
      (paperBranchSquaredStageMean_branchSides
        G n orientation history).symm
    _ ≤ partialNCKSquaredStepFactor C p *
        (paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate (paperNCKBranchSides G history)
              history.length hi false) (history.length + 1) +
          paperBranchSquaredStageMean G n orientation
            (paperCanonicalNCKSideUpdate (paperNCKBranchSides G history)
              history.length hi true) (history.length + 1)) := h
    _ = partialNCKSquaredStepFactor C p *
        (paperNCKBranchSquaredStageMean G n orientation
            (paperNCKBranchChild false history) +
          paperNCKBranchSquaredStageMean G n orientation
            (paperNCKBranchChild true history)) := by
      rw [paperCanonicalNCKSideUpdate_branchSides G history hi false,
        paperCanonicalNCKSideUpdate_branchSides G history hi true]
      have hFalse :
          paperBranchSquaredStageMean G n orientation
              (paperNCKBranchSides G (paperNCKBranchChild false history))
              (history.length + 1) =
            paperNCKBranchSquaredStageMean G n orientation
              (paperNCKBranchChild false history) := by
        simpa [paperNCKBranchChild_length] using
          (paperBranchSquaredStageMean_branchSides G n orientation
            (paperNCKBranchChild false history))
      have hTrue :
          paperBranchSquaredStageMean G n orientation
              (paperNCKBranchSides G (paperNCKBranchChild true history))
              (history.length + 1) =
            paperNCKBranchSquaredStageMean G n orientation
              (paperNCKBranchChild true history) := by
        simpa [paperNCKBranchChild_length] using
          (paperBranchSquaredStageMean_branchSides G n orientation
            (paperNCKBranchChild true history))
      rw [hFalse, hTrue]

/-! ## The branch-root first moment -/

/-- Changing only propositionally equal finite row/column edge sets does not
change the norm of the corresponding literal matrix. -/
theorem norm_paperYMatrix_congr_edges
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n)
    {R R' C C' : Finset (Fin G.edges)}
    (hR : R = R') (hC : C = C') :
    ‖paperYMatrix G n orientation R C w‖ =
      ‖paperYMatrix G n orientation R' C' w‖ := by
  subst R'
  subst C'
  rfl

/-- At level zero the branch-history matrix and the former total-side stage
matrix have the same empty row/column index sets. -/
theorem paperNCKBranchStageNorm_nil_eq_unconditionalStageZero
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    ‖paperNCKBranchStageMatrix G n orientation [] w‖ =
      paperUnconditionalPartialNCKRawStageNorm G n orientation w 0 := by
  classical
  unfold paperNCKBranchStageMatrix
    paperUnconditionalPartialNCKRawStageNorm paperPartialNCKRawStageNorm
    paperPartialNCKStageMatrix
  simp only [List.length_nil]
  have hRowBranch :
      paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G []) 0 = ∅ :=
    paperPartialNCKStageRowEdges_zero G
      G.unconditionalBoundaryCleanMengerCertificate _
  have hColBranch :
      paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G []) 0 = ∅ :=
    paperPartialNCKStageColEdges_zero G
      G.unconditionalBoundaryCleanMengerCertificate _
  have hRowOld :
      paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) 0 = ∅ :=
    paperPartialNCKStageRowEdges_zero G
      G.unconditionalBoundaryCleanMengerCertificate _
  have hColOld :
      paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation) 0 = ∅ :=
    paperPartialNCKStageColEdges_zero G
      G.unconditionalBoundaryCleanMengerCertificate _
  exact norm_paperYMatrix_congr_edges G n orientation w
    (hRowBranch.trans hRowOld.symm) (hColBranch.trans hColOld.symm)

theorem paperNCKBranchSquaredStageMean_nil_eq_unconditionalStageZero
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperNCKBranchSquaredStageMean G n orientation [] =
      paperMean (fun w : PaperDecoupledNoise G n =>
        paperUnconditionalPartialNCKRawStageNorm G n orientation w 0 ^ 2) := by
  apply congrArg paperMean
  funext w
  rw [← paperNCKBranchStageNorm_nil_eq_unconditionalStageZero]

/-- Full binary iteration, Cauchy--Schwarz, and logarithmic moment transfer
at the exact canonical ordering length. -/
theorem paperRawStageZero_mean_le_branchingLogScale
    (G : PaperShape) (C L : ℝ) (p n : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hBranch : PaperBranchTreeRawNCKSquared G C p n)
    (orientation : Fin G.edges → Bool) :
    paperMean (fun w : PaperDecoupledNoise G n =>
      paperUnconditionalPartialNCKRawStageNorm G n orientation w 0) ≤
      Real.sqrt 2 ^ paperUnconditionalOrderingLength G *
        C ^ paperUnconditionalOrderingLength G *
        Real.rpow L ((paperUnconditionalOrderingLength G : ℝ) / 2) *
        Real.rpow (Real.log (n : ℝ))
          ((paperUnconditionalOrderingLength G : ℝ) / 2) *
        Real.sqrt ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G) := by
  let k := paperUnconditionalOrderingLength G
  let D := Real.sqrt ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G)
  let S := partialNCKSquaredStepFactor C p ^ k *
    ((2 : ℝ) ^ k * D ^ 2)
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hPower0 : 0 ≤ (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G :=
    by positivity
  have hDsq : D ^ 2 =
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
    exact Real.sq_sqrt hPower0
  have hSquared := paperNCKBranchStageZero_le_of_sumSquared
    G C p n hn
      (paperPartialNCKBranchingSumSquared_of_branchTree
        G C p n hBranch) orientation
  rw [paperNCKBranchSquaredStageMean_nil_eq_unconditionalStageZero,
    ← hDsq] at hSquared
  have hS0 : 0 ≤ S := by
    unfold S
    exact mul_nonneg
      (pow_nonneg (partialNCKSquaredStepFactor_nonneg C p) k)
      (mul_nonneg (pow_nonneg (by norm_num) k) (sq_nonneg D))
  have hMeanRoot :
      paperMean (fun w : PaperDecoupledNoise G n =>
        paperUnconditionalPartialNCKRawStageNorm G n orientation w 0) ≤
        Real.sqrt S := by
    apply paperMean_le_of_mean_pow_le_pow
      (fun w : PaperDecoupledNoise G n =>
        paperUnconditionalPartialNCKRawStageNorm G n orientation w 0)
      2 (Real.sqrt S) (by norm_num)
      (fun w => paperUnconditionalPartialNCKRawStageNorm_nonneg
        G n orientation w 0) (Real.sqrt_nonneg _)
    calc
      paperMean (fun w : PaperDecoupledNoise G n =>
          paperUnconditionalPartialNCKRawStageNorm G n orientation w 0 ^ 2) ≤
          S := by simpa [S, k] using hSquared
      _ = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
  have hRoot := sqrt_natCast_pow_le_const_mul_log_rpow_half
    L p k n hL0 hp hn hpLog
  calc
    paperMean (fun w : PaperDecoupledNoise G n =>
        paperUnconditionalPartialNCKRawStageNorm G n orientation w 0) ≤
        Real.sqrt S := hMeanRoot
    _ = Real.sqrt 2 ^ k * C ^ k * Real.sqrt ((p : ℝ) ^ k) * D := by
      exact sqrt_paperNCKBranchingSquaredScale C p k D hC0 hD0
    _ ≤ Real.sqrt 2 ^ k * C ^ k *
        (Real.rpow L ((k : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2)) * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRoot
          (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) k)
            (pow_nonneg hC0 k))) hD0
    _ = Real.sqrt 2 ^ paperUnconditionalOrderingLength G *
        C ^ paperUnconditionalOrderingLength G *
        Real.rpow L ((paperUnconditionalOrderingLength G : ℝ) / 2) *
        Real.rpow (Real.log (n : ℝ))
          ((paperUnconditionalOrderingLength G : ℝ) / 2) *
        Real.sqrt ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G) := by
      dsimp [k, D]
      ring

/-! ## Canonical-budget and orientation assembly -/

/-- Faithful branching upper bound from the honest two-child raw recurrence.
The explicit `sqrt(2)^f` is the cost of summing all `2^f` leaves before
taking the square root. -/
theorem paperTheorem48_upper_of_branchTreeRawNCK
    (G : PaperShape) (C L : ℝ) (p n : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hBranch : PaperBranchTreeRawNCKSquared G C p n) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) *
        ((G.edges : ℝ) ^ G.edges *
          (Real.sqrt 2 ^ paperTheorem48CanonicalOrderingBudget G *
            C ^ paperTheorem48CanonicalOrderingBudget G *
            Real.rpow L
              ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ))
              ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
            Real.rpow (n : ℝ)
              ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2))) := by
  classical
  let k := paperUnconditionalOrderingLength G
  let f := paperTheorem48CanonicalOrderingBudget G
  let D := Real.sqrt ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G)
  have hkf : k ≤ f := paperUnconditionalOrderingLength_le_canonicalBudget G
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hLog0 : 0 ≤ Real.log (n : ℝ) := le_trans (by norm_num) hlog
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hSqrtTwo : 1 ≤ Real.sqrt 2 :=
    Real.one_le_sqrt.mpr (by norm_num)
  have hTwoPow : Real.sqrt 2 ^ k ≤ Real.sqrt 2 ^ f :=
    pow_le_pow_right₀ hSqrtTwo hkf
  have hCpow : C ^ k ≤ C ^ f := pow_le_pow_right₀ hC hkf
  have hHalf : (k : ℝ) / 2 ≤ (f : ℝ) / 2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkf) (by norm_num)
  have hLpow : Real.rpow L ((k : ℝ) / 2) ≤
      Real.rpow L ((f : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL hHalf
  have hLogpow : Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) ≤
      Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) :=
    log_rpow_half_mono_of_nat_le n k f hlog hkf
  have hRawPiece : ∀ orientation,
      paperMean (fun w : PaperDecoupledNoise G n =>
        paperUnconditionalPartialNCKRawStageNorm G n orientation w 0) ≤
        Real.sqrt 2 ^ f * C ^ f * Real.rpow L ((f : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D := by
    intro orientation
    have hRaw := paperRawStageZero_mean_le_branchingLogScale
      G C L p n hC hL hp hn hpLog hBranch orientation
    calc
      paperMean (fun w : PaperDecoupledNoise G n =>
          paperUnconditionalPartialNCKRawStageNorm G n orientation w 0) ≤
          Real.sqrt 2 ^ k * C ^ k * Real.rpow L ((k : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) * D := hRaw
      _ ≤ Real.sqrt 2 ^ f * C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D := by
        have hFirst : Real.sqrt 2 ^ k * C ^ k ≤
            Real.sqrt 2 ^ f * C ^ f :=
          mul_le_mul hTwoPow hCpow (pow_nonneg hC0 _)
            (pow_nonneg (Real.sqrt_nonneg 2) _)
        have hSecond : Real.sqrt 2 ^ k * C ^ k *
              Real.rpow L ((k : ℝ) / 2) ≤
            Real.sqrt 2 ^ f * C ^ f *
              Real.rpow L ((f : ℝ) / 2) :=
          mul_le_mul hFirst hLpow (Real.rpow_nonneg hL0 _)
            (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) _)
              (pow_nonneg hC0 _))
        have hThird : Real.sqrt 2 ^ k * C ^ k *
                Real.rpow L ((k : ℝ) / 2) *
                Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) ≤
            Real.sqrt 2 ^ f * C ^ f *
                Real.rpow L ((f : ℝ) / 2) *
                Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) :=
          mul_le_mul hSecond hLogpow (Real.rpow_nonneg hLog0 _)
            (mul_nonneg
              (mul_nonneg (pow_nonneg (Real.sqrt_nonneg 2) _)
                (pow_nonneg hC0 _))
              (Real.rpow_nonneg hL0 _))
        exact mul_le_mul_of_nonneg_right hThird hD0
  have hPiece : ∀ orientation,
      paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖) ≤
        (G.edges : ℝ) ^ G.edges *
          (Real.sqrt 2 ^ f * C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D) := by
    intro orientation
    exact
      (paperMean_norm_orientedMatrix_le_edges_pow_edges_mul_rawStageZero
        G n orientation).trans
      (mul_le_mul_of_nonneg_left (hRawPiece orientation) (by positivity))
  calc
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        ∑ orientation : Fin G.edges → Bool,
          paperMean (fun w : PaperNoise n =>
            ‖paperOrientedGraphMatrix G n orientation w‖) :=
      paperGraphMatrix_l2_opNorm_mean_le_sum_orientedMean G n
    _ ≤ ∑ _orientation : Fin G.edges → Bool,
        (G.edges : ℝ) ^ G.edges *
          (Real.sqrt 2 ^ f * C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D) := by
      exact Finset.sum_le_sum fun orientation _ => hPiece orientation
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) *
        ((G.edges : ℝ) ^ G.edges *
          (Real.sqrt 2 ^ f * C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D)) := by
      simp
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) *
        ((G.edges : ℝ) ^ G.edges *
          (Real.sqrt 2 ^ paperTheorem48CanonicalOrderingBudget G *
            C ^ paperTheorem48CanonicalOrderingBudget G *
            Real.rpow L
              ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ))
              ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
            Real.rpow (n : ℝ)
              ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2))) := by
      have hScale : D = Real.rpow (n : ℝ)
          ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2) :=
        sqrt_natCast_pow_eq_rpow_half n
          (paperTheorem48CanonicalSizeExponent G)
      rw [hScale]

/-- Final trace-level formulation.  Its only analytic premises are the
explicit per-node dimension/log condition and the actual-stage dyadic
Gram-trace bound; the two-child NCK recurrence is derived internally. -/
theorem paperTheorem48_upper_of_branchTreeDyadicTrace
    (G : PaperShape) (C L : ℝ) (p n q : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hDim : PaperBranchTreeDimensionLogCondition G p n)
    (hTrace : PaperBranchTreeDyadicTraceBound G C p n q) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) *
        ((G.edges : ℝ) ^ G.edges *
          (Real.sqrt 2 ^ paperTheorem48CanonicalOrderingBudget G *
            C ^ paperTheorem48CanonicalOrderingBudget G *
            Real.rpow L
              ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ))
              ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
            Real.rpow (n : ℝ)
              ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2))) := by
  have hLedger := paperBranchTreeRawLedger_of_dyadicTraceBound
    G C p n q hDim hTrace
  exact paperTheorem48_upper_of_branchTreeRawNCK
    G C L p n hC hL hp hn hlog hpLog hLedger.branchStep

#print axioms paperPartialNCKBranchingSumSquared_of_branchTree
#print axioms paperRawStageZero_mean_le_branchingLogScale
#print axioms paperTheorem48_upper_of_branchTreeRawNCK
#print axioms paperTheorem48_upper_of_branchTreeDyadicTrace

end GraphMatrixReplica
