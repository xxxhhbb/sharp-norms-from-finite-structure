import R6.PaperIsolatedFormula21Application
import R6.PaperLogExponentAccounting
import R6.PaperNCKEndpoint

/-! # Assembly of the upper-bound side of Theorem 4.8

This module composes the now-unconditional combinatorial and flattening
parts of the proof.  The only remaining hypotheses in the final endpoint
are the analytic partial-NCK ledger: its one-step recurrence and the moment
comparison between the oriented graph matrix and the final ledger entry.
Those hypotheses are displayed separately and are not packaged as a hidden
certificate.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The size exponent in the Theorem 4.8 upper bound. -/
def paperTheorem48SizeExponent
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate) : ℕ :=
  G.roles - certificate.cut.card + G.isolatedMiddleRoles.card

/-- The square-root scale supplied by the concrete general-`W_iso`
formula-(21) endpoint. -/
def paperTheorem48TerminalScale
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) ^ paperTheorem48SizeExponent G certificate)

/-- Formula (21) bounds the finite-noise mean of every terminal squared
norm by the same separator power. -/
theorem paperIntermediateMarginalizedOriented_squaredNorm_mean_le
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) :
    paperMean (fun w : PaperNoise n =>
      ‖paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w‖ ^ 2) ≤
      (n : ℝ) ^ paperTheorem48SizeExponent G certificate := by
  calc
    paperMean (fun w : PaperNoise n =>
        ‖paperIntermediateMarginalizedOrientedMatrix
          G certificate D n orientation w‖ ^ 2) ≤
        paperMean (fun _w : PaperNoise n =>
          (n : ℝ) ^ paperTheorem48SizeExponent G certificate) := by
      apply paperMean_mono
      intro w
      exact paperIntermediateMarginalizedOriented_squaredNorm_le_minSeparatorPower
        G certificate D n hn orientation w
    _ = (n : ℝ) ^ paperTheorem48SizeExponent G certificate := by
      simp [paperMean]

/-- The terminal scale has square equal to the formula-(21) size power. -/
theorem paperTheorem48TerminalScale_sq
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (n : ℕ) :
    paperTheorem48TerminalScale G certificate n ^ 2 =
      (n : ℝ) ^ paperTheorem48SizeExponent G certificate := by
  unfold paperTheorem48TerminalScale
  rw [Real.sq_sqrt]
  positivity

/-- The square-root terminal scale is the literal real half power. -/
theorem paperTheorem48TerminalScale_eq_rpow
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (n : ℕ) :
    paperTheorem48TerminalScale G certificate n =
      Real.rpow (n : ℝ)
        ((paperTheorem48SizeExponent G certificate : ℝ) / 2) := by
  exact sqrt_natCast_pow_eq_rpow_half n
    (paperTheorem48SizeExponent G certificate)

/-- Theorem 4.8 upper-bound assembly endpoint, conditional only on the explicit
partial-NCK ledger.  `hStep` is the one-step analytic NCK/decoupling input;
`hMomentAtEnd` is the comparison of an oriented graph-matrix moment with the
last ledger entry.  The terminal ledger equality, formula-(21) estimate,
orientation triangle inequality, `k ≤ f(α)`, and all exponent arithmetic
are discharged in the proof. -/
theorem paperTheorem48_upper_of_partialNCKLedger
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (terminalSides : (Fin G.edges → Bool) →
      G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
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
          ‖paperIntermediateMarginalizedOrientedMatrix
            G certificate (terminalSides orientation)
              n orientation w‖ ^ 2))
    (hStep : ∀ orientation i,
      B orientation (i + 1) ≤
        partialNCKSquaredStepFactor C p * B orientation i)
    (hMomentAtEnd : ∀ orientation,
      paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) ≤
      B orientation certificate.paths.orderingEdges.card ^ m) :
    paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix G n w‖) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) *
        (C ^ (G.toPartiteShape.intermediateOrderingBudget
            certificate.cut.card) *
          Real.rpow L
            ((G.toPartiteShape.intermediateOrderingBudget
              certificate.cut.card : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ))
            ((G.toPartiteShape.intermediateOrderingBudget
              certificate.cut.card : ℝ) / 2) *
          Real.rpow (n : ℝ)
            ((paperTheorem48SizeExponent G certificate : ℝ) / 2)) := by
  classical
  let k := certificate.paths.orderingEdges.card
  let f := G.toPartiteShape.intermediateOrderingBudget certificate.cut.card
  let terminalScale := paperTheorem48TerminalScale G certificate n
  have hkf : k ≤ f := by
    exact certificate.card_orderingEdges_le
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hLog0 : 0 ≤ Real.log (n : ℝ) :=
    le_trans (by norm_num) hlog
  have hTerminalScale0 : 0 ≤ terminalScale := by
    exact Real.sqrt_nonneg _
  have hCpow : C ^ k ≤ C ^ f :=
    pow_le_pow_right₀ hC hkf
  have hHalf : (k : ℝ) / 2 ≤ (f : ℝ) / 2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkf) (by norm_num)
  have hLpow : Real.rpow L ((k : ℝ) / 2) ≤
      Real.rpow L ((f : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL hHalf
  have hLogpow : Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) ≤
      Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) :=
    log_rpow_half_mono_of_nat_le n k f hlog hkf
  have hPiece : ∀ orientation,
      paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖) ≤
        C ^ f * Real.rpow L ((f : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * terminalScale := by
    intro orientation
    have hInit : B orientation 0 ≤ terminalScale ^ 2 := by
      rw [hTerminal orientation]
      calc
        paperMean (fun w : PaperNoise n =>
            ‖paperIntermediateMarginalizedOrientedMatrix
              G certificate (terminalSides orientation)
                n orientation w‖ ^ 2) ≤
            (n : ℝ) ^ paperTheorem48SizeExponent G certificate :=
          paperIntermediateMarginalizedOriented_squaredNorm_mean_le
            G certificate (terminalSides orientation) n hn orientation
        _ = terminalScale ^ 2 := by
          symm
          exact paperTheorem48TerminalScale_sq G certificate n
    have hIter : B orientation k ≤
        partialNCKIteratedSquaredScale C p k terminalScale :=
      sequence_le_partialNCKIteratedSquaredScale
        (B orientation) C p k terminalScale hInit (hStep orientation)
    have hMoment :
        paperMean (fun w : PaperNoise n =>
          ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) ≤
        partialNCKIteratedSquaredScale C p k terminalScale ^ m :=
      (hMomentAtEnd orientation).trans
        (pow_le_pow_left₀ (hLedgerNonneg orientation k) hIter m)
    have hRaw := paperMean_le_partialNCKLogScale_of_evenMoment
      (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖)
      C L p k m n terminalScale hC0 hL0 hTerminalScale0
      hp hn hpLog hm
      (fun w => norm_nonneg (paperOrientedGraphMatrix G n orientation w))
      hMoment
    calc
      paperMean (fun w : PaperNoise n =>
          ‖paperOrientedGraphMatrix G n orientation w‖) ≤
          C ^ k * Real.rpow L ((k : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) * terminalScale := hRaw
      _ ≤ C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * terminalScale := by
        have hFirst :
            C ^ k * Real.rpow L ((k : ℝ) / 2) ≤
              C ^ f * Real.rpow L ((f : ℝ) / 2) := by
          exact mul_le_mul hCpow hLpow (Real.rpow_nonneg hL0 _)
            (pow_nonneg hC0 _)
        have hSecond :
            C ^ k * Real.rpow L ((k : ℝ) / 2) *
                Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) ≤
              C ^ f * Real.rpow L ((f : ℝ) / 2) *
                Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) := by
          exact mul_le_mul hFirst hLogpow (Real.rpow_nonneg hLog0 _)
            (mul_nonneg (pow_nonneg hC0 _) (Real.rpow_nonneg hL0 _))
        exact mul_le_mul_of_nonneg_right hSecond hTerminalScale0
  calc
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        ∑ orientation : Fin G.edges → Bool,
          paperMean (fun w : PaperNoise n =>
            ‖paperOrientedGraphMatrix G n orientation w‖) :=
      paperGraphMatrix_l2_opNorm_mean_le_sum_orientedMean G n
    _ ≤ ∑ _orientation : Fin G.edges → Bool,
          C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * terminalScale := by
      exact Finset.sum_le_sum fun orientation _ => hPiece orientation
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) *
          (C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * terminalScale) := by
      simp
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) *
        (C ^ (G.toPartiteShape.intermediateOrderingBudget
            certificate.cut.card) *
          Real.rpow L
            ((G.toPartiteShape.intermediateOrderingBudget
              certificate.cut.card : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ))
            ((G.toPartiteShape.intermediateOrderingBudget
              certificate.cut.card : ℝ) / 2) *
          Real.rpow (n : ℝ)
            ((paperTheorem48SizeExponent G certificate : ℝ) / 2)) := by
      have hScale : terminalScale =
          Real.rpow (n : ℝ)
            ((paperTheorem48SizeExponent G certificate : ℝ) / 2) :=
        paperTheorem48TerminalScale_eq_rpow G certificate n
      rw [hScale]

#print axioms
  paperIntermediateMarginalizedOriented_squaredNorm_mean_le
#print axioms paperTheorem48TerminalScale_sq
#print axioms paperTheorem48TerminalScale_eq_rpow
#print axioms paperTheorem48_upper_of_partialNCKLedger

end GraphMatrixReplica
