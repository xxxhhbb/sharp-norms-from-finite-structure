import GraphMatrix.Theorem48UpperAssembly

/-! # A concrete partial-NCK moment ledger

The ledger in this file is not an arbitrary numerical sequence: it is the
finite-noise `2m`-moment of an explicit family of intermediate chaos norms.
Its nonnegativity is automatic.  A terminal norm identification makes the
initial formula-(21) bound a theorem, while a final norm identification is
the explicit coupled/decoupled endpoint interface.  The sole analytic
inequality left is the adjacent-stage partial-NCK estimate.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The concrete `2m`-moment ledger of an explicit sequence of chaos norms. -/
def paperPartialNCKConcreteMomentLedger
    {α : Type} [Fintype α]
    (m : ℕ) (stageNorm : ℕ → α → ℝ) (i : ℕ) : ℝ :=
  paperMean (fun a => stageNorm i a ^ (2 * m))

/-- Every concrete moment-ledger entry is nonnegative. -/
theorem paperPartialNCKConcreteMomentLedger_nonneg
    {α : Type} [Fintype α]
    (m : ℕ) (stageNorm : ℕ → α → ℝ) (i : ℕ) :
    0 ≤ paperPartialNCKConcreteMomentLedger m stageNorm i := by
  unfold paperPartialNCKConcreteMomentLedger paperMean
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro a _
    rw [pow_mul]
    positivity

/-- If stage zero is the actual marginalized intermediate flattening, its
ledger entry is bounded unconditionally by formula (21). -/
theorem paperPartialNCKConcreteMomentLedger_zero_le_sizePower
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (orientation : Fin G.edges → Bool)
    (m n : ℕ)
    (stageNorm : ℕ → PaperNoise n → ℝ)
    (hn : 1 ≤ n)
    (hTerminalNorm : ∀ w,
      stageNorm 0 w =
        ‖paperIntermediateMarginalizedOrientedMatrix
          G certificate D n orientation w‖) :
    paperPartialNCKConcreteMomentLedger m stageNorm 0 ≤
      ((n : ℝ) ^ paperTheorem48SizeExponent G certificate) ^ m := by
  calc
    paperPartialNCKConcreteMomentLedger m stageNorm 0 =
        paperMean (fun w : PaperNoise n =>
          (‖paperIntermediateMarginalizedOrientedMatrix
            G certificate D n orientation w‖ ^ 2) ^ m) := by
      unfold paperPartialNCKConcreteMomentLedger
      congr 1
      funext w
      rw [hTerminalNorm w, pow_mul]
    _ ≤ paperMean (fun _w : PaperNoise n =>
          ((n : ℝ) ^ paperTheorem48SizeExponent G certificate) ^ m) := by
      apply paperMean_mono
      intro w
      apply pow_le_pow_left₀
      · positivity
      · exact paperIntermediateMarginalizedOriented_squaredNorm_le_minSeparatorPower
          G certificate D n hn orientation w
    _ = ((n : ℝ) ^ paperTheorem48SizeExponent G certificate) ^ m := by
      simp [paperMean]

/-- The final norm identification turns the last concrete ledger entry into
the oriented graph-matrix moment exactly. -/
theorem paperPartialNCKConcreteMomentLedger_final_eq
    (G : PaperShape) (n m k : ℕ)
    (orientation : Fin G.edges → Bool)
    (stageNorm : ℕ → PaperNoise n → ℝ)
    (hFinalNorm : ∀ w,
      stageNorm k w = ‖paperOrientedGraphMatrix G n orientation w‖) :
    paperPartialNCKConcreteMomentLedger m stageNorm k =
      paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) := by
  unfold paperPartialNCKConcreteMomentLedger
  congr 1
  funext w
  rw [hFinalNorm w]

/-- Iterating the sole adjacent-stage NCK inequality and using the concrete
terminal formula-(21) bound yields the standard iterated squared scale. -/
theorem paperOrientedMoment_le_iteratedScale_of_concreteLedger
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (orientation : Fin G.edges → Bool)
    (C : ℝ) (p m n : ℕ) (hn : 1 ≤ n)
    (stageNorm : ℕ → PaperNoise n → ℝ)
    (hTerminalNorm : ∀ w,
      stageNorm 0 w =
        ‖paperIntermediateMarginalizedOrientedMatrix
          G certificate D n orientation w‖)
    (hFinalNorm : ∀ w,
      stageNorm certificate.paths.orderingEdges.card w =
        ‖paperOrientedGraphMatrix G n orientation w‖)
    (hStep : ∀ i,
      paperPartialNCKConcreteMomentLedger m stageNorm (i + 1) ≤
        partialNCKSquaredStepFactor C p ^ m *
          paperPartialNCKConcreteMomentLedger m stageNorm i) :
    paperMean (fun w : PaperNoise n =>
      ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) ≤
      partialNCKIteratedSquaredScale C p
        certificate.paths.orderingEdges.card
        (paperTheorem48TerminalScale G certificate n) ^ m := by
  let k := certificate.paths.orderingEdges.card
  let ledger := paperPartialNCKConcreteMomentLedger m stageNorm
  let stepFactor := partialNCKSquaredStepFactor C p
  have hLedgerZero : ledger 0 ≤
      ((n : ℝ) ^ paperTheorem48SizeExponent G certificate) ^ m := by
    exact paperPartialNCKConcreteMomentLedger_zero_le_sizePower
      G certificate D orientation m n stageNorm hn hTerminalNorm
  have hIter : ledger k ≤ stepFactor ^ (m * k) * ledger 0 := by
    calc
      ledger k ≤ (stepFactor ^ m) ^ k * ledger 0 :=
        sequence_le_geometric_of_step ledger (stepFactor ^ m)
          (pow_nonneg (partialNCKSquaredStepFactor_nonneg C p) m)
          hStep k
      _ = stepFactor ^ (m * k) * ledger 0 := by
        rw [← pow_mul]
  have hScale : ledger k ≤
      stepFactor ^ (m * k) *
        ((n : ℝ) ^ paperTheorem48SizeExponent G certificate) ^ m :=
    hIter.trans (mul_le_mul_of_nonneg_left hLedgerZero
      (pow_nonneg (partialNCKSquaredStepFactor_nonneg C p) _))
  calc
    paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) =
        ledger k := by
      symm
      exact paperPartialNCKConcreteMomentLedger_final_eq
        G n m k orientation stageNorm hFinalNorm
    _ ≤ stepFactor ^ (m * k) *
          ((n : ℝ) ^ paperTheorem48SizeExponent G certificate) ^ m := hScale
    _ = partialNCKIteratedSquaredScale C p k
          (paperTheorem48TerminalScale G certificate n) ^ m := by
      rw [partialNCKIteratedSquaredScale,
        paperTheorem48TerminalScale_sq]
      simp only [mul_pow, ← pow_mul]
      rw [Nat.mul_comm m k]

/-- Theorem 4.8 upper assembly with a concrete matrix-norm ledger.  Apart
from the two explicit endpoint identifications, the only analytic inequality
assumed is `hStep`, the adjacent-stage partial-NCK estimate. -/
theorem paperTheorem48_upper_of_concretePartialNCK
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (terminalSides : (Fin G.edges → Bool) →
      G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (C L : ℝ) (p m n : ℕ)
    (stageNorm : (Fin G.edges → Bool) → ℕ → PaperNoise n → ℝ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hm : 0 < m)
    (hTerminalNorm : ∀ orientation w,
      stageNorm orientation 0 w =
        ‖paperIntermediateMarginalizedOrientedMatrix
          G certificate (terminalSides orientation)
            n orientation w‖)
    (hFinalNorm : ∀ orientation w,
      stageNorm orientation certificate.paths.orderingEdges.card w =
        ‖paperOrientedGraphMatrix G n orientation w‖)
    (hStep : ∀ orientation i,
      paperPartialNCKConcreteMomentLedger m (stageNorm orientation) (i + 1) ≤
        partialNCKSquaredStepFactor C p ^ m *
          paperPartialNCKConcreteMomentLedger m (stageNorm orientation) i) :
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
  have hkf : k ≤ f := certificate.card_orderingEdges_le
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hLog0 : 0 ≤ Real.log (n : ℝ) := le_trans (by norm_num) hlog
  have hTerminalScale0 : 0 ≤ terminalScale := Real.sqrt_nonneg _
  have hCpow : C ^ k ≤ C ^ f := pow_le_pow_right₀ hC hkf
  have hHalf : (k : ℝ) / 2 ≤ (f : ℝ) / 2 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hkf) (by norm_num)
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
    have hMoment :=
      paperOrientedMoment_le_iteratedScale_of_concreteLedger
        G certificate (terminalSides orientation) orientation C p m n hn
        (stageNorm orientation) (hTerminalNorm orientation)
        (hFinalNorm orientation) (hStep orientation)
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
              C ^ f * Real.rpow L ((f : ℝ) / 2) :=
          mul_le_mul hCpow hLpow (Real.rpow_nonneg hL0 _)
            (pow_nonneg hC0 _)
        have hSecond :
            C ^ k * Real.rpow L ((k : ℝ) / 2) *
                Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) ≤
              C ^ f * Real.rpow L ((f : ℝ) / 2) *
                Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) :=
          mul_le_mul hFirst hLogpow (Real.rpow_nonneg hLog0 _)
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


end GraphMatrixReplica
