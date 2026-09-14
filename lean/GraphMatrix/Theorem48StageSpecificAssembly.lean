import GraphMatrix.Theorem48RawFinalAssembly

/-! # Theorem 4.8 from stage-specific raw NCK estimates

The generic `MatrixRademacherNCKSquared` interface quantifies over arbitrary
finite matrix families.  The paper only needs finitely many concrete raw
stage inequalities.  This module states precisely those inequalities and
reruns the corrected raw-ledger assembly from that weaker input.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Exactly the raw squared-mean NCK inequalities visited by the canonical
paper construction.  There is no quantification over unrelated matrices. -/
def PaperStageSpecificRawNCKSquared
    (G : PaperShape) (C : ℝ) (p n : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (stage : ℕ),
    stage < paperUnconditionalOrderingLength G →
      paperUnconditionalDecoupledSquaredStageMean G n orientation stage ≤
        partialNCKSquaredStepFactor C p *
          paperUnconditionalDecoupledSquaredStageMean G n orientation
            (stage + 1)

/-- The stage-specific forward inequalities give the corrected reverse-ledger
recurrence. -/
theorem paperTheorem48RawAnalyticLedger_step_of_stageSpecific
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hStage : PaperStageSpecificRawNCKSquared G C p n)
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
  have h := hStage orientation j hjlt
  have hsucc : j + 1 = k - i := by
    dsimp [j]
    omega
  rw [hsucc] at h
  simpa [paperTheorem48RawAnalyticLedger, k,
    Nat.min_eq_left (Nat.le_of_lt hi),
    Nat.min_eq_left (by omega : i + 1 ≤ k), j] using h

/-- Raw-ledger iteration from only the concrete paper-stage inequalities. -/
theorem paperTheorem48RawAnalyticLedger_iterated_of_stageSpecific
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hn : 1 ≤ n)
    (hStage : PaperStageSpecificRawNCKSquared G C p n)
    (orientation : Fin G.edges → Bool) :
    paperTheorem48RawAnalyticLedger G n orientation
        (paperUnconditionalOrderingLength G) ≤
      partialNCKIteratedSquaredScale C p
        (paperUnconditionalOrderingLength G)
        (Real.sqrt ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G)) := by
  let k := paperUnconditionalOrderingLength G
  let D := Real.sqrt ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G)
  have hInit : paperTheorem48RawAnalyticLedger G n orientation 0 ≤ D ^ 2 := by
    calc
      paperTheorem48RawAnalyticLedger G n orientation 0 =
          paperUnconditionalDecoupledSquaredStageMean G n orientation k := by
        simp [paperTheorem48RawAnalyticLedger, k]
      _ ≤ (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G :=
        paperUnconditionalFinalLiteralStage_mean_le_canonicalPower_unconditional
          G n hn orientation
      _ = D ^ 2 := by
        symm
        dsimp [D]
        rw [Real.sq_sqrt]
        positivity
  have hIter :
      paperTheorem48RawAnalyticLedger G n orientation k ≤
        partialNCKSquaredStepFactor C p ^ k *
          paperTheorem48RawAnalyticLedger G n orientation 0 := by
    exact sequence_le_geometric_of_step_lt
      (paperTheorem48RawAnalyticLedger G n orientation)
      (partialNCKSquaredStepFactor C p)
      (partialNCKSquaredStepFactor_nonneg C p) k
      (fun i hi => paperTheorem48RawAnalyticLedger_step_of_stageSpecific
        G C p n hStage orientation i hi)
  calc
    paperTheorem48RawAnalyticLedger G n orientation k ≤
        partialNCKSquaredStepFactor C p ^ k *
          paperTheorem48RawAnalyticLedger G n orientation 0 := hIter
    _ ≤ partialNCKSquaredStepFactor C p ^ k * D ^ 2 := by
      exact mul_le_mul_of_nonneg_left hInit
        (pow_nonneg (partialNCKSquaredStepFactor_nonneg C p) k)
    _ = partialNCKIteratedSquaredScale C p k D := rfl

/-- Final canonical Theorem 4.8 upper assembly using only the actual paper
stages and the genuine high-moment coupled-to-raw comparison. -/
theorem paperTheorem48_upper_of_stageSpecificRawNCK
    (G : PaperShape)
    (C L : ℝ) (p m n : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hm : 0 < m)
    (hCoupled : PaperSharedCoupledToRawDecoupledComparison G n m)
    (hStage : PaperStageSpecificRawNCKSquared G C p n) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) *
        (C ^ paperTheorem48CanonicalOrderingBudget G *
          Real.rpow L
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ))
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (n : ℝ)
            ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2)) := by
  classical
  let k := paperUnconditionalOrderingLength G
  let f := paperTheorem48CanonicalOrderingBudget G
  let D := Real.sqrt ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G)
  have hkf : k ≤ f := paperUnconditionalOrderingLength_le_canonicalBudget G
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hLog0 : 0 ≤ Real.log (n : ℝ) := le_trans (by norm_num) hlog
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hCpow : C ^ k ≤ C ^ f := pow_le_pow_right₀ hC hkf
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
          Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D := by
    intro orientation
    have hIter : paperTheorem48RawAnalyticLedger G n orientation k ≤
        partialNCKIteratedSquaredScale C p k D :=
      paperTheorem48RawAnalyticLedger_iterated_of_stageSpecific
        G C p n hn hStage orientation
    have hMoment :
        paperMean (fun w : PaperNoise n =>
          ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) ≤
        partialNCKIteratedSquaredScale C p k D ^ m :=
      (hCoupled orientation).trans
        (pow_le_pow_left₀
          (paperTheorem48RawAnalyticLedger_nonneg G n orientation k)
          hIter m)
    have hRaw := paperMean_le_partialNCKLogScale_of_evenMoment
      (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖)
      C L p k m n D hC0 hL0 hD0 hp hn hpLog hm
      (fun w => norm_nonneg (paperOrientedGraphMatrix G n orientation w))
      hMoment
    calc
      paperMean (fun w : PaperNoise n =>
          ‖paperOrientedGraphMatrix G n orientation w‖) ≤
          C ^ k * Real.rpow L ((k : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) * D := hRaw
      _ ≤ C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D := by
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
        exact mul_le_mul_of_nonneg_right hSecond hD0
  calc
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        ∑ orientation : Fin G.edges → Bool,
          paperMean (fun w : PaperNoise n =>
            ‖paperOrientedGraphMatrix G n orientation w‖) :=
      paperGraphMatrix_l2_opNorm_mean_le_sum_orientedMean G n
    _ ≤ ∑ _orientation : Fin G.edges → Bool,
          C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D := by
      exact Finset.sum_le_sum fun orientation _ => hPiece orientation
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) *
          (C ^ f * Real.rpow L ((f : ℝ) / 2) *
            Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) * D) := by
      simp
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) *
        (C ^ paperTheorem48CanonicalOrderingBudget G *
          Real.rpow L
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ))
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (n : ℝ)
            ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2)) := by
      have hScale : D = Real.rpow (n : ℝ)
          ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2) :=
        sqrt_natCast_pow_eq_rpow_half n
          (paperTheorem48CanonicalSizeExponent G)
      rw [hScale]


end GraphMatrixReplica
