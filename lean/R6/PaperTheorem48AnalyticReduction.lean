import R6.PaperTheorem48UnconditionalGeometry

/-! # Theorem 4.8 reduced to two analytic inputs

The finite geometry is now completely canonical.  This file fixes a concrete
numeric ledger built from the literal decoupled partial-NCK stage matrices and
packages the two remaining analytic statements:

* comparison of the shared/coupled oriented chaos with the decoupled endpoint;
* the one-step partial-NCK estimate along the reversed stage chain.

The stage index is clipped at the canonical ordering length.  Consequently the
ledger is constant after the last relevant stage, and the one-step hypothesis
is required only for indices strictly before that length.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The mean squared norm of one literal, canonically parameterized,
decoupled partial-NCK stage. -/
def paperUnconditionalDecoupledSquaredStageMean
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (stage : ℕ) : ℝ :=
  paperMean (fun w : PaperDecoupledNoise G n =>
    paperUnconditionalPartialNCKRawStageNorm G n orientation w stage ^ 2)

theorem paperUnconditionalDecoupledSquaredStageMean_nonneg
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (stage : ℕ) :
    0 ≤ paperUnconditionalDecoupledSquaredStageMean G n orientation stage := by
  unfold paperUnconditionalDecoupledSquaredStageMean paperMean
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro w _hw
    positivity

/-- The canonical analytic ledger, read from the terminal flattening back to
the fully random chaos.  Index zero is the already identified marginalized
terminal matrix.  Positive indices use the literal decoupled raw stages in
reverse order.  Clipping by `min` makes the ledger constant past the canonical
ordering length.

For the degenerate zero-length chain the unique endpoint is the terminal
quantity, so no artificial decoupling step is introduced. -/
def paperTheorem48AnalyticLedger
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) : ℝ :=
  let k := paperUnconditionalOrderingLength G
  let j := min i k
  if j = 0 then
    paperMean (fun w : PaperNoise n =>
      ‖paperIntermediateMarginalizedOrientedMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation)
        n orientation w‖ ^ 2)
  else
    paperUnconditionalDecoupledSquaredStageMean G n orientation (k - j)

@[simp] theorem paperTheorem48AnalyticLedger_zero
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperTheorem48AnalyticLedger G n orientation 0 =
      paperMean (fun w : PaperNoise n =>
        ‖paperIntermediateMarginalizedOrientedMatrix G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation)
          n orientation w‖ ^ 2) := by
  simp [paperTheorem48AnalyticLedger]

theorem paperTheorem48AnalyticLedger_nonneg
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (i : ℕ) :
    0 ≤ paperTheorem48AnalyticLedger G n orientation i := by
  unfold paperTheorem48AnalyticLedger
  dsimp only
  split_ifs
  · unfold paperMean
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro w _hw
      positivity
  · exact paperUnconditionalDecoupledSquaredStageMean_nonneg G n
      orientation _

/-- The first and only endpoint input: the even moment of the original
shared-noise oriented matrix is controlled by the endpoint of the concrete
decoupled stage ledger.  When the canonical chain has length zero, the two
endpoints coincide and the statement correctly reduces to its degenerate
coupled form. -/
def PaperSharedCoupledToDecoupledComparison
    (G : PaperShape) (n m : ℕ) : Prop :=
  ∀ orientation : Fin G.edges → Bool,
    paperMean (fun w : PaperNoise n =>
      ‖paperOrientedGraphMatrix G n orientation w‖ ^ (2 * m)) ≤
      paperTheorem48AnalyticLedger G n orientation
        (paperUnconditionalOrderingLength G) ^ m

/-- The second and only iterative input: one partial-NCK step for every
genuinely active transition of the clipped reverse ledger. -/
def PaperUnconditionalPartialNCKOneStep
    (G : PaperShape) (n p : ℕ) (C : ℝ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (i : ℕ),
    i < paperUnconditionalOrderingLength G →
      paperTheorem48AnalyticLedger G n orientation (i + 1) ≤
        partialNCKSquaredStepFactor C p *
          paperTheorem48AnalyticLedger G n orientation i

/-- Beyond the canonical ordering length the clipped analytic ledger is
constant. -/
theorem paperTheorem48AnalyticLedger_eq_of_orderingLength_le
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    {i j : ℕ}
    (hi : paperUnconditionalOrderingLength G ≤ i)
    (hj : paperUnconditionalOrderingLength G ≤ j) :
    paperTheorem48AnalyticLedger G n orientation i =
      paperTheorem48AnalyticLedger G n orientation j := by
  simp only [paperTheorem48AnalyticLedger, Nat.min_eq_right hi,
    Nat.min_eq_right hj]

/-- Numerical hypotheses already present in Theorem 4.8 make a constant tail
of the ledger satisfy the globally quantified step interface used by the old
assembly theorem. -/
theorem paperTheorem48AnalyticLedger_step_all
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hC : 1 ≤ C) (hp : 1 ≤ p)
    (hStep : PaperUnconditionalPartialNCKOneStep G n p C) :
    ∀ (orientation : Fin G.edges → Bool) (i : ℕ),
      paperTheorem48AnalyticLedger G n orientation (i + 1) ≤
        partialNCKSquaredStepFactor C p *
          paperTheorem48AnalyticLedger G n orientation i := by
  intro orientation i
  by_cases hi : i < paperUnconditionalOrderingLength G
  · exact hStep orientation i hi
  · have hki : paperUnconditionalOrderingLength G ≤ i :=
      Nat.le_of_not_gt hi
    have hki1 : paperUnconditionalOrderingLength G ≤ i + 1 :=
      hki.trans (Nat.le_add_right i 1)
    have hEq :
        paperTheorem48AnalyticLedger G n orientation (i + 1) =
          paperTheorem48AnalyticLedger G n orientation i :=
      paperTheorem48AnalyticLedger_eq_of_orderingLength_le G n orientation
        hki1 hki
    have hpReal : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hp
    have hC2 : (1 : ℝ) ≤ C ^ 2 := by
      nlinarith [sq_nonneg (C - 1)]
    have hFactor : (1 : ℝ) ≤ partialNCKSquaredStepFactor C p := by
      unfold partialNCKSquaredStepFactor
      calc
        (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ C ^ 2 * (p : ℝ) :=
          mul_le_mul hC2 hpReal (by norm_num) (by positivity)
    rw [hEq]
    exact le_mul_of_one_le_left
      (paperTheorem48AnalyticLedger_nonneg G n orientation i) hFactor

/-- Theorem 4.8 after the complete finite-geometric reduction.  No cut,
path family, separator, edge ordering, R/C side assignment, or terminal gauge
is exposed.  Besides the standard numerical regime, the only assumptions are
the named coupled-to-decoupled endpoint comparison and the named one-step
partial-NCK inequality. -/
theorem paperTheorem48_upper_of_two_analytic_inputs
    (G : PaperShape)
    (C L : ℝ) (p m n : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hpLog : (p : ℝ) ≤ L * Real.log (n : ℝ))
    (hm : 0 < m)
    (hShared : PaperSharedCoupledToDecoupledComparison G n m)
    (hPartialNCK : PaperUnconditionalPartialNCKOneStep G n p C) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) *
        (C ^ paperTheorem48CanonicalOrderingBudget G *
          Real.rpow L
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (Real.log (n : ℝ))
            ((paperTheorem48CanonicalOrderingBudget G : ℝ) / 2) *
          Real.rpow (n : ℝ)
            ((paperTheorem48CanonicalSizeExponent G : ℝ) / 2)) := by
  apply paperTheorem48_upper_of_unconditionalPartialNCKLedger G
    (paperTheorem48AnalyticLedger G n) C L p m n
    hC hL hp hn hlog hpLog hm
  · exact fun orientation i =>
      paperTheorem48AnalyticLedger_nonneg G n orientation i
  · exact fun orientation => paperTheorem48AnalyticLedger_zero G n orientation
  · exact paperTheorem48AnalyticLedger_step_all G C p n hC hp hPartialNCK
  · exact hShared

#print axioms paperUnconditionalDecoupledSquaredStageMean_nonneg
#print axioms paperTheorem48AnalyticLedger_step_all
#print axioms paperTheorem48_upper_of_two_analytic_inputs

end GraphMatrixReplica
