import R6.PaperPartialNCKStageReindexIsometry

/-! # Uniform bound for the raw decoupled terminal stage

The residual noise at the raw terminal may use a different noise copy for
each shape edge.  Formula (21) only needs the pointwise unit bound, so the
isolated-role marginalization and covered-support argument remain valid.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-! ## Zero padding does not increase the L2 operator norm -/

/-- Adding zero row and column blocks to a finite matrix cannot increase its
`ℓ₂` operator norm. -/
theorem paper_l2_opNorm_fromBlocks_zero_le
    {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    (A : Matrix m n ℝ) :
    ‖Matrix.fromBlocks A (0 : Matrix m n' ℝ)
        (0 : Matrix m' n ℝ) (0 : Matrix m' n' ℝ)‖ ≤ ‖A‖ := by
  classical
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro x
  let xLeft : EuclideanSpace ℝ n :=
    WithLp.toLp 2 (fun j => x (Sum.inl j))
  have hxLeft : ‖xLeft‖ ≤ ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    gcongr
    simp only [xLeft, Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hA := Matrix.l2_opNorm_mulVec A xLeft
  have hOutput :
      ‖(EuclideanSpace.equiv (m ⊕ m') ℝ).symm <|
          (Matrix.fromBlocks A (0 : Matrix m n' ℝ)
            (0 : Matrix m' n ℝ) (0 : Matrix m' n' ℝ)).mulVec x‖ =
        ‖(EuclideanSpace.equiv m ℝ).symm <| A.mulVec xLeft‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Matrix.mulVec, Matrix.fromBlocks, dotProduct, xLeft,
      Fintype.sum_sum_type]
  change ‖(EuclideanSpace.equiv (m ⊕ m') ℝ).symm <|
      (Matrix.fromBlocks A (0 : Matrix m n' ℝ)
        (0 : Matrix m' n ℝ) (0 : Matrix m' n' ℝ)).mulVec x‖ ≤
    ‖A‖ * ‖x‖
  rw [hOutput]
  exact hA.trans (mul_le_mul_of_nonneg_left hxLeft (norm_nonneg A))

/-! ## Residual edge signs on covered assignments -/

/-- The raw residual sign product, evaluated on the non-isolated roles. -/
def paperCoveredDecoupledNoiseProductOn
    (G : PaperShape) {n : ℕ} (Z : Finset (Fin G.edges))
    (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) : ℝ :=
  ∏ e ∈ Z, paperEdgeSign (decoupled e)
    (covered ⟨G.source e, G.source_mem_coveredRoles_isolatedMiddle e⟩)
    (covered ⟨G.target e, G.target_mem_coveredRoles_isolatedMiddle e⟩)

theorem abs_paperCoveredDecoupledNoiseProductOn_eq_one
    (G : PaperShape) {n : ℕ} (Z : Finset (Fin G.edges))
    (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    |paperCoveredDecoupledNoiseProductOn G Z decoupled covered| = 1 := by
  classical
  unfold paperCoveredDecoupledNoiseProductOn
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro e _he
  unfold paperEdgeSign
  split <;> norm_num

/-- The residual covered weight before imposing covered injectivity. -/
def paperCoveredRawTerminalCoreAmplitude
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) : ℝ := by
  classical
  exact if paperCoveredOrientationCompatible G orientation covered then
    paperCoveredDecoupledNoiseProductOn G Z decoupled covered
  else 0

/-- Covered raw weight, including the injectivity indicator needed for the
uniform hidden-fiber cardinality. -/
def paperCoveredInjectiveRawTerminalAmplitude
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) : ℝ := by
  classical
  exact if Function.Injective covered then
    paperCoveredRawTerminalCoreAmplitude G n orientation Z decoupled covered
  else 0

theorem abs_paperCoveredInjectiveRawTerminalAmplitude_le_one
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    |paperCoveredInjectiveRawTerminalAmplitude
      G n orientation Z decoupled covered| ≤ 1 := by
  classical
  unfold paperCoveredInjectiveRawTerminalAmplitude
    paperCoveredRawTerminalCoreAmplitude
  by_cases hi : Function.Injective covered <;>
    by_cases ho : paperCoveredOrientationCompatible G orientation covered <;>
    simp [hi, ho, abs_paperCoveredDecoupledNoiseProductOn_eq_one]

/-- The residual decoupled product does not see isolated middle labels. -/
theorem paperDecoupledNoiseProductOn_merge_eq_covered
    (G : PaperShape) {n : ℕ} (Z : Finset (Fin G.edges))
    (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles))
    (hidden : PaperVisibleTuple n G.isolatedMiddleRoles) :
    paperDecoupledNoiseProductOn G Z decoupled
        (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden) =
      paperCoveredDecoupledNoiseProductOn G Z decoupled covered := by
  classical
  unfold paperDecoupledNoiseProductOn
    paperCoveredDecoupledNoiseProductOn
  apply Finset.prod_congr rfl
  intro e _he
  rw [mergeCoveredIsolatedAssignment_apply_covered
      G.isolatedMiddleRoles covered hidden (G.source e)
        (G.source_mem_coveredRoles_isolatedMiddle e),
    mergeCoveredIsolatedAssignment_apply_covered
      G.isolatedMiddleRoles covered hidden (G.target e)
        (G.target_mem_coveredRoles_isolatedMiddle e)]

/-- Full-assignment summand appearing in a raw terminal entry. -/
def paperRawTerminalAssignmentAmplitude
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (decoupled : PaperDecoupledNoise G n)
    (assignment : PaperAssignment G n) : ℝ :=
  paperOrientedAssignmentWeight G orientation assignment *
    paperDecoupledNoiseProductOn G Z decoupled assignment

theorem paperRawTerminalAssignmentAmplitude_merge_eq
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles))
    (hidden : PaperVisibleTuple n G.isolatedMiddleRoles) :
    paperRawTerminalAssignmentAmplitude G n orientation Z decoupled
        (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden) =
      if Function.Injective (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden) then
        paperCoveredRawTerminalCoreAmplitude
          G n orientation Z decoupled covered
      else 0 := by
  classical
  unfold paperRawTerminalAssignmentAmplitude paperOrientedAssignmentWeight
    paperCoveredRawTerminalCoreAmplitude
  rw [paperAssignmentOrientationCompatible_merge_iff,
    paperDecoupledNoiseProductOn_merge_eq_covered]
  by_cases hi : Function.Injective (mergeCoveredIsolatedAssignment
      G.isolatedMiddleRoles covered hidden) <;>
    by_cases ho : paperCoveredOrientationCompatible G orientation covered <;>
    simp [hi, ho]

/-! ## Exact isolated-fiber factorization -/

theorem sum_hidden_paperRawTerminalAssignmentAmplitude_eq
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (decoupled : PaperDecoupledNoise G n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    (∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
      paperRawTerminalAssignmentAmplitude G n orientation Z decoupled
        (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden)) =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) *
        paperCoveredInjectiveRawTerminalAmplitude
          G n orientation Z decoupled covered := by
  classical
  rw [show (∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
      paperRawTerminalAssignmentAmplitude G n orientation Z decoupled
        (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden)) =
      ∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
        if Function.Injective (mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden) then
          paperCoveredRawTerminalCoreAmplitude
            G n orientation Z decoupled covered
        else 0 by
      apply Finset.sum_congr rfl
      intro hidden _
      exact paperRawTerminalAssignmentAmplitude_merge_eq
        G n orientation Z decoupled covered hidden]
  rw [sum_hidden_if_merge_injective_eq_card_mul]
  by_cases hc : Function.Injective covered
  · rw [card_injectiveHiddenFiber_of_injective
      G.isolatedMiddleRoles covered hc]
    simp [paperCoveredInjectiveRawTerminalAmplitude, hc]
  · rw [card_injectiveHiddenFiber_of_not_injective
      G.isolatedMiddleRoles covered hc]
    simp [paperCoveredInjectiveRawTerminalAmplitude, hc]

theorem sum_assignment_if_covered_test_paperRawTerminalAmplitude_eq
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (Z : Finset (Fin G.edges)) (decoupled : PaperDecoupledNoise G n)
    (test : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → Prop)
    [DecidablePred test] :
    (∑ assignment : PaperAssignment G n,
      if test (paperAssignmentRestriction
          (coveredRoles G.isolatedMiddleRoles) assignment) then
        paperRawTerminalAssignmentAmplitude
          G n orientation Z decoupled assignment
      else 0) =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) *
        ∑ covered : PaperVisibleTuple n
            (coveredRoles G.isolatedMiddleRoles),
          if test covered then
            paperCoveredInjectiveRawTerminalAmplitude
              G n orientation Z decoupled covered
          else 0 := by
  classical
  rw [sum_assignment_eq_sum_covered_sum_isolated]
  calc
    _ = ∑ covered : PaperVisibleTuple n
          (coveredRoles G.isolatedMiddleRoles),
        if test covered then
          ∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
            paperRawTerminalAssignmentAmplitude G n orientation Z decoupled
              (mergeCoveredIsolatedAssignment
                G.isolatedMiddleRoles covered hidden)
        else 0 := by
      apply Finset.sum_congr rfl
      intro covered _
      simp only [paperAssignmentRestriction_merge_covered]
      by_cases ht : test covered <;> simp [ht]
    _ = ∑ covered : PaperVisibleTuple n
          (coveredRoles G.isolatedMiddleRoles),
        if test covered then
          ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
              G.isolatedMiddleRoles.card : ℕ) *
            paperCoveredInjectiveRawTerminalAmplitude
              G n orientation Z decoupled covered
        else 0 := by
      apply Finset.sum_congr rfl
      intro covered _
      by_cases ht : test covered
      · simp only [ht, if_true]
        exact sum_hidden_paperRawTerminalAssignmentAmplitude_eq
          G n orientation Z decoupled covered
      · simp [ht]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro covered _
      by_cases ht : test covered <;> simp [ht]

/-! ## Covered formula-(21) data and the raw terminal -/

/-- Nearly-combinatorial data for the raw terminal covered core. -/
def paperRawTerminalCoveredCoreData
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) :
    PaperNearlyCombinatorialFlatteningData
      (PaperCoveredRole G) n D.coveredRowRoles D.coveredColRoles where
  weight := paperCoveredInjectiveRawTerminalAmplitude G n orientation
    (Finset.univ \ paperCertificateOrderingEdges G certificate) decoupled
  weight_abs_le_one :=
    abs_paperCoveredInjectiveRawTerminalAmplitude_le_one G n orientation
      (Finset.univ \ paperCertificateOrderingEdges G certificate) decoupled
  active_jointly_injective := by
    intro a b _ _ hRow hCol
    apply paperAssignmentRestriction_pair_injective_of_union_eq_univ
      D.coveredRowRoles D.coveredColRoles
        D.coveredRowRoles_union_coveredColRoles_eq_univ
    exact Prod.ext hRow hCol

/-- Exact isolated-fiber factorization of an arbitrary raw decoupled
terminal matrix. -/
theorem paperPartialNCKRawTerminalMatrix_eq_smul_coveredCore
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) :
    paperPartialNCKRawTerminalMatrix G certificate D n orientation decoupled =
      (((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) : ℝ) •
        (paperRawTerminalCoveredCoreData
          G certificate D n orientation decoupled).matrix := by
  classical
  ext row col
  unfold paperPartialNCKRawTerminalMatrix paperYThroughCoordinates
    PaperNearlyCombinatorialFlatteningData.matrix
    paperRawTerminalCoveredCoreData
  convert
    (sum_assignment_if_covered_test_paperRawTerminalAmplitude_eq
      G n orientation
        (Finset.univ \ paperCertificateOrderingEdges G certificate)
        decoupled
        (fun covered =>
          paperAssignmentRestriction D.coveredRowRoles covered = row ∧
          paperAssignmentRestriction D.coveredColRoles covered = col)) using 1
  · apply Finset.sum_congr rfl
    intro assignment _ha
    by_cases h :
        paperAssignmentRestriction D.coveredRowRoles
              (paperAssignmentRestriction
                (coveredRoles G.isolatedMiddleRoles) assignment) = row ∧
          paperAssignmentRestriction D.coveredColRoles
              (paperAssignmentRestriction
                (coveredRoles G.isolatedMiddleRoles) assignment) = col
    · simp [paperIntermediateCoveredRowMap,
        paperIntermediateCoveredColMap,
        paperRawTerminalAssignmentAmplitude, h]
    · simp [paperIntermediateCoveredRowMap,
        paperIntermediateCoveredColMap,
        h]
  · rfl

/-- Formula (21) for the covered raw terminal core. -/
theorem paperRawTerminalCoveredCore_formula21_squaredNorm_le
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) :
    ‖(paperRawTerminalCoveredCoreData
        G certificate D n orientation decoupled).matrix‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent
        D.coveredRowRoles D.coveredColRoles :=
  (paperRawTerminalCoveredCoreData
    G certificate D n orientation decoupled).formula21_squaredNorm_le

/-- Raw terminal squared norm with the exact covered-plus-isolated
formula-(21) exponent. -/
theorem paperPartialNCKRawTerminal_squaredNorm_le_coreExponent
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) :
    ‖paperPartialNCKRawTerminalMatrix
        G certificate D n orientation decoupled‖ ^ 2 ≤
      (n : ℝ) ^
        (flatteningComplementExponent
            D.coveredRowRoles D.coveredColRoles +
          2 * G.isolatedMiddleRoles.card) := by
  classical
  let scalarNat :=
    (n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
      G.isolatedMiddleRoles.card
  let coreMatrix :=
    (paperRawTerminalCoveredCoreData
      G certificate D n orientation decoupled).matrix
  have hScalarNat : scalarNat ≤ n ^ G.isolatedMiddleRoles.card :=
    isolatedExtensionDescFactorial_le_pow G n
  have hScalar : (scalarNat : ℝ) ≤
      (n : ℝ) ^ G.isolatedMiddleRoles.card := by
    exact_mod_cast hScalarNat
  have hScalarNonneg : 0 ≤ (scalarNat : ℝ) := by positivity
  have hScalarSq : (scalarNat : ℝ) ^ 2 ≤
      ((n : ℝ) ^ G.isolatedMiddleRoles.card) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) ^ G.isolatedMiddleRoles.card - scalarNat)]
  have hCore : ‖coreMatrix‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent
        D.coveredRowRoles D.coveredColRoles :=
    paperRawTerminalCoveredCore_formula21_squaredNorm_le
      G certificate D n orientation decoupled
  calc
    ‖paperPartialNCKRawTerminalMatrix
        G certificate D n orientation decoupled‖ ^ 2 =
        (scalarNat : ℝ) ^ 2 * ‖coreMatrix‖ ^ 2 := by
      rw [paperPartialNCKRawTerminalMatrix_eq_smul_coveredCore]
      simp only [scalarNat, coreMatrix, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hScalarNonneg, mul_pow]
    _ ≤ ((n : ℝ) ^ G.isolatedMiddleRoles.card) ^ 2 *
          ((n : ℝ) ^ flatteningComplementExponent
            D.coveredRowRoles D.coveredColRoles) := by
      exact mul_le_mul hScalarSq hCore (sq_nonneg _) (by positivity)
    _ = (n : ℝ) ^
          (flatteningComplementExponent
              D.coveredRowRoles D.coveredColRoles +
            2 * G.isolatedMiddleRoles.card) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- Raw-decoupled form of the general-`W_iso` formula-(21) endpoint. -/
theorem paperPartialNCKRawTerminal_squaredNorm_le_minSeparatorPower
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) :
    ‖paperPartialNCKRawTerminalMatrix
        G certificate D n orientation decoupled‖ ^ 2 ≤
      (n : ℝ) ^
        (G.roles - certificate.cut.card +
          G.isolatedMiddleRoles.card) := by
  refine (paperPartialNCKRawTerminal_squaredNorm_le_coreExponent
    G certificate D n orientation decoupled).trans ?_
  apply pow_le_pow_right₀
  · exact_mod_cast hn
  · rw [D.coveredComplementExponent_add_twice_isolated]
    have hBound :=
      D.exponentNumerator_le_roles_sub_cut_add_isolated certificate
    simpa [G.isolatedMiddleRoles_eq_toPartiteShape] using hBound

/-- Canonical, certificate-free pointwise terminal bound. -/
theorem paperUnconditionalRawTerminal_squaredNorm_le_canonicalPower
    (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool)
    (decoupled : PaperDecoupledNoise G n) :
    ‖paperPartialNCKRawTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation)
        n orientation decoupled‖ ^ 2 ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
  have h := paperPartialNCKRawTerminal_squaredNorm_le_minSeparatorPower
    G G.unconditionalBoundaryCleanMengerCertificate
      (G.unconditionalIntermediateSides orientation)
      n hn orientation decoupled
  have hExponent :
      G.roles - G.unconditionalBoundaryCleanMengerCertificate.cut.card +
          G.isolatedMiddleRoles.card =
        paperTheorem48CanonicalSizeExponent G := by
    unfold paperTheorem48CanonicalSizeExponent
    have hCut := G.unconditionalMengerCut_card_eq_separatorNumber
    omega
  exact h.trans_eq (congrArg (fun e : ℕ => (n : ℝ) ^ e) hExponent)

/-- Finite mean of the arbitrary-decoupled raw terminal obeys the same
canonical power bound. -/
theorem paperUnconditionalRawTerminal_squaredNorm_mean_le_canonicalPower
    (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) :
    paperMean (fun decoupled : PaperDecoupledNoise G n =>
      ‖paperPartialNCKRawTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation)
        n orientation decoupled‖ ^ 2) ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
  calc
    paperMean (fun decoupled : PaperDecoupledNoise G n =>
        ‖paperPartialNCKRawTerminalMatrix G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation)
          n orientation decoupled‖ ^ 2) ≤
      paperMean (fun _decoupled : PaperDecoupledNoise G n =>
        (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G) := by
      apply paperMean_mono
      intro decoupled
      exact paperUnconditionalRawTerminal_squaredNorm_le_canonicalPower
        G n hn orientation decoupled
    _ = (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
      simp [paperMean]

/-! ## Exact remaining terminal-coordinate compression interface -/

/-- Purely algebraic zero-padding statement between the literal last stage
and the duplicate-free raw terminal coordinates.  It contains no analytic
estimate beyond the norm monotonicity of coordinate compression. -/
def PaperFinalLiteralToRawTerminalNorm
    (G : PaperShape) (n : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool)
      (decoupled : PaperDecoupledNoise G n),
    paperUnconditionalPartialNCKRawStageNorm G n orientation decoupled
        (paperUnconditionalOrderingLength G) ≤
      ‖paperPartialNCKRawTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate
        (G.unconditionalIntermediateSides orientation)
        n orientation decoupled‖

/-- The terminal-coordinate compression and the raw formula-(21) theorem
give the literal last-stage mean bound needed for iteration. -/
theorem paperUnconditionalFinalLiteralStage_mean_le_canonicalPower
    (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (hTerminalIndex : PaperFinalLiteralToRawTerminalNorm G n)
    (orientation : Fin G.edges → Bool) :
    paperUnconditionalDecoupledSquaredStageMean G n orientation
        (paperUnconditionalOrderingLength G) ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
  unfold paperUnconditionalDecoupledSquaredStageMean
  calc
    paperMean (fun decoupled : PaperDecoupledNoise G n =>
        paperUnconditionalPartialNCKRawStageNorm G n orientation decoupled
          (paperUnconditionalOrderingLength G) ^ 2) ≤
      paperMean (fun decoupled : PaperDecoupledNoise G n =>
        ‖paperPartialNCKRawTerminalMatrix G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation)
          n orientation decoupled‖ ^ 2) := by
      apply paperMean_mono
      intro decoupled
      exact pow_le_pow_left₀
        (paperPartialNCKRawStageNorm_nonneg G
          G.unconditionalBoundaryCleanMengerCertificate
          (G.unconditionalIntermediateSides orientation)
          n orientation decoupled (paperUnconditionalOrderingLength G))
        (hTerminalIndex orientation decoupled) 2
    _ ≤ (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G :=
      paperUnconditionalRawTerminal_squaredNorm_mean_le_canonicalPower
        G n hn orientation

#print axioms paper_l2_opNorm_fromBlocks_zero_le
#print axioms paperPartialNCKRawTerminalMatrix_eq_smul_coveredCore
#print axioms paperUnconditionalRawTerminal_squaredNorm_le_canonicalPower
#print axioms paperUnconditionalRawTerminal_squaredNorm_mean_le_canonicalPower
#print axioms paperUnconditionalFinalLiteralStage_mean_le_canonicalPower

end GraphMatrixReplica
