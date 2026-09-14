import R6.PaperIsolatedInjectiveFiberCount

/-! # Exact isolated-role factorization of the oriented amplitude

For an isolated middle role, no shape edge reads its label.  Thus edge
orientation and the shared unordered-edge noise are functions of the covered
assignment alone; global injectivity is the only hidden-coordinate
condition.  Combining this observation with the exact injective fiber count
gives a falling-factorial scalar and a covered-assignment core.

The scalar is uniform only after the covered core includes the covered
injectivity indicator.  We do not assert that the raw fiber cardinality is
independent of a non-injective covered assignment.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Orientation compatibility evaluated entirely on the covered roles. -/
def paperCoveredOrientationCompatible
    (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) : Prop :=
  orientation = fun e => decide
    (covered ⟨G.source e, G.source_mem_coveredRoles_isolatedMiddle e⟩ <
      covered ⟨G.target e, G.target_mem_coveredRoles_isolatedMiddle e⟩)

/-- Shared unordered-edge noise evaluated entirely on the covered roles. -/
def paperCoveredNoiseProduct
    (G : PaperShape) {n : ℕ} (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) : ℝ :=
  ∏ e : Fin G.edges,
    paperEdgeSign w
      (covered ⟨G.source e,
        G.source_mem_coveredRoles_isolatedMiddle e⟩)
      (covered ⟨G.target e,
        G.target_mem_coveredRoles_isolatedMiddle e⟩)

/-- The covered orientation/noise core, before imposing injectivity on the
covered assignment itself. -/
def paperCoveredOrientedCoreAmplitude
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) : ℝ :=
  by
    classical
    exact if paperCoveredOrientationCompatible G orientation covered then
      paperCoveredNoiseProduct G w covered
    else 0

/-- The genuine covered core.  Including covered injectivity makes the
falling-factorial extension scalar uniform over all covered assignments. -/
def paperCoveredInjectiveOrientedCoreAmplitude
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) : ℝ :=
  by
    classical
    exact if Function.Injective covered then
      paperCoveredOrientedCoreAmplitude G n orientation w covered
    else 0

@[simp] theorem paperAssignmentRestriction_merge_covered
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hidden : PaperVisibleTuple n isolated) :
    paperAssignmentRestriction (coveredRoles isolated)
        (mergeCoveredIsolatedAssignment isolated covered hidden) =
      covered := by
  funext x
  exact mergeCoveredIsolatedAssignment_apply_covered
    isolated covered hidden x.1 x.2

/-- A merged assignment has the covered orientation precisely when its
covered part does. -/
theorem paperAssignmentOrientationCompatible_merge_iff
    (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles))
    (hidden : PaperVisibleTuple n G.isolatedMiddleRoles) :
    paperAssignmentOrientationCompatible G orientation
        (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden) ↔
      paperCoveredOrientationCompatible G orientation covered := by
  unfold paperAssignmentOrientationCompatible
    paperCoveredOrientationCompatible
  have hFunctions :
      (fun e => decide
        (mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden (G.source e) <
          mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden (G.target e))) =
        fun e => decide
          (covered ⟨G.source e,
              G.source_mem_coveredRoles_isolatedMiddle e⟩ <
            covered ⟨G.target e,
              G.target_mem_coveredRoles_isolatedMiddle e⟩) := by
    funext e
    rw [mergeCoveredIsolatedAssignment_apply_covered
        G.isolatedMiddleRoles covered hidden (G.source e)
          (G.source_mem_coveredRoles_isolatedMiddle e),
      mergeCoveredIsolatedAssignment_apply_covered
        G.isolatedMiddleRoles covered hidden (G.target e)
          (G.target_mem_coveredRoles_isolatedMiddle e)]
  rw [hFunctions]

/-- The shared noise product of a merge is exactly its covered noise
product. -/
theorem paperAssignmentNoiseProduct_merge_eq
    (G : PaperShape) {n : ℕ} (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles))
    (hidden : PaperVisibleTuple n G.isolatedMiddleRoles) :
    paperAssignmentNoiseProduct G w
        (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden) =
      paperCoveredNoiseProduct G w covered := by
  classical
  unfold paperAssignmentNoiseProduct paperCoveredNoiseProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [paperAssignmentEdgeCoordinate]
  rw [mergeCoveredIsolatedAssignment_apply_covered
      G.isolatedMiddleRoles covered hidden (G.source e)
        (G.source_mem_coveredRoles_isolatedMiddle e),
    mergeCoveredIsolatedAssignment_apply_covered
      G.isolatedMiddleRoles covered hidden (G.target e)
        (G.target_mem_coveredRoles_isolatedMiddle e)]

/-- Pointwise decomposition: after fixing covered values, the amplitude is
the global-injectivity indicator times a hidden-independent core. -/
theorem paperOrientedFlatteningAmplitude_merge_eq_if_injective
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles))
    (hidden : PaperVisibleTuple n G.isolatedMiddleRoles) :
    paperOrientedFlatteningAmplitude G n orientation w
        (mergeCoveredIsolatedAssignment
          G.isolatedMiddleRoles covered hidden) =
      if Function.Injective
          (mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden) then
        paperCoveredOrientedCoreAmplitude G n orientation w covered
      else 0 := by
  classical
  rw [paperOrientedFlatteningAmplitude,
    paperAssignmentNoiseProduct_merge_eq]
  unfold paperOrientedAssignmentWeight paperCoveredOrientedCoreAmplitude
  rw [paperAssignmentOrientationCompatible_merge_iff]
  by_cases hInjective : Function.Injective
      (mergeCoveredIsolatedAssignment
        G.isolatedMiddleRoles covered hidden) <;>
    by_cases hOrientation :
      paperCoveredOrientationCompatible G orientation covered <;>
    simp [hInjective, hOrientation]

/-- Exact fixed-covered fiber sum.  The raw fiber cardinality is retained,
so the statement is valid for both injective and non-injective covered
assignments. -/
theorem sum_hidden_paperOrientedFlatteningAmplitude_eq_fiberCard_mul
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    (∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
        paperOrientedFlatteningAmplitude G n orientation w
          (mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden)) =
      (Fintype.card (InjectiveHiddenFiber
        G.isolatedMiddleRoles covered) : ℝ) *
        paperCoveredOrientedCoreAmplitude G n orientation w covered := by
  classical
  calc
    (∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
        paperOrientedFlatteningAmplitude G n orientation w
          (mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden)) =
        ∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
          if Function.Injective
              (mergeCoveredIsolatedAssignment
                G.isolatedMiddleRoles covered hidden) then
            paperCoveredOrientedCoreAmplitude G n orientation w covered
          else 0 := by
      apply Finset.sum_congr rfl
      intro hidden _
      exact paperOrientedFlatteningAmplitude_merge_eq_if_injective
        G n orientation w covered hidden
    _ = (Fintype.card (InjectiveHiddenFiber
          G.isolatedMiddleRoles covered) : ℝ) *
          paperCoveredOrientedCoreAmplitude G n orientation w covered :=
      sum_hidden_if_merge_injective_eq_card_mul
        G.isolatedMiddleRoles covered
          (paperCoveredOrientedCoreAmplitude G n orientation w covered)

/-- Uniform falling-factorial factorization.  The covered injectivity
indicator is part of the core, so the scalar depends only on `n` and the two
role-set cardinalities, not on the particular injective covered image. -/
theorem sum_hidden_paperOrientedFlatteningAmplitude_eq_descFactorial_mul
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    (∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
        paperOrientedFlatteningAmplitude G n orientation w
          (mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden)) =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) *
        paperCoveredInjectiveOrientedCoreAmplitude
          G n orientation w covered := by
  classical
  rw [sum_hidden_paperOrientedFlatteningAmplitude_eq_fiberCard_mul]
  by_cases hCovered : Function.Injective covered
  · rw [card_injectiveHiddenFiber_of_injective
      G.isolatedMiddleRoles covered hCovered]
    simp [paperCoveredInjectiveOrientedCoreAmplitude, hCovered]
  · rw [card_injectiveHiddenFiber_of_not_injective
      G.isolatedMiddleRoles covered hCovered]
    simp [paperCoveredInjectiveOrientedCoreAmplitude, hCovered]

/-- Matrix-entry-ready form.  Any predicate depending only on the covered
assignment (for example prescribed row and column restrictions) passes
through isolated marginalization and receives the same uniform scalar. -/
theorem sum_assignment_if_covered_test_paperOrientedAmplitude_eq
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (test : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → Prop)
    [DecidablePred test] :
    (∑ assignment : PaperAssignment G n,
        if test (paperAssignmentRestriction
            (coveredRoles G.isolatedMiddleRoles) assignment) then
          paperOrientedFlatteningAmplitude G n orientation w assignment
        else 0) =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) *
        ∑ covered : PaperVisibleTuple n
            (coveredRoles G.isolatedMiddleRoles),
          if test covered then
            paperCoveredInjectiveOrientedCoreAmplitude
              G n orientation w covered
          else 0 := by
  classical
  rw [sum_assignment_eq_sum_covered_sum_isolated]
  calc
    (∑ covered : PaperVisibleTuple n
          (coveredRoles G.isolatedMiddleRoles),
        ∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
          if test (paperAssignmentRestriction
              (coveredRoles G.isolatedMiddleRoles)
              (mergeCoveredIsolatedAssignment
                G.isolatedMiddleRoles covered hidden)) then
            paperOrientedFlatteningAmplitude G n orientation w
              (mergeCoveredIsolatedAssignment
                G.isolatedMiddleRoles covered hidden)
          else 0) =
        ∑ covered : PaperVisibleTuple n
            (coveredRoles G.isolatedMiddleRoles),
          if test covered then
            ∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
              paperOrientedFlatteningAmplitude G n orientation w
                (mergeCoveredIsolatedAssignment
                  G.isolatedMiddleRoles covered hidden)
          else 0 := by
      apply Finset.sum_congr rfl
      intro covered _
      simp only [paperAssignmentRestriction_merge_covered]
      by_cases hTest : test covered <;> simp [hTest]
    _ = ∑ covered : PaperVisibleTuple n
            (coveredRoles G.isolatedMiddleRoles),
          if test covered then
            ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
                G.isolatedMiddleRoles.card : ℕ) *
              paperCoveredInjectiveOrientedCoreAmplitude
                G n orientation w covered
          else 0 := by
      apply Finset.sum_congr rfl
      intro covered _
      by_cases hTest : test covered
      · simp only [hTest, if_true]
        exact sum_hidden_paperOrientedFlatteningAmplitude_eq_descFactorial_mul
          G n orientation w covered
      · simp [hTest]
    _ = ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
            G.isolatedMiddleRoles.card : ℕ) *
          ∑ covered : PaperVisibleTuple n
              (coveredRoles G.isolatedMiddleRoles),
            if test covered then
              paperCoveredInjectiveOrientedCoreAmplitude
                G n orientation w covered
            else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro covered _
      by_cases hTest : test covered <;> simp [hTest]

/-- The unconditioned assignment sum is the special case of the preceding
entry-ready identity with the constantly true covered test. -/
theorem sum_assignment_paperOrientedFlatteningAmplitude_eq
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    (∑ assignment : PaperAssignment G n,
        paperOrientedFlatteningAmplitude G n orientation w assignment) =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) *
        ∑ covered : PaperVisibleTuple n
            (coveredRoles G.isolatedMiddleRoles),
          paperCoveredInjectiveOrientedCoreAmplitude
            G n orientation w covered := by
  simpa using
    (sum_assignment_if_covered_test_paperOrientedAmplitude_eq
      G n orientation w (fun _ => True))

/-! ## Matrix packaging -/

/-- The full oriented assignment matrix seen through arbitrary row and
column coordinate maps of the covered assignment.  Intermediate
flattenings specialize these maps to their visible-role restrictions. -/
def paperOrientedMatrixThroughCoveredCoordinates
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    {rows cols : Type*}
    (rowMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → rows)
    (colMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → cols) :
    Matrix rows cols ℝ := by
  classical
  exact fun row col =>
    ∑ assignment : PaperAssignment G n,
      if rowMap (paperAssignmentRestriction
            (coveredRoles G.isolatedMiddleRoles) assignment) = row ∧
          colMap (paperAssignmentRestriction
            (coveredRoles G.isolatedMiddleRoles) assignment) = col then
        paperOrientedFlatteningAmplitude G n orientation w assignment
      else 0

/-- The corresponding matrix whose summation variables are only the
covered assignments and whose weight includes covered injectivity. -/
def paperCoveredInjectiveOrientedCoreMatrix
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    {rows cols : Type*}
    (rowMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → rows)
    (colMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → cols) :
    Matrix rows cols ℝ := by
  classical
  exact fun row col =>
    ∑ covered : PaperVisibleTuple n
        (coveredRoles G.isolatedMiddleRoles),
      if rowMap covered = row ∧ colMap covered = col then
        paperCoveredInjectiveOrientedCoreAmplitude
          G n orientation w covered
      else 0

/-- Entrywise exact factorization through arbitrary covered coordinate
maps. -/
theorem paperOrientedMatrixThroughCoveredCoordinates_apply
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    {rows cols : Type*}
    (rowMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → rows)
    (colMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → cols)
    (row : rows) (col : cols) :
    paperOrientedMatrixThroughCoveredCoordinates
        G n orientation w rowMap colMap row col =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) *
        paperCoveredInjectiveOrientedCoreMatrix
          G n orientation w rowMap colMap row col := by
  classical
  simpa [paperOrientedMatrixThroughCoveredCoordinates,
    paperCoveredInjectiveOrientedCoreMatrix] using
      (sum_assignment_if_covered_test_paperOrientedAmplitude_eq
        G n orientation w
          (fun covered => rowMap covered = row ∧ colMap covered = col))

/-- Matrix-level exact factorization.  The scalar is uniform because the
covered matrix already zeroes non-injective covered assignments. -/
theorem paperOrientedMatrixThroughCoveredCoordinates_eq_smul
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    {rows cols : Type*}
    (rowMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → rows)
    (colMap : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles) → cols) :
    paperOrientedMatrixThroughCoveredCoordinates
        G n orientation w rowMap colMap =
      (((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) : ℝ) •
        paperCoveredInjectiveOrientedCoreMatrix
          G n orientation w rowMap colMap := by
  classical
  ext row col
  exact paperOrientedMatrixThroughCoveredCoordinates_apply
    G n orientation w rowMap colMap row col

#print axioms paperOrientedFlatteningAmplitude_merge_eq_if_injective
#print axioms sum_hidden_paperOrientedFlatteningAmplitude_eq_fiberCard_mul
#print axioms sum_hidden_paperOrientedFlatteningAmplitude_eq_descFactorial_mul
#print axioms sum_assignment_if_covered_test_paperOrientedAmplitude_eq
#print axioms sum_assignment_paperOrientedFlatteningAmplitude_eq
#print axioms paperOrientedMatrixThroughCoveredCoordinates_eq_smul

end GraphMatrixReplica
