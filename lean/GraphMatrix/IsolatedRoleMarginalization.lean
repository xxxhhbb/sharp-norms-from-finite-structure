import GraphMatrix.IntermediateFormula21Application

/-! # Marginalizing isolated role coordinates

Full assignments split canonically into values on the complement of a finite
isolated set and values on that isolated set.  We prove the finite-sum
decomposition, the exact `n ^ |W|` factor under independence, and the
corresponding absolute-value bound for arbitrary bounded summands.

For the paper amplitude, edge orientation and shared edge noise are
independent of isolated values, but global injectivity is not.  Its precise
extra invariance premise is kept explicit.  Without it, the unconditional
fiber bound still loses at most `n ^ |W_iso|`.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Roles outside a selected isolated set. -/
def coveredRoles
    {α : Type*} [Fintype α] [DecidableEq α]
    (isolated : Finset α) : Finset α :=
  Finset.univ \ isolated

/-- Merge values on the covered and isolated coordinates. -/
def mergeCoveredIsolatedAssignment
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hidden : PaperVisibleTuple n isolated) : α → Fin n :=
  fun x => if hx : x ∈ isolated then hidden ⟨x, hx⟩ else
    covered ⟨x, Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩⟩

@[simp] theorem mergeCoveredIsolatedAssignment_apply_isolated
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hidden : PaperVisibleTuple n isolated)
    (x : α) (hx : x ∈ isolated) :
    mergeCoveredIsolatedAssignment isolated covered hidden x =
      hidden ⟨x, hx⟩ := by
  simp [mergeCoveredIsolatedAssignment, hx]

@[simp] theorem mergeCoveredIsolatedAssignment_apply_covered
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hidden : PaperVisibleTuple n isolated)
    (x : α) (hx : x ∈ coveredRoles isolated) :
    mergeCoveredIsolatedAssignment isolated covered hidden x =
      covered ⟨x, hx⟩ := by
  have hNotIso : x ∉ isolated := (Finset.mem_sdiff.mp hx).2
  simp [mergeCoveredIsolatedAssignment, hNotIso]

/-- Full assignments are canonically covered assignments paired with
isolated-coordinate assignments. -/
def assignmentEquivCoveredTimesIsolated
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (isolated : Finset α) :
    (α → Fin n) ≃
      PaperVisibleTuple n (coveredRoles isolated) ×
        PaperVisibleTuple n isolated where
  toFun assignment :=
    (paperAssignmentRestriction (coveredRoles isolated) assignment,
      paperAssignmentRestriction isolated assignment)
  invFun pair := mergeCoveredIsolatedAssignment isolated pair.1 pair.2
  left_inv assignment := by
    funext x
    by_cases hx : x ∈ isolated
    · simp [mergeCoveredIsolatedAssignment, hx,
        paperAssignmentRestriction]
    · simp [mergeCoveredIsolatedAssignment, hx,
        paperAssignmentRestriction]
  right_inv pair := by
    apply Prod.ext
    · funext x
      exact mergeCoveredIsolatedAssignment_apply_covered
        isolated pair.1 pair.2 x.1 x.2
    · funext x
      exact mergeCoveredIsolatedAssignment_apply_isolated
        isolated pair.1 pair.2 x.1 x.2

/-- Exact Fubini decomposition of a finite sum over all role assignments. -/
theorem sum_assignment_eq_sum_covered_sum_isolated
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (isolated : Finset α)
    (term : (α → Fin n) → ℝ) :
    (∑ assignment : α → Fin n, term assignment) =
      ∑ covered : PaperVisibleTuple n (coveredRoles isolated),
        ∑ hidden : PaperVisibleTuple n isolated,
          term (mergeCoveredIsolatedAssignment isolated covered hidden) := by
  classical
  calc
    (∑ assignment : α → Fin n, term assignment) =
        ∑ pair : PaperVisibleTuple n (coveredRoles isolated) ×
            PaperVisibleTuple n isolated,
          term ((assignmentEquivCoveredTimesIsolated n isolated).symm pair) := by
      exact Fintype.sum_equiv
        (assignmentEquivCoveredTimesIsolated n isolated)
        term
        (fun pair =>
          term ((assignmentEquivCoveredTimesIsolated n isolated).symm pair))
        (fun assignment => by simp)
    _ = ∑ covered : PaperVisibleTuple n (coveredRoles isolated),
          ∑ hidden : PaperVisibleTuple n isolated,
            term (mergeCoveredIsolatedAssignment isolated covered hidden) := by
      rw [Fintype.sum_prod_type]
      rfl

/-- There are exactly `n ^ |W|` assignments of the isolated coordinates. -/
theorem card_isolatedAssignments
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (isolated : Finset α) :
    Fintype.card (PaperVisibleTuple n isolated) = n ^ isolated.card := by
  simp [PaperVisibleTuple]

/-- Exact isolated-coordinate factor for one covered fiber under the minimal
pointwise independence condition. -/
theorem sum_isolated_eq_pow_mul_of_independent
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (isolated : Finset α)
    (term : (α → Fin n) → ℝ)
    (coveredTerm : PaperVisibleTuple n (coveredRoles isolated) → ℝ)
    (hIndependent : ∀ covered hidden,
      term (mergeCoveredIsolatedAssignment isolated covered hidden) =
        coveredTerm covered)
    (covered : PaperVisibleTuple n (coveredRoles isolated)) :
    (∑ hidden : PaperVisibleTuple n isolated,
        term (mergeCoveredIsolatedAssignment isolated covered hidden)) =
      (n ^ isolated.card : ℕ) * coveredTerm covered := by
  classical
  simp_rw [hIndependent covered]
  calc
    (∑ _hidden : PaperVisibleTuple n isolated, coveredTerm covered) =
        (Fintype.card (PaperVisibleTuple n isolated) : ℝ) *
          coveredTerm covered := by simp
    _ = (n ^ isolated.card : ℕ) * coveredTerm covered := by
      rw [card_isolatedAssignments]

/-- Global exact factorization under isolated-coordinate independence. -/
theorem sum_assignment_eq_pow_mul_sum_covered_of_independent
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (isolated : Finset α)
    (term : (α → Fin n) → ℝ)
    (coveredTerm : PaperVisibleTuple n (coveredRoles isolated) → ℝ)
    (hIndependent : ∀ covered hidden,
      term (mergeCoveredIsolatedAssignment isolated covered hidden) =
        coveredTerm covered) :
    (∑ assignment : α → Fin n, term assignment) =
      (n ^ isolated.card : ℕ) * ∑ covered, coveredTerm covered := by
  classical
  rw [sum_assignment_eq_sum_covered_sum_isolated]
  calc
    (∑ covered : PaperVisibleTuple n (coveredRoles isolated),
        ∑ hidden : PaperVisibleTuple n isolated,
          term (mergeCoveredIsolatedAssignment isolated covered hidden)) =
        ∑ covered : PaperVisibleTuple n (coveredRoles isolated),
          (n ^ isolated.card : ℕ) * coveredTerm covered := by
      apply Finset.sum_congr rfl
      intro covered _
      exact sum_isolated_eq_pow_mul_of_independent
        n isolated term coveredTerm hIndependent covered
    _ = (n ^ isolated.card : ℕ) * ∑ covered, coveredTerm covered := by
      rw [Finset.mul_sum]

/-- A pointwise `B`-bounded summand loses at most the isolated-fiber size. -/
theorem abs_sum_isolated_le_pow_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (isolated : Finset α)
    (term : (α → Fin n) → ℝ) (B : ℝ)
    (hBound : ∀ assignment, |term assignment| ≤ B)
    (covered : PaperVisibleTuple n (coveredRoles isolated)) :
    |∑ hidden : PaperVisibleTuple n isolated,
        term (mergeCoveredIsolatedAssignment isolated covered hidden)| ≤
      (n ^ isolated.card : ℕ) * B := by
  classical
  calc
    |∑ hidden : PaperVisibleTuple n isolated,
        term (mergeCoveredIsolatedAssignment isolated covered hidden)| ≤
        ∑ hidden : PaperVisibleTuple n isolated,
          |term (mergeCoveredIsolatedAssignment isolated covered hidden)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _hidden : PaperVisibleTuple n isolated, B := by
      exact Finset.sum_le_sum fun hidden _ =>
        hBound (mergeCoveredIsolatedAssignment isolated covered hidden)
    _ = (n ^ isolated.card : ℕ) * B := by
      calc
        (∑ _hidden : PaperVisibleTuple n isolated, B) =
            (Fintype.card (PaperVisibleTuple n isolated) : ℝ) * B := by
          simp
        _ = (n ^ isolated.card : ℕ) * B := by
          rw [card_isolatedAssignments]

/-! ## The paper amplitude -/

/-- The paper-shape and underlying partite-shape definitions select the same
isolated roles. -/
theorem PaperShape.isolatedMiddleRoles_eq_toPartiteShape
    (G : PaperShape) :
    G.isolatedMiddleRoles = G.toPartiteShape.isolatedMiddleRoles := by
  rfl

/-- Every shape-edge source is a covered role. -/
theorem PaperShape.source_mem_coveredRoles_isolatedMiddle
    (G : PaperShape) (e : Fin G.edges) :
    G.source e ∈ coveredRoles G.isolatedMiddleRoles := by
  apply Finset.mem_sdiff.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hIso
  have h := (G.mem_isolatedMiddleRoles_iff (G.source e)).1 hIso
  exact (h.2.2 e).1 rfl

/-- Every shape-edge target is a covered role. -/
theorem PaperShape.target_mem_coveredRoles_isolatedMiddle
    (G : PaperShape) (e : Fin G.edges) :
    G.target e ∈ coveredRoles G.isolatedMiddleRoles := by
  apply Finset.mem_sdiff.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hIso
  have h := (G.mem_isolatedMiddleRoles_iff (G.target e)).1 hIso
  exact (h.2.2 e).2 rfl

/-- Shared edge noise depends only on covered role values. -/
theorem paperAssignmentNoiseProduct_eq_of_coveredRestriction_eq
    (G : PaperShape) {n : ℕ} (w : PaperNoise n)
    (a b : PaperAssignment G n)
    (hCovered :
      paperAssignmentRestriction (coveredRoles G.isolatedMiddleRoles) a =
        paperAssignmentRestriction (coveredRoles G.isolatedMiddleRoles) b) :
    paperAssignmentNoiseProduct G w a =
      paperAssignmentNoiseProduct G w b := by
  classical
  unfold paperAssignmentNoiseProduct
  apply Finset.prod_congr rfl
  intro e _
  have hSource : a (G.source e) = b (G.source e) :=
    congrFun hCovered ⟨G.source e,
      G.source_mem_coveredRoles_isolatedMiddle e⟩
  have hTarget : a (G.target e) = b (G.target e) :=
    congrFun hCovered ⟨G.target e,
      G.target_mem_coveredRoles_isolatedMiddle e⟩
  simp only [paperAssignmentEdgeCoordinate]
  rw [hSource, hTarget]

/-- Edge orientation compatibility depends only on covered values. -/
theorem paperAssignmentOrientationCompatible_iff_of_coveredRestriction_eq
    (G : PaperShape) {n : ℕ} (orientation : Fin G.edges → Bool)
    (a b : PaperAssignment G n)
    (hCovered :
      paperAssignmentRestriction (coveredRoles G.isolatedMiddleRoles) a =
        paperAssignmentRestriction (coveredRoles G.isolatedMiddleRoles) b) :
    paperAssignmentOrientationCompatible G orientation a ↔
      paperAssignmentOrientationCompatible G orientation b := by
  unfold paperAssignmentOrientationCompatible
  have hFunctions :
      (fun e => decide (a (G.source e) < a (G.target e))) =
        fun e => decide (b (G.source e) < b (G.target e)) := by
    funext e
    have hSource : a (G.source e) = b (G.source e) :=
      congrFun hCovered ⟨G.source e,
        G.source_mem_coveredRoles_isolatedMiddle e⟩
    have hTarget : a (G.target e) = b (G.target e) :=
      congrFun hCovered ⟨G.target e,
        G.target_mem_coveredRoles_isolatedMiddle e⟩
    rw [hSource, hTarget]
  rw [hFunctions]

/-- The sole extra condition needed for the full oriented amplitude to
ignore isolated values is invariance of global injectivity. -/
theorem paperOrientedFlatteningAmplitude_eq_of_coveredRestriction_eq
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (a b : PaperAssignment G n)
    (hCovered :
      paperAssignmentRestriction (coveredRoles G.isolatedMiddleRoles) a =
        paperAssignmentRestriction (coveredRoles G.isolatedMiddleRoles) b)
    (hInjective : Function.Injective a ↔ Function.Injective b) :
    paperOrientedFlatteningAmplitude G n orientation w a =
      paperOrientedFlatteningAmplitude G n orientation w b := by
  have hOrientation :=
    paperAssignmentOrientationCompatible_iff_of_coveredRestriction_eq
      G orientation a b hCovered
  have hNoise :=
    paperAssignmentNoiseProduct_eq_of_coveredRestriction_eq G w a b hCovered
  unfold paperOrientedFlatteningAmplitude paperOrientedAssignmentWeight
  rw [hNoise]
  have hCondition :
      (Function.Injective a ∧
          paperAssignmentOrientationCompatible G orientation a) ↔
        (Function.Injective b ∧
          paperAssignmentOrientationCompatible G orientation b) :=
    and_congr hInjective hOrientation
  by_cases ha : Function.Injective a ∧
      paperAssignmentOrientationCompatible G orientation a
  · have hb := hCondition.mp ha
    simp [ha, hb]
  · have hb : ¬ (Function.Injective b ∧
        paperAssignmentOrientationCompatible G orientation b) :=
      fun hb => ha (hCondition.mpr hb)
    simp [ha, hb]

/-- Unconditional isolated-fiber bound for the actual oriented amplitude. -/
theorem abs_sum_isolated_paperOrientedFlatteningAmplitude_le
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    |∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
        paperOrientedFlatteningAmplitude G n orientation w
          (mergeCoveredIsolatedAssignment
            G.isolatedMiddleRoles covered hidden)| ≤
      (n ^ G.isolatedMiddleRoles.card : ℕ) := by
  simpa using abs_sum_isolated_le_pow_mul
    n G.isolatedMiddleRoles
    (paperOrientedFlatteningAmplitude G n orientation w) 1
    (abs_paperOrientedFlatteningAmplitude_le_one G n orientation w)
    covered


end GraphMatrixReplica
