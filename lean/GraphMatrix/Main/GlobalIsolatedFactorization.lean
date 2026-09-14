import GraphMatrix.IsolatedAmplitudeFactorization
import GraphMatrix.Model.ColorUpperLpAdapter

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica

theorem main_left_mem_covered (G : PaperShape) (i : Fin G.leftSize) :
    G.left i ∈ coveredRoles G.isolatedMiddleRoles := by
  classical
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  intro h
  exact ((G.mem_isolatedMiddleRoles_iff _).mp h).1
    ((G.mem_leftBoundaryFinset_iff _).mpr ⟨i, rfl⟩)

theorem main_right_mem_covered (G : PaperShape) (i : Fin G.rightSize) :
    G.right i ∈ coveredRoles G.isolatedMiddleRoles := by
  classical
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  intro h
  exact ((G.mem_isolatedMiddleRoles_iff _).mp h).2.1
    ((G.mem_rightBoundaryFinset_iff _).mpr ⟨i, rfl⟩)

def mainCoveredEntryCompatible (G : PaperShape) {n : ℕ}
    (covered : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles))
    (row : PaperRow G n) (col : PaperCol G n) : Prop :=
  (∀ i, covered ⟨G.left i, main_left_mem_covered G i⟩ = row i) ∧
    (∀ j, covered ⟨G.right j, main_right_mem_covered G j⟩ = col j)

/-- The globally injective reduced sum retains the original ordered boundary
indices and the original shared unordered-edge sign sample. -/
def mainCoveredGlobalMatrix (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ := by
  classical
  exact fun row col => ∑ covered : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles),
    if Function.Injective covered then
      if mainCoveredEntryCompatible G covered row col then paperCoveredNoiseProduct G w covered else 0
    else 0

theorem main_merge_entry_iff (G : PaperShape) {n : ℕ}
    (covered : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles))
    (hidden : PaperVisibleTuple n G.isolatedMiddleRoles)
    (row : PaperRow G n) (col : PaperCol G n) :
    ((∀ i, mergeCoveredIsolatedAssignment G.isolatedMiddleRoles covered hidden (G.left i) = row i) ∧
      (∀ j, mergeCoveredIsolatedAssignment G.isolatedMiddleRoles covered hidden (G.right j) = col j)) ↔
      mainCoveredEntryCompatible G covered row col := by
  simp only [mainCoveredEntryCompatible,
    mergeCoveredIsolatedAssignment_apply_covered _ _ _ _ (main_left_mem_covered G _),
    mergeCoveredIsolatedAssignment_apply_covered _ _ _ _ (main_right_mem_covered G _)]

/-- Exact isolated-role factor for an original graph-matrix entry, including
small n, noninjective covered assignments, empty boundaries, and no isolated roles. -/
theorem main_global_entry_eq_isolated_factor (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (row : PaperRow G n) (col : PaperCol G n) :
    paperGraphMatrix G n w row col =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        mainCoveredGlobalMatrix G n w row col := by
  classical
  let term : PaperAssignment G n → ℝ := fun x =>
    if (∀ i, x (G.left i) = row i) ∧ (∀ j, x (G.right j) = col j) then
      paperAssignmentNoiseProduct G w x else 0
  have hZero : paperGraphMatrix G n w row col =
      ∑ x : PaperAssignment G n, if Function.Injective x then term x else 0 := by
    exact sum_paperRealization_eq_sum_assignment_if_injective G n term
  rw [hZero, sum_assignment_eq_sum_covered_sum_isolated n G.isolatedMiddleRoles]
  unfold mainCoveredGlobalMatrix
  have hInner (covered : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles)) :
      (∑ hidden : PaperVisibleTuple n G.isolatedMiddleRoles,
        if Function.Injective (mergeCoveredIsolatedAssignment G.isolatedMiddleRoles covered hidden) then
          term (mergeCoveredIsolatedAssignment G.isolatedMiddleRoles covered hidden) else 0) =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        (if Function.Injective covered then
          if mainCoveredEntryCompatible G covered row col then paperCoveredNoiseProduct G w covered else 0
        else 0) := by
    dsimp only [term]
    simp_rw [main_merge_entry_iff, paperAssignmentNoiseProduct_merge_eq]
    rw [sum_hidden_if_merge_injective_eq_card_mul]
    by_cases hc : Function.Injective covered
    · rw [card_injectiveHiddenFiber_of_injective G.isolatedMiddleRoles covered hc]
      simp only [if_pos hc]
    · rw [card_injectiveHiddenFiber_of_not_injective G.isolatedMiddleRoles covered hc]
      simp [hc]
  simp_rw [hInner]
  rw [← Finset.mul_sum]

theorem main_global_matrix_eq_isolated_smul (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    paperGraphMatrix G n w =
      (((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial G.isolatedMiddleRoles.card : ℕ) : ℝ) •
        mainCoveredGlobalMatrix G n w := by
  ext row col
  exact main_global_entry_eq_isolated_factor G n w row col

theorem main_global_norm_eq_isolated_mul (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    ‖paperGraphMatrix G n w‖ =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        ‖mainCoveredGlobalMatrix G n w‖ := by
  rw [main_global_matrix_eq_isolated_smul, norm_smul, Real.norm_of_nonneg (by positivity)]

theorem main_global_mean_eq_isolated_mul (G : PaperShape) (n : ℕ) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) =
      ((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        paperMean (fun w : PaperNoise n => ‖mainCoveredGlobalMatrix G n w‖) := by
  simp_rw [main_global_norm_eq_isolated_mul]
  unfold paperMean
  rw [← Finset.mul_sum]
  ring

end GraphMatrixReplica
