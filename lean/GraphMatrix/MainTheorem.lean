import GraphMatrix.Main.ActualConditionalSync
import GraphMatrix.Main.FullGraphUpper
import GraphMatrix.ZeroResidualLower
import GraphMatrix.Main.InjectiveBoundaryNorm

noncomputable section
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace GraphMatrixReplica

/-- The original lower bound, including the zero-residual shape, with all
probability and counting obligations discharged. -/
theorem expected_norm_lower_bound (G : PaperShape) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  classical
  have hLower : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
    by_cases hz : (mainIsolatedReducedShape G).roles = 0
    · obtain ⟨c, hc, N, hN⟩ := main_zeroResidual_originalLower G hz
      refine ⟨c, hc, N, ?_⟩
      intro n hn
      simpa only [mainOriginalPowerScale, mul_assoc] using hN n hn
    · have hr : 0 < (mainIsolatedReducedShape G).roles := Nat.pos_of_ne_zero hz
      exact main_originalLower_from_reduced_witnesses G hr
        (fun S _ => main_actual_uniformWitness_constants (mainIsolatedReducedShape G) hr S)
  obtain ⟨c, hc, N, hN⟩ := hLower
  exact ⟨c, hc, max 1 N, le_max_left _ _,
    fun n hn => hN n ((le_max_right _ _).trans hn)⟩

/-- One graph-only pair of positive constants and one positive common threshold
for the original globally-injective graph matrix. -/
theorem expected_norm_two_sided (G : PaperShape) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖)) ∧
      (paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        C * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
          G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
            Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2)) := by
  obtain ⟨c, hc, L, hL, hLower⟩ := expected_norm_lower_bound G
  obtain ⟨C, hC, U, hUpper⟩ := main_full_globalMean_sharp G
  refine ⟨c, C, hc, hC, max L U, hL.trans (le_max_left _ _), ?_⟩
  intro n hn
  exact ⟨hLower n ((le_max_left _ _).trans hn),
    hUpper n ((le_max_right _ _).trans hn)⟩

/-- The literal paper endpoint: rows and columns are injective ordered-boundary
labelings, with the exact original power and logarithmic exponents. -/
theorem injective_expected_norm_two_sided (G : PaperShape) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖injectiveGraphMatrix G n w‖)) ∧
      (paperMean (fun w : PaperNoise n => ‖injectiveGraphMatrix G n w‖) ≤
        C * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
          G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
            Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2)) := by
  obtain ⟨c, C, hc, hC, N, hN, h⟩ := expected_norm_two_sided G
  refine ⟨c, C, hc, hC, N, hN, ?_⟩
  intro n hn
  rw [main_paperInjectiveGraphMatrix_mean_norm_eq]
  exact h n hn

end GraphMatrixReplica
