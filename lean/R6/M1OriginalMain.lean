import R6.M1ActualConditionalSync
import R6.M1FullGraphUpper
import R6.ZeroResidualLower
import R6.M1InjectiveBoundaryNorm

noncomputable section
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace GraphMatrixReplica

/-- The original lower bound, including the zero-residual shape, with all
probability and counting obligations discharged. -/
theorem root_original_globalLower (G : PaperShape) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  classical
  have hLower : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
    by_cases hz : (rootIsolatedReducedShape G).roles = 0
    · obtain ⟨c, hc, N, hN⟩ := root_zeroResidual_originalLower G hz
      refine ⟨c, hc, N, ?_⟩
      intro n hn
      simpa only [rootOriginalPowerScale, mul_assoc] using hN n hn
    · have hr : 0 < (rootIsolatedReducedShape G).roles := Nat.pos_of_ne_zero hz
      exact root_originalLower_from_reduced_witnesses G hr
        (fun S _ => root_actual_uniformWitness_constants (rootIsolatedReducedShape G) hr S)
  obtain ⟨c, hc, N, hN⟩ := hLower
  exact ⟨c, hc, max 1 N, le_max_left _ _,
    fun n hn => hN n ((le_max_right _ _).trans hn)⟩

/-- One graph-only pair of positive constants and one positive common threshold
for the original globally-injective graph matrix. -/
theorem root_original_globalTwoSided (G : PaperShape) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖)) ∧
      (paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        C * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
          G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
            Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2)) := by
  obtain ⟨c, hc, L, hL, hLower⟩ := root_original_globalLower G
  obtain ⟨C, hC, U, hUpper⟩ := root_full_globalMean_sharp G
  refine ⟨c, C, hc, hC, max L U, hL.trans (le_max_left _ _), ?_⟩
  intro n hn
  exact ⟨hLower n ((le_max_left _ _).trans hn),
    hUpper n ((le_max_right _ _).trans hn)⟩

/-- The literal paper endpoint: rows and columns are injective ordered-boundary
labelings, with the exact original power and logarithmic exponents. -/
theorem root_original_injectiveTwoSided (G : PaperShape) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (c * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖rootPaperInjectiveGraphMatrix G n w‖)) ∧
      (paperMean (fun w : PaperNoise n => ‖rootPaperInjectiveGraphMatrix G n w‖) ≤
        C * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
          G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
            Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2)) := by
  obtain ⟨c, C, hc, hC, N, hN, h⟩ := root_original_globalTwoSided G
  refine ⟨c, C, hc, hC, N, hN, ?_⟩
  intro n hn
  rw [root_paperInjectiveGraphMatrix_mean_norm_eq]
  exact h n hn

#check @root_original_globalLower
#check @root_original_globalTwoSided
#check @root_original_injectiveTwoSided
#print axioms root_original_globalLower
#print axioms root_original_globalTwoSided
#print axioms root_original_injectiveTwoSided
end GraphMatrixReplica
