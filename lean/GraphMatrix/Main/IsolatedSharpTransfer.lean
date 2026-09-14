import GraphMatrix.Main.ReducedActiveComponents
import GraphMatrix.Main.IsolatedScalarBounds

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica

def mainCorePowerScale (G : PaperShape) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (((G.roles : ℝ) - G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
    Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2)

def mainOriginalPowerScale (G : PaperShape) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
    G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
    Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2)

theorem main_isolated_card_le_roles (G : PaperShape) :
    G.isolatedMiddleRoles.card ≤ G.roles := by
  simpa using Finset.card_le_univ G.isolatedMiddleRoles

theorem main_global_mean_eq_reduced_mean (G : PaperShape) (n : ℕ) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) =
      ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix (mainIsolatedReducedShape G) n w‖) := by
  rw [main_global_mean_eq_isolated_mul]
  simp_rw [main_coveredGlobalMatrix_eq_reducedGraphMatrix]
  have hc : (coveredRoles G.isolatedMiddleRoles).card = G.roles - G.isolatedMiddleRoles.card :=
    main_reduced_roles G
  rw [hc]

theorem main_originalPowerScale_eq_pow_mul_reduced (G : PaperShape) (n : ℕ)
    (hn : 0 < n) :
    mainOriginalPowerScale G n =
      (n : ℝ) ^ G.isolatedMiddleRoles.card * mainCorePowerScale (mainIsolatedReducedShape G) n := by
  unfold mainOriginalPowerScale mainCorePowerScale
  rw [main_reduced_roles, main_reduced_separatorNumber_eq, main_reduced_activeMaximum_eq]
  rw [Nat.cast_sub (main_isolated_card_le_roles G)]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n)]
  congr 2
  ring

theorem main_corePowerScale_nonneg (G : PaperShape) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ mainCorePowerScale G n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  unfold mainCorePowerScale
  positivity

/-- A proved sharp bound for the reduced graph transfers to the actual original
graph with the manuscript's isolated-role exponent. This is a reduction lemma,
not a substitute for proving the reduced graph bound. -/
theorem main_isolated_sharp_twoSided_transfer (G : PaperShape) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) (N : ℕ)
    (hReduced : ∀ n : ℕ, N ≤ n →
      c * mainCorePowerScale (mainIsolatedReducedShape G) n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix (mainIsolatedReducedShape G) n w‖) ∧
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix (mainIsolatedReducedShape G) n w‖) ≤
        C * mainCorePowerScale (mainIsolatedReducedShape G) n) :
    0 < c / (2 : ℝ) ^ G.isolatedMiddleRoles.card ∧
    ∀ n : ℕ, max N (max 2 (2 * G.roles)) ≤ n →
      (c / (2 : ℝ) ^ G.isolatedMiddleRoles.card) * mainOriginalPowerScale G n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ∧
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        C * mainOriginalPowerScale G n := by
  refine ⟨by positivity, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnTwo : 2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRoles : 2 * G.roles ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hs := main_isolated_scalar_real_bounds n G.roles G.isolatedMiddleRoles.card
    (main_isolated_card_le_roles G) hnRoles
  have hBound := hReduced n hnN
  have hScale := main_corePowerScale_nonneg (mainIsolatedReducedShape G) n (by omega)
  have hScalar : (0 : ℝ) ≤
      ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) := by
    positivity
  rw [main_global_mean_eq_reduced_mean,
    main_originalPowerScale_eq_pow_mul_reduced G n (by omega)]
  constructor
  · calc
      _ = ((n : ℝ) / 2) ^ G.isolatedMiddleRoles.card *
          (c * mainCorePowerScale (mainIsolatedReducedShape G) n) := by
            rw [div_pow]
            ring
      _ ≤ ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
          (c * mainCorePowerScale (mainIsolatedReducedShape G) n) :=
            mul_le_mul_of_nonneg_right hs.1 (mul_nonneg hc.le hScale)
      _ ≤ _ := mul_le_mul_of_nonneg_left hBound.1 hScalar
  · calc
      _ ≤ ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
          (C * mainCorePowerScale (mainIsolatedReducedShape G) n) :=
            mul_le_mul_of_nonneg_left hBound.2 hScalar
      _ ≤ (n : ℝ) ^ G.isolatedMiddleRoles.card *
          (C * mainCorePowerScale (mainIsolatedReducedShape G) n) :=
            mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hC.le hScale)
      _ = _ := by ring

theorem main_isolated_sharp_upper_transfer (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C)
    (hUpper : paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix (mainIsolatedReducedShape G) n w‖) ≤
        C * mainCorePowerScale (mainIsolatedReducedShape G) n) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      C * mainOriginalPowerScale G n := by
  have hScalar : (0 : ℝ) ≤
      ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) := by
    positivity
  have hScalarUpper :
      (((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) : ℝ) ≤
        (n : ℝ) ^ G.isolatedMiddleRoles.card := by
    exact_mod_cast main_isolated_scalar_le_pow n G.roles G.isolatedMiddleRoles.card
  rw [main_global_mean_eq_reduced_mean,
    main_originalPowerScale_eq_pow_mul_reduced G n (by omega)]
  calc
    _ ≤ ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        (C * mainCorePowerScale (mainIsolatedReducedShape G) n) :=
          mul_le_mul_of_nonneg_left hUpper hScalar
    _ ≤ (n : ℝ) ^ G.isolatedMiddleRoles.card *
        (C * mainCorePowerScale (mainIsolatedReducedShape G) n) :=
          mul_le_mul_of_nonneg_right hScalarUpper
            (mul_nonneg hC (main_corePowerScale_nonneg _ n hn))
    _ = _ := by ring

end GraphMatrixReplica
