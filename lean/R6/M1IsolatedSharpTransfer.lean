import R6.M1ReducedActiveComponents
import R6.M1IsolatedScalarBounds

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica

def rootCorePowerScale (G : PaperShape) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (((G.roles : ℝ) - G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
    Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2)

def rootOriginalPowerScale (G : PaperShape) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
    G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
    Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2)

theorem root_isolated_card_le_roles (G : PaperShape) :
    G.isolatedMiddleRoles.card ≤ G.roles := by
  simpa using Finset.card_le_univ G.isolatedMiddleRoles

theorem root_global_mean_eq_reduced_mean (G : PaperShape) (n : ℕ) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) =
      ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖) := by
  rw [root_global_mean_eq_isolated_mul]
  simp_rw [root_coveredGlobalMatrix_eq_reducedGraphMatrix]
  have hc : (coveredRoles G.isolatedMiddleRoles).card = G.roles - G.isolatedMiddleRoles.card :=
    root_reduced_roles G
  rw [hc]

theorem root_originalPowerScale_eq_pow_mul_reduced (G : PaperShape) (n : ℕ)
    (hn : 0 < n) :
    rootOriginalPowerScale G n =
      (n : ℝ) ^ G.isolatedMiddleRoles.card * rootCorePowerScale (rootIsolatedReducedShape G) n := by
  unfold rootOriginalPowerScale rootCorePowerScale
  rw [root_reduced_roles, root_reduced_separatorNumber_eq, root_reduced_activeMaximum_eq]
  rw [Nat.cast_sub (root_isolated_card_le_roles G)]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n)]
  congr 2
  ring

theorem root_corePowerScale_nonneg (G : PaperShape) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ rootCorePowerScale G n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  unfold rootCorePowerScale
  positivity

/-- A proved sharp bound for the reduced graph transfers to the actual original
graph with the manuscript's isolated-role exponent. This is a reduction lemma,
not a substitute for proving the reduced graph bound. -/
theorem root_isolated_sharp_twoSided_transfer (G : PaperShape) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C) (N : ℕ)
    (hReduced : ∀ n : ℕ, N ≤ n →
      c * rootCorePowerScale (rootIsolatedReducedShape G) n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖) ∧
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖) ≤
        C * rootCorePowerScale (rootIsolatedReducedShape G) n) :
    0 < c / (2 : ℝ) ^ G.isolatedMiddleRoles.card ∧
    ∀ n : ℕ, max N (max 2 (2 * G.roles)) ≤ n →
      (c / (2 : ℝ) ^ G.isolatedMiddleRoles.card) * rootOriginalPowerScale G n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ∧
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        C * rootOriginalPowerScale G n := by
  refine ⟨by positivity, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnTwo : 2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRoles : 2 * G.roles ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hs := root_isolated_scalar_real_bounds n G.roles G.isolatedMiddleRoles.card
    (root_isolated_card_le_roles G) hnRoles
  have hBound := hReduced n hnN
  have hScale := root_corePowerScale_nonneg (rootIsolatedReducedShape G) n (by omega)
  have hScalar : (0 : ℝ) ≤
      ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) := by
    positivity
  rw [root_global_mean_eq_reduced_mean,
    root_originalPowerScale_eq_pow_mul_reduced G n (by omega)]
  constructor
  · calc
      _ = ((n : ℝ) / 2) ^ G.isolatedMiddleRoles.card *
          (c * rootCorePowerScale (rootIsolatedReducedShape G) n) := by
            rw [div_pow]
            ring
      _ ≤ ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
          (c * rootCorePowerScale (rootIsolatedReducedShape G) n) :=
            mul_le_mul_of_nonneg_right hs.1 (mul_nonneg hc.le hScale)
      _ ≤ _ := mul_le_mul_of_nonneg_left hBound.1 hScalar
  · calc
      _ ≤ ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
          (C * rootCorePowerScale (rootIsolatedReducedShape G) n) :=
            mul_le_mul_of_nonneg_left hBound.2 hScalar
      _ ≤ (n : ℝ) ^ G.isolatedMiddleRoles.card *
          (C * rootCorePowerScale (rootIsolatedReducedShape G) n) :=
            mul_le_mul_of_nonneg_right hs.2 (mul_nonneg hC.le hScale)
      _ = _ := by ring

theorem root_isolated_sharp_upper_transfer (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C)
    (hUpper : paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖) ≤
        C * rootCorePowerScale (rootIsolatedReducedShape G) n) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      C * rootOriginalPowerScale G n := by
  have hScalar : (0 : ℝ) ≤
      ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) := by
    positivity
  have hScalarUpper :
      (((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) : ℝ) ≤
        (n : ℝ) ^ G.isolatedMiddleRoles.card := by
    exact_mod_cast root_isolated_scalar_le_pow n G.roles G.isolatedMiddleRoles.card
  rw [root_global_mean_eq_reduced_mean,
    root_originalPowerScale_eq_pow_mul_reduced G n (by omega)]
  calc
    _ ≤ ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        (C * rootCorePowerScale (rootIsolatedReducedShape G) n) :=
          mul_le_mul_of_nonneg_left hUpper hScalar
    _ ≤ (n : ℝ) ^ G.isolatedMiddleRoles.card *
        (C * rootCorePowerScale (rootIsolatedReducedShape G) n) :=
          mul_le_mul_of_nonneg_right hScalarUpper
            (mul_nonneg hC (root_corePowerScale_nonneg _ n hn))
    _ = _ := by ring

#print axioms root_global_mean_eq_reduced_mean
#print axioms root_originalPowerScale_eq_pow_mul_reduced
#print axioms root_isolated_sharp_twoSided_transfer
#print axioms root_isolated_sharp_upper_transfer
end GraphMatrixReplica
