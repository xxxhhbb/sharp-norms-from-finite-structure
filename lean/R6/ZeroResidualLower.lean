import R6.M1NoActiveLower
import R6.PaperR16ColorUpperLpAdapter
import R6.PaperRademacherWalshProjection

/-! # The zero-role residual lower branch

If deleting the isolated middle roles leaves no roles at all, the reduced
matrix is the one-by-one matrix with entry one.  The already-proved sharp
isolated-role transfer then restores the exact falling-factorial contribution
for the original matrix.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace GraphMatrixReplica

/-- The manuscript core scale is exactly one for a zero-role shape. -/
theorem root_zeroRole_corePowerScale_eq_one
    (P : PaperShape) (hroles : P.roles = 0) (n : ℕ) :
    rootCorePowerScale P n = 1 := by
  have hs : P.toPartiteShape.rightLeftSeparatorNumber = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [PartiteShape.rightLeftSeparatorNumber,
      P.toPartiteShape_roles, hroles] using
      Finset.card_le_univ P.toPartiteShape.minimumRightLeftSeparator
  have ha : P.toPartiteShape.c079ActiveMaximum = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa [P.toPartiteShape_roles, hroles] using
      P.toPartiteShape.c079ActiveMaximum_le_roles
  simp [rootCorePowerScale, hroles, hs, ha]

/-- Exact reduced lower input when the isolated-role reduction has no roles. -/
theorem root_zeroRole_globalMean_lower
    (P : PaperShape) (hroles : P.roles = 0) :
    ∀ n : ℕ, 1 ≤ n →
      (1 : ℝ) * rootCorePowerScale P n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix P n w‖) := by
  intro n hn
  rw [root_zeroRole_corePowerScale_eq_one P hroles n, mul_one]
  simp only [paperR16_zeroRole_graphMatrix_norm_eq_one P hroles,
    paperMean_const_function]
  norm_num

/-- Full original sharp lower bound in the last missing boundary case: after
removing isolated middle roles, no role remains. -/
theorem root_zeroResidual_originalLower
    (G : PaperShape)
    (hzero : (rootIsolatedReducedShape G).roles = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * rootOriginalPowerScale G n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  have hReduced : ∀ n : ℕ, 1 ≤ n →
      (1 : ℝ) * rootCorePowerScale (rootIsolatedReducedShape G) n ≤
          paperMean (fun w : PaperNoise n =>
            ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖) ∧
        paperMean (fun w : PaperNoise n =>
            ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖) ≤
          (1 : ℝ) * rootCorePowerScale (rootIsolatedReducedShape G) n := by
    intro n hn
    have hScale := root_zeroRole_corePowerScale_eq_one
      (rootIsolatedReducedShape G) hzero n
    have hMean : paperMean (fun w : PaperNoise n =>
        ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖) = 1 := by
      simp only [paperR16_zeroRole_graphMatrix_norm_eq_one
        (rootIsolatedReducedShape G) hzero, paperMean_const_function]
    rw [hScale, hMean]
    norm_num
  have h := root_isolated_sharp_twoSided_transfer G 1 1
    (by norm_num) (by norm_num) 1 hReduced
  exact ⟨1 / (2 : ℝ) ^ G.isolatedMiddleRoles.card, h.1,
    max 1 (max 2 (2 * G.roles)), fun n hn => (h.2 n hn).1⟩

/-- Complete original lower branch when the active maximum is zero, including
the formerly omitted case in which the isolated-role reduction has no roles. -/
theorem root_noActiveMaximum_originalLower_all
    (G : PaperShape)
    (hZero : G.toPartiteShape.c079ActiveMaximum = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * rootOriginalPowerScale G n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  by_cases hroles : (rootIsolatedReducedShape G).roles = 0
  · exact root_zeroResidual_originalLower G hroles
  · exact root_noActiveMaximum_originalLower G (Nat.pos_of_ne_zero hroles) hZero

#print axioms root_zeroRole_corePowerScale_eq_one
#print axioms root_zeroRole_globalMean_lower
#print axioms root_zeroResidual_originalLower
#print axioms root_noActiveMaximum_originalLower_all

end GraphMatrixReplica
