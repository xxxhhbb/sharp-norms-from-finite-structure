import R6.M1IsolatedSharpTransfer
import R6.PaperR16ColorLowerFinal
import R6.PaperRoleColoringExistence

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica

theorem root_finiteUniformL1_eq_mean_norm {Ω E : Type} [Fintype Ω] [NormedAddCommGroup E]
    (f : Ω → E) : paperFiniteUniformLq f 1 = paperMean (fun w => ‖f w‖) := by
  rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ 1 (by norm_num)]
  simp only [Real.rpow_one, inv_one]

theorem root_uniformRoleDimension_bounds (r n : ℕ) (hr : 0 < r) (hn : 2 * r ≤ n) :
    (1 / (2 * (r : ℝ))) * n ≤ (n / r : ℕ) ∧ (n / r : ℕ) ≤ n := by
  constructor
  · have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hdiv : (n / r : ℕ) * (r : ℝ) + (n % r : ℕ) = n := by
      exact_mod_cast (show (n / r) * r + n % r = n by simpa [Nat.mul_comm] using Nat.div_add_mod n r)
    have hmod : ((n % r : ℕ) : ℝ) < r := by exact_mod_cast Nat.mod_lt n hr
    have hnR : 2 * (r : ℝ) ≤ n := by exact_mod_cast hn
    rw [show (1 / (2 * (r : ℝ))) * n = (n : ℝ) / (2 * r) by ring]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)).mpr
    nlinarith
  · exact Nat.div_le_self n r

theorem root_uniformColor_mean_lower (G : PaperShape) (hNoIso : G.HasNoIsolatedMiddleRoles)
    (n : ℕ) :
    (Fintype.card G.R16BoundaryFixingAutomorphism : ℝ) *
      paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape)
          (fun _ : Fin G.roles => n / G.roles) =>
        ‖c027PartiteBoundaryMatrixReal G (fun _ => n / G.roles) epsilon‖) ≤
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  simpa only [root_finiteUniformL1_eq_mean_norm] using
    (uniformPaperRoleColoring G n).independentTypedColorLower hNoIso 1 (by norm_num)

theorem root_reduced_hasNoIsolated (G : PaperShape) :
    (rootIsolatedReducedShape G).HasNoIsolatedMiddleRoles := by
  intro v
  exact root_reduced_not_isolated G v

/-- Exact color-to-global lower reduction at the fixed floor-sized dimensions.
The actual typed lower theorem is intentionally still a premise of this bridge. -/
theorem root_uniformTyped_lower_to_global (G : PaperShape) (hNoIso : G.HasNoIsolatedMiddleRoles)
    (c : ℝ) (hc : 0 < c) (N : ℕ)
    (hTyped : ∀ n : ℕ, N ≤ n → c * rootCorePowerScale G n ≤
      paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape)
          (fun _ : Fin G.roles => n / G.roles) =>
        ‖c027PartiteBoundaryMatrixReal G (fun _ => n / G.roles) epsilon‖)) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, N ≤ n → c' * rootCorePowerScale G n ≤
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  let k : ℝ := Fintype.card G.R16BoundaryFixingAutomorphism
  have hk : 0 < k := G.colorLowerCoefficient_pos
  refine ⟨k * c, mul_pos hk hc, ?_⟩
  intro n hn
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hTyped n hn) hk.le).trans
    (root_uniformColor_mean_lower G hNoIso n)

/-- Restore the actual falling-factorial isolated contribution in a lower bound.
This transport theorem does not assert the still-needed reduced lower bound. -/
theorem root_isolated_sharp_lower_transfer (G : PaperShape) (c : ℝ) (hc : 0 < c)
    (N : ℕ)
    (hLower : ∀ n : ℕ, N ≤ n → c * rootCorePowerScale (rootIsolatedReducedShape G) n ≤
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix (rootIsolatedReducedShape G) n w‖)) :
    0 < c / (2 : ℝ) ^ G.isolatedMiddleRoles.card ∧
      ∀ n : ℕ, max N (max 2 (2 * G.roles)) ≤ n →
        (c / (2 : ℝ) ^ G.isolatedMiddleRoles.card) * rootOriginalPowerScale G n ≤
          paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  refine ⟨by positivity, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnTwo : 2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnRoles : 2 * G.roles ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hs := root_isolated_scalar_real_bounds n G.roles G.isolatedMiddleRoles.card
    (root_isolated_card_le_roles G) hnRoles
  have hScale := root_corePowerScale_nonneg (rootIsolatedReducedShape G) n (by omega)
  have hScalar : (0 : ℝ) ≤
      ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) := by
    positivity
  rw [root_global_mean_eq_reduced_mean,
    root_originalPowerScale_eq_pow_mul_reduced G n (by omega)]
  calc
    _ = ((n : ℝ) / 2) ^ G.isolatedMiddleRoles.card *
        (c * rootCorePowerScale (rootIsolatedReducedShape G) n) := by
      rw [div_pow]; ring
    _ ≤ ((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) *
        (c * rootCorePowerScale (rootIsolatedReducedShape G) n) :=
      mul_le_mul_of_nonneg_right hs.1 (mul_nonneg hc.le hScale)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hLower n hnN) hScalar

#print axioms root_uniformRoleDimension_bounds
#print axioms root_uniformColor_mean_lower
#print axioms root_reduced_hasNoIsolated
#print axioms root_uniformTyped_lower_to_global
#print axioms root_isolated_sharp_lower_transfer
end GraphMatrixReplica
