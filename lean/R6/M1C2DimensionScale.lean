import R6.M1C2RoleAllocation
import R6.M1C2CoefficientScale

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open PaperR16 PaperR16.C2Actual
attribute [local instance] Classical.propDecidable

def rootC2FreshRoleCount (P : PaperShape) (S : Finset (Fin P.roles)) : ℕ :=
  (C1C2.rows P S \ C1C2.separator P S).card +
    (C1C2.cols P S \ C1C2.separator P S).card

def rootC2ActiveRoleCount (P : PaperShape) (S : Finset (Fin P.roles)) : ℕ :=
  ∑ K : P2a.ActiveComponent P.toPartiteShape S, Fintype.card (P2a.ComponentRole K)

theorem root_C2_dimensionFactor_uniform (P : PaperShape) (S : Finset (Fin P.roles)) (m : ℕ) :
    rootC2DimensionFactor P S (fun _ => m) =
      (m : ℝ) ^ ((rootC2FreshRoleCount P S : ℝ) / 2) := by
  have he : rootC2DimensionFactor P S (fun _ => m) =
      Real.sqrt ((m : ℝ) ^ rootC2FreshRoleCount P S) := by
    have hcard (A B : Finset (C1C2.Retained P S)) :
        Fintype.card {v : C1C2.Retained P S // v ∈ A ∧ v ∉ B} = (A \ B).card := by
      let e : {v : C1C2.Retained P S // v ∈ A ∧ v ∉ B} ≃ ↥(A \ B) :=
        Equiv.subtypeEquivRight fun _ => Finset.mem_sdiff.symm
      exact (Fintype.card_congr e).trans (Fintype.card_coe _)
    simp [rootC2DimensionFactor, rootC2FreshRoleCount, C2.RoleAssign,
      C1C2.retainedLabel, X, Fintype.card_pi, pow_add, hcard]
  rw [he, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 1
  ring

theorem root_C2_dimensionFactor_uniform_lower (P : PaperShape) (S : Finset (Fin P.roles))
    (m n : ℕ) (a : ℝ) (ha : 0 ≤ a) (hm : a * n ≤ m) :
    (a * n) ^ ((rootC2FreshRoleCount P S : ℝ) / 2) ≤
      rootC2DimensionFactor P S (fun _ => m) := by
  rw [root_C2_dimensionFactor_uniform]
  exact Real.rpow_le_rpow (mul_nonneg ha (Nat.cast_nonneg n)) hm (by positivity)

theorem root_C2_fresh_active_exponent (P : PaperShape) (S : Finset (Fin P.roles))
    (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) :
    (rootC2FreshRoleCount P S : ℝ) / 2 + (rootC2ActiveRoleCount P S : ℝ) / 2 =
      ((P.roles : ℝ) - S.card) / 2 := by
  have h : (rootC2FreshRoleCount P S : ℝ) + S.card + rootC2ActiveRoleCount P S = P.roles := by
    exact_mod_cast root_C2_full_role_allocation P S hNoIso hMin
  linarith

/-- Exact n-exponent and graph-constant separation after a synchronous
active-component threshold is inserted into the actual C2 expectation bound. -/
theorem root_C2_combined_scale_eq (P : PaperShape) (S : Finset (Fin P.roles))
    (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (n : ℕ) (hn : 0 < n) (a c p L : ℝ) (ha : 0 ≤ a) :
    ((a * n) ^ ((rootC2FreshRoleCount P S : ℝ) / 2) *
        (c * (n : ℝ) ^ ((rootC2ActiveRoleCount P S : ℝ) / 2) * L) * p) /
          (Real.sqrt 3 ^ freshCount P S) =
      (a ^ ((rootC2FreshRoleCount P S : ℝ) / 2) * c * p /
        (Real.sqrt 3 ^ freshCount P S)) *
          (n : ℝ) ^ (((P.roles : ℝ) - S.card) / 2) * L := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ ((rootC2FreshRoleCount P S : ℝ) / 2) *
      (n : ℝ) ^ ((rootC2ActiveRoleCount P S : ℝ) / 2) =
        (n : ℝ) ^ (((P.roles : ℝ) - S.card) / 2) := by
    rw [← Real.rpow_add hnR, root_C2_fresh_active_exponent P S hNoIso hMin]
  rw [Real.mul_rpow ha hnR.le]
  calc
    _ = (a ^ ((rootC2FreshRoleCount P S : ℝ) / 2) * c * p /
        (Real.sqrt 3 ^ freshCount P S)) *
      ((n : ℝ) ^ ((rootC2FreshRoleCount P S : ℝ) / 2) *
        (n : ℝ) ^ ((rootC2ActiveRoleCount P S : ℝ) / 2)) * L := by ring
    _ = _ := by rw [hp]

#print axioms root_C2_dimensionFactor_uniform
#print axioms root_C2_dimensionFactor_uniform_lower
#print axioms root_C2_fresh_active_exponent
#print axioms root_C2_combined_scale_eq
end GraphMatrixReplica
