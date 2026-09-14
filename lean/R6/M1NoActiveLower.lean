import R6.M1UniformLowerEndpoint
import R6.PaperRademacherWalshProjection

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open PaperR16 PaperR16.C2Actual
attribute [local instance] Classical.propDecidable

/-- Empty genuine active family: the actual product weight is one, so a
separator witness has probability exactly one at the c=1 threshold. -/
theorem root_noActive_witnessProbability_eq_one (P : PaperShape) (S : Finset (Fin P.roles))
    (hActive : P.toPartiteShape.c079ActiveComponentCount S = 0)
    (hr : 0 < P.roles) (n : ℕ) (hn : 2 * P.roles ≤ n) :
    rootUniformWitnessProbability P S 1 n = 1 := by
  have hcard : Fintype.card (P2a.ActiveComponent P.toPartiteShape S) = 0 :=
    (root_activeComponent_card_eq_count P.toPartiteShape S).trans hActive
  letI : IsEmpty (P2a.ActiveComponent P.toPartiteShape S) := Fintype.card_eq_zero_iff.mp hcard
  have hD : rootC2ActiveRoleCount P S = 0 := by simp [rootC2ActiveRoleCount]
  have hT : rootLowerWitnessThreshold P S 1 n = 1 := by
    simp [rootLowerWitnessThreshold, hD, hActive]
  have hm : 0 < n / P.roles := Nat.div_pos (by omega) hr
  let s : CutAssignment (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles) :=
    fun _ => ⟨0, hm⟩
  have hWeight (ω : FrozenSample (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles)) :
      actualWeight (G := P.toPartiteShape) S (fun _ => n / P.roles) ω s = 1 := by
    simp [actualWeight]
  have hEvent (ω : FrozenSample (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles)) :
      ∃ t : CutAssignment (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles),
        rootLowerWitnessThreshold P S 1 n ≤
          |actualWeight (G := P.toPartiteShape) S (fun _ => n / P.roles) ω t| := by
    refine ⟨s, ?_⟩
    rw [hT, hWeight]
    norm_num
  simp only [rootUniformWitnessProbability, finiteUniformProbability, hEvent, if_true,
    paperMean_const_function]

/-- Unconditional lower half for a no-isolated graph with a*=0 and positive
role count. This is a proved branch of the original theorem, not a P3 premise. -/
theorem root_noActiveMaximum_globalLower (P : PaperShape)
    (hNoIso : P.HasNoIsolatedMiddleRoles) (hr : 0 < P.roles)
    (hZero : P.toPartiteShape.c079ActiveMaximum = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * rootCorePowerScale P n ≤ paperMean (fun w : PaperNoise n => ‖paperGraphMatrix P n w‖) := by
  apply root_noIsolated_globalLower_of_witnesses P hNoIso hr
  intro S hMin
  have hA : P.toPartiteShape.c079ActiveComponentCount S = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa only [hZero] using P.toPartiteShape.c079ActiveComponentCount_le_maximum S hMin
  refine ⟨1, 1, by norm_num, by norm_num, 2 * P.roles, ?_⟩
  intro n hn
  exact (root_noActive_witnessProbability_eq_one P S hA hr n hn).symm.le

/-- Original globally injective lower bound for a*=0, including all detached
and isolated contributions, provided some non-isolated role remains. -/
theorem root_noActiveMaximum_originalLower (G : PaperShape)
    (hr : 0 < (rootIsolatedReducedShape G).roles)
    (hZero : G.toPartiteShape.c079ActiveMaximum = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * rootOriginalPowerScale G n ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  have hReduced : (rootIsolatedReducedShape G).toPartiteShape.c079ActiveMaximum = 0 := by
    rw [root_reduced_activeMaximum_eq, hZero]
  obtain ⟨c, hc, N, hLower⟩ := root_noActiveMaximum_globalLower (rootIsolatedReducedShape G)
    (root_reduced_hasNoIsolated G) hr hReduced
  have h := root_isolated_sharp_lower_transfer G c hc N hLower
  exact ⟨c / (2 : ℝ) ^ G.isolatedMiddleRoles.card, h.1, max N (max 2 (2 * G.roles)), h.2⟩

#print axioms root_noActive_witnessProbability_eq_one
#print axioms root_noActiveMaximum_globalLower
#print axioms root_noActiveMaximum_originalLower
end GraphMatrixReplica
