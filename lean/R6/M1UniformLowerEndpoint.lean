import R6.M1ColorLowerAssembly
import R6.M1C2WitnessExpectation
import R6.M1C2DimensionScale

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open PaperR16 PaperR16.C2Actual
attribute [local instance] Classical.propDecidable

def rootUniformCutScale (P : PaperShape) (S : Finset (Fin P.roles)) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (((P.roles : ℝ) - S.card) / 2) *
    Real.log (n : ℝ) ^ ((P.toPartiteShape.c079ActiveComponentCount S : ℝ) / 2)

def rootLowerWitnessThreshold (P : PaperShape) (S : Finset (Fin P.roles)) (c : ℝ) (n : ℕ) : ℝ :=
  c * (n : ℝ) ^ ((rootC2ActiveRoleCount P S : ℝ) / 2) *
    Real.log (n : ℝ) ^ ((P.toPartiteShape.c079ActiveComponentCount S : ℝ) / 2)

def rootUniformWitnessProbability (P : PaperShape) (S : Finset (Fin P.roles))
    (c : ℝ) (n : ℕ) : ℝ :=
  finiteUniformProbability (fun ω : FrozenSample (G := P.toPartiteShape) S
      (fun _ : Fin P.roles => n / P.roles) =>
    ∃ s : CutAssignment (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles),
      rootLowerWitnessThreshold P S c n ≤
        |actualWeight (G := P.toPartiteShape) S (fun _ => n / P.roles) ω s|)

def rootUniformLowerConstant (P : PaperShape) (S : Finset (Fin P.roles)) (c p : ℝ) : ℝ :=
  (1 / (2 * (P.roles : ℝ))) ^ ((rootC2FreshRoleCount P S : ℝ) / 2) * c * p /
    (Real.sqrt 3 ^ freshCount P S)

theorem root_uniformLowerConstant_pos (P : PaperShape) (S : Finset (Fin P.roles))
    (hr : 0 < P.roles) (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    0 < rootUniformLowerConstant P S c p := by
  have hrR : (0 : ℝ) < P.roles := by exact_mod_cast hr
  unfold rootUniformLowerConstant
  positivity

theorem root_lowerWitnessThreshold_nonneg (P : PaperShape) (S : Finset (Fin P.roles))
    (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ rootLowerWitnessThreshold P S c n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  unfold rootLowerWitnessThreshold
  positivity

/-- The fixed floor-color typed lower endpoint. The remaining probabilistic
input is precisely the actual simultaneous-witness probability. -/
theorem root_uniformTyped_lower_from_probability (P : PaperShape) (S : Finset (Fin P.roles))
    (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) (hr : 0 < P.roles)
    (c p : ℝ) (hc : 0 < c) (hp : 0 < p) (n : ℕ) (hn : 2 * P.roles ≤ n)
    (hProb : p ≤ rootUniformWitnessProbability P S c n) :
    rootUniformLowerConstant P S c p * rootUniformCutScale P S n ≤
      paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape)
          (fun _ : Fin P.roles => n / P.roles) =>
        ‖c027PartiteBoundaryMatrixReal P (fun _ => n / P.roles) ε‖) := by
  let a : ℝ := 1 / (2 * (P.roles : ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hdim : ∀ _v : Fin P.roles, 0 < n / P.roles :=
    fun _ => Nat.div_pos (by omega) hr
  have hD := root_C2_dimensionFactor_uniform_lower P S (n / P.roles) n a ha
    (root_uniformRoleDimension_bounds P.roles n hr hn).1
  have ht := root_lowerWitnessThreshold_nonneg P S c hc.le n hn1
  have hMean := root_C2_mean_lower_of_witnessProbability P S (fun _ => n / P.roles)
    hNoIso hMin hdim (rootLowerWitnessThreshold P S c n) p ht hProb
  have hProd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD ht) hp.le
  have h := (div_le_div_of_nonneg_right hProd (by positivity)).trans hMean
  change ((a * n) ^ ((rootC2FreshRoleCount P S : ℝ) / 2) *
      (c * (n : ℝ) ^ ((rootC2ActiveRoleCount P S : ℝ) / 2) *
        Real.log (n : ℝ) ^ ((P.toPartiteShape.c079ActiveComponentCount S : ℝ) / 2)) * p) /
          (Real.sqrt 3 ^ freshCount P S) ≤ _ at h
  rw [root_C2_combined_scale_eq P S hNoIso hMin n hn0 a c p _ ha] at h
  simpa only [a, rootUniformLowerConstant, rootUniformCutScale, mul_assoc] using h

theorem root_minimum_cut_card_eq (P : PaperShape) (S : Finset (Fin P.roles))
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) :
    S.card = P.toPartiteShape.rightLeftSeparatorNumber := by
  exact Nat.le_antisymm
    (hMin.2 P.toPartiteShape.minimumRightLeftSeparator P.toPartiteShape.minimumRightLeftSeparator_isMinimum.1)
    (P.toPartiteShape.minimumRightLeftSeparator_isMinimum.2 S hMin.1)

theorem root_activeComponent_card_eq_count (G : PartiteShape) (S : Finset (Fin G.roles)) :
    Fintype.card (P2a.ActiveComponent G S) = G.c079ActiveComponentCount S := by
  simp [P2a.ActiveComponent, PartiteShape.c079ActiveComponentCount, Fintype.card_subtype]

/-- Once P3 supplies graph-only constants for one optimal minimum cut, color
transfer gives the original no-isolated graph mean, with a uniform threshold. -/
theorem root_uniform_globalLower_from_probability (P : PaperShape)
    (S : Finset (Fin P.roles)) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) (hr : 0 < P.roles)
    (hMax : P.toPartiteShape.c079ActiveComponentCount S = P.toPartiteShape.c079ActiveMaximum)
    (c p : ℝ) (hc : 0 < c) (hp : 0 < p) (N : ℕ)
    (hProb : ∀ n : ℕ, N ≤ n → p ≤ rootUniformWitnessProbability P S c n) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n →
      c' * rootCorePowerScale P n ≤ paperMean (fun w : PaperNoise n => ‖paperGraphMatrix P n w‖) := by
  have hTyped : ∀ n : ℕ, max N (2 * P.roles) ≤ n →
      rootUniformLowerConstant P S c p * rootCorePowerScale P n ≤
        paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape)
            (fun _ : Fin P.roles => n / P.roles) =>
          ‖c027PartiteBoundaryMatrixReal P (fun _ => n / P.roles) ε‖) := by
    intro n hn
    have h := root_uniformTyped_lower_from_probability P S hNoIso hMin hr c p hc hp n
      ((le_max_right _ _).trans hn) (hProb n ((le_max_left _ _).trans hn))
    simpa only [rootUniformCutScale, rootCorePowerScale, root_minimum_cut_card_eq P S hMin, hMax] using h
  obtain ⟨c', hc', hglobal⟩ := root_uniformTyped_lower_to_global P hNoIso
    (rootUniformLowerConstant P S c p) (root_uniformLowerConstant_pos P S hr c p hc hp)
    (max N (2 * P.roles)) hTyped
  exact ⟨c', hc', max N (2 * P.roles), hglobal⟩

/-- Choose the genuine active-maximizing minimum cut internally. The explicit
input remains the unproved P3 event-probability obligation, not a norm bound. -/
theorem root_noIsolated_globalLower_of_witnesses (P : PaperShape)
    (hNoIso : P.HasNoIsolatedMiddleRoles) (hr : 0 < P.roles)
    (hWitness : ∀ S : Finset (Fin P.roles), P.toPartiteShape.IsMinimumRightLeftSeparator S →
      ∃ c p : ℝ, 0 < c ∧ 0 < p ∧ ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n → p ≤ rootUniformWitnessProbability P S c n) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n →
      c' * rootCorePowerScale P n ≤ paperMean (fun w : PaperNoise n => ‖paperGraphMatrix P n w‖) := by
  obtain ⟨S, hMin, hMax⟩ := P.toPartiteShape.exists_minimum_with_c079ActiveMaximum
  obtain ⟨c, p, hc, hp, N, hProb⟩ := hWitness S hMin
  exact root_uniform_globalLower_from_probability P S hNoIso hMin hr hMax c p hc hp N hProb

/-- Restore all isolated roles after consuming P3 on the actual reduced graph.
The zero-residual branch belongs to the separate edgeless proof. -/
theorem root_originalLower_from_reduced_witnesses (G : PaperShape)
    (hr : 0 < (rootIsolatedReducedShape G).roles)
    (hWitness : ∀ S : Finset (Fin (rootIsolatedReducedShape G).roles),
      (rootIsolatedReducedShape G).toPartiteShape.IsMinimumRightLeftSeparator S →
        ∃ c p : ℝ, 0 < c ∧ 0 < p ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          p ≤ rootUniformWitnessProbability (rootIsolatedReducedShape G) S c n) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n →
      c' * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
        G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2) ≤
        paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  obtain ⟨c, hc, N, hLower⟩ := root_noIsolated_globalLower_of_witnesses
    (rootIsolatedReducedShape G) (root_reduced_hasNoIsolated G) hr hWitness
  have h := root_isolated_sharp_lower_transfer G c hc N hLower
  refine ⟨c / (2 : ℝ) ^ G.isolatedMiddleRoles.card, h.1, max N (max 2 (2 * G.roles)), ?_⟩
  intro n hn
  simpa only [rootOriginalPowerScale, mul_assoc] using h.2 n hn

#print root_originalLower_from_reduced_witnesses
#print axioms root_originalLower_from_reduced_witnesses
#print axioms root_noIsolated_globalLower_of_witnesses
#print axioms root_uniformTyped_lower_from_probability
#print axioms root_minimum_cut_card_eq
#print axioms root_activeComponent_card_eq_count
#print axioms root_uniform_globalLower_from_probability
end GraphMatrixReplica
