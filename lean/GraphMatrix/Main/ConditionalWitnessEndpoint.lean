import GraphMatrix.Main.FrozenWitnessLaw
import GraphMatrix.Main.InternalGoodFloor
import GraphMatrix.Main.ActiveThresholdProduct

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open Model Model.C2Actual
attribute [local instance] Classical.propDecidable

/-- A good-set probability and a pointwise conditional success probability
multiply under the actual finite product average. -/
theorem main_joint_probability_lower_from_good
    {A B : Type} [Fintype A] [Fintype B]
    (Good : A → Prop) (E : A → B → Prop) (q r : ℝ) (hr : 0 ≤ r)
    (hq : q ≤ finiteUniformProbability Good)
    (hConditional : ∀ a, Good a → r ≤ finiteUniformProbability (E a)) :
    r * q ≤ finiteUniformProbability (fun p : A × B => E p.1 p.2) := by
  have hGood := main_event_threshold_mul_le_mean Good
    (fun a => finiteUniformProbability (E a)) r
    (fun a => p3_finiteUniformProbability_nonneg (E a)) hConditional
  have hIter : paperMean (fun a => finiteUniformProbability (E a)) =
      finiteUniformProbability (fun p : A × B => E p.1 p.2) := by
    unfold finiteUniformProbability
    exact (P2a.paperMean_prod (fun a b => if E a b then (1 : ℝ) else 0)).symm
  exact (mul_le_mul_of_nonneg_left hq hr).trans (hGood.trans_eq hIter)

/-- Actual success uses a single separator tuple for every genuine component. -/
def mainSimultaneousComponentEvent (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (eps : ℝ) (n : ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) : Prop :=
  ∃ s : CutAssignment (G := P.toPartiteShape) cut dimension,
    ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      eps * (n : ℝ) ^ ((Fintype.card (P2a.ComponentRole K) : ℝ) / 2) *
        Real.sqrt (Real.log (n : ℝ)) ≤
      |componentContractionAt (G := P.toPartiteShape) cut dimension I R s K|

/-- Fixed-good-internal conditional success at least one half gives the exact
actual frozen witness probability q/2, with no probability-model replacement. -/
theorem main_uniformWitness_probability_of_conditional
    (P : PaperShape) (cut : Finset (Fin P.roles)) (eps q : ℝ)
    (heps : 0 ≤ eps) (n : ℕ) (hn : 1 ≤ n)
    (hq : q ≤ finiteUniformProbability
      (mainInternalGood P cut (fun _ : Fin P.roles => n / P.roles) n))
    (hConditional : ∀ I : P2a.InternalCube (G := P.toPartiteShape) cut
        (fun _ : Fin P.roles => n / P.roles),
      mainInternalGood P cut (fun _ : Fin P.roles => n / P.roles) n I →
      (1 / 2 : ℝ) ≤ finiteUniformProbability
        (mainSimultaneousComponentEvent P cut (fun _ : Fin P.roles => n / P.roles) eps n I)) :
    q / 2 ≤ mainUniformWitnessProbability P cut
      (eps ^ P.toPartiteShape.c079ActiveComponentCount cut) n := by
  let dimension := fun _ : Fin P.roles => n / P.roles
  let t := mainLowerWitnessThreshold P cut
    (eps ^ P.toPartiteShape.c079ActiveComponentCount cut) n
  let E := mainSimultaneousComponentEvent P cut dimension eps n
  let W := fun p : P2a.InternalCube (G := P.toPartiteShape) cut dimension ×
      P2a.RestCube (G := P.toPartiteShape) cut dimension =>
    ∃ s : CutAssignment (G := P.toPartiteShape) cut dimension,
      t ≤ |∏ K : P2a.ActiveComponent P.toPartiteShape cut,
        componentContractionAt (G := P.toPartiteShape) cut dimension p.1 p.2 s K|
  have hJoint := main_joint_probability_lower_from_good
    (mainInternalGood P cut dimension n) E q (1 / 2) (by norm_num) hq hConditional
  have hMono : finiteUniformProbability (fun p : P2a.InternalCube (G := P.toPartiteShape) cut dimension ×
      P2a.RestCube (G := P.toPartiteShape) cut dimension => E p.1 p.2) ≤ finiteUniformProbability W := by
    apply finiteUniformProbability_mono
    intro p hp
    obtain ⟨s, hs⟩ := hp
    refine ⟨s, ?_⟩
    dsimp [t]
    rw [← main_active_threshold_product P cut eps n hn, Finset.abs_prod]
    apply Finset.prod_le_prod
    · intro K _
      positivity
    · intro K _
      exact hs K
  have hLaw := main_frozen_witness_probability_eq_internalRest
    P.toPartiteShape cut dimension t
  calc
    q / 2 = (1 / 2 : ℝ) * q := by ring
    _ ≤ finiteUniformProbability W := hJoint.trans hMono
    _ = mainUniformWitnessProbability P cut
        (eps ^ P.toPartiteShape.c079ActiveComponentCount cut) n := hLaw.symm

/-- The last input can be a uniform conditional simultaneous-success bound;
the full internal good-set probability, graph constants, and frozen transport
are all supplied by proved theorems in this endpoint. -/
theorem main_uniformWitness_constants_of_conditional
    (P : PaperShape) (hr : 0 < P.roles) (cut : Finset (Fin P.roles))
    (eps : ℝ) (heps : 0 < eps) (N : ℕ)
    (hConditional : ∀ n : ℕ, N ≤ n →
      ∀ I : P2a.InternalCube (G := P.toPartiteShape) cut (fun _ : Fin P.roles => n / P.roles),
        mainInternalGood P cut (fun _ : Fin P.roles => n / P.roles) n I →
        (1 / 2 : ℝ) ≤ finiteUniformProbability
          (mainSimultaneousComponentEvent P cut (fun _ : Fin P.roles => n / P.roles) eps n I)) :
    ∃ c p : ℝ, 0 < c ∧ 0 < p ∧ ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n →
      p ≤ mainUniformWitnessProbability P cut c n := by
  obtain ⟨q, hq, M, hM, hGood⟩ := main_internalGood_uniform_floor P hr
  refine ⟨eps ^ P.toPartiteShape.c079ActiveComponentCount cut, q / 2,
    pow_pos heps _, by positivity, max N M, ?_⟩
  intro n hn
  exact main_uniformWitness_probability_of_conditional P cut eps q heps.le n
    (hM.trans ((le_max_right _ _).trans hn))
    (hGood cut n ((le_max_right _ _).trans hn))
    (hConditional n ((le_max_left _ _).trans hn))

end GraphMatrixReplica
