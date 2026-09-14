import GraphMatrix.Probability.Synchronization.ComponentJointLaw
import GraphMatrix.Main.Synchronization.HalfInstanceAdapter
import GraphMatrix.Main.Synchronization.UniformTiltConstants
import GraphMatrix.Main.Synchronization.TrialMass
import GraphMatrix.Main.InternalGoodFloor

/-!
# synchronized actual trials for all weighted sums
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica
open WeightedSignTilt
attribute [local instance] Classical.propDecidable

private theorem p3_product_finiteProbability_instances
    {A : Type} {B : A → Type}
    (i j : Fintype A) (f g : ∀ a, Fintype (B a))
    (E : ∀ a, B a → Prop) (d e : ∀ a, DecidablePred (E a)) :
    (letI := i
     ∏ a : A, @finiteUniformProbability (B a) (f a) (E a) (d a)) =
    (letI := j
     ∏ a : A, @finiteUniformProbability (B a) (g a) (E a) (e a)) := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim f g
  cases Subsingleton.elim d e
  rfl

private theorem p3_le_product_finiteProbability_instances
    {A : Type} {B : A → Type} (x : ℝ)
    (i j : Fintype A) (f g : ∀ a, Fintype (B a))
    (E : ∀ a, B a → Prop) (d e : ∀ a, DecidablePred (E a))
    (h : x ≤ (letI := i
      ∏ a : A, @finiteUniformProbability (B a) (f a) (E a) (d a))) :
    x ≤ (letI := j
      ∏ a : A, @finiteUniformProbability (B a) (g a) (E a) (e a)) :=
  h.trans_eq (p3_product_finiteProbability_instances i j f g E d e)

private theorem p3_finiteProbability_congr_instances
    {Omega : Type} (i j : Fintype Omega) (A B : Omega → Prop)
    (d : DecidablePred A) (e : DecidablePred B)
    (h : ∀ x, A x ↔ B x) :
    @finiteUniformProbability Omega i A d =
      @finiteUniformProbability Omega j B e := by
  have hAB : A = B := funext (fun x => propext (h x))
  subst B
  cases Subsingleton.elim i j
  cases Subsingleton.elim d e
  rfl

/-- The component-local tail event used in one actual packed trial. -/
abbrev p3WeightedSumComponentEvent
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (eps : ℝ) (n : ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (x : P3ComponentPairSample P dimension cut K) : Prop :=
  eps * (n : ℝ) ^ ((P1AD.roleCount P cut K.1 : ℝ) / 2) *
      Real.sqrt (Real.log (n : ℝ)) ≤
    |weightedSum
      (fun j => p1Z P dimension cut K.1
        (p3DistinguishedBoundaryRole P cut K).1
        (p3DistinguishedBoundaryRole P cut K).2
        (mainP1InternalSample P cut dimension I K) x.1 j) x.2|

/-- A single actual separator tuple (one packed trial) succeeds for every active
component, with the weighted sums read from the actual conditional cube. -/
abbrev p3WeightedSumSimultaneousEvent
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (eps : ℝ) (n : ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut
      (fun _ : Fin P.roles => n / P.roles))
    (R : P2a.RestCube (G := P.toPartiteShape) cut
      (fun _ : Fin P.roles => n / P.roles)) : Prop :=
  ∃ i : Fin (n / P.roles),
    ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      p3WeightedSumComponentEvent P cut (fun _ => n / P.roles) eps n I K
        (p3ComponentSampleFromRest P (fun _ => n / P.roles) cut
          (n / P.roles) (fun _ => le_rfl) i K R)

/-- For a graph-fixed positive tilt, every sufficiently large equal-floor model
has conditional synchronized weighted-sum success probability at least one
half for every complete internally-good realization. -/
theorem p3_actual_weightedSum_sync_half_uniform_floor
    (P : PaperShape) (hr : 0 < P.roles) :
    ∃ eps : ℝ, 0 < eps ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ (cut : Finset (Fin P.roles)) (n : ℕ), N ≤ n →
      ∀ I : P2a.InternalCube (G := P.toPartiteShape) cut
          (fun _ : Fin P.roles => n / P.roles),
        mainInternalGood P cut (fun _ : Fin P.roles => n / P.roles) n I →
        (1 / 2 : ℝ) ≤ finiteUniformProbability
          (p3WeightedSumSimultaneousEvent P cut eps n I) := by
  classical
  let a : ℝ := 1 / (2 * (P.roles : ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity)).2
    have hrR : (1 : ℝ) ≤ (P.roles : ℝ) := by exact_mod_cast hr
    nlinarith
  obtain ⟨pExt, cS, CS, hpExt, hcS, hCS, htail⟩ :=
    main_p3_component_tail_uniform_tilt P a 1 ha hab
  let eps := mainP3Tilt P.roles cS
  have heps : 0 < eps := main_P3Tilt_pos P.roles cS hr hcS
  obtain ⟨nTail, hnTail, htail⟩ := htail eps heps
  let c := mainP3TrialCoefficient P.roles pExt
  have hc : 0 < c := main_P3TrialCoefficient_pos P.roles pExt hpExt
  obtain ⟨nMass, hMass⟩ :=
    main_P3_floor_trial_mass_eventually P.roles hr c hc
  refine ⟨eps, heps, max nTail (max nMass (2 * P.roles)),
    hnTail.trans (le_max_left _ _), ?_⟩
  intro cut n hn I hI
  have hnTail' : nTail ≤ n := (le_max_left _ _).trans hn
  have hnMass' : nMass ≤ n :=
    (le_max_left nMass (2 * P.roles)).trans ((le_max_right _ _).trans hn)
  have hn2r : 2 * P.roles ≤ n :=
    (le_max_right nMass (2 * P.roles)).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (hMass n hnMass').1
  let dimension := fun _ : Fin P.roles => n / P.roles
  let m := n / P.roles
  have hTrialBound : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      m ≤ dimension u.1 := fun _ => le_rfl
  let E := fun K : P2a.ActiveComponent P.toPartiteShape cut =>
    p3WeightedSumComponentEvent P cut dimension eps n I K
  let base := pExt * ((1 / 2 : ℝ) *
    Real.exp (-(96 * eps ^ 2 * Real.log (n : ℝ) / cS)))
  have hEach : ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      base ≤ finiteUniformProbability (E K) := by
    intro K
    have h := htail cut K.1 K.2
      (p3DistinguishedBoundaryRole P cut K).1
      (p3DistinguishedBoundaryRole P cut K).2
      dimension n hnTail'
      (main_uniformFloor_balanced P hr cut K.1 n hn2r)
      (mainP1InternalSample P cut dimension I K) (hI K)
    convert h using 1
  let k := Fintype.card (P2a.ActiveComponent P.toPartiteShape cut)
  have hk : k ≤ P.roles := by
    have hcard := main_activeComponent_card_eq_count P.toPartiteShape cut
    have heq : k = P.toPartiteShape.c079ActiveComponentCount cut := by
      convert hcard using 1 <;> congr!
    exact heq.le.trans (P.toPartiteShape.c079ActiveComponentCount_le_roles cut)
  let rho := c * (n : ℝ) ^ (-(1 / 4 : ℝ))
  have hrhoProduct : rho ≤
      ∏ K : P2a.ActiveComponent P.toPartiteShape cut,
        finiteUniformProbability (E K) := by
    calc
      rho ≤ base ^ k := by
        simpa [rho, c, base, eps, k] using
          main_P3_component_tail_product_lower P.roles k n pExt cS
            hr hk hn1 hpExt hcS
      _ = ∏ _K : P2a.ActiveComponent P.toPartiteShape cut, base := by
        simp [k]
      _ ≤ ∏ K : P2a.ActiveComponent P.toPartiteShape cut,
          finiteUniformProbability (E K) := by
        apply Finset.prod_le_prod
        · intro K _
          positivity
        · intro K _
          exact hEach K
  have hrhoBounds : 0 ≤ rho ∧ rho ≤ 1 := by
    simpa [rho, c] using main_P3_trial_probability_bounds P.roles n pExt hpExt hn1
  have hfailure : (1 - rho) ^ m ≤ (1 / 2 : ℝ) := by
    apply main_P3_failure_factor_half m rho hrhoBounds.1 hrhoBounds.2
    simpa [m, rho, c] using (hMass n hnMass').2
  have hsync := main_p3_some_trial_half_canonical
    P dimension cut m (fun _ => le_rfl) E rho hrhoBounds.1
      (by convert hrhoProduct using 1) hfailure
  convert hsync using 1


end GraphMatrixReplica
