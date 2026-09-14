import R6.P3ActualP1ComponentLaw
import R6.P3SyncAmplification

/-!
# P3: exact joint P1 sample law on the actual conditional rest cube
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

/-- The P1 pair sample belonging to one active component. -/
abbrev P3ComponentPairSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :=
  P1SecondSample P dimension cut K.1
      (p3DistinguishedBoundaryRole P cut K).1 ×
    (Fin (dimension (p3DistinguishedBoundaryRole P cut K).1) → Bool)

/-- The Boolean coordinates for one fixed trial and component are exactly its
P1 second-stage pair sample. -/
def p3ComponentBitsEquivP1Sample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    ((Σ z : P2a.AttachedRole (G := P.toPartiteShape) cut K,
        Fin (dimension z.1)) → Bool) ≃
      P3ComponentPairSample P dimension cut K :=
  (P2a.reindexFunctionEquiv
      (p3AttachedLabelEquivComponentCoord P dimension cut K).symm).trans
    P2a.sumSigmaFunctionEquiv

/-- Simultaneously reindex every trial/component Boolean coordinate into the
corresponding P1 pair sample. -/
def p3TrialBitsEquivAllComponentSamples
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ) :
    (P2a.TrialScalar P.toPartiteShape cut dimension N → Bool) ≃
      (∀ _i : Fin N, ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
        P3ComponentPairSample P dimension cut K) :=
  (p3_sigmaFunctionEquiv
      (fun _i : Fin N =>
        Σ K : P2a.ActiveComponent P.toPartiteShape cut,
          Σ z : P2a.AttachedRole (G := P.toPartiteShape) cut K,
            Fin (dimension z.1)) Bool).trans
    (Equiv.piCongrRight (fun _i : Fin N =>
      (p3_sigmaFunctionEquiv
          (fun K : P2a.ActiveComponent P.toPartiteShape cut =>
            Σ z : P2a.AttachedRole (G := P.toPartiteShape) cut K,
              Fin (dimension z.1)) Bool).trans
        (Equiv.piCongrRight (fun K =>
          p3ComponentBitsEquivP1Sample P dimension cut K))))

/-- Decode all P1 component samples from one actual conditional rest sample. -/
def p3AllComponentSamplesFromRest
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) :=
  p3TrialBitsEquivAllComponentSamples P dimension cut N
    (fun g => p3TrialScalarBit (G := P.toPartiteShape) (cut := cut)
      dimension N hN g R)

/-- The simultaneous decoder agrees pointwise with the previously verified
one-trial/component decoder. -/
theorem p3AllComponentSamplesFromRest_apply
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    p3AllComponentSamplesFromRest P dimension cut N hN R i K =
      p3ComponentSampleFromRest P dimension cut N hN i K R := by
  rfl

/-- Every event on the full family of P1 pair samples has its exact product-cube
uniform probability under the actual conditional rest cube. -/
theorem p3AllComponentSamplesFromRest_uniform_probability
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (A : (∀ _i : Fin N,
        ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
          P3ComponentPairSample P dimension cut K) → Prop)
    [DecidablePred A] :
    finiteUniformProbability
        (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
          A (p3AllComponentSamplesFromRest P dimension cut N hN R)) =
      finiteUniformProbability A := by
  classical
  letI : Fintype
      (P2a.TrialScalar P.toPartiteShape cut dimension N → Bool) :=
    p3TrialScalarBoolCubeFintype (G := P.toPartiteShape) (cut := cut)
      dimension N
  let e := p3TrialBitsEquivAllComponentSamples P dimension cut N
  have hfull := conditional_trialScalarBit_uniform_probability
    (G := P.toPartiteShape) (cut := cut) dimension N hN
    (fun w => A (e w))
  calc
    finiteUniformProbability
        (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
          A (p3AllComponentSamplesFromRest P dimension cut N hN R)) =
        finiteUniformProbability
          (fun w : P2a.TrialScalar P.toPartiteShape cut dimension N → Bool =>
            A (e w)) := by
              have hs := by
                simpa [p3AllComponentSamplesFromRest, e] using hfull
              exact hs.trans
                (p3_finiteUniformProbability_fintype_irrel _ _ _)
    _ = finiteUniformProbability A :=
      p3_finiteUniformProbability_equiv e A

/-- Exact product law for simultaneous component-local events in every actual
packed trial. -/
theorem p3_actual_all_trial_component_event_product_law
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (E : ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      P3ComponentPairSample P dimension cut K → Prop)
    [∀ K, DecidablePred (E K)] :
    finiteUniformProbability
        (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
          ∀ i K, E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
      (∏ K : P2a.ActiveComponent P.toPartiteShape cut,
          finiteUniformProbability (E K)) ^ N := by
  classical
  let Xi := ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
    P3ComponentPairSample P dimension cut K
  let S : Xi → Prop := fun w => ∀ K, E K (w K)
  have hdecode :
      finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            ∀ i K,
              E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
        finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            ∀ i,
              S (p3AllComponentSamplesFromRest P dimension cut N hN R i)) := by
    rfl
  have hcomponent :
      finiteUniformProbability S =
        ∏ K : P2a.ActiveComponent P.toPartiteShape cut,
          finiteUniformProbability (E K) :=
    p3_finiteUniformProbability_dependent_all
      (fun K : P2a.ActiveComponent P.toPartiteShape cut =>
        P3ComponentPairSample P dimension cut K) E
  have htrial :
      finiteUniformProbability (fun w : Fin N → Xi => ∀ i, S (w i)) =
        ∏ _i : Fin N, finiteUniformProbability S := by
    have h := p3_finiteUniformProbability_dependent_all
      (fun _i : Fin N => Xi) (fun _i => S)
    exact (P1AD.finiteUniformProbability_decidable_irrel_explicit _ _ _).trans h
  calc
    finiteUniformProbability
        (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
          ∀ i K,
            E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
        finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            ∀ i,
              S (p3AllComponentSamplesFromRest P dimension cut N hN R i)) :=
      hdecode
    _ = finiteUniformProbability
          (fun w : Fin N → Xi => ∀ i, S (w i)) :=
      p3AllComponentSamplesFromRest_uniform_probability
        (P := P) (dimension := dimension) (cut := cut) (N := N) hN
        (A := fun w => ∀ i, S (w i))
    _ = ∏ _i : Fin N, finiteUniformProbability S := htrial
    _ = (∏ K : P2a.ActiveComponent P.toPartiteShape cut,
          finiteUniformProbability (E K)) ^ N := by
      rw [hcomponent]
      simp

/-- Public complement identity for the finite uniform probability. -/
theorem p3_finiteUniformProbability_compl
    {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (A : Omega → Prop) [DecidablePred A] :
    finiteUniformProbability (fun x => ¬ A x) =
      1 - finiteUniformProbability A := by
  classical
  have hpoint : ∀ x : Omega,
      (if ¬ A x then (1 : ℝ) else 0) =
        1 - (if A x then 1 else 0) := by
    intro x
    by_cases hx : A x <;> simp [hx]
  unfold finiteUniformProbability paperMean
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  simp
  have hcard : (Fintype.card Omega : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hcard]

/-- Exact probability that at least one packed trial succeeds simultaneously
for every active component. -/
theorem p3_actual_some_trial_all_component_event_probability
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (E : ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      P3ComponentPairSample P dimension cut K → Prop)
    [∀ K, DecidablePred (E K)] :
    finiteUniformProbability
        (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
          ∃ i, ∀ K,
            E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
      1 - (1 - (∏ K : P2a.ActiveComponent P.toPartiteShape cut,
          finiteUniformProbability (E K))) ^ N := by
  classical
  let Xi := ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
    P3ComponentPairSample P dimension cut K
  let S : Xi → Prop := fun w => ∀ K, E K (w K)
  have hdecode :
      finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            ∃ i, ∀ K,
              E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
        finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            ∃ i, S (p3AllComponentSamplesFromRest P dimension cut N hN R i)) := by
    rfl
  have hcomponent :
      finiteUniformProbability S =
        ∏ K : P2a.ActiveComponent P.toPartiteShape cut,
          finiteUniformProbability (E K) :=
    p3_finiteUniformProbability_dependent_all
      (fun K : P2a.ActiveComponent P.toPartiteShape cut =>
        P3ComponentPairSample P dimension cut K) E
  have hsome :
      finiteUniformProbability (fun w : Fin N → Xi => ∃ i, S (w i)) =
        1 - finiteUniformProbability (fun w : Fin N → Xi => ∀ i, ¬ S (w i)) := by
    calc
      finiteUniformProbability (fun w : Fin N → Xi => ∃ i, S (w i)) =
          finiteUniformProbability (fun w : Fin N → Xi => ¬ ∀ i, ¬ S (w i)) := by
        congr 1
        funext w
        simp
      _ = 1 - finiteUniformProbability
          (fun w : Fin N → Xi => ∀ i, ¬ S (w i)) :=
        p3_finiteUniformProbability_compl _
  calc
    finiteUniformProbability
        (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
          ∃ i, ∀ K,
            E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
        finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            ∃ i, S (p3AllComponentSamplesFromRest P dimension cut N hN R i)) :=
      hdecode
    _ = finiteUniformProbability (fun w : Fin N → Xi => ∃ i, S (w i)) :=
      p3AllComponentSamplesFromRest_uniform_probability
        (P := P) (dimension := dimension) (cut := cut) (N := N) hN
        (A := fun w => ∃ i, S (w i))
    _ = 1 - finiteUniformProbability
          (fun w : Fin N → Xi => ∀ i, ¬ S (w i)) := hsome
    _ = 1 - (1 - finiteUniformProbability S) ^ N := by
      rw [sync_all_fail_probability]
    _ = 1 - (1 - (∏ K : P2a.ActiveComponent P.toPartiteShape cut,
          finiteUniformProbability (E K))) ^ N := by
      rw [hcomponent]

/-- A lower bound on one whole-trial component product and a half-failure
estimate imply a half lower bound for actual synchronized success. -/
theorem p3_actual_some_trial_all_component_event_half
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (E : ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      P3ComponentPairSample P dimension cut K → Prop)
    [∀ K, DecidablePred (E K)]
    (rho : ℝ) (hrho0 : 0 ≤ rho)
    (hrho : rho ≤ ∏ K : P2a.ActiveComponent P.toPartiteShape cut,
      finiteUniformProbability (E K))
    (hfail : (1 - rho) ^ N ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤
      finiteUniformProbability
        (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
          ∃ i, ∀ K,
            E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) := by
  classical
  let p := ∏ K : P2a.ActiveComponent P.toPartiteShape cut,
    finiteUniformProbability (E K)
  have hp1 : p ≤ 1 := by
    let Xi := ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      P3ComponentPairSample P dimension cut K
    let S : Xi → Prop := fun w => ∀ K, E K (w K)
    have hcomponent : finiteUniformProbability S = p :=
      p3_finiteUniformProbability_dependent_all
        (fun K : P2a.ActiveComponent P.toPartiteShape cut =>
          P3ComponentPairSample P dimension cut K) E
    rw [← hcomponent]
    exact p3_finiteUniformProbability_le_one S
  have hbase0 : 0 ≤ 1 - p := by linarith
  have hbase : 1 - p ≤ 1 - rho := by
    linarith
  have hpow : (1 - p) ^ N ≤ (1 - rho) ^ N :=
    pow_le_pow_left₀ hbase0 hbase N
  rw [p3_actual_some_trial_all_component_event_probability]
  linarith

#print axioms p3ComponentBitsEquivP1Sample
#print axioms p3TrialBitsEquivAllComponentSamples
#print axioms p3AllComponentSamplesFromRest_apply
#print axioms p3AllComponentSamplesFromRest_uniform_probability
#print axioms p3_actual_all_trial_component_event_product_law
#print axioms p3_finiteUniformProbability_compl
#print axioms p3_actual_some_trial_all_component_event_probability
#print axioms p3_actual_some_trial_all_component_event_half

end GraphMatrixReplica
