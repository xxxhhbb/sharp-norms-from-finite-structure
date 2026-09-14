import R6.P3ActualP1TrialBridge

/-!
# P3: one actual trial/component has the P1 product sample law
-/

set_option autoImplicit false
noncomputable section
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

theorem p3_finiteUniformProbability_fintype_irrel
    {Omega : Type} (i j : Fintype Omega)
    (A : Omega → Prop) [DecidablePred A] :
    @finiteUniformProbability Omega i A inferInstance =
      @finiteUniformProbability Omega j A inferInstance := by
  unfold finiteUniformProbability
  exact P1AD.paperMean_fintype_irrel i j _

/-- Removing the fixed trial and component fields from a selected P2a scalar
is an exact equivalence, including dependent role-label types. -/
def p3SelectedScalarEquivAttachedLabel
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P3SelectedTrialComponentScalar P dimension cut N i K ≃
      (Σ z : P2a.AttachedRole (G := P.toPartiteShape) cut K,
        Fin (dimension z.1)) where
  toFun g := by
    rcases g with ⟨⟨i', K', z, j⟩, hi, hK⟩
    dsimp at hi hK
    subst i'
    subst K'
    exact ⟨z, j⟩
  invFun zj := ⟨⟨i, K, zj.1, zj.2⟩, rfl, rfl⟩
  left_inv g := by
    rcases g with ⟨⟨i', K', z, j⟩, hi, hK⟩
    dsimp at hi hK
    subst i'
    subst K'
    rfl
  right_inv zj := by
    rcases zj with ⟨z, j⟩
    rfl


def p3BoundaryRestSubtypeEquiv
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    {b : P1BoundaryRole P cut K.1 //
        b ≠ p3DistinguishedBoundaryRole P cut K} ≃
      P1BoundaryRestRole P cut K.1
        (p3DistinguishedBoundaryRole P cut K).1 where
  toFun b := ⟨b.1.1, b.1.2, fun h => b.2 (Subtype.ext h)⟩
  invFun v := ⟨⟨v.1, v.2.1⟩,
    fun h => v.2.2 (congrArg Subtype.val h)⟩
  left_inv b := by rcases b with ⟨⟨b, hb⟩, hne⟩; rfl
  right_inv v := by rcases v with ⟨v, hv, hne⟩; rfl

def p3BoundaryEqLabelEquiv
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    (Σ b : {b : P1BoundaryRole P cut K.1 //
        ¬ b ≠ p3DistinguishedBoundaryRole P cut K},
      Fin (dimension b.1.1)) ≃
      Fin (dimension (p3DistinguishedBoundaryRole P cut K).1) where
  toFun bj := by
    have hb : bj.1.1 = p3DistinguishedBoundaryRole P cut K :=
      Classical.not_not.mp bj.1.2
    exact Fin.cast (congrArg (fun b : P1BoundaryRole P cut K.1 =>
      dimension b.1) hb) bj.2
  invFun j := ⟨⟨p3DistinguishedBoundaryRole P cut K,
    by simp⟩, j⟩
  left_inv bj := by
    rcases bj with ⟨⟨b, hb⟩, j⟩
    have h : b = p3DistinguishedBoundaryRole P cut K :=
      Classical.not_not.mp hb
    subst b
    rfl
  right_inv j := rfl

def p3AttachedLabelEquivBoundaryLabelCoord
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    (Σ z : P2a.AttachedRole (G := P.toPartiteShape) cut K,
      Fin (dimension z.1)) ≃
    (Σ b : P1BoundaryRole P cut K.1, Fin (dimension b.1)) :=
  Equiv.sigmaCongr (p2aAttachedRoleEquivP1Boundary P cut K)
    (fun _ => Equiv.refl _)

/-- Generic `sumCompl` and sigma-distribution split the full boundary label
coordinate family at the distinguished boundary role. -/
def p3BoundaryLabelCoordSplitEquiv
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    (Σ b : P1BoundaryRole P cut K.1, Fin (dimension b.1)) ≃
    Sum
      (Σ v : P1BoundaryRestRole P cut K.1
          (p3DistinguishedBoundaryRole P cut K).1,
        Fin (dimension v.1))
      (Fin (dimension (p3DistinguishedBoundaryRole P cut K).1)) := by
  let z0 := p3DistinguishedBoundaryRole P cut K
  let Q : P1BoundaryRole P cut K.1 → Prop := fun b => b ≠ z0
  let eBase := Equiv.sumCompl Q
  let eSigma := Equiv.sigmaCongrLeft
    (β := fun b : P1BoundaryRole P cut K.1 => Fin (dimension b.1)) eBase
  let eDistrib := Equiv.sumSigmaDistrib
    (fun s : {b : P1BoundaryRole P cut K.1 // Q b} ⊕
        {b : P1BoundaryRole P cut K.1 // ¬Q b} =>
      Fin (dimension (eBase s).1))
  let eRest :
      (Σ a : {b : P1BoundaryRole P cut K.1 // Q b},
        Fin (dimension a.1.1)) ≃
      (Σ v : P1BoundaryRestRole P cut K.1
          (p3DistinguishedBoundaryRole P cut K).1,
        Fin (dimension v.1)) :=
    Equiv.sigmaCongr (p3BoundaryRestSubtypeEquiv P cut K)
      (fun _ => Equiv.refl _)
  let eEq :
      (Σ b : {b : P1BoundaryRole P cut K.1 // ¬Q b},
        Fin (dimension b.1.1)) ≃
      Fin (dimension (p3DistinguishedBoundaryRole P cut K).1) :=
    p3BoundaryEqLabelEquiv P dimension cut K
  exact eSigma.symm |>.trans eDistrib |>.trans (Equiv.sumCongr eRest eEq)

def p3AttachedLabelEquivComponentCoord
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :=
  (p3AttachedLabelEquivBoundaryLabelCoord P dimension cut K).trans
    (p3BoundaryLabelCoordSplitEquiv P dimension cut K)

def p3SelectedScalarEquivComponentCoord
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :=
  (p3SelectedScalarEquivAttachedLabel P dimension cut N i K).trans
    (p3AttachedLabelEquivComponentCoord P dimension cut K)

/-- Reindex the selected Boolean scalar family as exactly the P1 pair sample. -/
def p3SelectedBitsEquivP1Sample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    (P3SelectedTrialComponentScalar P dimension cut N i K → Bool) ≃
      (P1SecondSample P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1 ×
        (Fin (dimension (p3DistinguishedBoundaryRole P cut K).1) → Bool)) :=
  (P2a.reindexFunctionEquiv
      (p3SelectedScalarEquivComponentCoord P dimension cut N i K).symm).trans
    P2a.sumSigmaFunctionEquiv

/-- The P1 pair sample obtained from the actual conditional rest cube through
the full P2a eta family and the natural selected-coordinate equivalence. -/
def p3ComponentSampleFromRest
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) :=
  p3SelectedBitsEquivP1Sample P dimension cut N i K
    (fun g => p3TrialScalarBit (G := P.toPartiteShape) (cut := cut)
      dimension N hN g.1 R)

/-- Exact arbitrary-event law for one actual trial and component. -/
theorem p3ComponentSampleFromRest_uniform_probability
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (A : (P1SecondSample P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1 ×
        (Fin (dimension (p3DistinguishedBoundaryRole P cut K).1) → Bool)) → Prop)
    [DecidablePred A] :
    finiteUniformProbability (fun R :
        P2a.RestCube (G := P.toPartiteShape) cut dimension =>
      A (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
    finiteUniformProbability A := by
  classical
  letI : Fintype
      (P2a.TrialScalar P.toPartiteShape cut dimension N → Bool) :=
    p3TrialScalarBoolCubeFintype (G := P.toPartiteShape) (cut := cut)
      dimension N
  let Q : P2a.TrialScalar P.toPartiteShape cut dimension N → Prop :=
    fun g => g.1 = i ∧ g.2.1 = K
  let e := p3SelectedBitsEquivP1Sample P dimension cut N i K
  letI : Fintype
      ({g : P2a.TrialScalar P.toPartiteShape cut dimension N // Q g} → Bool) :=
    Fintype.ofFinite _
  have hfull := conditional_trialScalarBit_uniform_probability
    (G := P.toPartiteShape) (cut := cut) dimension N hN
    (fun w => A (e (fun g : {g // Q g} => w g.1)))
  have hrestrict :
      finiteUniformProbability
          (fun w : P2a.TrialScalar P.toPartiteShape cut dimension N → Bool =>
            A (e (fun g : {g // Q g} => w g.1))) =
        finiteUniformProbability
          (fun w : {g : P2a.TrialScalar P.toPartiteShape cut dimension N // Q g} → Bool =>
            A (e w)) := by
    unfold finiteUniformProbability
    have hcore := paperMean_boolCube_restrict Q
      (fun w => if A (e w) then (1 : ℝ) else 0)
    exact (P1AD.paperMean_fintype_irrel _ _ _).trans
      (hcore.trans (P1AD.paperMean_fintype_irrel _ _ _))
  calc
    finiteUniformProbability (fun R :
        P2a.RestCube (G := P.toPartiteShape) cut dimension =>
      A (p3ComponentSampleFromRest P dimension cut N hN i K R)) =
      finiteUniformProbability
        (fun w : P2a.TrialScalar P.toPartiteShape cut dimension N → Bool =>
          A (e (fun g : {g // Q g} => w g.1))) := by
            have hs := by
              simpa [p3ComponentSampleFromRest, e, Q] using hfull
            exact hs.trans
              (p3_finiteUniformProbability_fintype_irrel _ _ _)
    _ = finiteUniformProbability
        (fun w : P3SelectedTrialComponentScalar P dimension cut N i K → Bool =>
          A (e w)) := by simpa [Q] using hrestrict
    _ = finiteUniformProbability A :=
      p3_finiteUniformProbability_equiv e A

/-- The P1 one-component tail now holds on the actual P2a conditional rest
cube for every packed separator trial. -/
theorem p3_actual_component_tail_uniform_graph
    (P : PaperShape) (a b epsTilt : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hepsTilt : 0 < epsTilt) :
    ∃ pExt cS CS : ℝ, ∃ n0 : ℕ,
      0 < pExt ∧ 0 < cS ∧ 0 < CS ∧ 1 ≤ n0 ∧
      ∀ (cut : Finset (Fin P.roles))
        (K : P2a.ActiveComponent P.toPartiteShape cut)
        (dimension : Fin P.roles → ℕ) (n : ℕ), n0 ≤ n →
        P1AD.Balanced P dimension cut K.1 a b n →
        ∀ epsInternal : P1InternalSample P dimension cut K.1,
          P1AD.InternalGood P dimension cut K.1
            (p3DistinguishedBoundaryRole P cut K).1
            (p3DistinguishedBoundaryRole P cut K).2 n epsInternal →
          ∀ (N : ℕ)
            (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
              N ≤ dimension u.1) (i : Fin N),
          let k := P1AD.roleCount P cut K.1
          let t := epsTilt * (n : ℝ) ^ ((k : ℝ) / 2) *
            Real.sqrt (Real.log (n : ℝ))
          pExt * ((1 / 2 : ℝ) *
              Real.exp (-(96 * epsTilt ^ 2 * Real.log (n : ℝ) / cS))) ≤
            finiteUniformProbability
              (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
                t ≤ |WeightedSignTilt.weightedSum
                  (fun j => p1Z P dimension cut K.1
                    (p3DistinguishedBoundaryRole P cut K).1
                    (p3DistinguishedBoundaryRole P cut K).2
                    epsInternal
                    (p3ComponentSampleFromRest P dimension cut N hN i K R).1 j)
                  (p3ComponentSampleFromRest P dimension cut N hN i K R).2|) := by
  classical
  obtain ⟨pExt, cS, CS, n0, hpExt, hcS, hCS, hn0, htail⟩ :=
    p3_component_tail_uniform_graph P a b epsTilt ha hab hepsTilt
  refine ⟨pExt, cS, CS, n0, hpExt, hcS, hCS, hn0, ?_⟩
  intro cut K dimension n hn hBalanced epsInternal hInternal N hN i
  have hbase := htail cut K.1 K.2
    (p3DistinguishedBoundaryRole P cut K).1
    (p3DistinguishedBoundaryRole P cut K).2
    dimension n hn hBalanced epsInternal hInternal
  let k := P1AD.roleCount P cut K.1
  let t := epsTilt * (n : ℝ) ^ ((k : ℝ) / 2) *
    Real.sqrt (Real.log (n : ℝ))
  let A := fun x : P1SecondSample P dimension cut K.1
        (p3DistinguishedBoundaryRole P cut K).1 ×
      (Fin (dimension (p3DistinguishedBoundaryRole P cut K).1) → Bool) =>
    t ≤ |WeightedSignTilt.weightedSum
      (fun j => p1Z P dimension cut K.1
        (p3DistinguishedBoundaryRole P cut K).1
        (p3DistinguishedBoundaryRole P cut K).2 epsInternal x.1 j) x.2|
  have hlaw := p3ComponentSampleFromRest_uniform_probability
    P dimension cut N hN i K A
  calc
    pExt * ((1 / 2 : ℝ) *
        Real.exp (-(96 * epsTilt ^ 2 * Real.log (n : ℝ) / cS))) ≤
        finiteUniformProbability A := by
      simpa [A, t, k] using hbase
    _ = finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            A (p3ComponentSampleFromRest P dimension cut N hN i K R)) := hlaw.symm
    _ = finiteUniformProbability
          (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
            epsTilt * (n : ℝ) ^ ((P1AD.roleCount P cut K.1 : ℝ) / 2) *
                Real.sqrt (Real.log (n : ℝ)) ≤
              |WeightedSignTilt.weightedSum
                (fun j => p1Z P dimension cut K.1
                  (p3DistinguishedBoundaryRole P cut K).1
                  (p3DistinguishedBoundaryRole P cut K).2
                  epsInternal
                  (p3ComponentSampleFromRest P dimension cut N hN i K R).1 j)
                (p3ComponentSampleFromRest P dimension cut N hN i K R).2|) := by
      rfl

#print axioms p3SelectedScalarEquivAttachedLabel
#print axioms p3BoundaryRestSubtypeEquiv
#print axioms p3BoundaryEqLabelEquiv
#print axioms p3BoundaryLabelCoordSplitEquiv
#print axioms p3SelectedScalarEquivComponentCoord
#print axioms p3ComponentSampleFromRest_uniform_probability
#print axioms p3_actual_component_tail_uniform_graph

end GraphMatrixReplica
