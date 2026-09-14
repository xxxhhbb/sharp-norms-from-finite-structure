import GraphMatrix.Probability.Synchronization.FromP1Component
import GraphMatrix.Probability.TrialLawIdentification

/-!
# identify the actual attachment coordinates with boundary roles

This file is the first graph-specific connector from the primitive conditional
rest cube to the P1/component tail.  It proves that P2a's attached roles are
exactly P1's cut-adjacent component roles, without changing the stored graph or
forgetting edge occurrences.
-/

set_option autoImplicit false
noncomputable section
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

/-- The attached-role subtype and the boundary-role subtype describe
the same graph roles.  The proof explicitly converts orientation-independent
edge joining into the two incidence statements used by P1. -/
def p2aAttachedRoleEquivP1Boundary
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P2a.AttachedRole (G := P.toPartiteShape) cut K ≃
      P1BoundaryRole P cut K.1 where
  toFun z := by
    refine ⟨z.1, (mem_p1BoundaryRoles_iff P cut K.1 z.1).2 ⟨z.2.1, ?_⟩⟩
    obtain ⟨u, hu, e, he⟩ := z.2.2
    refine ⟨u, hu, e, ?_⟩
    rcases he with he | he
    · exact ⟨Or.inl he.1, Or.inr he.2⟩
    · exact ⟨Or.inr he.2, Or.inl he.1⟩
  invFun z := by
    have hz := (mem_p1BoundaryRoles_iff P cut K.1 z.1).1 z.2
    refine ⟨z.1, hz.1, ?_⟩
    obtain ⟨u, hu, e, hze, hue⟩ := hz.2
    refine ⟨u, hu, e, ?_⟩
    have hzOut : z.1 ∉ cut := P2a.componentRole_not_mem_cut hz.1
    rcases hze with hzs | hzt <;> rcases hue with hus | hut
    · exfalso
      apply hzOut
      have hzu : z.1 = u := hzs.symm.trans hus
      simpa [hzu] using hu
    · exact Or.inl ⟨hzs, hut⟩
    · exact Or.inr ⟨hus, hzt⟩
    · exfalso
      apply hzOut
      have hzu : z.1 = u := hzt.symm.trans hut
      simpa [hzu] using hu
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext rfl

@[simp] theorem p2aAttachedRoleEquivP1Boundary_apply_val
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z : P2a.AttachedRole (G := P.toPartiteShape) cut K) :
    (p2aAttachedRoleEquivP1Boundary P cut K z).1 = z.1 := rfl

/-- A canonical distinguished boundary role for every active component.  This
is chosen once from the graph and therefore precedes dimensions, internal
arrays, trials, and thresholds. -/
def p3DistinguishedAttachedRole
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P2a.AttachedRole (G := P.toPartiteShape) cut K :=
  Classical.choice (P2a.attachedRole_nonempty (G := P.toPartiteShape)
    (cut := cut) K)

def p3DistinguishedBoundaryRole
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P1BoundaryRole P cut K.1 :=
  p2aAttachedRoleEquivP1Boundary P cut K
    (p3DistinguishedAttachedRole P cut K)

@[simp] theorem p3DistinguishedBoundaryRole_val
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    (p3DistinguishedBoundaryRole P cut K).1 =
      (p3DistinguishedAttachedRole P cut K).1 := rfl

/-- Decode the product of every primitive crossing block as one Boolean
Rademacher coordinate. -/
def p3TrialScalarBit
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole G cut, N ≤ dimension u.1)
    (g : P2a.TrialScalar G cut dimension N)
    (R : P2a.RestCube cut dimension) : Bool :=
  if P2a.trialScalarEta dimension N hN g R = -1 then true else false

theorem p3TrialScalarEta_eq_one_or_neg_one
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole G cut, N ≤ dimension u.1)
    (g : P2a.TrialScalar G cut dimension N)
    (R : P2a.RestCube cut dimension) :
    P2a.trialScalarEta dimension N hN g R = 1 ∨
      P2a.trialScalarEta dimension N hN g R = -1 := by
  simpa [P2a.trialScalarEta, P2a.blockSign] using
    (P2a.blockSign_eq_one_or_neg_one
      (fun a : {a : P2a.RestAddress cut dimension //
          a ∈ P2a.trialScalarRestSupport dimension N hN g} => R a.1))

@[simp] theorem rademacherSign_p3TrialScalarBit
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole G cut, N ≤ dimension u.1)
    (g : P2a.TrialScalar G cut dimension N)
    (R : P2a.RestCube cut dimension) :
    (rademacherSign (p3TrialScalarBit dimension N hN g R) : ℝ) =
      P2a.trialScalarEta dimension N hN g R := by
  rcases p3TrialScalarEta_eq_one_or_neg_one dimension N hN g R with h | h
  · norm_num [p3TrialScalarBit, h, rademacherSign]
  · norm_num [p3TrialScalarBit, h, rademacherSign]

theorem rademacherSign_bool_injective :
    Function.Injective (fun b : Bool => (rademacherSign b : ℝ)) := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · norm_num [rademacherSign] at hab
  · norm_num [rademacherSign] at hab
  · rfl

/-- Every prescribed Boolean pattern of all actual eta coordinates has the
same mass as under the uniform Boolean cube.  This is stronger than marginal
independence and is the point-mass form needed for arbitrary tail events. -/
theorem conditional_trialScalarBit_pattern_mass
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole G cut, N ≤ dimension u.1)
    (pattern : P2a.TrialScalar G cut dimension N → Bool) :
    finiteUniformProbability (fun R : P2a.RestCube cut dimension =>
      ∀ g, p3TrialScalarBit dimension N hN g R = pattern g) =
    ((2 : ℝ)⁻¹) ^
      Fintype.card (P2a.TrialScalar G cut dimension N) := by
  classical
  let q : P2a.TrialScalar G cut dimension N → ℝ :=
    fun g => (rademacherSign (pattern g) : ℝ)
  have hq (g : P2a.TrialScalar G cut dimension N) :
      q g = 1 ∨ q g = -1 := by
    cases h : pattern g <;> norm_num [q, h, rademacherSign]
  have hpoint (R : P2a.RestCube cut dimension) :
      (if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
        then (1 : ℝ) else 0) =
      ∏ g : P2a.TrialScalar G cut dimension N,
        P2a.signPointIndicator (q g)
          (P2a.trialScalarEta dimension N hN g R) := by
    by_cases hpat : ∀ g, p3TrialScalarBit dimension N hN g R = pattern g
    · rw [if_pos hpat]
      symm
      apply Finset.prod_eq_one
      intro g _hg
      rw [← rademacherSign_p3TrialScalarBit dimension N hN g R]
      simp [P2a.signPointIndicator, q, hpat g]
    · rw [if_neg hpat]
      obtain ⟨g, hg⟩ := not_forall.mp hpat
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ g)
      have hne : q g ≠ P2a.trialScalarEta dimension N hN g R := by
        intro heq
        apply hg
        apply rademacherSign_bool_injective
        exact (rademacherSign_p3TrialScalarBit dimension N hN g R).trans heq.symm
      simp [P2a.signPointIndicator, hne.symm]
  calc
    finiteUniformProbability (fun R : P2a.RestCube cut dimension =>
        ∀ g, p3TrialScalarBit dimension N hN g R = pattern g) =
      paperMean (fun R : P2a.RestCube cut dimension =>
        ∏ g : P2a.TrialScalar G cut dimension N,
          P2a.signPointIndicator (q g)
            (P2a.trialScalarEta dimension N hN g R)) := by
        unfold finiteUniformProbability
        apply congrArg paperMean
        funext R
        by_cases hp : ∀ g, p3TrialScalarBit dimension N hN g R = pattern g
        · simpa [hp] using hpoint R
        · simpa [hp] using hpoint R
    _ = _ := P2a.conditional_eta_pattern_mass dimension N hN q hq

noncomputable local instance p3TrialScalarBoolCubeFintype
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ) :
    Fintype (P2a.TrialScalar G cut dimension N → Bool) :=
  Fintype.ofFinite _

/-- The complete decoded eta family is uniform for every observable, not only
for products of coordinate observables.  The proof partitions the rest cube by
all Boolean patterns and uses the exact point mass above. -/
theorem conditional_trialScalarBit_uniform_mean
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole G cut, N ≤ dimension u.1)
    (H : (P2a.TrialScalar G cut dimension N → Bool) → ℝ) :
    paperMean (fun R : P2a.RestCube cut dimension =>
      H (fun g => p3TrialScalarBit dimension N hN g R)) =
    paperMean H := by
  classical
  let mass : ℝ := ((2 : ℝ)⁻¹) ^
    Fintype.card (P2a.TrialScalar G cut dimension N)
  have hdecomp (R : P2a.RestCube cut dimension) :
      H (fun g => p3TrialScalarBit dimension N hN g R) =
      ∑ pattern : P2a.TrialScalar G cut dimension N → Bool,
        if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
        then H pattern else 0 := by
    classical
    let actual : P2a.TrialScalar G cut dimension N → Bool :=
      fun g => p3TrialScalarBit dimension N hN g R
    symm
    change (∑ pattern,
      if (∀ g, actual g = pattern g) then H pattern else 0) = H actual
    rw [Finset.sum_eq_single actual]
    · simp
    · intro pattern _hmem hne
      have hnot : ¬∀ g, actual g = pattern g := by
        intro hall
        apply hne
        exact funext fun g => (hall g).symm
      simp [hnot]
    · simp
  have hfiber
      (pattern : P2a.TrialScalar G cut dimension N → Bool) :
      paperMean (fun R : P2a.RestCube cut dimension =>
        if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
        then H pattern else 0) = H pattern * mass := by
    have hpoint (R : P2a.RestCube cut dimension) :
        (if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
          then H pattern else 0) =
        H pattern *
          (if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
            then (1 : ℝ) else 0) := by
      by_cases hp : ∀ g, p3TrialScalarBit dimension N hN g R = pattern g <;>
        simp [hp]
    calc
      paperMean (fun R : P2a.RestCube cut dimension =>
          if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
          then H pattern else 0) =
        paperMean (fun R : P2a.RestCube cut dimension =>
          H pattern *
            (if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
              then (1 : ℝ) else 0)) := by
            apply congrArg paperMean
            funext R
            exact hpoint R
      _ = H pattern * finiteUniformProbability
          (fun R : P2a.RestCube cut dimension =>
            ∀ g, p3TrialScalarBit dimension N hN g R = pattern g) := by
            unfold finiteUniformProbability paperMean
            rw [← Finset.mul_sum]
            ring
      _ = H pattern * mass := by
            rw [conditional_trialScalarBit_pattern_mass dimension N hN pattern]
  have hcard : Fintype.card
      (P2a.TrialScalar G cut dimension N → Bool) =
      2 ^ Fintype.card (P2a.TrialScalar G cut dimension N) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun]
    simp [Nat.card_eq_fintype_card]
  have hmass : mass =
      (Fintype.card
        (P2a.TrialScalar G cut dimension N → Bool) : ℝ)⁻¹ := by
    rw [hcard]
    norm_num [mass, Nat.cast_pow, inv_pow]
  calc
    paperMean (fun R : P2a.RestCube cut dimension =>
        H (fun g => p3TrialScalarBit dimension N hN g R)) =
      paperMean (fun R : P2a.RestCube cut dimension =>
        ∑ pattern : P2a.TrialScalar G cut dimension N → Bool,
          if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
          then H pattern else 0) := by
            apply congrArg paperMean
            funext R
            exact hdecomp R
    _ = ∑ pattern : P2a.TrialScalar G cut dimension N → Bool,
        paperMean (fun R : P2a.RestCube cut dimension =>
          if (∀ g, p3TrialScalarBit dimension N hN g R = pattern g)
          then H pattern else 0) := paperMean_sum _
    _ = ∑ pattern : P2a.TrialScalar G cut dimension N → Bool,
        H pattern * mass := by
          apply Finset.sum_congr rfl
          intro pattern _hpattern
          exact hfiber pattern
    _ = mass * ∑ pattern : P2a.TrialScalar G cut dimension N → Bool,
        H pattern := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro pattern _hpattern
          ring
    _ = paperMean H := by
      unfold paperMean
      rw [hmass]

theorem conditional_trialScalarBit_uniform_probability
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole G cut, N ≤ dimension u.1)
    (A : (P2a.TrialScalar G cut dimension N → Bool) → Prop)
    [DecidablePred A] :
    finiteUniformProbability (fun R : P2a.RestCube cut dimension =>
      A (fun g => p3TrialScalarBit dimension N hN g R)) =
    finiteUniformProbability A := by
  classical
  have h := conditional_trialScalarBit_uniform_mean dimension N hN
    (fun w => if A w then (1 : ℝ) else 0)
  unfold finiteUniformProbability
  exact h

/-- A function of a selected coordinate subcube has the same normalized mean
whether the unused Boolean coordinates are present or removed. -/
theorem paperMean_boolCube_restrict
    {α : Type} [Fintype α] (Q : α → Prop) [DecidablePred Q]
    (H : ({a : α // Q a} → Bool) → ℝ) :
    paperMean (fun w : α → Bool => H (fun a => w a.1)) = paperMean H := by
  classical
  let e := P2a.splitByPredicateEquiv Q (β := Bool)
  calc
    paperMean (fun w : α → Bool => H (fun a => w a.1)) =
      paperMean (fun x :
          ({a : α // Q a} → Bool) × ({a : α // ¬Q a} → Bool) =>
        H x.1) := by
          simpa [e, P2a.splitByPredicateEquiv] using
            (paperMean_equiv e (fun x :
              ({a : α // Q a} → Bool) × ({a : α // ¬Q a} → Bool) =>
              H x.1))
    _ = paperMean H :=
      P2a.paperMean_prod_fst_boolCube
        (ρ := {a : α // ¬Q a}) H

/-- Scalar indices belonging to one fixed separator tuple and one fixed active
component. -/
abbrev P3SelectedTrialComponentScalar
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :=
  {g : P2a.TrialScalar P.toPartiteShape cut dimension N //
    g.1 = i ∧ g.2.1 = K}


/-- P1's effective second-layer sample for one actual separator tuple and one
active component, read from the corresponding crossing blocks. -/
def p3TrialSecondSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) :
    P1SecondSample P dimension cut K.1
      (p3DistinguishedBoundaryRole P cut K).1 :=
  fun v j =>
    p3TrialScalarBit dimension N hN
      ⟨i, K,
        (p2aAttachedRoleEquivP1Boundary P cut K).symm
          ⟨v.1, v.2.1⟩,
        j⟩ R

/-- The distinguished boundary-role signs for the same tuple and component. -/
def p3TrialDistinguishedSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) :
    Fin (dimension (p3DistinguishedBoundaryRole P cut K).1) → Bool :=
  fun j =>
    p3TrialScalarBit dimension N hN
      ⟨i, K, p3DistinguishedAttachedRole P cut K, j⟩ R

/-- The actual conditional sample consumed by the component tail. -/
def p3TrialComponentSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) :=
  (p3TrialSecondSample P dimension cut N hN i K R,
    p3TrialDistinguishedSample P dimension cut N hN i K R)


end GraphMatrixReplica
