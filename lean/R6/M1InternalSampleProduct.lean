import R6.P3ActualP1TrialBridge
import R6.C2ActualAssignmentSplit

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

abbrev RootComponentInternalAddress (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) :=
  Σ K : P2a.ActiveComponent P.toPartiteShape cut,
    Σ e : P1InternalEdge P cut K.1, P1InternalCoordinate P dimension cut K.1 e

def rootComponentInternalAddressMap (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (x : RootComponentInternalAddress P cut dimension) :
    P2a.InternalAddress (G := P.toPartiteShape) cut dimension :=
  ⟨⟨x.2.1.1, x.2.2⟩, ⟨x.1, x.2.1.2.1, x.2.1.2.2⟩⟩

/-- Every original internal primitive address has exactly one active owner;
its edge occurrence and both endpoint labels are preserved. -/
theorem rootComponentInternalAddressMap_bijective
    (P : PaperShape) (cut : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ) :
    Function.Bijective (rootComponentInternalAddressMap P cut dimension) := by
  constructor
  · rintro ⟨K, e, ab⟩ ⟨L, f, cd⟩ h
    have hef : e.1 = f.1 := congrArg (fun x => x.1.1) h
    have hK : K = L := P2a.activeComponent_eq_of_common_role K L e.2.1
      (by simpa only [hef, p1ComponentRoles] using f.2.1)
    subst L
    have he : e = f := Subtype.ext hef
    subst f
    have hab : ab = cd := by
      have hraw := congrArg Subtype.val h
      exact eq_of_heq (Sigma.mk.inj hraw).2
    subst cd
    rfl
  · intro x
    obtain ⟨K, hs, ht⟩ := x.2
    exact ⟨⟨K, ⟨x.1.1, hs, ht⟩, x.1.2⟩, rfl⟩

def rootComponentInternalAddressEquiv
    (P : PaperShape) (cut : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ) :
    RootComponentInternalAddress P cut dimension ≃
      P2a.InternalAddress (G := P.toPartiteShape) cut dimension :=
  Equiv.ofBijective (rootComponentInternalAddressMap P cut dimension)
    (rootComponentInternalAddressMap_bijective P cut dimension)

/-- Actual P1 internal arrays, read directly from the complete P2a internal cube. -/
def rootP1InternalSample (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (K : P2a.ActiveComponent P.toPartiteShape cut) : P1InternalSample P dimension cut K.1 :=
  fun e ab => I (rootComponentInternalAddressMap P cut dimension ⟨K, e, ab⟩)

/-- The complete internal cube is exactly the dependent family of P1 internal
samples, including components with no internal edge coordinates. -/
def rootInternalSampleEquiv (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) :
    P2a.InternalCube (G := P.toPartiteShape) cut dimension ≃
      (∀ K : P2a.ActiveComponent P.toPartiteShape cut, P1InternalSample P dimension cut K.1) :=
  ((Equiv.arrowCongr (rootComponentInternalAddressEquiv P cut dimension).symm
      (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun _ _ => Bool))).trans
      (Equiv.piCongrRight (fun _ => Equiv.piCurry (fun _ _ => Bool)))

@[simp] theorem rootInternalSampleEquiv_apply
    (P : PaperShape) (cut : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension) :
    rootInternalSampleEquiv P cut dimension I = rootP1InternalSample P cut dimension I := rfl

/-- Arbitrary full-family observables have exactly the dependent uniform law. -/
theorem root_internalSample_mean (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (H : (∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      P1InternalSample P dimension cut K.1) → ℝ) :
    paperMean (fun I : P2a.InternalCube (G := P.toPartiteShape) cut dimension =>
      H (rootP1InternalSample P cut dimension I)) = paperMean H := by
  exact paperMean_equiv (rootInternalSampleEquiv P cut dimension) H

/-- Joint events on the disjoint actual internal arrays factor exactly. -/
theorem root_internalSample_probability_product
    (P : PaperShape) (cut : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ)
    (E : ∀ K : P2a.ActiveComponent P.toPartiteShape cut, P1InternalSample P dimension cut K.1 → Prop) :
    finiteUniformProbability (fun I : P2a.InternalCube (G := P.toPartiteShape) cut dimension =>
      ∀ K, E K (rootP1InternalSample P cut dimension I K)) =
      ∏ K, finiteUniformProbability (E K) := by
  unfold finiteUniformProbability
  rw [root_internalSample_mean P cut dimension
    (fun x => if ∀ K, E K (x K) then (1 : ℝ) else 0)]
  simpa only [Fintype.prod_boole, P2a.paperMean, paperMean] using
    P2a.paperMean_piProduct (fun K x => if E K x then (1 : ℝ) else 0)

/-- The full internally-good event reads every actual internal array, not just
one quadratic statistic or a conditional average. -/
def rootInternalGood (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (n : ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension) : Prop :=
  ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
    P1AD.InternalGood P dimension cut K.1
      (p3DistinguishedBoundaryRole P cut K).1
      (p3DistinguishedBoundaryRole P cut K).2 n
      (rootP1InternalSample P cut dimension I K)

/-- The actual complete internally-good event has a positive graph-uniform
product lower bound supplied by the proved P1 A-D theorem. -/
theorem root_internalGood_uniform_graph
    (P : PaperShape) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ p : ℝ, 0 < p ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ (cut : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ) (n : ℕ), N ≤ n →
        (∀ K : P2a.ActiveComponent P.toPartiteShape cut,
          P1AD.Balanced P dimension cut K.1 a b n) →
        p ^ Fintype.card (P2a.ActiveComponent P.toPartiteShape cut) ≤
          finiteUniformProbability (rootInternalGood P cut dimension n) := by
  obtain ⟨p, pExt, cQ, CQ, cS, CS, N, hp, hpExt, hcQ, hCQ, hcS, hCS, hN, hP⟩ :=
    P1AD.p1_D_uniform_graph P a b ha hab
  refine ⟨p, hp, N, hN, ?_⟩
  intro cut dimension n hn hBalanced
  let E := fun K : P2a.ActiveComponent P.toPartiteShape cut =>
    P1AD.InternalGood P dimension cut K.1
      (p3DistinguishedBoundaryRole P cut K).1
      (p3DistinguishedBoundaryRole P cut K).2 n
  have hprob : finiteUniformProbability (rootInternalGood P cut dimension n) =
      ∏ K, finiteUniformProbability (E K) := by
    convert root_internalSample_probability_product P cut dimension E using 1 <;> congr!
  calc
    p ^ Fintype.card (P2a.ActiveComponent P.toPartiteShape cut) =
        ∏ _K : P2a.ActiveComponent P.toPartiteShape cut, p := by simp
    _ ≤ ∏ K, finiteUniformProbability (E K) := by
      apply Finset.prod_le_prod
      · intro K _
        exact hp.le
      · intro K _
        exact (hP cut K.1 K.2 (p3DistinguishedBoundaryRole P cut K).1
          (p3DistinguishedBoundaryRole P cut K).2 dimension n hn (hBalanced K)).1
    _ = _ := hprob.symm

#print axioms rootComponentInternalAddressMap_bijective
#print axioms rootInternalSampleEquiv
#print axioms root_internalSample_mean
#print axioms root_internalSample_probability_product
#print axioms root_internalGood_uniform_graph
end GraphMatrixReplica
