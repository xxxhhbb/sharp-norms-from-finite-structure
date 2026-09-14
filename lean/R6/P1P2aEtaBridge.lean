import R6.P1P2aP3ActualLawBridge

/-!
# P1/P2a primitive eta identification

This module identifies P1's crossing-edge product with P2a's actual rest-cube
eta coordinate.  All maps retain the edge occurrence, endpoint orientation, and
typed labels.  No probabilistic or pointwise equality assumption is added.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

/-- A P2a attached role is exactly a member of P1's boundary-role finset for
the underlying active component. -/
theorem p2aAttachedRole_mem_p1BoundaryRoles
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z : P2a.AttachedRole (G := P.toPartiteShape) cut K) :
    z.1 ∈ p1BoundaryRoles P cut K.1 := by
  apply (mem_p1BoundaryRoles_iff P cut K.1 z.1).2
  refine ⟨z.2.1, ?_⟩
  obtain ⟨u, hu, e, he⟩ := z.2.2
  refine ⟨u, hu, e, ?_⟩
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨Or.inl hs, Or.inr ht⟩
  · exact ⟨Or.inr ht, Or.inl hs⟩

/-- P1 and P2a retain the same crossing edge occurrence; only their record
presentation differs. -/
def p1CrossingEquivP2aOccurrence
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z : P2a.AttachedRole (G := P.toPartiteShape) cut K) :
    P1CrossingEdgeAt P cut z.1 ≃
      P2a.CrossingOccurrence (G := P.toPartiteShape) cut z where
  toFun a := ⟨(a.edge, ⟨a.cutRole, a.cutRole_mem⟩), a.oriented⟩
  invFun c := ⟨c.1.1, c.1.2.1, c.1.2.2, c.2⟩
  left_inv a := by cases a; rfl
  right_inv c := by rcases c with ⟨⟨e, u⟩, h⟩; cases u; rfl

@[simp] theorem p1CrossingEquivP2aOccurrence_apply
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z : P2a.AttachedRole (G := P.toPartiteShape) cut K)
    (a : P1CrossingEdgeAt P cut z.1) :
    p1CrossingEquivP2aOccurrence P cut K z a =
      ⟨(a.edge, ⟨a.cutRole, a.cutRole_mem⟩), a.oriented⟩ := rfl

/-- The two presentations compute the identical typed primitive address. -/
theorem p1CrossingCoordinate_eq_p2a
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z : P2a.AttachedRole (G := P.toPartiteShape) cut K)
    (a : P1CrossingEdgeAt P cut z.1)
    (j : Fin (dimension z.1))
    (tau : P1CutLabel P dimension cut) :
    (⟨a.edge, p1CrossingCoordinate P dimension cut z.1 a j tau⟩ :
        P2a.PrimitiveAddress (G := P.toPartiteShape) dimension) =
      P2a.crossingPrimitiveAddress dimension
        (p1CrossingEquivP2aOccurrence P cut K z a) j
        (tau ⟨a.cutRole, a.cutRole_mem⟩) := by
  rfl

/-- The injective occurrence address parametrization is equivalent to the
support subtype used by `trialScalarEta`. -/
def p2aOccurrenceEquivRestSupport
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole G cut, N ≤ dimension u.1)
    (g : P2a.TrialScalar G cut dimension N) :
    P2a.CrossingOccurrence (G := G) cut g.2.2.1 ≃
      {a : P2a.RestAddress cut dimension //
        a ∈ P2a.trialScalarRestSupport dimension N hN g} :=
  Equiv.ofBijective
    (fun c => ⟨P2a.trialScalarRestAddress dimension N hN g c, by
      simp [P2a.trialScalarRestSupport]⟩)
    ⟨by
      intro c d h
      apply P2a.trialScalarAddress_injective dimension N hN g
      exact congrArg (fun a => a.1.1) h,
     by
      intro a
      rcases Finset.mem_image.mp a.2 with ⟨c, -, hc⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      exact hc⟩

/-- Restrict a full typed edge-array sample to P2a's conditional rest cube. -/
def p1TypedSampleRest
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (eps : P1TypedSample P dimension) :
    P2a.RestCube (G := P.toPartiteShape) cut dimension :=
  fun a => eps a.1.1 a.1.2

/-- P2a's diagonal separator labeling, exposed at P1's cut-label type. -/
def p2aSeparatorTrialAsP1
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (i : Fin N) : P1CutLabel P dimension cut :=
  fun u => P2a.separatorTrial (G := P.toPartiteShape) dimension N hN i u

/-- Exact pointwise identification of one P2a eta scalar and P1's primitive
crossing product at the diagonal separator trial. -/
theorem p2a_trialScalarEta_eq_p1EtaSignZ
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (eps : P1TypedSample P dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z : P2a.AttachedRole (G := P.toPartiteShape) cut K)
    (j : Fin (dimension z.1)) :
    P2a.trialScalarEta dimension N hN ⟨i, ⟨K, ⟨z, j⟩⟩⟩
        (p1TypedSampleRest P dimension cut eps) =
      (p1EtaSignZ P dimension cut z.1 eps
        (p2aSeparatorTrialAsP1 P dimension cut N hN i) j : ℝ) := by
  classical
  letI : Fintype (P1CrossingEdgeAt P cut z.1) := by
    apply Fintype.ofInjective (fun a => (a.edge, a.cutRole))
    intro a b h
    cases a
    cases b
    cases h
    rfl
  let e := (p1CrossingEquivP2aOccurrence P cut K z).trans
    (p2aOccurrenceEquivRestSupport
      (G := P.toPartiteShape) (cut := cut) dimension N hN
      (⟨i, ⟨K, ⟨z, j⟩⟩⟩ :
        P2a.TrialScalar P.toPartiteShape cut dimension N))
  unfold P2a.trialScalarEta p1EtaSignZ
  rw [← Equiv.prod_comp e]
  push_cast
  apply Finset.prod_congr rfl
  intro a _ha
  change (rademacherSign
      (eps (e a).1.1.1 (e a).1.1.2) : ℝ) =
    (rademacherSign
      (eps a.edge
        (p1CrossingCoordinate P dimension cut z.1 a j
          (p2aSeparatorTrialAsP1 P dimension cut N hN i))) : ℤ)
  rw [show (e a).1.1 =
      ⟨a.edge, p1CrossingCoordinate P dimension cut z.1 a j
        (p2aSeparatorTrialAsP1 P dimension cut N hN i)⟩ by
    exact (p1CrossingCoordinate_eq_p2a P dimension cut K z a j
      (p2aSeparatorTrialAsP1 P dimension cut N hN i)).symm]

/-- Retype a P1 boundary role as P2a's occurrence-aware attached role. -/
def p1BoundaryRoleAsP2aAttached
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (v : P1BoundaryRole P cut K.1) :
    P2a.AttachedRole (G := P.toPartiteShape) cut K := by
  refine ⟨v.1, ?_, ?_⟩
  · exact (mem_p1BoundaryRoles_iff P cut K.1 v.1).1 v.2 |>.1
  · obtain ⟨u, hu, e, hv, hU⟩ :=
      (mem_p1BoundaryRoles_iff P cut K.1 v.1).1 v.2 |>.2
    refine ⟨u, hu, e, ?_⟩
    rcases hv with hsz | htz <;> rcases hU with hsu | htu
    · exfalso
      have hzu : v.1 = u := hsz.symm.trans hsu
      have hvNot : v.1 ∉ cut := by
        exact P2a.componentRole_not_mem_cut
          ((mem_p1BoundaryRoles_iff P cut K.1 v.1).1 v.2 |>.1)
      exact hvNot (hzu ▸ hu)
    · exact Or.inl ⟨hsz, htu⟩
    · exact Or.inr ⟨hsu, htz⟩
    · exfalso
      have hzu : v.1 = u := htz.symm.trans htu
      have hvNot : v.1 ∉ cut := by
        exact P2a.componentRole_not_mem_cut
          ((mem_p1BoundaryRoles_iff P cut K.1 v.1).1 v.2 |>.1)
      exact hvNot (hzu ▸ hu)

/-- Every actual eta coordinate takes one of the two Rademacher values. -/
theorem p2a_trialScalarEta_eq_one_or_neg_one
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

/-- The actual P2a eta vectors, encoded at P1's Bool-valued effective
second-layer sample type.  `true` represents the sign `-1`. -/
def p2aEtaAsP1SecondSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z0 : Fin P.roles) : P1SecondSample P dimension cut K.1 z0 :=
  fun v j => decide
    (P2a.trialScalarEta dimension N hN
      ⟨i, ⟨K, ⟨p1BoundaryRoleAsP2aAttached P cut K ⟨v.1, v.2.1⟩, j⟩⟩⟩ R = -1)

/-- Decoding the P1 Bool interface recovers the exact P2a eta coordinate. -/
theorem rademacherSign_p2aEtaAsP1SecondSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z0 : Fin P.roles) (v : P1BoundaryRestRole P cut K.1 z0)
    (j : Fin (dimension v.1)) :
    (rademacherSign (p2aEtaAsP1SecondSample P dimension cut N hN R i K z0 v j) : ℝ) =
      P2a.trialScalarEta dimension N hN
        ⟨i, ⟨K, ⟨p1BoundaryRoleAsP2aAttached P cut K ⟨v.1, v.2.1⟩, j⟩⟩⟩ R := by
  rcases p2a_trialScalarEta_eq_one_or_neg_one
      (G := P.toPartiteShape) (cut := cut) dimension N hN
      (⟨i, ⟨K, ⟨p1BoundaryRoleAsP2aAttached P cut K ⟨v.1, v.2.1⟩, j⟩⟩⟩ :
        P2a.TrialScalar P.toPartiteShape cut dimension N) R with h | h
  · have hne : (1 : ℝ) ≠ -1 := by norm_num
    simp [p2aEtaAsP1SecondSample, h, hne, rademacherSign]
  · simp [p2aEtaAsP1SecondSample, h, rademacherSign]

/-- For an actual full edge-array sample, the P1 second-layer coordinate made
from its rest restriction is pointwise the primitive P1 crossing product. -/
theorem rademacherSign_p2aEtaAsP1SecondSample_eq_p1EtaSignZ
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (eps : P1TypedSample P dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z0 : Fin P.roles) (v : P1BoundaryRestRole P cut K.1 z0)
    (j : Fin (dimension v.1)) :
    (rademacherSign
      (p2aEtaAsP1SecondSample P dimension cut N hN
        (p1TypedSampleRest P dimension cut eps) i K z0 v j) : ℝ) =
      (p1EtaSignZ P dimension cut v.1 eps
        (p2aSeparatorTrialAsP1 P dimension cut N hN i) j : ℝ) := by
  rw [rademacherSign_p2aEtaAsP1SecondSample]
  exact p2a_trialScalarEta_eq_p1EtaSignZ P dimension cut N hN eps i K
    (p1BoundaryRoleAsP2aAttached P cut K ⟨v.1, v.2.1⟩) j

#print axioms p2aAttachedRole_mem_p1BoundaryRoles
#print axioms p1CrossingEquivP2aOccurrence
#print axioms p1CrossingCoordinate_eq_p2a
#print axioms p2aOccurrenceEquivRestSupport
#print axioms p2a_trialScalarEta_eq_p1EtaSignZ
#print axioms p1BoundaryRoleAsP2aAttached
#print axioms p2a_trialScalarEta_eq_one_or_neg_one
#print axioms rademacherSign_p2aEtaAsP1SecondSample
#print axioms rademacherSign_p2aEtaAsP1SecondSample_eq_p1EtaSignZ

end GraphMatrixReplica
