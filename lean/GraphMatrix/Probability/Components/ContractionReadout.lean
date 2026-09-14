import GraphMatrix.Main.InternalSampleProduct
import GraphMatrix.Probability.Synchronization.ComponentLaw
import GraphMatrix.Lower.Flattening.AllSeparatorContraction
import GraphMatrix.Probability.CrossingCoefficientIdentification
import GraphMatrix.Main.Synchronization.SampleReadoutBridge

/-! # Deterministic P2a/contraction to readout

This file contains only pointwise finite identities.  It does not assume a
contraction equality or any probability estimate.
-/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

/-- P2a's interior-role subtype and P1's `K \ B` subtype have the same roles. -/
def p2aInteriorRoleEquivP1Interior
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P2a.ComponentInteriorRole K ≃ P1InteriorRole P cut K.1 where
  toFun v := ⟨v.1.1, v.1.2, by
    intro hvB
    obtain ⟨_hvK, u, hu, e, hv, hU⟩ :=
      (mem_p1BoundaryRoles_iff P cut K.1 v.1.1).1 hvB
    apply v.2
    refine ⟨u, hu, e, ?_⟩
    rcases hv with hsz | htz <;> rcases hU with hsu | htu
    · exfalso
      have hzu : v.1.1 = u := hsz.symm.trans hsu
      exact (P2a.componentRole_not_mem_cut v.1.2) (hzu ▸ hu)
    · exact Or.inl ⟨hsz, htu⟩
    · exact Or.inr ⟨hsu, htz⟩
    · exfalso
      have hzu : v.1.1 = u := htz.symm.trans htu
      exact (P2a.componentRole_not_mem_cut v.1.2) (hzu ▸ hu)⟩
  invFun v := ⟨⟨v.1, v.2.1⟩, by
    intro htouch
    exact v.2.2 (p2aAttachedRole_mem_p1BoundaryRoles P cut K
      ⟨v.1, v.2.1, htouch⟩)⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    rfl

/-- Retype a interior assignment as the corresponding assignment. -/
def p2aInteriorAssignmentToP1
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (y : P2a.InteriorAssignment dimension K) :
    P1InteriorLabel P dimension cut K.1 :=
  fun v => y ((p2aInteriorRoleEquivP1Interior P cut K).symm v)

/-- Retype a full component assignment as P1's identical component-role
label family. -/
def p2aComponentAssignmentToP1
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (x : P2a.ComponentAssignment dimension K) :
    P1ComponentLabel P dimension cut K.1 :=
  fun v => x ⟨v.1, v.2⟩

/-- Retype a boundary assignment using the occurrence-aware boundary
equivalence already proved for the actual trial bridge. -/
def p2aBoundaryAssignmentToP1
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (xB : P2a.BoundaryAssignment dimension K) :
    P1BoundaryLabel P dimension cut K.1 :=
  fun v => xB ((p2aAttachedRoleEquivP1Boundary P cut K).symm v)

/-- Reindex the whole dependent interior-label family. -/
def p2aInteriorAssignmentEquivP1
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P2a.InteriorAssignment dimension K ≃
      P1InteriorLabel P dimension cut K.1 where
  toFun := p2aInteriorAssignmentToP1 P dimension cut K
  invFun u := fun v => u (p2aInteriorRoleEquivP1Interior P cut K v)
  left_inv y := by
    funext v
    have h := (p2aInteriorRoleEquivP1Interior P cut K).left_inv v
    cases h
    rfl
  right_inv u := by
    funext v
    have h := (p2aInteriorRoleEquivP1Interior P cut K).right_inv v
    cases h
    rfl

/-- Reindex the whole dependent boundary-label family. -/
def p2aBoundaryAssignmentEquivP1
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P2a.BoundaryAssignment dimension K ≃
      P1BoundaryLabel P dimension cut K.1 where
  toFun := p2aBoundaryAssignmentToP1 P dimension cut K
  invFun b := fun z => b (p2aAttachedRoleEquivP1Boundary P cut K z)
  left_inv xB := by
    funext z
    have h := (p2aAttachedRoleEquivP1Boundary P cut K).left_inv z
    cases h
    rfl
  right_inv b := by
    funext v
    have h := (p2aAttachedRoleEquivP1Boundary P cut K).right_inv v
    cases h
    rfl

/-- Split the boundary-role index itself into the roles distinct from `z0` and
the one distinguished role. -/
def p1BoundaryRoleSplitEquiv
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut K.1) :
    (P1BoundaryRestRole P cut K.1 z0 ⊕ Unit) ≃
      P1BoundaryRole P cut K.1 where
  toFun
    | Sum.inl v => ⟨v.1, v.2.1⟩
    | Sum.inr _ => ⟨z0, hz0⟩
  invFun b := if h : b.1 = z0 then Sum.inr ()
    else Sum.inl ⟨b.1, b.2, h⟩
  left_inv x := by
    cases x with
    | inl v => simp [v.2.2]
    | inr u => cases u; simp
  right_inv b := by
    by_cases h : b.1 = z0
    · simp only [dif_pos h]
      apply Subtype.ext
      exact h.symm
    · simp only [dif_neg h]

/-- Product over all boundary roles equals the product over the complement of
`z0`, followed by the distinguished factor. -/
theorem p1Boundary_prod_insert_eq_rest_mul_distinguished
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut K.1)
    (q : (b : P1BoundaryRole P cut K.1) → Fin (dimension b.1) → ℝ)
    (j : Fin (dimension z0))
    (r : P1BoundaryRestLabel P dimension cut K.1 z0) :
    (∏ b : P1BoundaryRole P cut K.1,
        q b (p1InsertBoundary P dimension cut K.1 z0 hz0 j r b)) =
      (∏ v : P1BoundaryRestRole P cut K.1 z0,
          q ⟨v.1, v.2.1⟩ (r v)) * q ⟨z0, hz0⟩ j := by
  classical
  let e := p1BoundaryRoleSplitEquiv P cut K z0 hz0
  let f : P1BoundaryRole P cut K.1 → ℝ := fun b =>
    q b (p1InsertBoundary P dimension cut K.1 z0 hz0 j r b)
  calc
    (∏ b : P1BoundaryRole P cut K.1, f b) =
        ∏ x : P1BoundaryRestRole P cut K.1 z0 ⊕ Unit, f (e x) :=
      (Equiv.prod_comp e f).symm
    _ = (∏ v : P1BoundaryRestRole P cut K.1 z0, f (e (Sum.inl v))) *
        ∏ u : Unit, f (e (Sum.inr u)) := by
      rw [Fintype.prod_sum_type]
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro v _hv
        simp [f, e, p1BoundaryRoleSplitEquiv, p1InsertBoundary, v.2.2]
      · simp [f, e, p1BoundaryRoleSplitEquiv, p1InsertBoundary]

/-- P2a's boundary/interior split reconstructs the same full assignment as
P1's `p1Glue`, after the two natural role reindexings. -/
theorem p2a_componentAssignmentToP1_split_eq_p1Glue
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (xB : P2a.BoundaryAssignment dimension K)
    (y : P2a.InteriorAssignment dimension K) :
    p2aComponentAssignmentToP1 P dimension cut K
        ((P2a.componentAssignmentEquiv dimension K).symm (xB, y)) =
      p1Glue P dimension cut K.1
        (p2aBoundaryAssignmentToP1 P dimension cut K xB)
        (p2aInteriorAssignmentToP1 P dimension cut K y) := by
  classical
  funext v
  by_cases hvB : v.1 ∈ p1BoundaryRoles P cut K.1
  · let z := (p2aAttachedRoleEquivP1Boundary P cut K).symm ⟨v.1, hvB⟩
    have hzRole :
        (⟨z.1, z.2.1⟩ : P2a.ComponentRole K) = ⟨v.1, v.2⟩ :=
      Subtype.ext rfl
    simp only [p2aComponentAssignmentToP1, p1Glue, hvB,
      p2aBoundaryAssignmentToP1]
    change (P2a.componentAssignmentEquiv dimension K).symm (xB, y)
        ⟨v.1, v.2⟩ = xB z
    cases hzRole
    exact P2a.componentAssignmentEquiv_symm_boundary dimension K xB y z
  · let w := (p2aInteriorRoleEquivP1Interior P cut K).symm
      ⟨v.1, v.2, hvB⟩
    have hwRole : w.1 = (⟨v.1, v.2⟩ : P2a.ComponentRole K) :=
      Subtype.ext rfl
    simp only [p2aComponentAssignmentToP1, p1Glue, hvB,
      p2aInteriorAssignmentToP1]
    change (P2a.componentAssignmentEquiv dimension K).symm (xB, y)
        ⟨v.1, v.2⟩ = y w
    cases hwRole
    exact P2a.componentAssignmentEquiv_symm_interior dimension K xB y w

/-- The actual internal monomial reads exactly P1's internal sample for
the same component, edge occurrence and endpoint labels. -/
theorem p2a_componentInternalMonomial_eq_p1
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (x : P2a.ComponentAssignment dimension K) :
    P2a.componentInternalMonomial dimension I K x =
      (p1InternalMonomialZ P dimension cut K.1
        (p2aComponentAssignmentToP1 P dimension cut K x)
        (mainP1InternalSample P cut dimension I K) : ℝ) := by
  classical
  unfold P2a.componentInternalMonomial p1InternalMonomialZ
    mainP1InternalSample mainComponentInternalAddressMap
    P2a.componentInternalAddress
  push_cast
  rfl

/-- The deterministic coefficient obtained by summing P2a's actual internal
monomial over all interior labels is exactly P1's `gamma`. -/
theorem p2a_componentGamma_eq_p1Gamma
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (K : P2a.ActiveComponent P.toPartiteShape cut)
    (xB : P2a.BoundaryAssignment dimension K) :
    P2a.componentGamma dimension I K xB =
      p1Gamma P dimension cut K.1
        (p2aBoundaryAssignmentToP1 P dimension cut K xB)
        (mainP1InternalSample P cut dimension I K) := by
  classical
  unfold P2a.componentGamma p1Gamma p1GammaZ
  push_cast
  let e := p2aInteriorAssignmentEquivP1 P dimension cut K
  calc
    (∑ y : P2a.InteriorAssignment dimension K,
        P2a.componentInternalMonomial dimension I K
          ((P2a.componentAssignmentEquiv dimension K).symm (xB, y))) =
      ∑ y : P2a.InteriorAssignment dimension K,
        (p1InternalMonomialZ P dimension cut K.1
          (p1Glue P dimension cut K.1
            (p2aBoundaryAssignmentToP1 P dimension cut K xB)
            (e y))
          (mainP1InternalSample P cut dimension I K) : ℝ) := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [p2a_componentInternalMonomial_eq_p1,
          p2a_componentAssignmentToP1_split_eq_p1Glue]
        rfl
    _ = ∑ u : P1InteriorLabel P dimension cut K.1,
        (p1InternalMonomialZ P dimension cut K.1
          (p1Glue P dimension cut K.1
            (p2aBoundaryAssignmentToP1 P dimension cut K xB) u)
          (mainP1InternalSample P cut dimension I K) : ℝ) :=
      Equiv.sum_comp e (fun u : P1InteriorLabel P dimension cut K.1 =>
        (p1InternalMonomialZ P dimension cut K.1
          (p1Glue P dimension cut K.1
            (p2aBoundaryAssignmentToP1 P dimension cut K xB) u)
          (mainP1InternalSample P cut dimension I K) : ℝ))

set_option maxHeartbeats 4000000 in
/-- After inserting the distinguished boundary label, P2a's eta product
is the second-layer character times the distinguished actual eta sign. -/
theorem p2a_componentEtaProduct_of_p1InsertBoundary
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (j : Fin (dimension (p3DistinguishedBoundaryRole P cut K).1))
    (r : P1BoundaryRestLabel P dimension cut K.1
      (p3DistinguishedBoundaryRole P cut K).1) :
    P2a.componentEtaProduct dimension N hN R i K
        (fun z => p1InsertBoundary P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1
          (p3DistinguishedBoundaryRole P cut K).2 j r
          (p2aAttachedRoleEquivP1Boundary P cut K z)) =
      (p1SecondCharacterZ P dimension cut K.1
        (p3DistinguishedBoundaryRole P cut K).1 r
        (p3TrialSecondSample P dimension cut N hN i K R) : ℝ) *
      (rademacherSign
        (p3TrialDistinguishedSample P dimension cut N hN i K R j) : ℝ) := by
  classical
  let eA := p2aAttachedRoleEquivP1Boundary P cut K
  let d := p3DistinguishedBoundaryRole P cut K
  let b := p1InsertBoundary P dimension cut K.1 d.1 d.2 j r
  let q : (v : P1BoundaryRole P cut K.1) → Fin (dimension v.1) → ℝ :=
    fun v x => P2a.trialScalarEta dimension N hN
      ⟨i, ⟨K, ⟨eA.symm v, x⟩⟩⟩ R
  let f : P1BoundaryRole P cut K.1 → ℝ := fun v => q v (b v)
  have hprod :
      P2a.componentEtaProduct dimension N hN R i K
          (fun z => b (eA z)) =
        ∏ v : P1BoundaryRole P cut K.1, f v := by
    unfold P2a.componentEtaProduct
    apply Fintype.prod_equiv eA
    intro z
    have h := eA.left_inv z
    cases h
    rfl
  rw [show (fun z => p1InsertBoundary P dimension cut K.1 d.1 d.2 j r
      (p2aAttachedRoleEquivP1Boundary P cut K z)) =
      (fun z => b (eA z)) by rfl, hprod]
  change (∏ v : P1BoundaryRole P cut K.1, q v (b v)) = _
  rw [p1Boundary_prod_insert_eq_rest_mul_distinguished
    P dimension cut K d.1 d.2 q j r]
  unfold p1SecondCharacterZ
  push_cast
  congr 1
  · apply Finset.prod_congr rfl
    intro v _hv
    symm
    simpa [q, eA, p3TrialSecondSample] using
      (rademacherSign_p3TrialScalarBit
        (G := P.toPartiteShape) (cut := cut) dimension N hN
        (⟨i, K,
          (p2aAttachedRoleEquivP1Boundary P cut K).symm
            ⟨v.1, v.2.1⟩,
          r v⟩ : P2a.TrialScalar P.toPartiteShape cut dimension N) R)
  · have hd : eA.symm d = p3DistinguishedAttachedRole P cut K := by
      dsimp [eA, d, p3DistinguishedBoundaryRole]
      exact (p2aAttachedRoleEquivP1Boundary P cut K).left_inv _
    change P2a.trialScalarEta dimension N hN
        ⟨i, K, eA.symm d, j⟩ R =
      (rademacherSign
        (p3TrialScalarBit dimension N hN
          ⟨i, K, p3DistinguishedAttachedRole P cut K, j⟩ R) : ℝ)
    cases hd
    exact (rademacherSign_p3TrialScalarBit
      (G := P.toPartiteShape) (cut := cut) dimension N hN
      (⟨i, K, p3DistinguishedAttachedRole P cut K, j⟩ :
        P2a.TrialScalar P.toPartiteShape cut dimension N) R).symm

/-- The two Bool sign conventions used by and `WeightedSignTilt` differ
by one global minus sign. -/
theorem rademacherSign_eq_neg_weightedSign (b : Bool) :
    (rademacherSign b : ℝ) = -WeightedSignTilt.sign b := by
  cases b <;> norm_num [rademacherSign, WeightedSignTilt.sign]

/-- Exact contraction readout for one component and diagonal trial.
The global minus sign is forced by the two Bool encodings above. -/
theorem p2a_componentContraction_eq_neg_weightedSum_trial
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P2a.componentContraction dimension N hN I R i K =
      -WeightedSignTilt.weightedSum
        (fun j => p1Z P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1
          (p3DistinguishedBoundaryRole P cut K).2
          (mainP1InternalSample P cut dimension I K)
          (p3TrialSecondSample P dimension cut N hN i K R) j)
        (p3TrialDistinguishedSample P dimension cut N hN i K R) := by
  classical
  let d := p3DistinguishedBoundaryRole P cut K
  let epsI := mainP1InternalSample P cut dimension I K
  let eta := p3TrialSecondSample P dimension cut N hN i K R
  let outer := p3TrialDistinguishedSample P dimension cut N hN i K R
  let e :
      (Fin (dimension d.1) ×
        P1BoundaryRestLabel P dimension cut K.1 d.1) ≃
        P2a.BoundaryAssignment dimension K :=
    (P1AD.boundarySplitEquiv P dimension cut K.1 d.1 d.2).trans
      (p2aBoundaryAssignmentEquivP1 P dimension cut K).symm
  rw [P2a.componentContraction_eq_gamma_eta]
  calc
    (∑ xB : P2a.BoundaryAssignment dimension K,
        P2a.componentGamma dimension I K xB *
          P2a.componentEtaProduct dimension N hN R i K xB) =
      ∑ jr : Fin (dimension d.1) ×
          P1BoundaryRestLabel P dimension cut K.1 d.1,
        P2a.componentGamma dimension I K (e jr) *
          P2a.componentEtaProduct dimension N hN R i K (e jr) := by
        exact (Equiv.sum_comp e _).symm
    _ = ∑ jr : Fin (dimension d.1) ×
          P1BoundaryRestLabel P dimension cut K.1 d.1,
        p1Gamma P dimension cut K.1
            (p1InsertBoundary P dimension cut K.1 d.1 d.2 jr.1 jr.2) epsI *
          ((p1SecondCharacterZ P dimension cut K.1 d.1 jr.2 eta : ℝ) *
            (rademacherSign (outer jr.1) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro jr _hjr
        rcases jr with ⟨j, r⟩
        have hGamma := p2a_componentGamma_eq_p1Gamma
          P dimension cut I K (e (j, r))
        have hEta := p2a_componentEtaProduct_of_p1InsertBoundary
          P dimension cut N hN R i K j r
        have hb : p2aBoundaryAssignmentToP1 P dimension cut K (e (j, r)) =
            p1InsertBoundary P dimension cut K.1 d.1 d.2 j r := by
          dsimp [e, P1AD.boundarySplitEquiv]
          change (p2aBoundaryAssignmentEquivP1 P dimension cut K)
              ((p2aBoundaryAssignmentEquivP1 P dimension cut K).symm
                (p1InsertBoundary P dimension cut K.1 d.1 d.2 j r)) = _
          exact (p2aBoundaryAssignmentEquivP1 P dimension cut K).apply_symm_apply _
        have heX : e (j, r) = fun z =>
            p1InsertBoundary P dimension cut K.1 d.1 d.2 j r
              (p2aAttachedRoleEquivP1Boundary P cut K z) := by
          funext z
          rfl
        calc
          P2a.componentGamma dimension I K (e (j, r)) *
              P2a.componentEtaProduct dimension N hN R i K (e (j, r)) =
            p1Gamma P dimension cut K.1
                (p2aBoundaryAssignmentToP1 P dimension cut K (e (j, r)))
                (mainP1InternalSample P cut dimension I K) *
              P2a.componentEtaProduct dimension N hN R i K (e (j, r)) := by
                rw [hGamma]
          _ = p1Gamma P dimension cut K.1
                (p1InsertBoundary P dimension cut K.1 d.1 d.2 j r) epsI *
              ((p1SecondCharacterZ P dimension cut K.1 d.1 r eta : ℝ) *
                (rademacherSign (outer j) : ℝ)) := by
                rw [hb, heX]
                simpa [d, epsI, eta, outer] using congrArg
                  (fun t => p1Gamma P dimension cut K.1
                    (p1InsertBoundary P dimension cut K.1 d.1 d.2 j r) epsI * t)
                  hEta
    _ = ∑ j : Fin (dimension d.1),
        p1Z P dimension cut K.1 d.1 d.2 epsI eta j *
          (rademacherSign (outer j) : ℝ) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [Prod.fst, Prod.snd]
        unfold p1Z
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
    _ = -WeightedSignTilt.weightedSum
        (fun j => p1Z P dimension cut K.1 d.1 d.2 epsI eta j) outer := by
        unfold WeightedSignTilt.weightedSum
        simp_rw [rademacherSign_eq_neg_weightedSign]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
    _ = _ := by rfl

/-- Absolute-value form consumed by the tail event. -/
theorem p2a_componentContraction_abs_eq_weightedSum_trial
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    |P2a.componentContraction dimension N hN I R i K| =
      |WeightedSignTilt.weightedSum
        (fun j => p1Z P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1
          (p3DistinguishedBoundaryRole P cut K).2
          (mainP1InternalSample P cut dimension I K)
          (p3TrialSecondSample P dimension cut N hN i K R) j)
        (p3TrialDistinguishedSample P dimension cut N hN i K R)| := by
  rw [p2a_componentContraction_eq_neg_weightedSum_trial]
  exact abs_neg _

/-- The same absolute readout in the equivalence-based sample coordinates used
by the finalized probability law. -/
theorem p2a_componentContraction_abs_eq_weightedSum
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    |P2a.componentContraction dimension N hN I R i K| =
      |WeightedSignTilt.weightedSum
        (fun j => p1Z P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1
          (p3DistinguishedBoundaryRole P cut K).2
          (mainP1InternalSample P cut dimension I K)
          (p3ComponentSampleFromRest P dimension cut N hN i K R).1 j)
        (p3ComponentSampleFromRest P dimension cut N hN i K R).2| := by
  rw [p3ComponentSampleFromRest_eq_trialComponentSample]
  exact p2a_componentContraction_abs_eq_weightedSum_trial
    P dimension cut N hN I R i K

set_option backward.isDefEq.respectTransparency true in
/-- Actual contraction at a diagonal separator tuple, exposed directly in
the sample coordinates consumed by the probability theorem. -/
theorem actualComponentContraction_abs_eq_p1WeightedSum
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (omega : Model.C2Actual.FrozenSample (G := P.toPartiteShape) cut dimension)
    (N : ℕ) (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    |Model.C2Actual.actualComponentContraction (G := P.toPartiteShape)
        cut dimension omega
        (P2a.separatorTrial (G := P.toPartiteShape) dimension N hN i) K| =
      |WeightedSignTilt.weightedSum
        (fun j => p1Z P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1
          (p3DistinguishedBoundaryRole P cut K).2
          (mainP1InternalSample P cut dimension
            (Model.C2Actual.frozenInternalCube (G := P.toPartiteShape)
              cut dimension omega) K)
          (p3ComponentSampleFromRest P dimension cut N hN i K
            (Model.C2Actual.frozenRestCube (G := P.toPartiteShape)
              cut dimension omega)).1 j)
        (p3ComponentSampleFromRest P dimension cut N hN i K
          (Model.C2Actual.frozenRestCube (G := P.toPartiteShape)
            cut dimension omega)).2| := by
  rw [Model.C2Actual.actualComponentContraction_eq_p2a]
  exact p2a_componentContraction_abs_eq_weightedSum
    P dimension cut N hN
      (Model.C2Actual.frozenInternalCube (G := P.toPartiteShape)
        cut dimension omega)
      (Model.C2Actual.frozenRestCube (G := P.toPartiteShape)
        cut dimension omega) i K


end GraphMatrixReplica
