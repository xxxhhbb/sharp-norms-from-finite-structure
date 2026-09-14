import GraphMatrix.Counting.ActiveComponents
import GraphMatrix.Counting.PathNoiseProductLaw
import GraphMatrix.PartiteBoundaryMatrixTrace
import GraphMatrix.ToPartiteBridge
import GraphMatrix.DistinctCoordinateTrials

/-!
# typed edge coordinates and conditional product law

This module is intended to formalize the finite-coordinate core of directly
on `JointEdgeSignSample`.  It does not introduce an independent replacement
model.  The primitive address keeps the edge occurrence and the two endpoint
label types.  Internal conditioning is a literal partition of those addresses.

All theorem bodies are explicit; no proof placeholder or added logical assumption is present.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica
namespace P2a

set_option maxHeartbeats 800000

attribute [local instance] Classical.propDecidable

/-- Universe-polymorphic version of the existing normalized finite sum.
It agrees definitionally with the original mean on the actual Type0 model. -/
def paperMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ a, f a

theorem paperMean_eq_original {α : Type} [Fintype α] (f : α → ℝ) :
    paperMean f = GraphMatrixReplica.paperMean f := rfl

theorem paperMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) :
    paperMean (fun a => f (e a)) = paperMean f := by
  unfold paperMean
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

theorem paperMean_coordinateProduct
    {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (F : I → Ω → ℝ) :
    paperMean (fun w : I → Ω => ∏ i : I, F i (w i)) =
      ∏ i : I, paperMean (F i) := by
  classical
  unfold paperMean
  rw [Fintype.card_fun]
  push_cast
  rw [← Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [inv_pow]

/-! ## 1. Primitive typed addresses and the exact full/internal/rest split -/

/-- A primitive random coordinate of the actual typed edge-array model.
The outer `Sigma` keeps the edge occurrence; the second component has the
actual source/target dependent label types. -/
abbrev PrimitiveAddress {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) : Type :=
  Σ e : Fin G.edges, EdgeSignCoordinate dimension e

/-- Currying/uncurrying only: this is the original `JointEdgeSignSample`, with
no change of probability model. -/
def jointSampleEquivPrimitive {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) :
    JointEdgeSignSample dimension ≃ (PrimitiveAddress dimension → Bool) where
  toFun ε a := ε a.1 a.2
  invFun w e ab := w ⟨e, ab⟩
  left_inv ε := by
    funext e ab
    rfl
  right_inv w := by
    funext a
    rcases a with ⟨e, ab⟩
    rfl

@[simp] theorem jointSampleEquivPrimitive_apply
    {G : PartiteShape} (dimension : Fin G.roles → ℕ)
    (ε : JointEdgeSignSample dimension) (e : Fin G.edges)
    (ab : EdgeSignCoordinate dimension e) :
    jointSampleEquivPrimitive dimension ε ⟨e, ab⟩ = ε e ab := rfl

/-- Split a finite coordinate cube by an actual predicate on coordinates. -/
def splitByPredicateEquiv {α β : Type*} (P : α → Prop)
    [DecidablePred P] :
    (α → β) ≃ (({a : α // P a} → β) × ({a : α // ¬ P a} → β)) where
  toFun f :=
    ⟨fun a => f a.1, fun a => f a.1⟩
  invFun x a := if h : P a then x.1 ⟨a, h⟩ else x.2 ⟨a, h⟩
  left_inv f := by
    funext a
    by_cases h : P a <;> simp [h]
  right_inv x := by
    apply Prod.ext
    · funext a
      simp [a.2]
    · funext a
      simp [a.2]

/-- Genuine C079 active components. -/
abbrev ActiveComponent (G : PartiteShape)
    (cut : Finset (Fin G.roles)) :=
  {c : G.C079CutComponent cut // c.IsActive}

/-- A primitive address is internal iff both endpoints of its edge occurrence
lie in one actual active component of `G - cut`. -/
def IsInternalAddress {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (a : PrimitiveAddress dimension) : Prop :=
  ∃ K : ActiveComponent G cut,
    G.source a.1 ∈ G.c079ComponentRoles cut K.1 ∧
    G.target a.1 ∈ G.c079ComponentRoles cut K.1

abbrev InternalAddress {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ) :=
  {a : PrimitiveAddress dimension // IsInternalAddress cut dimension a}

abbrev RestAddress {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ) :=
  {a : PrimitiveAddress dimension // ¬ IsInternalAddress cut dimension a}

abbrev InternalCube {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ) :=
  InternalAddress cut dimension → Bool

abbrev RestCube {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ) :=
  RestAddress cut dimension → Bool

/-- The exact sample-space rearrangement used for conditioning. -/
def internalRestEquiv {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ) :
    JointEdgeSignSample dimension ≃
      (InternalCube cut dimension × RestCube cut dimension) := by
  classical
  exact (jointSampleEquivPrimitive dimension).trans
    (splitByPredicateEquiv (IsInternalAddress cut dimension))

/-- Uniform average on a product is the iterated uniform average.  This is a
finite algebraic identity and does not assume probabilistic independence. -/
theorem paperMean_prod
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    paperMean (fun x : α × β => f x.1 x.2) =
      paperMean (fun a : α => paperMean (f a)) := by
  classical
  unfold paperMean
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type]
  rw [← Finset.mul_sum]
  ring

/-- Fixed-complete-internal-realization conditional mean. -/
def conditionalRestMean {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (I : InternalCube cut dimension)
    (F : JointEdgeSignSample dimension → ℝ) : ℝ :=
  paperMean (fun R : RestCube cut dimension =>
    F ((internalRestEquiv cut dimension).symm (I, R)))

/-- Exact total-expectation identity for the *complete* internal realization.
This is stronger and more precise than conditioning only on an internal good
event. -/
theorem paperMean_eq_internal_then_rest
    {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (F : JointEdgeSignSample dimension → ℝ) :
    paperMean F =
      paperMean (fun I : InternalCube cut dimension =>
        conditionalRestMean cut dimension I F) := by
  classical
  let e := internalRestEquiv cut dimension
  calc
    paperMean F =
        paperMean (fun x : InternalCube cut dimension × RestCube cut dimension =>
          F (e.symm x)) := by
      simpa [e] using
        (paperMean_equiv e
          (fun x : InternalCube cut dimension × RestCube cut dimension =>
            F (e.symm x)))
    _ = paperMean (fun I : InternalCube cut dimension =>
          paperMean (fun R : RestCube cut dimension =>
            F (e.symm (I, R)))) := by
      exact paperMean_prod
        (fun I : InternalCube cut dimension =>
          fun R : RestCube cut dimension => F (e.symm (I, R)))
    _ = _ := by
      rfl

/-! ## 2. Component geometry and actual crossing occurrences -/

/-- Membership in a genuine cut component implies being outside the cut. -/
theorem componentRole_not_mem_cut
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    {c : G.C079CutComponent cut} {v : Fin G.roles}
    (hv : v ∈ G.c079ComponentRoles cut c) : v ∉ cut := by
  exact ((G.mem_c079ComponentRoles_iff cut c v).1 hv).1

/-- Two genuine cut components which contain the same surviving role are equal. -/
theorem activeComponent_eq_of_common_role
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (K L : ActiveComponent G cut) {v : Fin G.roles}
    (hvK : v ∈ G.c079ComponentRoles cut K.1)
    (hvL : v ∈ G.c079ComponentRoles cut L.1) : K = L := by
  apply Subtype.ext
  obtain ⟨hvCutK, hK⟩ :=
    (G.mem_c079ComponentRoles_iff cut K.1 v).1 hvK
  obtain ⟨hvCutL, hL⟩ :=
    (G.mem_c079ComponentRoles_iff cut L.1 v).1 hvL
  have hsub :
      (⟨v, hvCutK⟩ : {w : Fin G.roles // w ∉ cut}) =
        ⟨v, hvCutL⟩ := by
    exact Subtype.ext rfl
  rw [← hsub] at hL
  exact hK.symm.trans hL

/-- An edge occurrence joins `v` and `u`, independently of which one is the
stored source and which one is the stored target. -/
def EdgeJoins (G : PartiteShape) (e : Fin G.edges)
    (v u : Fin G.roles) : Prop :=
  (G.source e = v ∧ G.target e = u) ∨
  (G.source e = u ∧ G.target e = v)

/-- Roles in an active component which really touch the separator. -/
abbrev AttachedRole {G : PartiteShape} (cut : Finset (Fin G.roles))
    (K : ActiveComponent G cut) :=
  {z : Fin G.roles //
    z ∈ G.c079ComponentRoles cut K.1 ∧
      ∃ u : Fin G.roles, u ∈ cut ∧
        ∃ e : Fin G.edges, EdgeJoins G e z u}

/-- The separator role subtype. -/
abbrev SeparatorRole (G : PartiteShape)
    (cut : Finset (Fin G.roles)) :=
  {u : Fin G.roles // u ∈ cut}

/-- A concrete crossing edge occurrence for one attached component role.  The
edge occurrence itself is retained in the type. -/
abbrev CrossingOccurrence {G : PartiteShape}
    (cut : Finset (Fin G.roles))
    {K : ActiveComponent G cut} (z : AttachedRole cut K) :=
  {eu : Fin G.edges × SeparatorRole G cut //
    EdgeJoins G eu.1 z.1 eu.2.1}

/-- Every attached role has at least one concrete crossing occurrence. -/
theorem crossingOccurrence_nonempty
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    {K : ActiveComponent G cut} (z : AttachedRole cut K) :
    Nonempty (CrossingOccurrence cut z) := by
  obtain ⟨u, huCut, e, he⟩ := z.2.2
  exact ⟨⟨(e, ⟨u, huCut⟩), he⟩⟩

/-- Active attachment implies at least one attached role.  This converts the
`IsAttached` incidence formulation in C079 to the orientation-aware
`EdgeJoins` formulation used by typed coordinates. -/
theorem attachedRole_nonempty
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (K : ActiveComponent G cut) : Nonempty (AttachedRole cut K) := by
  obtain ⟨v, hvK, u, huCut, e, hve, hue⟩ := K.2.2
  have hvOut : v ∉ cut := componentRole_not_mem_cut hvK
  refine ⟨⟨v, hvK, ?_⟩⟩
  refine ⟨u, huCut, e, ?_⟩
  rcases hve with hvs | hvt <;> rcases hue with hus | hut
  · exfalso
    apply hvOut
    have hvu : v = u := hvs.symm.trans hus
    simpa [hvu] using huCut
  · exact Or.inl ⟨hvs, hut⟩
  · exact Or.inr ⟨hus, hvt⟩
  · exfalso
    apply hvOut
    have hvu : v = u := hvt.symm.trans hut
    simpa [hvu] using huCut

/-- Transport a typed role label across an equality of roles. -/
def castRoleLabel {G : PartiteShape}
    (dimension : Fin G.roles → ℕ)
    {v w : Fin G.roles} (h : v = w)
    (x : Fin (dimension v)) : Fin (dimension w) :=
  Fin.cast (congrArg dimension h) x

@[simp] theorem castRoleLabel_val
    {G : PartiteShape} (dimension : Fin G.roles → ℕ)
    {v w : Fin G.roles} (h : v = w)
    (x : Fin (dimension v)) :
    (castRoleLabel dimension h x).val = x.val := rfl

/-- The actual primitive address read by a crossing occurrence.  The stored
source/target direction is respected in each branch. -/
def crossingPrimitiveAddress
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    {K : ActiveComponent G cut} {z : AttachedRole cut K}
    (c : CrossingOccurrence cut z)
    (j : Fin (dimension z.1))
    (q : Fin (dimension c.1.2.1)) : PrimitiveAddress dimension :=
  ⟨c.1.1, by
    classical
    by_cases h : G.source c.1.1 = z.1 ∧ G.target c.1.1 = c.1.2.1
    · exact (castRoleLabel dimension h.1.symm j,
        castRoleLabel dimension h.2.symm q)
    · have hr := Or.resolve_left c.2 h
      exact (castRoleLabel dimension hr.1.symm q,
        castRoleLabel dimension hr.2.symm j)⟩

/-- Reading a crossing address never reads an internal coordinate: one endpoint
is an actual separator role. -/
theorem crossingPrimitiveAddress_not_internal
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    {K : ActiveComponent G cut} {z : AttachedRole cut K}
    (c : CrossingOccurrence cut z)
    (j : Fin (dimension z.1))
    (q : Fin (dimension c.1.2.1)) :
    ¬ IsInternalAddress cut dimension
      (crossingPrimitiveAddress dimension c j q) := by
  intro hInt
  obtain ⟨L, hsL, htL⟩ := hInt
  rcases c with ⟨⟨e, u⟩, hc⟩
  rcases hc with hc | hc
  · have huL : u.1 ∈ G.c079ComponentRoles cut L.1 := by
      simpa [crossingPrimitiveAddress, hc.2] using htL
    exact (componentRole_not_mem_cut huL) u.2
  · have huL : u.1 ∈ G.c079ComponentRoles cut L.1 := by
      simpa [crossingPrimitiveAddress, hc.1] using hsL
    exact (componentRole_not_mem_cut huL) u.2

/-- Equality of two actual typed crossing addresses forces equality of the edge
occurrence, both endpoint roles, and the *values* of the component/separator
labels.  Mixed source/target orientations are impossible because the component
endpoint is outside `cut` while the separator endpoint lies in `cut`. -/
theorem crossingPrimitiveAddress_collision
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    {K L : ActiveComponent G cut}
    {z : AttachedRole cut K} {z' : AttachedRole cut L}
    (c : CrossingOccurrence cut z)
    (d : CrossingOccurrence cut z')
    (j : Fin (dimension z.1))
    (j' : Fin (dimension z'.1))
    (q : Fin (dimension c.1.2.1))
    (q' : Fin (dimension d.1.2.1))
    (haddr : crossingPrimitiveAddress dimension c j q =
      crossingPrimitiveAddress dimension d j' q') :
    c.1.1 = d.1.1 ∧
      z.1 = z'.1 ∧
      c.1.2.1 = d.1.2.1 ∧
      j.val = j'.val ∧ q.val = q'.val := by
  have he : c.1.1 = d.1.1 :=
    congrArg Sigma.fst haddr
  have hfirst :
      (crossingPrimitiveAddress dimension c j q).2.1.val =
      (crossingPrimitiveAddress dimension d j' q').2.1.val :=
    congrArg (fun a : PrimitiveAddress dimension => a.2.1.val) haddr
  have hsecond :
      (crossingPrimitiveAddress dimension c j q).2.2.val =
      (crossingPrimitiveAddress dimension d j' q').2.2.val :=
    congrArg (fun a : PrimitiveAddress dimension => a.2.2.val) haddr
  rcases c with ⟨⟨e, u⟩, hc⟩
  rcases d with ⟨⟨e', u'⟩, hd⟩
  dsimp at he
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · have hz : z.1 = z'.1 :=
      hc.1.symm.trans ((congrArg G.source he).trans hd.1)
    have hu : u.1 = u'.1 :=
      hc.2.symm.trans ((congrArg G.target he).trans hd.2)
    refine ⟨he, hz, hu, ?_, ?_⟩
    · simpa [crossingPrimitiveAddress, hc, hd, castRoleLabel] using hfirst
    · simpa [crossingPrimitiveAddress, hc, hd, castRoleLabel] using hsecond
  · have hzu : z.1 = u'.1 :=
      hc.1.symm.trans ((congrArg G.source he).trans hd.1)
    have hzOut : z.1 ∉ cut := componentRole_not_mem_cut z.2.1
    exfalso
    apply hzOut
    simpa [hzu] using u'.2
  · have huz : u.1 = z'.1 :=
      hc.1.symm.trans ((congrArg G.source he).trans hd.1)
    have hzOut : z'.1 ∉ cut := componentRole_not_mem_cut z'.2.1
    exfalso
    apply hzOut
    simpa [← huz] using u.2
  · have hzu : u.1 ≠ z.1 := by
      intro h
      exact (componentRole_not_mem_cut z.2.1) (h ▸ u.2)
    have hzu' : u'.1 ≠ z'.1 := by
      intro h
      exact (componentRole_not_mem_cut z'.2.1) (h ▸ u'.2)
    have hz : z.1 = z'.1 :=
      hc.2.symm.trans ((congrArg G.target he).trans hd.2)
    have hu : u.1 = u'.1 :=
      hc.1.symm.trans ((congrArg G.source he).trans hd.1)
    refine ⟨he, hz, hu, ?_, ?_⟩
    · simpa [crossingPrimitiveAddress, hc, hd, hzu, hzu', castRoleLabel] using hsecond
    · simpa [crossingPrimitiveAddress, hc, hd, hzu, hzu', castRoleLabel] using hfirst

/-! ## 3. Diagonal separator trials and pairwise-disjoint actual supports -/

/-- Diagonal separator tuple, now indexed by the actual separator-role subtype. -/
def separatorTrial
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (i : Fin N) (u : SeparatorRole G cut) : Fin (dimension u.1) :=
  PaperR16LowerSync.diagonalTrial
    (fun u : SeparatorRole G cut => dimension u.1) N hN i u

/-- One scalar eta-coordinate: trial, active component, attached component role,
and one typed component-role label. -/
abbrev TrialScalar
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ) (N : ℕ) :=
  Σ i : Fin N,
    Σ K : ActiveComponent G cut,
      Σ z : AttachedRole cut K, Fin (dimension z.1)

@[simp] theorem separatorTrial_val
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (i : Fin N) (u : SeparatorRole G cut) :
    (separatorTrial dimension N hN i u).val = i.val := rfl

/-- Address map for one eta-coordinate and one crossing occurrence. -/
def trialScalarAddress
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N)
    (c : CrossingOccurrence cut g.2.2.1) : PrimitiveAddress dimension :=
  crossingPrimitiveAddress dimension c g.2.2.2
    (separatorTrial dimension N hN g.1 c.1.2)

/-- For a fixed eta-coordinate, distinct crossing occurrences are distinct
primitive coordinates. -/
theorem trialScalarAddress_injective
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    Function.Injective (trialScalarAddress dimension N hN g) := by
  intro c d hcd
  have hcol := crossingPrimitiveAddress_collision dimension c d
    g.2.2.2 g.2.2.2
    (separatorTrial dimension N hN g.1 c.1.2)
    (separatorTrial dimension N hN g.1 d.1.2) hcd
  apply Subtype.ext
  apply Prod.ext
  · exact hcol.1
  · exact Subtype.ext hcol.2.2.1

/-- Collision of addresses belonging to two trial scalars forces the trial
scalars themselves to be equal.  This is the graph-specific step which upgrades
the local one-tuple statement to all trials and all active components. -/
theorem trialScalar_eq_of_address_eq
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g h : TrialScalar G cut dimension N)
    (c : CrossingOccurrence cut g.2.2.1)
    (d : CrossingOccurrence cut h.2.2.1)
    (haddr : trialScalarAddress dimension N hN g c =
      trialScalarAddress dimension N hN h d) : g = h := by
  rcases g with ⟨i, g⟩
  rcases g with ⟨K, g⟩
  rcases g with ⟨z, j⟩
  rcases h with ⟨i', h⟩
  rcases h with ⟨L, h⟩
  rcases h with ⟨z', j'⟩
  dsimp only at c d haddr ⊢
  have hcol := crossingPrimitiveAddress_collision dimension c d
    j j'
    (separatorTrial dimension N hN i c.1.2)
    (separatorTrial dimension N hN i' d.1.2) haddr
  have hK : K = L := by
    apply activeComponent_eq_of_common_role K L z.2.1
    simpa [hcol.2.1] using z'.2.1
  have hi : i = i' := by
    apply Fin.ext
    simpa only [separatorTrial_val] using hcol.2.2.2.2
  subst i'
  subst L
  have hz : z = z' := Subtype.ext hcol.2.1
  subst z'
  have hj : j = j' := Fin.ext hcol.2.2.2.1
  subst j'
  rfl

/-- The actual primitive support of one eta-coordinate. -/
def trialScalarSupport
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    Finset (PrimitiveAddress dimension) := by
  classical
  exact Finset.univ.image (trialScalarAddress dimension N hN g)

/-- Every eta support is nonempty, including singleton-component cases. -/
theorem trialScalarSupport_nonempty
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    (trialScalarSupport dimension N hN g).Nonempty := by
  classical
  let c : CrossingOccurrence cut g.2.2.1 :=
    Classical.choice (crossingOccurrence_nonempty g.2.2.1)
  refine ⟨trialScalarAddress dimension N hN g c, ?_⟩
  simp [trialScalarSupport, c]

/-- Supports of distinct trial/component/role/label scalars are genuinely
disjoint subsets of primitive typed coordinates. -/
theorem trialScalarSupport_pairwise_disjoint
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1) :
    Pairwise (fun g h : TrialScalar G cut dimension N =>
      Disjoint (trialScalarSupport dimension N hN g)
        (trialScalarSupport dimension N hN h)) := by
  classical
  intro g h hgh
  rw [Finset.disjoint_left]
  intro a hag hah
  rcases Finset.mem_image.mp hag with ⟨c, -, rfl⟩
  rcases Finset.mem_image.mp hah with ⟨d, -, hd⟩
  exact hgh (trialScalar_eq_of_address_eq dimension N hN g h c d hd.symm)

/-- A crossing support has empty intersection with the internal block. -/
theorem trialScalarSupport_disjoint_internal
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    ∀ a ∈ trialScalarSupport dimension N hN g,
      ¬ IsInternalAddress cut dimension a := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨c, -, rfl⟩
  exact crossingPrimitiveAddress_not_internal dimension c g.2.2.2
    (separatorTrial dimension N hN g.1 c.1.2)

/-- The same actual crossing address, now typed as a coordinate of the
conditional `rest` cube. -/
def trialScalarRestAddress
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N)
    (c : CrossingOccurrence cut g.2.2.1) : RestAddress cut dimension :=
  ⟨trialScalarAddress dimension N hN g c,
    crossingPrimitiveAddress_not_internal dimension c g.2.2.2
      (separatorTrial dimension N hN g.1 c.1.2)⟩

/-- Rest-cube support of one scalar eta. -/
def trialScalarRestSupport
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    Finset (RestAddress cut dimension) := by
  classical
  exact Finset.univ.image (trialScalarRestAddress dimension N hN g)

/-- Every actual rest support is nonempty. -/
theorem trialScalarRestSupport_nonempty
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    (trialScalarRestSupport dimension N hN g).Nonempty := by
  classical
  let c : CrossingOccurrence cut g.2.2.1 :=
    Classical.choice (crossingOccurrence_nonempty g.2.2.1)
  refine ⟨trialScalarRestAddress dimension N hN g c, ?_⟩
  simp [trialScalarRestSupport, c]

/-- Pairwise disjointness survives the coercion into the conditional rest cube. -/
theorem trialScalarRestSupport_pairwise_disjoint
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1) :
    Pairwise (fun g h : TrialScalar G cut dimension N =>
      Disjoint (trialScalarRestSupport dimension N hN g)
        (trialScalarRestSupport dimension N hN h)) := by
  classical
  intro g h hgh
  rw [Finset.disjoint_left]
  intro a hag hah
  rcases Finset.mem_image.mp hag with ⟨c, -, rfl⟩
  rcases Finset.mem_image.mp hah with ⟨d, -, hd⟩
  apply hgh
  apply trialScalar_eq_of_address_eq dimension N hN g h c d
  exact congrArg Subtype.val hd.symm

/-! ## 4. Generic finite-cube block factorization from coordinate disjointness -/

/-- Coordinates belonging to a block family. -/
abbrev BlockCoordinate {ι κ : Type*} (C : ι → Finset κ) :=
  Σ i : ι, {x : κ // x ∈ C i}

/-- Coordinates not read by any block. -/
abbrev ResidualCoordinate {ι κ : Type*} (C : ι → Finset κ) :=
  {x : κ // ∀ i : ι, x ∉ C i}

/-- Disjoint blocks plus their residual form an explicit coordinate
reindexing of the original finite cube. -/
def blockResidualCoordinateEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ι → Finset κ)
    (hdis : Pairwise (fun i j : ι => Disjoint (C i) (C j))) :
    Sum (BlockCoordinate C) (ResidualCoordinate C) ≃ κ := by
  classical
  let f : Sum (BlockCoordinate C) (ResidualCoordinate C) → κ :=
    fun s => match s with
      | Sum.inl z => z.2.1
      | Sum.inr z => z.1
  refine Equiv.ofBijective f ?_
  constructor
  · intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            rcases a with ⟨i, x⟩
            rcases b with ⟨j, y⟩
            dsimp [f] at hab
            have hij : i = j := by
              by_contra hne
              have hd := Finset.disjoint_left.mp (hdis hne)
              exact hd x.2 (by simpa [hab] using y.2)
            subst j
            have hxy : x = y := Subtype.ext hab
            subst y
            rfl
        | inr b =>
            rcases a with ⟨i, x⟩
            dsimp [f] at hab
            exfalso
            exact b.2 i (by simpa [hab] using x.2)
    | inr a =>
        cases b with
        | inl b =>
            rcases b with ⟨j, y⟩
            dsimp [f] at hab
            exfalso
            exact a.2 j (by simpa [← hab] using y.2)
        | inr b =>
            dsimp [f] at hab
            exact congrArg Sum.inr (Subtype.ext hab)
  · intro x
    by_cases hused : ∃ i : ι, x ∈ C i
    · let i : ι := Classical.choose hused
      have hxi : x ∈ C i := Classical.choose_spec hused
      exact ⟨Sum.inl ⟨i, ⟨x, hxi⟩⟩, rfl⟩
    · have hres : ∀ i : ι, x ∉ C i := by
        intro i hxi
        exact hused ⟨i, hxi⟩
      exact ⟨Sum.inr ⟨x, hres⟩, rfl⟩

/-- Reindex a function space along an equivalence of coordinate types. -/
def reindexFunctionEquiv {α β γ : Type*} (e : α ≃ β) :
    (β → γ) ≃ (α → γ) where
  toFun f a := f (e a)
  invFun g b := g (e.symm b)
  left_inv f := by
    funext b
    simp
  right_inv g := by
    funext a
    simp

/-- Functions on a sum whose left summand is a dependent sigma are exactly a
dependent family of functions, together with a residual function. -/
def sumSigmaFunctionEquiv
    {ι γ ρ : Type*} {A : ι → Type*} :
    (Sum (Σ i : ι, A i) ρ → γ) ≃
      ((∀ i : ι, A i → γ) × (ρ → γ)) where
  toFun f :=
    ⟨fun i x => f (Sum.inl ⟨i, x⟩),
      fun r => f (Sum.inr r)⟩
  invFun x s :=
    match s with
    | Sum.inl z => x.1 z.1 z.2
    | Sum.inr r => x.2 r
  left_inv f := by
    funext s
    cases s <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i a
      rfl
    · funext r
      rfl

/-- Explicit cube splitting into all disjoint support blocks plus unused
coordinates. -/
def disjointBlockCubeEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ι → Finset κ)
    (hdis : Pairwise (fun i j : ι => Disjoint (C i) (C j))) :
    (κ → Bool) ≃
      ((∀ i : ι, ({x : κ // x ∈ C i} → Bool)) ×
        (ResidualCoordinate C → Bool)) :=
  (reindexFunctionEquiv (blockResidualCoordinateEquiv C hdis)).trans
    sumSigmaFunctionEquiv

/-- The block part of `disjointBlockCubeEquiv` is literal restriction of the
original coordinate assignment. -/
theorem disjointBlockCubeEquiv_block_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (C : ι → Finset κ)
    (hdis : Pairwise (fun i j : ι => Disjoint (C i) (C j)))
    (w : κ → Bool) (i : ι) (x : {x : κ // x ∈ C i}) :
    (disjointBlockCubeEquiv C hdis w).1 i x = w x.1 := by
  rfl

/-- Averaging a function over an unused finite Boolean cube does not change its
normalized mean. -/
theorem paperMean_prod_fst_boolCube
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq ρ]
    (f : α → ℝ) :
    paperMean (fun x : α × (ρ → Bool) => f x.1) = paperMean f := by
  classical
  unfold paperMean
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hβ : (Fintype.card (ρ → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hβ]
  simp

/-- Dependent finite-product version of `paperMean_coordinateProduct`. -/
theorem paperMean_piProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (F : ∀ i : ι, Ω i → ℝ) :
    paperMean (fun w : ∀ i : ι, Ω i => ∏ i : ι, F i (w i)) =
      ∏ i : ι, paperMean (F i) := by
  classical
  unfold paperMean
  rw [Fintype.card_pi]
  push_cast
  rw [← Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_inv_distrib]

/-- Exact factorization for arbitrary observables, obtained solely from
coordinate disjointness. -/
theorem paperMean_disjointBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C : ι → Finset κ)
    (hdis : Pairwise (fun i j : ι => Disjoint (C i) (C j)))
    (F : ∀ i : ι, ({x : κ // x ∈ C i} → Bool) → ℝ) :
    paperMean (fun w : κ → Bool =>
      ∏ i : ι, F i (fun x => w x.1)) =
      ∏ i : ι, paperMean (F i) := by
  classical
  let e := disjointBlockCubeEquiv C hdis
  have he : ∀ w i, (e w).1 i = fun x => w x.1 := by
    intro w i
    funext x
    exact disjointBlockCubeEquiv_block_apply C hdis w i x
  calc
    paperMean (fun w : κ → Bool =>
        ∏ i : ι, F i (fun x => w x.1)) =
      paperMean (fun x :
          (∀ i : ι, ({x : κ // x ∈ C i} → Bool)) ×
            (ResidualCoordinate C → Bool) =>
        ∏ i : ι, F i (x.1 i)) := by
      simpa only [he] using
        (paperMean_equiv e
          (fun x :
            (∀ i : ι, ({x : κ // x ∈ C i} → Bool)) ×
              (ResidualCoordinate C → Bool) =>
            ∏ i : ι, F i (x.1 i)))
    _ = paperMean (fun x :
          ∀ i : ι, ({x : κ // x ∈ C i} → Bool) =>
        ∏ i : ι, F i (x i)) := by
      exact paperMean_prod_fst_boolCube (ρ := ResidualCoordinate C)
        (fun x : ∀ i : ι, ({x : κ // x ∈ C i} → Bool) =>
          ∏ i : ι, F i (x i))
    _ = _ := paperMean_piProduct F

/-! ## 5. One nonempty support product is one unbiased sign -/

/-- Product of the Rademacher signs in one support block. -/
def blockSign {κ : Type*} [Fintype κ]
    (w : κ → Bool) : ℝ :=
  ∏ x : κ, (rademacherSign (w x) : ℝ)

/-- A finite product of Rademacher signs is always `+1` or `-1`. -/
theorem blockSign_eq_one_or_neg_one
    {κ : Type*} [Fintype κ] (w : κ → Bool) :
    blockSign w = 1 ∨ blockSign w = -1 := by
  classical
  unfold blockSign
  generalize (Finset.univ : Finset κ) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases ih with ih | ih <;> rw [ih] <;>
        cases hb : w a <;> norm_num [rademacherSign]

/-- The mean of a nonempty product of independent Rademacher coordinates is
zero. -/
theorem paperMean_blockSign_eq_zero
    {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ] :
    paperMean (fun w : κ → Bool => blockSign w) = 0 := by
  classical
  change paperMean (fun w : κ → Bool =>
    ∏ x : κ, (rademacherSign (w x) : ℝ)) = 0
  rw [paperMean_coordinateProduct
    (F := fun _ : κ => fun b : Bool => (rademacherSign b : ℝ))]
  have hsingle :
      paperMean (fun b : Bool => (rademacherSign b : ℝ)) = 0 := by
    norm_num [paperMean, rademacherSign]
  simp [hsingle]

/-- Linearity helpers for the normalized finite mean. -/
theorem paperMean_add
    {α : Type*} [Fintype α] (f g : α → ℝ) :
    paperMean (fun x => f x + g x) = paperMean f + paperMean g := by
  classical
  unfold paperMean
  rw [Finset.sum_add_distrib]
  ring

theorem paperMean_mul
    {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    paperMean (fun x => c * f x) = c * paperMean f := by
  classical
  unfold paperMean
  rw [← Finset.mul_sum]
  ring

theorem paperMean_const
    {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    paperMean (fun _ : α => c) = c := by
  classical
  unfold paperMean
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hcard]

/-- Hence an arbitrary function of one nonempty support product has exactly the
uniform two-point law. -/
theorem paperMean_function_blockSign
    {κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    (F : ℝ → ℝ) :
    paperMean (fun w : κ → Bool => F (blockSign w)) =
      (F 1 + F (-1)) / 2 := by
  classical
  let A : ℝ := (F 1 + F (-1)) / 2
  let B : ℝ := (F 1 - F (-1)) / 2
  have hpoint : ∀ w : κ → Bool,
      F (blockSign w) = A + B * blockSign w := by
    intro w
    rcases blockSign_eq_one_or_neg_one w with h | h
    · rw [h]
      simp [A, B]
      ring
    · rw [h]
      simp [A, B]
      ring
  calc
    paperMean (fun w : κ → Bool => F (blockSign w)) =
        paperMean (fun w : κ → Bool => A + B * blockSign w) := by
      apply congrArg paperMean
      funext w
      exact hpoint w
    _ = paperMean (fun _ : κ → Bool => A) +
        paperMean (fun w : κ → Bool => B * blockSign w) := by
      exact paperMean_add _ _
    _ = A + B * paperMean (fun w : κ → Bool => blockSign w) := by
      rw [paperMean_const, paperMean_mul]
    _ = A := by rw [paperMean_blockSign_eq_zero]; ring
    _ = _ := by rfl

/-! ## 6. Instantiate the generic block law on the actual conditional rest cube -/

/-- Product sign of one actual trial scalar, read only from its actual rest
support.  The support subtype is nonempty by `trialScalarSupport_nonempty`. -/
def trialScalarEta
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N)
    (R : RestCube cut dimension) : ℝ :=
  ∏ a : {a : RestAddress cut dimension //
      a ∈ trialScalarRestSupport dimension N hN g},
    (rademacherSign (R a.1) : ℝ)

/-- The full family of eta scalars is an exact independent family under the
conditional rest-cube uniform law.  `F` is arbitrary; no independence premise
appears in the theorem. -/
theorem conditional_eta_joint_product_law
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (F : TrialScalar G cut dimension N → ℝ → ℝ) :
    paperMean (fun R : RestCube cut dimension =>
      ∏ g : TrialScalar G cut dimension N,
        F g (trialScalarEta dimension N hN g R)) =
    ∏ g : TrialScalar G cut dimension N,
      ((F g 1 + F g (-1)) / 2) := by
  classical
  let C : TrialScalar G cut dimension N →
      Finset (RestAddress cut dimension) :=
    trialScalarRestSupport dimension N hN
  have hdis : Pairwise (fun g h : TrialScalar G cut dimension N =>
      Disjoint (C g) (C h)) := by
    simpa [C] using
      trialScalarRestSupport_pairwise_disjoint dimension N hN
  let H : ∀ g : TrialScalar G cut dimension N,
      ({a : RestAddress cut dimension // a ∈ C g} → Bool) → ℝ :=
    fun g w => F g (blockSign w)
  calc
    paperMean (fun R : RestCube cut dimension =>
        ∏ g : TrialScalar G cut dimension N,
          F g (trialScalarEta dimension N hN g R)) =
      ∏ g : TrialScalar G cut dimension N, paperMean (H g) := by
        simpa [C, H, trialScalarEta, blockSign] using
          (paperMean_disjointBlocks C hdis H)
    _ = ∏ g : TrialScalar G cut dimension N,
        ((F g 1 + F g (-1)) / 2) := by
      apply Finset.prod_congr rfl
      intro g _hg
      have hs : (C g).Nonempty := by
        simpa [C] using
          (trialScalarRestSupport_nonempty dimension N hN g)
      let a : RestAddress cut dimension :=
        Classical.choose hs
      have ha : a ∈ C g := Classical.choose_spec hs
      letI : Nonempty {a : RestAddress cut dimension // a ∈ C g} :=
        ⟨⟨a, ha⟩⟩
      exact paperMean_function_blockSign (F g)

/-- Point-mass form: every prescribed sign pattern on all trial scalars has
mass exactly `(1/2)^(#TrialScalar)`, i.e. `2^{-#TrialScalar}`. -/
def signPointIndicator (q x : ℝ) : ℝ := if x = q then 1 else 0

theorem conditional_eta_pattern_mass
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (q : TrialScalar G cut dimension N → ℝ)
    (hq : ∀ g, q g = 1 ∨ q g = -1) :
    paperMean (fun R : RestCube cut dimension =>
      ∏ g : TrialScalar G cut dimension N,
        signPointIndicator (q g)
          (trialScalarEta dimension N hN g R)) =
    ((2 : ℝ)⁻¹) ^ Fintype.card (TrialScalar G cut dimension N) := by
  classical
  rw [conditional_eta_joint_product_law dimension N hN
    (fun g x => signPointIndicator (q g) x)]
  have hhalf : ∀ g : TrialScalar G cut dimension N,
      (signPointIndicator (q g) 1 + signPointIndicator (q g) (-1)) / 2 =
        (2 : ℝ)⁻¹ := by
    intro g
    rcases hq g with h | h <;> norm_num [signPointIndicator, h]
  simp_rw [hhalf]
  simp

/-- Cardinality of the scalar eta index family.  This is the exponent
`N * Σ_K Σ_{z∈B_K} m_z` from the paper statement. -/
theorem card_trialScalar
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ) :
    Fintype.card (TrialScalar G cut dimension N) =
      N *
        (∑ K : ActiveComponent G cut,
          ∑ z : AttachedRole cut K, dimension z.1) := by
  classical
  simp [TrialScalar, Fintype.card_sigma, Finset.mul_sum]

/-- The conditional point mass in the exponent form requested in P2a. -/
theorem conditional_eta_pattern_mass_explicit
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (q : TrialScalar G cut dimension N → ℝ)
    (hq : ∀ g, q g = 1 ∨ q g = -1) :
    paperMean (fun R : RestCube cut dimension =>
      ∏ g : TrialScalar G cut dimension N,
        signPointIndicator (q g)
          (trialScalarEta dimension N hN g R)) =
    ((2 : ℝ)⁻¹) ^
      (N * (∑ K : ActiveComponent G cut,
        ∑ z : AttachedRole cut K, dimension z.1)) := by
  rw [conditional_eta_pattern_mass dimension N hN q hq]
  rw [card_trialScalar dimension N]


/-! ## 7. Unconditional factorization of component-internal events -/

/-- The actual internal primitive-coordinate block of one active component. -/
def componentInternalSupport
    {G : PartiteShape} (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (K : ActiveComponent G cut) : Finset (PrimitiveAddress dimension) := by
  classical
  exact Finset.univ.filter fun a =>
    G.source a.1 ∈ G.c079ComponentRoles cut K.1 ∧
    G.target a.1 ∈ G.c079ComponentRoles cut K.1

/-- Different genuine active components have disjoint internal primitive
coordinate blocks.  The edge occurrence and typed labels remain part of every
coordinate. -/
theorem componentInternalSupport_pairwise_disjoint
    {G : PartiteShape} (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ) :
    Pairwise (fun K L : ActiveComponent G cut =>
      Disjoint (componentInternalSupport cut dimension K)
        (componentInternalSupport cut dimension L)) := by
  classical
  intro K L hKL
  rw [Finset.disjoint_left]
  intro a haK haL
  have hK := (Finset.mem_filter.mp haK).2
  have hL := (Finset.mem_filter.mp haL).2
  apply hKL
  exact activeComponent_eq_of_common_role K L hK.1 hL.1

/-- Arbitrary functions of different active components' internal arrays factor
exactly under the original full typed-edge uniform law.  This is the formal
finite-space interface needed for P1's componentwise internal good events. -/
theorem internalComponentFunction_product_law
    {G : PartiteShape} (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (F : ∀ K : ActiveComponent G cut,
      ({a : PrimitiveAddress dimension //
          a ∈ componentInternalSupport cut dimension K} → Bool) → ℝ) :
    paperMean (fun ε : JointEdgeSignSample dimension =>
      ∏ K : ActiveComponent G cut,
        F K (fun a => (jointSampleEquivPrimitive dimension ε) a.1)) =
      ∏ K : ActiveComponent G cut, paperMean (F K) := by
  classical
  let C : ActiveComponent G cut → Finset (PrimitiveAddress dimension) :=
    componentInternalSupport cut dimension
  have hdis : Pairwise (fun K L : ActiveComponent G cut =>
      Disjoint (C K) (C L)) := by
    simpa [C] using componentInternalSupport_pairwise_disjoint cut dimension
  let H : (PrimitiveAddress dimension → Bool) → ℝ :=
    fun w => ∏ K : ActiveComponent G cut,
      F K (fun a => w a.1)
  calc
    paperMean (fun ε : JointEdgeSignSample dimension =>
        ∏ K : ActiveComponent G cut,
          F K (fun a => (jointSampleEquivPrimitive dimension ε) a.1)) =
      paperMean H := by
        simpa [H] using
          (paperMean_equiv (jointSampleEquivPrimitive dimension) H)
    _ = ∏ K : ActiveComponent G cut, paperMean (F K) := by
      simpa [C, H] using paperMean_disjointBlocks C hdis F

/-- Indicator form of the previous theorem.  Its left side is the indicator of
simultaneous occurrence of all component-local events; the right side is the
product of their exact finite probabilities. -/
theorem internalComponentEvent_product_law
    {G : PartiteShape} (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (A : ∀ K : ActiveComponent G cut,
      ({a : PrimitiveAddress dimension //
          a ∈ componentInternalSupport cut dimension K} → Bool) → Prop)
    [hA : ∀ K, DecidablePred (A K)] :
    paperMean (fun ε : JointEdgeSignSample dimension =>
      ∏ K : ActiveComponent G cut,
        if A K (fun a => (jointSampleEquivPrimitive dimension ε) a.1)
        then (1 : ℝ) else 0) =
      ∏ K : ActiveComponent G cut,
        paperMean (fun w => if A K w then (1 : ℝ) else 0) := by
  classical
  exact internalComponentFunction_product_law cut dimension
    (fun K w => if A K w then (1 : ℝ) else 0)

/-! ## 8. Boundary cases encoded by the same theorem -/

/-- No trials: the eta family is empty and the product law is `1 = 1`. -/
theorem conditional_eta_joint_product_law_zero_trials
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    (hN : ∀ u : SeparatorRole G cut, 0 ≤ dimension u.1)
    (F : TrialScalar G cut dimension 0 → ℝ → ℝ) :
    paperMean (fun R : RestCube cut dimension =>
      ∏ g : TrialScalar G cut dimension 0,
        F g (trialScalarEta dimension 0 hN g R)) = 1 := by
  rw [conditional_eta_joint_product_law dimension 0 hN F]
  simp

/-- If there are no active components, the eta index family is empty for every
`N`; this includes empty separator situations where no active component can be
attached. -/
theorem trialScalar_empty_of_no_active
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hact : IsEmpty (ActiveComponent G cut)) :
    IsEmpty (TrialScalar G cut dimension N) := by
  letI : IsEmpty (ActiveComponent G cut) := hact
  constructor
  intro g
  exact isEmptyElim g.2.1

/-! ## 9. PaperShape bridge

`PaperShape.toPartiteShape_source/target` are definitional (`rfl`), so every
address above retains the original paper edge occurrence and original stored
orientation.  The following theorem records that no coordinate renaming occurs
in the bridge. -/

@[simp] theorem paperPrimitiveAddress_source_target
    (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin G.edges)
    (a : Fin (dimension (G.source e)))
    (b : Fin (dimension (G.target e))) :
    (jointSampleEquivPrimitive (G := G.toPartiteShape) dimension
      (fun e ab => false) ⟨e, (a, b)⟩) = false := rfl


end P2a
end GraphMatrixReplica
