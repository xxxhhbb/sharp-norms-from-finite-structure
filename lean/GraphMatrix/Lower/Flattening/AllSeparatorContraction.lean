import GraphMatrix.Lower.Flattening.ActualAssignmentSplit

/-!
# contraction for every separator assignment

`P2a.componentContraction` is trial-indexed.  needs the same deterministic
finite contraction at an arbitrary separator tuple.  The definitions below
read the same original primitive addresses and prove compatibility with the
diagonal tuple.
-/

noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace GraphMatrixReplica.Model.C2Actual

open GraphMatrixReplica
open GraphMatrixReplica.P2a
open GraphMatrixReplica.Model.ActualPrimitiveObservations

attribute [local instance] Classical.propDecidable

variable {G : PartiteShape} (cut : Finset (Fin G.roles))
variable (dimension : Fin G.roles → ℕ)

abbrev CutAssignment :=
  ∀ u : SeparatorRole G cut, Fin (dimension u.1)

/-- The genuine rest-cube address of one crossing occurrence evaluated at an
arbitrary separator assignment. -/
def separatorRestAddress
    (s : CutAssignment cut dimension)
    {K : ActiveComponent G cut} (z : AttachedRole cut K)
    (j : Fin (dimension z.1)) (c : CrossingOccurrence cut z) :
    RestAddress cut dimension :=
  ⟨crossingPrimitiveAddress dimension c j (s c.1.2),
    crossingPrimitiveAddress_not_internal dimension c j (s c.1.2)⟩

/-- Product of all actual crossing occurrences incident to one attached role. -/
def separatorEta
    (s : CutAssignment cut dimension) (R : RestCube cut dimension)
    {K : ActiveComponent G cut} (z : AttachedRole cut K)
    (j : Fin (dimension z.1)) : ℝ :=
  ∏ c : CrossingOccurrence cut z,
    (rademacherSign (R (separatorRestAddress cut dimension s z j c)) : ℝ)

/-- Crossing part of a component monomial for an arbitrary separator tuple. -/
def componentCrossingProductAt
    (s : CutAssignment cut dimension) (R : RestCube cut dimension)
    (K : ActiveComponent G cut) (x : ComponentAssignment dimension K) : ℝ :=
  ∏ z : AttachedRole cut K,
    separatorEta cut dimension s R z (x ⟨z.1, z.2.1⟩)

/-- Arbitrary-separator version of the actual component contraction. -/
def componentContractionAt
    (I : InternalCube cut dimension) (R : RestCube cut dimension)
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut) : ℝ :=
  ∑ x : ComponentAssignment dimension K,
    componentInternalMonomial dimension I K x *
      componentCrossingProductAt cut dimension s R K x

/-- Rest-address map for a fixed scalar is injective. -/
theorem trialScalarRestAddress_injective
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    Function.Injective (trialScalarRestAddress dimension N hN g) := by
  intro c d h
  apply trialScalarAddress_injective dimension N hN g
  exact congrArg Subtype.val h

/-- The image-support subtype used in `trialScalarEta` is exactly the original
crossing-occurrence type. -/
def trialRestSupportEquiv
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) :
    CrossingOccurrence cut g.2.2.1 ≃
      {a : RestAddress cut dimension //
        a ∈ trialScalarRestSupport dimension N hN g} where
  toFun c := ⟨trialScalarRestAddress dimension N hN g c, by
    classical
    simp [trialScalarRestSupport]⟩
  invFun a := by
    classical
    exact Classical.choose (Finset.mem_image.mp a.2)
  left_inv c := by
    classical
    apply trialScalarRestAddress_injective cut dimension N hN g
    let hmem : trialScalarRestAddress dimension N hN g c ∈
        trialScalarRestSupport dimension N hN g := by
      simp [trialScalarRestSupport]
    have hs := Classical.choose_spec (Finset.mem_image.mp hmem)
    exact hs.2
  right_inv a := by
    classical
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp a.2)).2

/-- P2a's support-subtype product is just the product over the concrete
crossing occurrences. -/
theorem trialScalarEta_eq_crossingProduct
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (g : TrialScalar G cut dimension N) (R : RestCube cut dimension) :
    trialScalarEta dimension N hN g R =
      ∏ c : CrossingOccurrence cut g.2.2.1,
        (rademacherSign (R (trialScalarRestAddress dimension N hN g c)) : ℝ) := by
  classical
  unfold trialScalarEta
  let e := trialRestSupportEquiv cut dimension N hN g
  symm
  apply Fintype.prod_equiv e
  intro c
  rfl

/-- At a diagonal separator tuple, the arbitrary-separator eta is literally the
old eta. -/
theorem separatorEta_eq_trialScalarEta
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (R : RestCube cut dimension) (i : Fin N)
    (K : ActiveComponent G cut) (z : AttachedRole cut K)
    (j : Fin (dimension z.1)) :
    separatorEta cut dimension (separatorTrial dimension N hN i) R z j =
      trialScalarEta dimension N hN ⟨i, ⟨K, ⟨z, j⟩⟩⟩ R := by
  classical
  rw [trialScalarEta_eq_crossingProduct cut dimension N hN
    ⟨i, ⟨K, ⟨z, j⟩⟩⟩ R]
  unfold separatorEta separatorRestAddress trialScalarRestAddress trialScalarAddress
  apply Finset.prod_congr rfl
  intro c _
  rfl

/-- Hence the arbitrary-separator crossing product specializes to the existing
crossing product. -/
theorem componentCrossingProductAt_eq_p2a
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (R : RestCube cut dimension) (i : Fin N)
    (K : ActiveComponent G cut) (x : ComponentAssignment dimension K) :
    componentCrossingProductAt cut dimension (separatorTrial dimension N hN i)
        R K x =
      componentCrossingProduct dimension N hN R i K x := by
  classical
  unfold componentCrossingProductAt componentCrossingProduct
  apply Finset.prod_congr rfl
  intro z _
  exact separatorEta_eq_trialScalarEta cut dimension N hN R i K z
    (x ⟨z.1, z.2.1⟩)

/-- Arbitrary-separator contraction specializes exactly to P2a's old diagonal
contraction. -/
theorem componentContractionAt_eq_p2a
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (I : InternalCube cut dimension) (R : RestCube cut dimension)
    (i : Fin N) (K : ActiveComponent G cut) :
    componentContractionAt cut dimension I R (separatorTrial dimension N hN i) K =
      componentContraction dimension N hN I R i K := by
  classical
  unfold componentContractionAt componentContraction
  apply Finset.sum_congr rfl
  intro x _
  rw [componentCrossingProductAt_eq_p2a cut dimension N hN R i K x]

/-- A crossing edge is nonfresh because one endpoint is in an active component. -/
def crossingNonfreshEdge
    {K : ActiveComponent G cut} {z : AttachedRole cut K}
    (c : CrossingOccurrence cut z) : NonfreshEdge cut := by
  refine ⟨c.1.1, ?_⟩
  intro hf
  have hzD : z.1 ∈ activeUnion G cut :=
    (mem_activeUnion_iff G cut z.1).2 ⟨K.1, K.2, z.2.1⟩
  have hzR : z.1 ∉ retainedRoles G cut := by
    intro hR
    exact (mem_retainedRoles_iff G cut z.1).1 hR hzD
  apply hzR
  apply retained_of_fresh_incident G cut hf
  rcases c.2 with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

/-- An internal edge of an active component is nonfresh. -/
def internalNonfreshEdge (K : ActiveComponent G cut)
    (e : ComponentInternalEdge K) : NonfreshEdge cut := by
  refine ⟨e.1, ?_⟩
  intro hf
  have hsD : G.source e.1 ∈ activeUnion G cut :=
    (mem_activeUnion_iff G cut _).2 ⟨K.1, K.2, e.2.1⟩
  exact (mem_retainedRoles_iff G cut _).1 hf.1 hsD

/-- Canonical harmless fresh filler used only to turn a frozen nonfresh sample
back into a complete original sample. -/
def zeroFreshSample : FreshSample cut dimension := fun _ _ => false

def frozenJointSample (ω : FrozenSample cut dimension) : JointEdgeSignSample dimension :=
  assembleSample cut dimension ω (zeroFreshSample cut dimension)

def frozenInternalCube (ω : FrozenSample cut dimension) : InternalCube cut dimension :=
  (internalRestEquiv cut dimension (frozenJointSample cut dimension ω)).1

def frozenRestCube (ω : FrozenSample cut dimension) : RestCube cut dimension :=
  (internalRestEquiv cut dimension (frozenJointSample cut dimension ω)).2

/-- The internal/rest splitter reads an internal coordinate without changing it. -/
theorem internalRestEquiv_internal_apply
    (ε : JointEdgeSignSample dimension) (a : InternalAddress cut dimension) :
    (internalRestEquiv cut dimension ε).1 a = ε a.1.1 a.1.2 := by
  rfl

/-- The analogous rest-coordinate identity. -/
theorem internalRestEquiv_rest_apply
    (ε : JointEdgeSignSample dimension) (a : RestAddress cut dimension) :
    (internalRestEquiv cut dimension ε).2 a = ε a.1.1 a.1.2 := by
  rfl

/-- Frozen internal coordinates read exactly the supplied nonfresh array. -/
theorem frozenInternalCube_apply
    (ω : FrozenSample cut dimension) (K : ActiveComponent G cut)
    (e : ComponentInternalEdge K) (x : ComponentAssignment dimension K) :
    frozenInternalCube cut dimension ω (componentInternalAddress dimension K e x) =
      ω (internalNonfreshEdge cut K e)
        (x ⟨G.source e.1, e.2.1⟩, x ⟨G.target e.1, e.2.2⟩) := by
  rw [frozenInternalCube, internalRestEquiv_internal_apply]
  exact assembleSample_nonfresh cut dimension ω (zeroFreshSample cut dimension)
    (internalNonfreshEdge cut K e) _

/-- Frozen crossing coordinates likewise read the original nonfresh edge array. -/
theorem frozenRestCube_crossing_apply
    (ω : FrozenSample cut dimension) (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) (z : AttachedRole cut K)
    (j : Fin (dimension z.1)) (c : CrossingOccurrence cut z) :
    frozenRestCube cut dimension ω (separatorRestAddress cut dimension s z j c) =
      ω (crossingNonfreshEdge cut c)
        (crossingPrimitiveAddress dimension c j (s c.1.2)).2 := by
  rw [frozenRestCube, internalRestEquiv_rest_apply]
  exact assembleSample_nonfresh cut dimension ω (zeroFreshSample cut dimension)
    (crossingNonfreshEdge cut c) _

/-- The scalar `T_K(ω,s)` for every separator assignment. -/
def actualComponentContraction
    (ω : FrozenSample cut dimension) (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) : ℝ :=
  componentContractionAt cut dimension (frozenInternalCube cut dimension ω)
    (frozenRestCube cut dimension ω) s K

/-- Product weight over the actual active components. Empty active family gives
`1` by the standard empty-product convention. -/
def actualWeight
    (ω : FrozenSample cut dimension) (s : CutAssignment cut dimension) : ℝ :=
  ∏ K : ActiveComponent G cut, actualComponentContraction cut dimension ω s K


/-- The two and only two shapes of an original nonfresh edge owned by `K`:
either both endpoints lie in `K`, or exactly one endpoint lies in `K` and the
other is a concrete separator role. -/
abbrev InternalOrCrossing (K : ActiveComponent G cut) :=
  Sum (ComponentInternalEdge K)
    (Σ z : AttachedRole cut K, CrossingOccurrence cut z)

/-- Classification of every owner edge into an internal occurrence or a unique
orientation-aware crossing occurrence. -/
def ownedEdgeClassEquiv (K : ActiveComponent G cut) :
    OwnedNonfreshEdge cut K ≃ InternalOrCrossing cut K where
  toFun e := by
    classical
    by_cases hsK : G.source e.1.1 ∈ G.c079ComponentRoles cut K.1
    · by_cases htK : G.target e.1.1 ∈ G.c079ComponentRoles cut K.1
      · exact Sum.inl ⟨e.1.1, hsK, htK⟩
      · have htS := (owned_target_mem_component_or_cut cut K e).resolve_left htK
        let z : AttachedRole cut K :=
          ⟨G.source e.1.1, hsK,
            ⟨G.target e.1.1, htS, e.1.1, Or.inl ⟨rfl, rfl⟩⟩⟩
        let c : CrossingOccurrence cut z :=
          ⟨(e.1.1, ⟨G.target e.1.1, htS⟩), Or.inl ⟨rfl, rfl⟩⟩
        exact Sum.inr ⟨z, c⟩
    · have hsS := (owned_source_mem_component_or_cut cut K e).resolve_left hsK
      by_cases htK : G.target e.1.1 ∈ G.c079ComponentRoles cut K.1
      · let z : AttachedRole cut K :=
          ⟨G.target e.1.1, htK,
            ⟨G.source e.1.1, hsS, e.1.1, Or.inr ⟨rfl, rfl⟩⟩⟩
        let c : CrossingOccurrence cut z :=
          ⟨(e.1.1, ⟨G.source e.1.1, hsS⟩), Or.inr ⟨rfl, rfl⟩⟩
        exact Sum.inr ⟨z, c⟩
      · exfalso
        have htS := (owned_target_mem_component_or_cut cut K e).resolve_left htK
        apply e.1.2
        exact ⟨cut_subset_retainedRoles G cut hsS,
          cut_subset_retainedRoles G cut htS⟩
  invFun z := by
    classical
    rcases z with e | zc
    · let nf : NonfreshEdge cut := internalNonfreshEdge cut K e
      exact ⟨nf, nonfresh_owner_eq_of_source_mem cut nf K e.2.1⟩
    · rcases zc with ⟨z, c⟩
      let nf : NonfreshEdge cut := crossingNonfreshEdge cut c
      refine ⟨nf, ?_⟩
      rcases c.2 with h | h
      · exact nonfresh_owner_eq_of_source_mem cut nf K (by change G.source c.1.1 ∈ _; rw [h.1]; exact z.2.1)
      · exact nonfresh_owner_eq_of_target_mem cut nf K (by change G.target c.1.1 ∈ _; rw [h.2]; exact z.2.1)
  left_inv e := by
    classical
    dsimp
    split <;> split
    all_goals try { apply Subtype.ext; apply Subtype.ext; rfl }
    all_goals contradiction
  right_inv z := by
    classical
    rcases z with e | zc
    · dsimp [internalNonfreshEdge]
      simp only [dif_pos e.2.1, dif_pos e.2.2]
    · rcases zc with ⟨z, c⟩
      rcases c with ⟨⟨e, u⟩, hc⟩
      rcases hc with hc | hc
      · have hs : G.source e ∈ G.c079ComponentRoles cut K.1 := hc.1 ▸ z.2.1
        have ht : G.target e ∉ G.c079ComponentRoles cut K.1 := by
          intro h
          exact componentRole_not_mem_cut h (hc.2 ▸ u.2)
        dsimp only
        dsimp [crossingNonfreshEdge]
        rw [dif_pos hs, dif_neg ht]
        apply congrArg Sum.inr
        rcases z with ⟨z, hz⟩
        rcases u with ⟨u, hu⟩
        dsimp at hc
        obtain ⟨hsz, htu⟩ := hc
        subst z
        subst u
        rfl
      · have ht : G.target e ∈ G.c079ComponentRoles cut K.1 := hc.2 ▸ z.2.1
        have hs : G.source e ∉ G.c079ComponentRoles cut K.1 := by
          intro h
          exact componentRole_not_mem_cut h (hc.1 ▸ u.2)
        dsimp only
        dsimp [crossingNonfreshEdge]
        rw [dif_neg hs, dif_pos ht]
        apply congrArg Sum.inr
        rcases z with ⟨z, hz⟩
        rcases u with ⟨u, hu⟩
        dsimp at hc
        obtain ⟨hsu, htz⟩ := hc
        subst z
        subst u
        rfl

/-- Read the source label of an edge owned by `K`, using the component assignment
on a component endpoint and the arbitrary separator assignment on a cut endpoint. -/
def ownedSourceLabel
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) (e : OwnedNonfreshEdge cut K) :
    Fin (dimension (G.source e.1.1)) := by
  classical
  by_cases hsK : G.source e.1.1 ∈ G.c079ComponentRoles cut K.1
  · exact x ⟨G.source e.1.1, hsK⟩
  · exact s ⟨G.source e.1.1, (owned_source_mem_component_or_cut cut K e).resolve_left hsK⟩

/-- Target-endpoint version of `ownedSourceLabel`. -/
def ownedTargetLabel
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) (e : OwnedNonfreshEdge cut K) :
    Fin (dimension (G.target e.1.1)) := by
  classical
  by_cases htK : G.target e.1.1 ∈ G.c079ComponentRoles cut K.1
  · exact x ⟨G.target e.1.1, htK⟩
  · exact s ⟨G.target e.1.1, (owned_target_mem_component_or_cut cut K e).resolve_left htK⟩


@[simp] theorem ownedSourceLabel_of_component
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) (e : OwnedNonfreshEdge cut K)
    (hsK : G.source e.1.1 ∈ G.c079ComponentRoles cut K.1) :
    ownedSourceLabel cut dimension s K x e =
      x ⟨G.source e.1.1, hsK⟩ := by
  classical
  simp [ownedSourceLabel, hsK]

@[simp] theorem ownedSourceLabel_of_cut
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) (e : OwnedNonfreshEdge cut K)
    (hsS : G.source e.1.1 ∈ cut) :
    ownedSourceLabel cut dimension s K x e =
      s ⟨G.source e.1.1, hsS⟩ := by
  classical
  have hn : G.source e.1.1 ∉ G.c079ComponentRoles cut K.1 :=
    fun h => componentRole_not_mem_cut h hsS
  simp [ownedSourceLabel, hn]

@[simp] theorem ownedTargetLabel_of_component
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) (e : OwnedNonfreshEdge cut K)
    (htK : G.target e.1.1 ∈ G.c079ComponentRoles cut K.1) :
    ownedTargetLabel cut dimension s K x e =
      x ⟨G.target e.1.1, htK⟩ := by
  classical
  simp [ownedTargetLabel, htK]

@[simp] theorem ownedTargetLabel_of_cut
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) (e : OwnedNonfreshEdge cut K)
    (htS : G.target e.1.1 ∈ cut) :
    ownedTargetLabel cut dimension s K x e =
      s ⟨G.target e.1.1, htS⟩ := by
  classical
  have hn : G.target e.1.1 ∉ G.c079ComponentRoles cut K.1 :=
    fun h => componentRole_not_mem_cut h htS
  simp [ownedTargetLabel, hn]


/-- Owner-typed form of an internal component edge. -/
def internalOwnedEdge (K : ActiveComponent G cut) (e : ComponentInternalEdge K) :
    OwnedNonfreshEdge cut K :=
  ⟨internalNonfreshEdge cut K e,
    nonfresh_owner_eq_of_source_mem cut (internalNonfreshEdge cut K e) K e.2.1⟩

/-- Owner-typed form of a concrete crossing occurrence. -/
def crossingOwnedEdge (K : ActiveComponent G cut) (z : AttachedRole cut K)
    (c : CrossingOccurrence cut z) : OwnedNonfreshEdge cut K := by
  let nf : NonfreshEdge cut := crossingNonfreshEdge cut c
  refine ⟨nf, ?_⟩
  rcases c.2 with h | h
  · exact nonfresh_owner_eq_of_source_mem cut nf K (by change G.source c.1.1 ∈ _; rw [h.1]; exact z.2.1)
  · exact nonfresh_owner_eq_of_target_mem cut nf K (by change G.target c.1.1 ∈ _; rw [h.2]; exact z.2.1)

@[simp] theorem internalOwnedEdge_val
    (K : ActiveComponent G cut) (e : ComponentInternalEdge K) :
    (internalOwnedEdge cut K e).1.1 = e.1 := rfl

@[simp] theorem crossingOwnedEdge_val
    (K : ActiveComponent G cut) (z : AttachedRole cut K)
    (c : CrossingOccurrence cut z) :
    (crossingOwnedEdge cut K z c).1.1 = c.1.1 := rfl

/-- For a crossing occurrence, the endpoint labels recovered from the owner
classification are exactly the orientation-aware primitive coordinate used by
P2a. -/
theorem ownedLabels_crossing
    (s : CutAssignment cut dimension) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) (z : AttachedRole cut K)
    (c : CrossingOccurrence cut z) :
    (ownedSourceLabel cut dimension s K x (crossingOwnedEdge cut K z c),
      ownedTargetLabel cut dimension s K x (crossingOwnedEdge cut K z c)) =
      (crossingPrimitiveAddress dimension c
        (x ⟨z.1, z.2.1⟩) (s c.1.2)).2 := by
  classical
  rcases c with ⟨⟨e, u⟩, hc⟩
  rcases hc with hc | hc
  · have hsK : G.source e ∈ G.c079ComponentRoles cut K.1 := by
      simpa [hc.1] using z.2.1
    have htS : G.target e ∈ cut := by simpa [hc.2] using u.2
    rw [ownedSourceLabel_of_component cut dimension s K x
      (crossingOwnedEdge cut K z ⟨⟨e, u⟩, Or.inl hc⟩) hsK]
    rw [ownedTargetLabel_of_cut cut dimension s K x
      (crossingOwnedEdge cut K z ⟨⟨e, u⟩, Or.inl hc⟩) htS]
    rcases z with ⟨z, hz⟩
    rcases u with ⟨u, hu⟩
    dsimp at hc
    obtain ⟨hsz, htu⟩ := hc
    subst z
    subst u
    simp [crossingPrimitiveAddress, castRoleLabel]
  · have hsS : G.source e ∈ cut := by simpa [hc.1] using u.2
    have htK : G.target e ∈ G.c079ComponentRoles cut K.1 := by
      simpa [hc.2] using z.2.1
    rw [ownedSourceLabel_of_cut cut dimension s K x
      (crossingOwnedEdge cut K z ⟨⟨e, u⟩, Or.inr hc⟩) hsS]
    rw [ownedTargetLabel_of_component cut dimension s K x
      (crossingOwnedEdge cut K z ⟨⟨e, u⟩, Or.inr hc⟩) htK]
    rcases z with ⟨z, hz⟩
    rcases u with ⟨u, hu⟩
    dsimp at hc
    obtain ⟨hsu, htz⟩ := hc
    subst z
    subst u
    have hne : G.source e ≠ G.target e := by
      intro h
      exact componentRole_not_mem_cut htK (h ▸ hsS)
    simp [crossingPrimitiveAddress, castRoleLabel, hne]


@[simp] theorem ownedEdgeClassEquiv_symm_inl
    (K : ActiveComponent G cut) (e : ComponentInternalEdge K) :
    (ownedEdgeClassEquiv cut K).symm (Sum.inl e) = internalOwnedEdge cut K e := by
  rfl

@[simp] theorem ownedEdgeClassEquiv_symm_inr
    (K : ActiveComponent G cut) (z : AttachedRole cut K)
    (c : CrossingOccurrence cut z) :
    (ownedEdgeClassEquiv cut K).symm (Sum.inr ⟨z, c⟩) =
      crossingOwnedEdge cut K z c := by
  rfl

/-- The literal product of the frozen signs on all original nonfresh edge IDs
owned by one active component.  This is the object needed for the expansion of
`partiteBoundaryMatrix`; no edge occurrence is quotient-identified. -/
def ownedComponentMonomial
    (ω : FrozenSample cut dimension) (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) (x : ComponentAssignment dimension K) : ℝ :=
  ∏ e : OwnedNonfreshEdge cut K,
    (rademacherSign
      (ω e.1 (ownedSourceLabel cut dimension s K x e,
        ownedTargetLabel cut dimension s K x e)) : ℝ)

/-- Direct original-edge definition of the component contraction.  The equality
with `actualComponentContraction` is the first remaining graph-specific
finite-product decomposition if the later chaos connection is not yet loaded. -/
def ownedComponentContraction
    (ω : FrozenSample cut dimension) (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) : ℝ :=
  ∑ x : ComponentAssignment dimension K,
    ownedComponentMonomial cut dimension ω s K x

/-- The direct original-edge monomial is exactly the internal product times
the arbitrary-separator crossing product. -/
theorem ownedComponentMonomial_eq_internal_crossing
    (ω : FrozenSample cut dimension) (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) (x : ComponentAssignment dimension K) :
    ownedComponentMonomial cut dimension ω s K x =
      componentInternalMonomial dimension (frozenInternalCube cut dimension ω) K x *
        componentCrossingProductAt cut dimension s
          (frozenRestCube cut dimension ω) K x := by
  classical
  unfold ownedComponentMonomial
  rw [← Equiv.prod_comp (ownedEdgeClassEquiv cut K).symm]
  rw [Fintype.prod_sum_type]
  congr 1
  · unfold componentInternalMonomial
    apply Finset.prod_congr rfl
    intro e _he
    change (rademacherSign (ω (internalOwnedEdge cut K e).1
      (ownedSourceLabel cut dimension s K x (internalOwnedEdge cut K e),
       ownedTargetLabel cut dimension s K x (internalOwnedEdge cut K e))) : ℝ) = _
    rw [frozenInternalCube_apply]
    rw [ownedSourceLabel_of_component cut dimension s K x
      (internalOwnedEdge cut K e) e.2.1]
    rw [ownedTargetLabel_of_component cut dimension s K x
      (internalOwnedEdge cut K e) e.2.2]
    rfl
  · rw [Fintype.prod_sigma]
    unfold componentCrossingProductAt separatorEta
    apply Finset.prod_congr rfl
    intro z _hz
    apply Finset.prod_congr rfl
    intro c _hc
    change (rademacherSign (ω (crossingOwnedEdge cut K z c).1
      (ownedSourceLabel cut dimension s K x (crossingOwnedEdge cut K z c),
       ownedTargetLabel cut dimension s K x (crossingOwnedEdge cut K z c))) : ℝ) = _
    rw [frozenRestCube_crossing_apply]
    rw [ownedLabels_crossing cut dimension s K x z c]
    rfl

/-- Therefore the all-separator component contraction is literally the finite
sub-sum of the original frozen edge monomial on the nonfresh edges owned by K. -/
theorem ownedComponentContraction_eq_actual
    (ω : FrozenSample cut dimension) (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) :
    ownedComponentContraction cut dimension ω s K =
      actualComponentContraction cut dimension ω s K := by
  classical
  unfold ownedComponentContraction actualComponentContraction componentContractionAt
  apply Finset.sum_congr rfl
  intro x _hx
  exact ownedComponentMonomial_eq_internal_crossing cut dimension ω s K x

/-- Exact compatibility requested by on a diagonal tuple the new
all-separator contraction is the existing contraction of the restrictions
of the same original frozen primitive sample. -/
theorem actualComponentContraction_eq_p2a
    (ω : FrozenSample cut dimension)
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (i : Fin N) (K : ActiveComponent G cut) :
    actualComponentContraction cut dimension ω (separatorTrial dimension N hN i) K =
      componentContraction dimension N hN
        (frozenInternalCube cut dimension ω) (frozenRestCube cut dimension ω) i K := by
  exact componentContractionAt_eq_p2a cut dimension N hN
    (frozenInternalCube cut dimension ω) (frozenRestCube cut dimension ω) i K


end GraphMatrixReplica.Model.C2Actual
