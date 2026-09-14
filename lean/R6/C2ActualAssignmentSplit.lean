import R6.PaperR16ActualPrimitiveObservations
import R6.P2aComponentContraction

/-!
# C2 actual assignment/sample split

Deterministic bookkeeping for the actual typed partite model.  This file does
not replace the original edge arrays: it partitions their genuine edge IDs into
fresh and nonfresh occurrences, and partitions complete role assignments into
retained labels and labels on the genuine active components of `G - cut`.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.PaperR16.C2Actual

open GraphMatrixReplica
open GraphMatrixReplica.P2a
open GraphMatrixReplica.PaperR16.ActualPrimitiveObservations

attribute [local instance] Classical.propDecidable

variable {G : PartiteShape} (cut : Finset (Fin G.roles))
variable (dimension : Fin G.roles → ℕ)

abbrev RetainedRole := {v : Fin G.roles // v ∈ retainedRoles G cut}
abbrev RetainedAssignment := ∀ v : RetainedRole cut, Fin (dimension v.1)
abbrev ActiveFamilyAssignment :=
  ∀ K : ActiveComponent G cut, ComponentAssignment dimension K

abbrev ActualFreshEdge := FreshEdge G cut
abbrev NonfreshEdge := {e : Fin G.edges // ¬ Fresh G cut e}

abbrev FreshSample :=
  ∀ e : ActualFreshEdge cut, EdgeSignCoordinate dimension e.1 → Bool

abbrev FrozenSample :=
  ∀ e : NonfreshEdge cut, EdgeSignCoordinate dimension e.1 → Bool

/-- Assemble the actual original edge sample from the two complementary sets of
original edge IDs. -/
def assembleSample (ω : FrozenSample cut dimension) (ξ : FreshSample cut dimension) :
    JointEdgeSignSample dimension :=
  fun e ab => if h : Fresh G cut e then ξ ⟨e, h⟩ ab else ω ⟨e, h⟩ ab

@[simp] theorem assembleSample_fresh
    (ω : FrozenSample cut dimension) (ξ : FreshSample cut dimension)
    (e : ActualFreshEdge cut) (ab : EdgeSignCoordinate dimension e.1) :
    assembleSample cut dimension ω ξ e.1 ab = ξ e ab := by
  simp [assembleSample, e.2]

@[simp] theorem assembleSample_nonfresh
    (ω : FrozenSample cut dimension) (ξ : FreshSample cut dimension)
    (e : NonfreshEdge cut) (ab : EdgeSignCoordinate dimension e.1) :
    assembleSample cut dimension ω ξ e.1 ab = ω e ab := by
  simp [assembleSample, e.2]

/-- Exact splitting of the genuine `JointEdgeSignSample`; no random coordinate
is copied or dropped. -/
def sampleSplitEquiv :
    JointEdgeSignSample dimension ≃
      (FrozenSample cut dimension × FreshSample cut dimension) where
  toFun ε :=
    ⟨fun e ab => ε e.1 ab, fun e ab => ε e.1 ab⟩
  invFun p := assembleSample cut dimension p.1 p.2
  left_inv ε := by
    funext e ab
    by_cases h : Fresh G cut e <;> simp [assembleSample, h]
  right_inv p := by
    apply Prod.ext
    · funext e ab
      simp [assembleSample, e.2]
    · funext e ab
      simp [assembleSample, e.2]

/-- Choose the unique genuine active component containing a role known to lie
in the active union. -/
def activeComponentOfMem (v : Fin G.roles) (hv : v ∈ activeUnion G cut) :
    ActiveComponent G cut :=
  let h := (mem_activeUnion_iff G cut v).1 hv
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem activeComponentOfMem_mem (v : Fin G.roles)
    (hv : v ∈ activeUnion G cut) :
    v ∈ G.c079ComponentRoles cut (activeComponentOfMem cut v hv).1 := by
  let h := (mem_activeUnion_iff G cut v).1 hv
  change v ∈ G.c079ComponentRoles cut (Classical.choose h)
  exact (Classical.choose_spec h).2

/-- Uniqueness of the chosen active component. -/
theorem activeComponentOfMem_eq (v : Fin G.roles)
    (hv : v ∈ activeUnion G cut) (K : ActiveComponent G cut)
    (hvK : v ∈ G.c079ComponentRoles cut K.1) :
    activeComponentOfMem cut v hv = K := by
  exact activeComponent_eq_of_common_role
    (activeComponentOfMem cut v hv) K
    (activeComponentOfMem_mem cut v hv) hvK

/-- Every full typed assignment is exactly a retained assignment together with
one assignment on every actual active component. -/
def fullAssignmentEquiv :
    PartiteRoleAssignment dimension ≃
      (RetainedAssignment cut dimension × ActiveFamilyAssignment cut dimension) where
  toFun φ :=
    ⟨fun v => φ v.1,
      fun K v => φ v.1⟩
  invFun p v := by
    classical
    by_cases hvR : v ∈ retainedRoles G cut
    · exact p.1 ⟨v, hvR⟩
    · have hvD : v ∈ activeUnion G cut := by
        by_contra hnot
        exact hvR ((mem_retainedRoles_iff G cut v).2 hnot)
      let K := activeComponentOfMem cut v hvD
      exact p.2 K ⟨v, activeComponentOfMem_mem cut v hvD⟩
  left_inv φ := by
    funext v
    classical
    by_cases hvR : v ∈ retainedRoles G cut
    · simp [hvR]
    · have hvD : v ∈ activeUnion G cut := by
        by_contra hnot
        exact hvR ((mem_retainedRoles_iff G cut v).2 hnot)
      simp [hvR]
  right_inv p := by
    classical
    apply Prod.ext
    · funext v
      simp [v.2]
    · funext K v
      have hvD : v.1 ∈ activeUnion G cut :=
        (mem_activeUnion_iff G cut v.1).2 ⟨K.1, K.2, v.2⟩
      have hvR : v.1 ∉ retainedRoles G cut := by
        intro hR
        exact (mem_retainedRoles_iff G cut v.1).1 hR hvD
      have hK : activeComponentOfMem cut v.1 hvD = K :=
        activeComponentOfMem_eq cut v.1 hvD K v.2
      change (if h : v.1 ∈ retainedRoles G cut then p.1 ⟨v.1, h⟩ else
        p.2 (activeComponentOfMem cut v.1 hvD)
          ⟨v.1, activeComponentOfMem_mem cut v.1 hvD⟩) = p.2 K v
      simp only [dif_neg hvR]
      have transport (L K : ActiveComponent G cut) (h : L = K)
          (u : Fin G.roles) (huL : u ∈ G.c079ComponentRoles cut L.1)
          (huK : u ∈ G.c079ComponentRoles cut K.1) :
          p.2 L ⟨u, huL⟩ = p.2 K ⟨u, huK⟩ := by
        cases h
        rfl
      exact transport _ _ hK _ _ _

@[simp] theorem fullAssignmentEquiv_apply_retained
    (φ : PartiteRoleAssignment dimension) (v : RetainedRole cut) :
    (fullAssignmentEquiv cut dimension φ).1 v = φ v.1 := rfl

@[simp] theorem fullAssignmentEquiv_apply_component
    (φ : PartiteRoleAssignment dimension) (K : ActiveComponent G cut)
    (v : ComponentRole K) :
    (fullAssignmentEquiv cut dimension φ).2 K v = φ v.1 := rfl


@[simp] theorem fullAssignmentEquiv_symm_retained
    (p : RetainedAssignment cut dimension × ActiveFamilyAssignment cut dimension)
    (v : RetainedRole cut) :
    (fullAssignmentEquiv cut dimension).symm p v.1 = p.1 v := by
  have h := congrArg Prod.fst ((fullAssignmentEquiv cut dimension).apply_symm_apply p)
  exact congrFun h v

@[simp] theorem fullAssignmentEquiv_symm_component
    (p : RetainedAssignment cut dimension × ActiveFamilyAssignment cut dimension)
    (K : ActiveComponent G cut) (v : ComponentRole K) :
    (fullAssignmentEquiv cut dimension).symm p v.1 = p.2 K v := by
  have h := congrArg Prod.snd ((fullAssignmentEquiv cut dimension).apply_symm_apply p)
  exact congrFun (congrFun h K) v

/-- A nonfresh original edge has at least one endpoint in the actual active
union. -/
theorem nonfresh_has_active_endpoint (e : NonfreshEdge cut) :
    G.source e.1 ∈ activeUnion G cut ∨ G.target e.1 ∈ activeUnion G cut := by
  classical
  by_cases hs : G.source e.1 ∈ activeUnion G cut
  · exact Or.inl hs
  · right
    by_contra ht
    apply e.2
    exact ⟨(mem_retainedRoles_iff G cut _).2 hs,
      (mem_retainedRoles_iff G cut _).2 ht⟩

/-- Canonical owner of a nonfresh edge: the active component containing its
first active endpoint.  The next lemmas show that this does not depend on which
active endpoint is selected. -/
def nonfreshOwner (e : NonfreshEdge cut) : ActiveComponent G cut := by
  classical
  by_cases hs : G.source e.1 ∈ activeUnion G cut
  · exact activeComponentOfMem cut (G.source e.1) hs
  · have ht : G.target e.1 ∈ activeUnion G cut :=
      (nonfresh_has_active_endpoint cut e).resolve_left hs
    exact activeComponentOfMem cut (G.target e.1) ht

/-- For an owned nonfresh edge, its source is either in the owner or in the
separator. -/
theorem nonfresh_source_mem_owner_or_cut (e : NonfreshEdge cut) :
    G.source e.1 ∈ G.c079ComponentRoles cut (nonfreshOwner cut e).1 ∨
      G.source e.1 ∈ cut := by
  classical
  unfold nonfreshOwner
  by_cases hsD : G.source e.1 ∈ activeUnion G cut
  · left
    simpa [hsD] using activeComponentOfMem_mem cut (G.source e.1) hsD
  · have htD : G.target e.1 ∈ activeUnion G cut :=
      (nonfresh_has_active_endpoint cut e).resolve_left hsD
    by_cases hsCut : G.source e.1 ∈ cut
    · exact Or.inr hsCut
    · left
      have htK := activeComponentOfMem_mem cut (G.target e.1) htD
      simpa [hsD, htD] using
        G.c079ComponentRoles_edge_closed_outside_cut cut
          (activeComponentOfMem cut (G.target e.1) htD).1 htK e.1
          (Or.inr rfl) (Or.inl rfl) hsCut

/-- The target analogue. -/
theorem nonfresh_target_mem_owner_or_cut (e : NonfreshEdge cut) :
    G.target e.1 ∈ G.c079ComponentRoles cut (nonfreshOwner cut e).1 ∨
      G.target e.1 ∈ cut := by
  classical
  unfold nonfreshOwner
  by_cases hsD : G.source e.1 ∈ activeUnion G cut
  · by_cases htCut : G.target e.1 ∈ cut
    · exact Or.inr htCut
    · left
      have hsK := activeComponentOfMem_mem cut (G.source e.1) hsD
      simpa [hsD] using
        G.c079ComponentRoles_edge_closed_outside_cut cut
          (activeComponentOfMem cut (G.source e.1) hsD).1 hsK e.1
          (Or.inl rfl) (Or.inr rfl) htCut
  · have htD : G.target e.1 ∈ activeUnion G cut :=
      (nonfresh_has_active_endpoint cut e).resolve_left hsD
    left
    simpa [hsD, htD] using activeComponentOfMem_mem cut (G.target e.1) htD

/-- No original edge can join two distinct active components. -/
theorem edge_no_distinct_active_components
    (K L : ActiveComponent G cut) (e : Fin G.edges)
    (hs : G.source e ∈ G.c079ComponentRoles cut K.1)
    (ht : G.target e ∈ G.c079ComponentRoles cut L.1) : K = L := by
  have htOut : G.target e ∉ cut := componentRole_not_mem_cut ht
  have htK : G.target e ∈ G.c079ComponentRoles cut K.1 :=
    G.c079ComponentRoles_edge_closed_outside_cut cut K.1 hs e
      (Or.inl rfl) (Or.inr rfl) htOut
  exact activeComponent_eq_of_common_role K L htK ht

/-- If either endpoint of a nonfresh edge lies in an active component, that
component is exactly its canonical owner. -/
theorem nonfresh_owner_eq_of_source_mem (e : NonfreshEdge cut)
    (K : ActiveComponent G cut)
    (hsK : G.source e.1 ∈ G.c079ComponentRoles cut K.1) :
    nonfreshOwner cut e = K := by
  have hsD : G.source e.1 ∈ activeUnion G cut :=
    (mem_activeUnion_iff G cut _).2 ⟨K.1, K.2, hsK⟩
  unfold nonfreshOwner
  simp only [hsD, dif_pos]
  exact activeComponentOfMem_eq cut (G.source e.1) hsD K hsK

theorem nonfresh_owner_eq_of_target_mem (e : NonfreshEdge cut)
    (K : ActiveComponent G cut)
    (htK : G.target e.1 ∈ G.c079ComponentRoles cut K.1) :
    nonfreshOwner cut e = K := by
  classical
  by_cases hsD : G.source e.1 ∈ activeUnion G cut
  · let L := activeComponentOfMem cut (G.source e.1) hsD
    have hsL : G.source e.1 ∈ G.c079ComponentRoles cut L.1 :=
      activeComponentOfMem_mem cut (G.source e.1) hsD
    have hLK : L = K := edge_no_distinct_active_components cut L K e.1 hsL htK
    unfold nonfreshOwner
    simpa [hsD, L] using hLK
  · have htD : G.target e.1 ∈ activeUnion G cut :=
      (nonfresh_has_active_endpoint cut e).resolve_left hsD
    unfold nonfreshOwner
    simp only [hsD, dif_neg]
    exact activeComponentOfMem_eq cut (G.target e.1) htD K htK

abbrev OwnedNonfreshEdge (K : ActiveComponent G cut) :=
  {e : NonfreshEdge cut // nonfreshOwner cut e = K}

/-- The nonfresh edge set is the disjoint sigma-union of the edge sets owned by
actual active components. -/
def nonfreshEdgeOwnerEquiv :
    NonfreshEdge cut ≃ Σ K : ActiveComponent G cut, OwnedNonfreshEdge cut K where
  toFun e := ⟨nonfreshOwner cut e, ⟨e, rfl⟩⟩
  invFun z := z.2.1
  left_inv e := rfl
  right_inv z := by
    rcases z with ⟨K, e, he⟩
    dsimp
    cases he
    rfl

/-- After the owner has been fixed, every endpoint outside the component is
literally a separator endpoint. -/
theorem owned_source_mem_component_or_cut (K : ActiveComponent G cut)
    (e : OwnedNonfreshEdge cut K) :
    G.source e.1.1 ∈ G.c079ComponentRoles cut K.1 ∨ G.source e.1.1 ∈ cut := by
  have h := nonfresh_source_mem_owner_or_cut cut e.1
  simpa [e.2] using h

theorem owned_target_mem_component_or_cut (K : ActiveComponent G cut)
    (e : OwnedNonfreshEdge cut K) :
    G.target e.1.1 ∈ G.c079ComponentRoles cut K.1 ∨ G.target e.1.1 ∈ cut := by
  have h := nonfresh_target_mem_owner_or_cut cut e.1
  simpa [e.2] using h

#print axioms sampleSplitEquiv
#print axioms fullAssignmentEquiv
#print axioms nonfresh_has_active_endpoint
#print axioms edge_no_distinct_active_components
#print axioms nonfreshEdgeOwnerEquiv

end GraphMatrixReplica.PaperR16.C2Actual
