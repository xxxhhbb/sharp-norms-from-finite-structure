import GraphMatrix.Lower.Flattening.Theorems

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open Model Model.C2Actual Model.ActualPrimitiveObservations
attribute [local instance] Classical.propDecidable

private theorem main_c2_subtype_heq {α : Type*} {P Q : α → Prop}
    (hpq : P = Q) (x : {w : α // P w}) (y : {w : α // Q w})
    (hval : x.1 = y.1) : HEq x y := by
  cases hpq
  exact heq_of_eq (Subtype.ext hval)

def mainActiveRoleSigmaEquiv (G : PartiteShape) (S : Finset (Fin G.roles)) :
    (Σ K : P2a.ActiveComponent G S, P2a.ComponentRole K) ≃ ↥(activeUnion G S) where
  toFun p := ⟨p.2.1, (mem_activeUnion_iff G S p.2.1).mpr ⟨p.1.1, p.1.2, p.2.2⟩⟩
  invFun v := ⟨activeComponentOfMem (G := G) S v.1 v.2,
    ⟨v.1, activeComponentOfMem_mem (G := G) S v.1 v.2⟩⟩
  left_inv p := by
    rcases p with ⟨K, v⟩
    have hv : v.1 ∈ activeUnion G S := (mem_activeUnion_iff G S v.1).mpr ⟨K.1, K.2, v.2⟩
    have hK := activeComponentOfMem_eq (G := G) S v.1 hv K v.2
    apply Sigma.ext hK
    apply main_c2_subtype_heq
      (congrArg (fun L : P2a.ActiveComponent G S => fun u => u ∈ G.c079ComponentRoles S L.1) hK)
    rfl
  right_inv v := Subtype.ext rfl

theorem main_active_component_roles_sum (G : PartiteShape) (S : Finset (Fin G.roles)) :
    (∑ K : P2a.ActiveComponent G S, Fintype.card (P2a.ComponentRole K)) =
      (activeUnion G S).card := by
  calc
    _ = Fintype.card (Σ K : P2a.ActiveComponent G S, P2a.ComponentRole K) := Fintype.card_sigma.symm
    _ = Fintype.card ↥(activeUnion G S) := Fintype.card_congr (mainActiveRoleSigmaEquiv G S)
    _ = _ := Fintype.card_coe _

def mainC2SeparatorRoleEquiv (P : PaperShape) (S : Finset (Fin P.roles)) :
    ↥(C1C2.separator P S) ≃ ↥S where
  toFun v := ⟨v.1.1, (Finset.mem_filter.mp v.2).2⟩
  invFun s := ⟨⟨s.1, cut_subset_retainedRoles P.toPartiteShape S s.2⟩,
    by simp [C1C2.separator, s.2]⟩
  left_inv v := Subtype.ext (Subtype.ext rfl)
  right_inv s := Subtype.ext rfl

theorem main_C2_separator_card (P : PaperShape) (S : Finset (Fin P.roles)) :
    (C1C2.separator P S).card = S.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (mainC2SeparatorRoleEquiv P S)

theorem main_C2_retained_card (P : PaperShape) (S : Finset (Fin P.roles)) :
    Fintype.card (C1C2.Retained P S) = P.roles - (activeUnion P.toPartiteShape S).card := by
  change Fintype.card ↥(retainedRoles P.toPartiteShape S) = _
  rw [Fintype.card_coe, retainedRoles, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

theorem main_twoSide_card_allocation {R : Type*} [Fintype R] [DecidableEq R]
    (row col sep : Finset R) (hcover : row ∪ col = Finset.univ) (hinter : row ∩ col = sep) :
    (row \ sep).card + (col \ sep).card + sep.card = Fintype.card R := by
  have hr : sep ⊆ row := by rw [← hinter]; exact Finset.inter_subset_left
  have hc : sep ⊆ col := by rw [← hinter]; exact Finset.inter_subset_right
  have hcard := Finset.card_union_add_card_inter row col
  rw [hcover, hinter, Finset.card_univ] at hcard
  rw [Finset.card_sdiff_of_subset hr, Finset.card_sdiff_of_subset hc]
  have hrc := Finset.card_le_card hr
  have hcc := Finset.card_le_card hc
  omega

/-- Exact allocation of all original roles between the two fresh side fibers,
the separator, and the genuine active components. -/
theorem main_C2_full_role_allocation (P : PaperShape) (S : Finset (Fin P.roles))
    (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) :
    (C1C2.rows P S \ C1C2.separator P S).card +
      (C1C2.cols P S \ C1C2.separator P S).card + S.card +
        (∑ K : P2a.ActiveComponent P.toPartiteShape S, Fintype.card (P2a.ComponentRole K)) = P.roles := by
  have hcover : C1C2.rows P S ∪ C1C2.cols P S = Finset.univ := by
    convert C1C2.actual_cover P S hNoIso hMin using 1 <;> congr!
  have h := main_twoSide_card_allocation (C1C2.rows P S) (C1C2.cols P S)
    (C1C2.separator P S) hcover (C1C2.actual_inter P S hNoIso hMin)
  rw [main_C2_separator_card, main_C2_retained_card] at h
  rw [main_active_component_roles_sum]
  have hcard : (activeUnion P.toPartiteShape S).card ≤ P.roles := by
    simpa using Finset.card_le_univ (activeUnion P.toPartiteShape S)
  omega

end GraphMatrixReplica
