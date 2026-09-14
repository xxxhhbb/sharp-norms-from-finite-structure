import R6.C079MaxPackingBoundaryComponent

/-!
Scratch-only component-side partition of the *full* graph outside a separator.
It is a combinatorial assignment of roles, not yet the set of primitive
coordinates actually observed after conditioning away R16 active components.
-/

noncomputable section

namespace GraphMatrixReplica.PaperR16.SeparatorScratch

variable (G : PartiteShape) (cut : Finset (Fin G.roles))

def cutComponentOf (v : Fin G.roles) (hv : v ∉ cut) :
    G.C079CutComponent cut :=
  (G.c079CutGraph cut).connectedComponentMk ⟨v, hv⟩

def componentMeetsRight (c : G.C079CutComponent cut) : Prop :=
  ∃ v ∈ G.c079ComponentRoles cut c, v ∈ G.rightBoundary

def componentMeetsLeft (c : G.C079CutComponent cut) : Prop :=
  ∃ v ∈ G.c079ComponentRoles cut c, v ∈ G.leftBoundary

theorem separator_component_not_both
    (hSep : G.IsRightLeftSeparator cut)
    (c : G.C079CutComponent cut) :
    ¬ (componentMeetsRight G cut c ∧ componentMeetsLeft G cut c) := by
  rintro ⟨hR, hL⟩
  obtain ⟨v, hv, path, hAvoid⟩ :=
    G.c079_bothBoundaryComponent_gives_avoidingPath cut c hR hL
  obtain ⟨o, ho⟩ := hSep v hv path
  exact hAvoid o ho

def componentSide (c : G.C079CutComponent cut) : Bool := by
  classical
  exact decide (componentMeetsRight G cut c)

def rowRoles : Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∈ cut ∨ ∃ hv : v ∉ cut,
      componentSide G cut (cutComponentOf G cut v hv) = false

def colRoles : Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∈ cut ∨ ∃ hv : v ∉ cut,
      componentSide G cut (cutComponentOf G cut v hv) = true

theorem vertex_mem_own_component (v : Fin G.roles) (hv : v ∉ cut) :
    v ∈ G.c079ComponentRoles cut (cutComponentOf G cut v hv) := by
  apply (G.mem_c079ComponentRoles_iff cut _ v).2
  exact ⟨hv, rfl⟩

theorem cutComponentOf_eq_of_edge
    {v w : Fin G.roles} (hv : v ∉ cut) (hw : w ∉ cut)
    (e : Fin G.edges) (hve : G.EdgeIncident e v)
    (hwe : G.EdgeIncident e w) :
    cutComponentOf G cut v hv = cutComponentOf G cut w hw := by
  have hvComp := vertex_mem_own_component G cut v hv
  have hwComp := G.c079ComponentRoles_edge_closed_outside_cut cut
    (cutComponentOf G cut v hv) hvComp e hve hwe hw
  exact (G.mem_c079ComponentRoles_iff cut _ w).mp hwComp |>.2.symm

theorem mem_rowRoles_of_cut {v : Fin G.roles} (hv : v ∈ cut) :
    v ∈ rowRoles G cut := by
  classical
  simp [rowRoles, hv]

theorem mem_colRoles_of_cut {v : Fin G.roles} (hv : v ∈ cut) :
    v ∈ colRoles G cut := by
  classical
  simp [colRoles, hv]

theorem mem_rowRoles_of_side_false {v : Fin G.roles} (hv : v ∉ cut)
    (hSide : componentSide G cut (cutComponentOf G cut v hv) = false) :
    v ∈ rowRoles G cut := by
  classical
  simp [rowRoles, hv, hSide]

theorem mem_colRoles_of_side_true {v : Fin G.roles} (hv : v ∉ cut)
    (hSide : componentSide G cut (cutComponentOf G cut v hv) = true) :
    v ∈ colRoles G cut := by
  classical
  simp [colRoles, hv, hSide]

theorem edge_has_single_component_side (e : Fin G.edges) :
    (G.source e ∈ rowRoles G cut ∧ G.target e ∈ rowRoles G cut) ∨
      (G.source e ∈ colRoles G cut ∧ G.target e ∈ colRoles G cut) := by
  classical
  by_cases hs : G.source e ∈ cut
  · by_cases ht : G.target e ∈ cut
    · exact Or.inl ⟨mem_rowRoles_of_cut G cut hs,
        mem_rowRoles_of_cut G cut ht⟩
    · cases hSide : componentSide G cut
          (cutComponentOf G cut (G.target e) ht) with
      | false =>
          exact Or.inl ⟨mem_rowRoles_of_cut G cut hs,
            mem_rowRoles_of_side_false G cut ht hSide⟩
      | true =>
          exact Or.inr ⟨mem_colRoles_of_cut G cut hs,
            mem_colRoles_of_side_true G cut ht hSide⟩
  · by_cases ht : G.target e ∈ cut
    · cases hSide : componentSide G cut
          (cutComponentOf G cut (G.source e) hs) with
      | false =>
          exact Or.inl ⟨mem_rowRoles_of_side_false G cut hs hSide,
            mem_rowRoles_of_cut G cut ht⟩
      | true =>
          exact Or.inr ⟨mem_colRoles_of_side_true G cut hs hSide,
            mem_colRoles_of_cut G cut ht⟩
    · have hComp := cutComponentOf_eq_of_edge G cut hs ht e
        (Or.inl rfl) (Or.inr rfl)
      cases hSide : componentSide G cut
          (cutComponentOf G cut (G.source e) hs) with
      | false =>
          have hTargetSide : componentSide G cut
              (cutComponentOf G cut (G.target e) ht) = false := by
            rw [← hComp, hSide]
          exact Or.inl ⟨mem_rowRoles_of_side_false G cut hs hSide,
            mem_rowRoles_of_side_false G cut ht hTargetSide⟩
      | true =>
          have hTargetSide : componentSide G cut
              (cutComponentOf G cut (G.target e) ht) = true := by
            rw [← hComp, hSide]
          exact Or.inr ⟨mem_colRoles_of_side_true G cut hs hSide,
            mem_colRoles_of_side_true G cut ht hTargetSide⟩

theorem rightBoundary_subset_colRoles :
    G.rightBoundary ⊆ colRoles G cut := by
  classical
  intro v hvRight
  by_cases hvCut : v ∈ cut
  · simp [colRoles, hvCut]
  · have hRight : componentMeetsRight G cut
        (cutComponentOf G cut v hvCut) :=
      ⟨v, vertex_mem_own_component G cut v hvCut, hvRight⟩
    have hSide : componentSide G cut
        (cutComponentOf G cut v hvCut) = true := by
      simp [componentSide, hRight]
    simp [colRoles, hvCut, hSide]

theorem leftBoundary_subset_rowRoles
    (hSep : G.IsRightLeftSeparator cut) :
    G.leftBoundary ⊆ rowRoles G cut := by
  classical
  intro v hvLeft
  by_cases hvCut : v ∈ cut
  · simp [rowRoles, hvCut]
  · have hLeft : componentMeetsLeft G cut
        (cutComponentOf G cut v hvCut) :=
      ⟨v, vertex_mem_own_component G cut v hvCut, hvLeft⟩
    have hNotRight : ¬ componentMeetsRight G cut
        (cutComponentOf G cut v hvCut) := by
      intro hRight
      exact separator_component_not_both G cut hSep _ ⟨hRight, hLeft⟩
    have hSide : componentSide G cut
        (cutComponentOf G cut v hvCut) = false := by
      simp [componentSide, hNotRight]
    simp [rowRoles, hvCut, hSide]

theorem componentRoles_union_eq_univ :
    rowRoles G cut ∪ colRoles G cut = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  by_cases hv : v ∈ cut
  · simp [rowRoles, colRoles, hv]
  · cases hSide : componentSide G cut (cutComponentOf G cut v hv) with
    | false =>
        simp [rowRoles, colRoles, hv, hSide]
    | true =>
        simp [rowRoles, colRoles, hv, hSide]

theorem componentRoles_inter_eq_cut :
    rowRoles G cut ∩ colRoles G cut = cut := by
  classical
  ext v
  by_cases hv : v ∈ cut
  · simp [rowRoles, colRoles, hv]
  · cases hSide : componentSide G cut (cutComponentOf G cut v hv) with
    | false =>
        simp [rowRoles, colRoles, hv, hSide]
    | true =>
        simp [rowRoles, colRoles, hv, hSide]

#print axioms separator_component_not_both
#print axioms cutComponentOf_eq_of_edge
#print axioms edge_has_single_component_side
#print axioms rightBoundary_subset_colRoles
#print axioms leftBoundary_subset_rowRoles
#print axioms componentRoles_union_eq_univ
#print axioms componentRoles_inter_eq_cut

end GraphMatrixReplica.PaperR16.SeparatorScratch
