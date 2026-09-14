import GraphMatrix.Main.BoundaryCoreShape
import GraphMatrix.Counting.DisjointPathLayerCount
import GraphMatrix.FiniteMengerCertificate

noncomputable section
namespace GraphMatrixReplica
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

def mainCoreLiftPath (G : PaperShape) {v : Fin (mainBoundaryCoreShape G).toPartiteShape.roles}
    (path : (mainBoundaryCoreShape G).toPartiteShape.EdgePathToLeft v) :
    G.toPartiteShape.EdgePathToLeft (mainCoreInclude G v) :=
  match path with
  | .finish v hv => .finish _ ((main_core_left_iff G v).mp hv)
  | .step e w hStart hEnd tail => .step ((mainCoreEdgeIso G) e).1 (mainCoreInclude G w)
      ((main_core_incident_iff G e _).mp hStart)
      ((main_core_incident_iff G e w).mp hEnd) (mainCoreLiftPath G tail)

def mainCoreReducePath (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v) : ∀ hv : v ∈ mainCoreRoles G,
      (mainBoundaryCoreShape G).toPartiteShape.EdgePathToLeft (mainCoreIndex G v hv) := by
  induction path with
  | finish v hl =>
    intro hv
    exact .finish _ ((main_core_left_iff G _).mpr (by simpa using hl))
  | @step v e w hStart hEnd tail ih =>
    intro hv
    have he := main_incident_coreEdge G e hv hStart
    have hw := main_coreRoles_edgeClosed G v hv e w hStart hEnd
    let en := (mainCoreEdgeIso G).symm ⟨e, he⟩
    apply PartiteShape.EdgePathToLeft.step en (mainCoreIndex G w hw)
    · apply (main_core_incident_iff G en _).mpr
      simpa [en] using hStart
    · apply (main_core_incident_iff G en _).mpr
      simpa [en] using hEnd
    · exact ih hw

theorem mainCore_path_hits_of_occurrence {H : PartiteShape} {v : Fin H.roles}
    (path : H.EdgePathToLeft v) (cut : Finset (Fin H.roles)) :
    ∀ o, path.vertexAt o ∈ cut → path.Hits cut := by
  induction path with
  | finish v hv => intro o ho; exact ho
  | @step v e w hStart hEnd tail ih =>
    intro o
    refine Fin.cases ?_ (fun i => ?_) o
    · intro ho; exact Or.inl ho
    · intro ho; exact Or.inr (ih i ho)

def mainCoreLiftCut (G : PaperShape) (cut : Finset (Fin (mainBoundaryCoreShape G).roles)) :
    Finset (Fin G.roles) := cut.map (mainCoreInclude G)

def mainCorePullCut (G : PaperShape) (cut : Finset (Fin G.roles)) :
    Finset (Fin (mainBoundaryCoreShape G).roles) :=
  Finset.univ.filter fun v => mainCoreInclude G v ∈ cut

@[simp] theorem main_coreIndex_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (v : Fin G.roles) (hv : v ∈ mainCoreRoles G) :
    mainCoreIndex G v hv ∈ cut ↔ v ∈ mainCoreLiftCut G cut := by
  constructor
  · intro h
    exact Finset.mem_map.mpr ⟨mainCoreIndex G v hv, h, main_coreInclude_index G v hv⟩
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp h
    have hi : u = mainCoreIndex G v hv :=
      (mainCoreInclude G).injective (he.trans (main_coreInclude_index G v hv).symm)
    simpa only [hi] using hu

theorem main_coreLiftPath_hits_pullCut (G : PaperShape)
    {v : Fin (mainBoundaryCoreShape G).toPartiteShape.roles}
    (path : (mainBoundaryCoreShape G).toPartiteShape.EdgePathToLeft v)
    (cut : Finset (Fin G.roles)) :
    (mainCoreLiftPath G path).Hits cut ↔ path.Hits (mainCorePullCut G cut) := by
  induction path with
  | finish v hv => simp [mainCoreLiftPath, PartiteShape.EdgePathToLeft.Hits, mainCorePullCut]
  | @step v e w hStart hEnd tail ih =>
    simpa [mainCoreLiftPath, PartiteShape.EdgePathToLeft.Hits, mainCorePullCut] using or_congr Iff.rfl ih

theorem main_coreReducePath_hits_liftCut (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v) (hv : v ∈ mainCoreRoles G)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles)) :
    (mainCoreReducePath G path hv).Hits cut ↔ path.Hits (mainCoreLiftCut G cut) := by
  induction path with
  | finish v hLeft =>
    simpa only [mainCoreReducePath, PartiteShape.EdgePathToLeft.Hits] using
      main_coreIndex_mem_liftCut G cut v hv
  | @step v e w hStart hEnd tail ih =>
    simpa only [mainCoreReducePath, PartiteShape.EdgePathToLeft.Hits] using
      or_congr (main_coreIndex_mem_liftCut G cut v hv)
        (ih (main_coreRoles_edgeClosed G v hv e w hStart hEnd))

theorem main_core_separator_pullCut (G : PaperShape) (cut : Finset (Fin G.roles))
    (h : G.toPartiteShape.IsRightLeftSeparator cut) :
    (mainBoundaryCoreShape G).toPartiteShape.IsRightLeftSeparator (mainCorePullCut G cut) := by
  intro v hv path
  obtain ⟨o, ho⟩ := h (mainCoreInclude G v) ((main_core_right_iff G v).mp hv) (mainCoreLiftPath G path)
  have hh := mainCore_path_hits_of_occurrence (mainCoreLiftPath G path) cut o ho
  exact path.exists_hitOccurrence _ ((main_coreLiftPath_hits_pullCut G path cut).mp hh)

theorem main_core_separator_liftCut (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (h : (mainBoundaryCoreShape G).toPartiteShape.IsRightLeftSeparator cut) :
    G.toPartiteShape.IsRightLeftSeparator (mainCoreLiftCut G cut) := by
  intro v hv path
  have hCore : v ∈ mainCoreRoles G := by
    obtain ⟨i, rfl⟩ := (G.mem_rightBoundaryFinset_iff v).mp hv
    exact main_right_mem_coreRoles G i
  have hRight : mainCoreIndex G v hCore ∈ (mainBoundaryCoreShape G).toPartiteShape.rightBoundary :=
    (main_core_right_iff G _).mpr (by simpa using hv)
  obtain ⟨o, ho⟩ := h _ hRight (mainCoreReducePath G path hCore)
  have hh := mainCore_path_hits_of_occurrence (mainCoreReducePath G path hCore) cut o ho
  exact path.exists_hitOccurrence _ ((main_coreReducePath_hits_liftCut G path hCore cut).mp hh)

theorem main_corePullCut_card_le (G : PaperShape) (cut : Finset (Fin G.roles)) :
    (mainCorePullCut G cut).card ≤ cut.card := by
  apply Finset.card_le_card_of_injOn (mainCoreInclude G)
  · intro v hv; exact (Finset.mem_filter.mp hv).2
  · exact (mainCoreInclude G).injective.injOn

theorem main_core_separatorNumber_eq (G : PaperShape) :
    (mainBoundaryCoreShape G).toPartiteShape.rightLeftSeparatorNumber =
      G.toPartiteShape.rightLeftSeparatorNumber := by
  let H := (mainBoundaryCoreShape G).toPartiteShape
  apply Nat.le_antisymm
  · have h := H.minimumRightLeftSeparator_isMinimum.2
      (mainCorePullCut G G.toPartiteShape.minimumRightLeftSeparator)
      (main_core_separator_pullCut G _ G.toPartiteShape.minimumRightLeftSeparator_isMinimum.1)
    exact h.trans (main_corePullCut_card_le G _)
  · have h := G.toPartiteShape.minimumRightLeftSeparator_isMinimum.2
      (mainCoreLiftCut G H.minimumRightLeftSeparator)
      (main_core_separator_liftCut G _ H.minimumRightLeftSeparator_isMinimum.1)
    simpa [mainCoreLiftCut, PartiteShape.rightLeftSeparatorNumber, H] using h

theorem main_coreLiftPullCut_eq_inter (G : PaperShape) (cut : Finset (Fin G.roles)) :
    mainCoreLiftCut G (mainCorePullCut G cut) = cut ∩ mainCoreRoles G := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hu).2, (mainCoreRoleIso G u).2⟩
  · intro hv
    obtain ⟨hc, hi⟩ := Finset.mem_inter.mp hv
    apply Finset.mem_map.mpr
    refine ⟨mainCoreIndex G v hi, ?_, main_coreInclude_index G v hi⟩
    simp [mainCorePullCut, hc]

theorem main_minSeparator_subset_core (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) : cut ⊆ mainCoreRoles G := by
  have hs := main_core_separator_liftCut G _ (main_core_separator_pullCut G cut hMin.1)
  rw [main_coreLiftPullCut_eq_inter] at hs
  have he : cut ∩ mainCoreRoles G = cut :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hMin.2 _ hs)
  rw [← he]
  exact Finset.inter_subset_right

theorem main_coreLiftCut_minimal (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (hMin : (mainBoundaryCoreShape G).toPartiteShape.IsMinimumRightLeftSeparator cut) :
    G.toPartiteShape.IsMinimumRightLeftSeparator (mainCoreLiftCut G cut) := by
  refine ⟨main_core_separator_liftCut G cut hMin.1, ?_⟩
  intro other ho
  have h := (hMin.2 _ (main_core_separator_pullCut G other ho)).trans (main_corePullCut_card_le G other)
  simpa [mainCoreLiftCut] using h

theorem main_corePullCut_minimal (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    (mainBoundaryCoreShape G).toPartiteShape.IsMinimumRightLeftSeparator (mainCorePullCut G cut) := by
  refine ⟨main_core_separator_pullCut G cut hMin.1, ?_⟩
  intro other ho
  have h := hMin.2 _ (main_core_separator_liftCut G other ho)
  have he : mainCoreLiftCut G (mainCorePullCut G cut) = cut := by
    rw [main_coreLiftPullCut_eq_inter, Finset.inter_eq_left.mpr (main_minSeparator_subset_core G cut hMin)]
  have hc := congrArg Finset.card he
  simp only [mainCoreLiftCut, Finset.card_map] at hc h
  exact hc ▸ h

end GraphMatrixReplica
