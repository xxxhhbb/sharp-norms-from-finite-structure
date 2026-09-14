import R6.M1BoundaryCoreShape
import R6.C079DisjointPathLayerCount
import R6.FiniteMengerCertificate

noncomputable section
namespace GraphMatrixReplica
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

def rootCoreLiftPath (G : PaperShape) {v : Fin (rootBoundaryCoreShape G).toPartiteShape.roles}
    (path : (rootBoundaryCoreShape G).toPartiteShape.EdgePathToLeft v) :
    G.toPartiteShape.EdgePathToLeft (rootCoreInclude G v) :=
  match path with
  | .finish v hv => .finish _ ((root_core_left_iff G v).mp hv)
  | .step e w hStart hEnd tail => .step ((rootCoreEdgeIso G) e).1 (rootCoreInclude G w)
      ((root_core_incident_iff G e _).mp hStart)
      ((root_core_incident_iff G e w).mp hEnd) (rootCoreLiftPath G tail)

def rootCoreReducePath (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v) : ∀ hv : v ∈ rootCoreRoles G,
      (rootBoundaryCoreShape G).toPartiteShape.EdgePathToLeft (rootCoreIndex G v hv) := by
  induction path with
  | finish v hl =>
    intro hv
    exact .finish _ ((root_core_left_iff G _).mpr (by simpa using hl))
  | @step v e w hStart hEnd tail ih =>
    intro hv
    have he := root_incident_coreEdge G e hv hStart
    have hw := root_coreRoles_edgeClosed G v hv e w hStart hEnd
    let en := (rootCoreEdgeIso G).symm ⟨e, he⟩
    apply PartiteShape.EdgePathToLeft.step en (rootCoreIndex G w hw)
    · apply (root_core_incident_iff G en _).mpr
      simpa [en] using hStart
    · apply (root_core_incident_iff G en _).mpr
      simpa [en] using hEnd
    · exact ih hw

theorem rootCore_path_hits_of_occurrence {H : PartiteShape} {v : Fin H.roles}
    (path : H.EdgePathToLeft v) (cut : Finset (Fin H.roles)) :
    ∀ o, path.vertexAt o ∈ cut → path.Hits cut := by
  induction path with
  | finish v hv => intro o ho; exact ho
  | @step v e w hStart hEnd tail ih =>
    intro o
    refine Fin.cases ?_ (fun i => ?_) o
    · intro ho; exact Or.inl ho
    · intro ho; exact Or.inr (ih i ho)

def rootCoreLiftCut (G : PaperShape) (cut : Finset (Fin (rootBoundaryCoreShape G).roles)) :
    Finset (Fin G.roles) := cut.map (rootCoreInclude G)

def rootCorePullCut (G : PaperShape) (cut : Finset (Fin G.roles)) :
    Finset (Fin (rootBoundaryCoreShape G).roles) :=
  Finset.univ.filter fun v => rootCoreInclude G v ∈ cut

@[simp] theorem root_coreIndex_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (v : Fin G.roles) (hv : v ∈ rootCoreRoles G) :
    rootCoreIndex G v hv ∈ cut ↔ v ∈ rootCoreLiftCut G cut := by
  constructor
  · intro h
    exact Finset.mem_map.mpr ⟨rootCoreIndex G v hv, h, root_coreInclude_index G v hv⟩
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp h
    have hi : u = rootCoreIndex G v hv :=
      (rootCoreInclude G).injective (he.trans (root_coreInclude_index G v hv).symm)
    simpa only [hi] using hu

theorem root_coreLiftPath_hits_pullCut (G : PaperShape)
    {v : Fin (rootBoundaryCoreShape G).toPartiteShape.roles}
    (path : (rootBoundaryCoreShape G).toPartiteShape.EdgePathToLeft v)
    (cut : Finset (Fin G.roles)) :
    (rootCoreLiftPath G path).Hits cut ↔ path.Hits (rootCorePullCut G cut) := by
  induction path with
  | finish v hv => simp [rootCoreLiftPath, PartiteShape.EdgePathToLeft.Hits, rootCorePullCut]
  | @step v e w hStart hEnd tail ih =>
    simpa [rootCoreLiftPath, PartiteShape.EdgePathToLeft.Hits, rootCorePullCut] using or_congr Iff.rfl ih

theorem root_coreReducePath_hits_liftCut (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v) (hv : v ∈ rootCoreRoles G)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles)) :
    (rootCoreReducePath G path hv).Hits cut ↔ path.Hits (rootCoreLiftCut G cut) := by
  induction path with
  | finish v hLeft =>
    simpa only [rootCoreReducePath, PartiteShape.EdgePathToLeft.Hits] using
      root_coreIndex_mem_liftCut G cut v hv
  | @step v e w hStart hEnd tail ih =>
    simpa only [rootCoreReducePath, PartiteShape.EdgePathToLeft.Hits] using
      or_congr (root_coreIndex_mem_liftCut G cut v hv)
        (ih (root_coreRoles_edgeClosed G v hv e w hStart hEnd))

theorem root_core_separator_pullCut (G : PaperShape) (cut : Finset (Fin G.roles))
    (h : G.toPartiteShape.IsRightLeftSeparator cut) :
    (rootBoundaryCoreShape G).toPartiteShape.IsRightLeftSeparator (rootCorePullCut G cut) := by
  intro v hv path
  obtain ⟨o, ho⟩ := h (rootCoreInclude G v) ((root_core_right_iff G v).mp hv) (rootCoreLiftPath G path)
  have hh := rootCore_path_hits_of_occurrence (rootCoreLiftPath G path) cut o ho
  exact path.exists_hitOccurrence _ ((root_coreLiftPath_hits_pullCut G path cut).mp hh)

theorem root_core_separator_liftCut (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (h : (rootBoundaryCoreShape G).toPartiteShape.IsRightLeftSeparator cut) :
    G.toPartiteShape.IsRightLeftSeparator (rootCoreLiftCut G cut) := by
  intro v hv path
  have hCore : v ∈ rootCoreRoles G := by
    obtain ⟨i, rfl⟩ := (G.mem_rightBoundaryFinset_iff v).mp hv
    exact root_right_mem_coreRoles G i
  have hRight : rootCoreIndex G v hCore ∈ (rootBoundaryCoreShape G).toPartiteShape.rightBoundary :=
    (root_core_right_iff G _).mpr (by simpa using hv)
  obtain ⟨o, ho⟩ := h _ hRight (rootCoreReducePath G path hCore)
  have hh := rootCore_path_hits_of_occurrence (rootCoreReducePath G path hCore) cut o ho
  exact path.exists_hitOccurrence _ ((root_coreReducePath_hits_liftCut G path hCore cut).mp hh)

theorem root_corePullCut_card_le (G : PaperShape) (cut : Finset (Fin G.roles)) :
    (rootCorePullCut G cut).card ≤ cut.card := by
  apply Finset.card_le_card_of_injOn (rootCoreInclude G)
  · intro v hv; exact (Finset.mem_filter.mp hv).2
  · exact (rootCoreInclude G).injective.injOn

theorem root_core_separatorNumber_eq (G : PaperShape) :
    (rootBoundaryCoreShape G).toPartiteShape.rightLeftSeparatorNumber =
      G.toPartiteShape.rightLeftSeparatorNumber := by
  let H := (rootBoundaryCoreShape G).toPartiteShape
  apply Nat.le_antisymm
  · have h := H.minimumRightLeftSeparator_isMinimum.2
      (rootCorePullCut G G.toPartiteShape.minimumRightLeftSeparator)
      (root_core_separator_pullCut G _ G.toPartiteShape.minimumRightLeftSeparator_isMinimum.1)
    exact h.trans (root_corePullCut_card_le G _)
  · have h := G.toPartiteShape.minimumRightLeftSeparator_isMinimum.2
      (rootCoreLiftCut G H.minimumRightLeftSeparator)
      (root_core_separator_liftCut G _ H.minimumRightLeftSeparator_isMinimum.1)
    simpa [rootCoreLiftCut, PartiteShape.rightLeftSeparatorNumber, H] using h

theorem root_coreLiftPullCut_eq_inter (G : PaperShape) (cut : Finset (Fin G.roles)) :
    rootCoreLiftCut G (rootCorePullCut G cut) = cut ∩ rootCoreRoles G := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hu).2, (rootCoreRoleIso G u).2⟩
  · intro hv
    obtain ⟨hc, hi⟩ := Finset.mem_inter.mp hv
    apply Finset.mem_map.mpr
    refine ⟨rootCoreIndex G v hi, ?_, root_coreInclude_index G v hi⟩
    simp [rootCorePullCut, hc]

theorem root_minSeparator_subset_core (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) : cut ⊆ rootCoreRoles G := by
  have hs := root_core_separator_liftCut G _ (root_core_separator_pullCut G cut hMin.1)
  rw [root_coreLiftPullCut_eq_inter] at hs
  have he : cut ∩ rootCoreRoles G = cut :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hMin.2 _ hs)
  rw [← he]
  exact Finset.inter_subset_right

theorem root_coreLiftCut_minimal (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (hMin : (rootBoundaryCoreShape G).toPartiteShape.IsMinimumRightLeftSeparator cut) :
    G.toPartiteShape.IsMinimumRightLeftSeparator (rootCoreLiftCut G cut) := by
  refine ⟨root_core_separator_liftCut G cut hMin.1, ?_⟩
  intro other ho
  have h := (hMin.2 _ (root_core_separator_pullCut G other ho)).trans (root_corePullCut_card_le G other)
  simpa [rootCoreLiftCut] using h

theorem root_corePullCut_minimal (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    (rootBoundaryCoreShape G).toPartiteShape.IsMinimumRightLeftSeparator (rootCorePullCut G cut) := by
  refine ⟨root_core_separator_pullCut G cut hMin.1, ?_⟩
  intro other ho
  have h := hMin.2 _ (root_core_separator_liftCut G other ho)
  have he : rootCoreLiftCut G (rootCorePullCut G cut) = cut := by
    rw [root_coreLiftPullCut_eq_inter, Finset.inter_eq_left.mpr (root_minSeparator_subset_core G cut hMin)]
  have hc := congrArg Finset.card he
  simp only [rootCoreLiftCut, Finset.card_map] at hc h
  exact hc ▸ h

#print axioms rootCoreLiftPath
#print axioms rootCoreReducePath
#print axioms root_core_separatorNumber_eq
#print axioms root_minSeparator_subset_core
#print axioms root_coreLiftCut_minimal
#print axioms root_corePullCut_minimal
end GraphMatrixReplica
