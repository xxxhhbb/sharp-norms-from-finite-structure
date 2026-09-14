import GraphMatrix.Main.IsolatedReducedShape
import GraphMatrix.Counting.DisjointPathLayerCount
import GraphMatrix.FiniteMengerCertificate

noncomputable section
namespace GraphMatrixReplica
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

def mainReducedInclude (G : PaperShape) :
    Fin (mainIsolatedReducedShape G).roles ↪ Fin G.roles where
  toFun v := ((mainCoveredRoleIso G) v).1
  inj' := fun _ _ h => (mainCoveredRoleIso G).injective (Subtype.ext h)

def mainReducedIndex (G : PaperShape) (v : Fin G.roles)
    (hv : v ∈ coveredRoles G.isolatedMiddleRoles) : Fin (mainIsolatedReducedShape G).roles :=
  (mainCoveredRoleIso G).symm ⟨v, hv⟩

@[simp] theorem main_include_index (G : PaperShape) (v : Fin G.roles)
    (hv : v ∈ coveredRoles G.isolatedMiddleRoles) :
    mainReducedInclude G (mainReducedIndex G v hv) = v := by
  simp [mainReducedInclude, mainReducedIndex]

theorem main_reduced_left_iff (G : PaperShape) (v : Fin (mainIsolatedReducedShape G).roles) :
    v ∈ (mainIsolatedReducedShape G).toPartiteShape.leftBoundary ↔
      mainReducedInclude G v ∈ G.toPartiteShape.leftBoundary := by
  change v ∈ (mainIsolatedReducedShape G).leftBoundaryFinset ↔
    mainReducedInclude G v ∈ G.leftBoundaryFinset
  rw [(mainIsolatedReducedShape G).mem_leftBoundaryFinset_iff v,
    G.mem_leftBoundaryFinset_iff (mainReducedInclude G v)]
  change (∃ i, (mainCoveredRoleIso G).symm ⟨G.left i, _⟩ = v) ↔
    ∃ i, G.left i = ((mainCoveredRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem main_reduced_right_iff (G : PaperShape) (v : Fin (mainIsolatedReducedShape G).roles) :
    v ∈ (mainIsolatedReducedShape G).toPartiteShape.rightBoundary ↔
      mainReducedInclude G v ∈ G.toPartiteShape.rightBoundary := by
  change v ∈ (mainIsolatedReducedShape G).rightBoundaryFinset ↔
    mainReducedInclude G v ∈ G.rightBoundaryFinset
  rw [(mainIsolatedReducedShape G).mem_rightBoundaryFinset_iff v,
    G.mem_rightBoundaryFinset_iff (mainReducedInclude G v)]
  change (∃ i, (mainCoveredRoleIso G).symm ⟨G.right i, _⟩ = v) ↔
    ∃ i, G.right i = ((mainCoveredRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem main_reduced_incident_iff (G : PaperShape) (e : Fin G.edges)
    (v : Fin (mainIsolatedReducedShape G).roles) :
    (mainIsolatedReducedShape G).toPartiteShape.EdgeIncident e v ↔
      G.toPartiteShape.EdgeIncident e (mainReducedInclude G v) := by
  change ((mainCoveredRoleIso G).symm ⟨G.source e, _⟩ = v ∨
      (mainCoveredRoleIso G).symm ⟨G.target e, _⟩ = v) ↔
    G.source e = ((mainCoveredRoleIso G) v).1 ∨ G.target e = ((mainCoveredRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem main_incident_covered (G : PaperShape) {v : Fin G.roles} (e : Fin G.edges)
    (h : G.toPartiteShape.EdgeIncident e v) : v ∈ coveredRoles G.isolatedMiddleRoles := by
  rcases h with h | h
  · exact h ▸ G.source_mem_coveredRoles_isolatedMiddle e
  · exact h ▸ G.target_mem_coveredRoles_isolatedMiddle e

theorem main_right_covered (G : PaperShape) {v : Fin G.roles}
    (h : v ∈ G.toPartiteShape.rightBoundary) : v ∈ coveredRoles G.isolatedMiddleRoles := by
  obtain ⟨i, rfl⟩ := (G.mem_rightBoundaryFinset_iff v).mp h
  exact main_right_mem_covered G i

def mainLiftPath (G : PaperShape) {v : Fin (mainIsolatedReducedShape G).toPartiteShape.roles}
    (path : (mainIsolatedReducedShape G).toPartiteShape.EdgePathToLeft v) :
    G.toPartiteShape.EdgePathToLeft (mainReducedInclude G v) :=
  match path with
  | .finish v hv => .finish _ ((main_reduced_left_iff G v).mp hv)
  | .step e w hStart hEnd tail => .step e (mainReducedInclude G w)
      ((main_reduced_incident_iff G e _).mp hStart)
      ((main_reduced_incident_iff G e w).mp hEnd) (mainLiftPath G tail)

def mainReducePath (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v) :
    ∀ hv : v ∈ coveredRoles G.isolatedMiddleRoles,
      (mainIsolatedReducedShape G).toPartiteShape.EdgePathToLeft (mainReducedIndex G v hv) := by
  induction path with
  | finish v hLeft =>
      intro hv
      exact .finish _ ((main_reduced_left_iff G _).mpr (by simpa using hLeft))
  | @step v e w hStart hEnd tail ih =>
      intro hv
      exact .step e (mainReducedIndex G w (main_incident_covered G e hEnd))
        ((main_reduced_incident_iff G e _).mpr (by simpa using hStart))
        ((main_reduced_incident_iff G e _).mpr (by simpa using hEnd))
        (ih (main_incident_covered G e hEnd))

theorem main_path_hits_of_occurrence {H : PartiteShape} {v : Fin H.roles}
    (path : H.EdgePathToLeft v) (cut : Finset (Fin H.roles)) :
    ∀ o : Fin path.vertexCount, path.vertexAt o ∈ cut → path.Hits cut := by
  induction path with
  | finish v hv => intro o ho; exact ho
  | @step v e w hStart hEnd tail ih =>
      intro o
      refine Fin.cases ?_ (fun j => ?_) o
      · intro ho; exact Or.inl ho
      · intro ho; exact Or.inr (ih j ho)

def mainLiftCut (G : PaperShape) (cut : Finset (Fin (mainIsolatedReducedShape G).roles)) :
    Finset (Fin G.roles) := cut.map (mainReducedInclude G)

def mainPullCut (G : PaperShape) (cut : Finset (Fin G.roles)) :
    Finset (Fin (mainIsolatedReducedShape G).roles) :=
  Finset.univ.filter fun v => mainReducedInclude G v ∈ cut

@[simp] theorem main_index_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (v : Fin G.roles) (hv : v ∈ coveredRoles G.isolatedMiddleRoles) :
    mainReducedIndex G v hv ∈ cut ↔ v ∈ mainLiftCut G cut := by
  constructor
  · intro h
    exact Finset.mem_map.mpr ⟨mainReducedIndex G v hv, h, main_include_index G v hv⟩
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp h
    have hi : u = mainReducedIndex G v hv :=
      (mainReducedInclude G).injective (he.trans (main_include_index G v hv).symm)
    simpa only [hi] using hu

theorem main_liftPath_hits_pullCut (G : PaperShape)
    {v : Fin (mainIsolatedReducedShape G).toPartiteShape.roles}
    (path : (mainIsolatedReducedShape G).toPartiteShape.EdgePathToLeft v)
    (cut : Finset (Fin G.roles)) :
    (mainLiftPath G path).Hits cut ↔ path.Hits (mainPullCut G cut) := by
  induction path with
  | finish v hv => simp [mainLiftPath, PartiteShape.EdgePathToLeft.Hits, mainPullCut]
  | @step v e w hStart hEnd tail ih =>
      simpa [mainLiftPath, PartiteShape.EdgePathToLeft.Hits, mainPullCut] using
        or_congr Iff.rfl ih

theorem main_reducePath_hits_liftCut (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v)
    (hv : v ∈ coveredRoles G.isolatedMiddleRoles)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles)) :
    (mainReducePath G path hv).Hits cut ↔ path.Hits (mainLiftCut G cut) := by
  induction path with
  | finish v hLeft =>
      simpa only [mainReducePath, PartiteShape.EdgePathToLeft.Hits] using
        main_index_mem_liftCut G cut v hv
  | @step v e w hStart hEnd tail ih =>
      simpa only [mainReducePath, PartiteShape.EdgePathToLeft.Hits] using
        or_congr (main_index_mem_liftCut G cut v hv) (ih (main_incident_covered G e hEnd))

theorem main_separator_pullCut (G : PaperShape) (cut : Finset (Fin G.roles))
    (h : G.toPartiteShape.IsRightLeftSeparator cut) :
    (mainIsolatedReducedShape G).toPartiteShape.IsRightLeftSeparator (mainPullCut G cut) := by
  intro v hv path
  obtain ⟨o, ho⟩ := h (mainReducedInclude G v) ((main_reduced_right_iff G v).mp hv)
    (mainLiftPath G path)
  have hh := main_path_hits_of_occurrence (mainLiftPath G path) cut o ho
  exact path.exists_hitOccurrence _ ((main_liftPath_hits_pullCut G path cut).mp hh)

theorem main_separator_liftCut (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (h : (mainIsolatedReducedShape G).toPartiteShape.IsRightLeftSeparator cut) :
    G.toPartiteShape.IsRightLeftSeparator (mainLiftCut G cut) := by
  intro v hv path
  have hCovered := main_right_covered G hv
  have hRight : mainReducedIndex G v hCovered ∈
      (mainIsolatedReducedShape G).toPartiteShape.rightBoundary :=
    (main_reduced_right_iff G _).mpr (by simpa using hv)
  obtain ⟨o, ho⟩ := h _ hRight (mainReducePath G path hCovered)
  have hh := main_path_hits_of_occurrence (mainReducePath G path hCovered) cut o ho
  exact path.exists_hitOccurrence _ ((main_reducePath_hits_liftCut G path hCovered cut).mp hh)

theorem main_pullCut_card_le (G : PaperShape) (cut : Finset (Fin G.roles)) :
    (mainPullCut G cut).card ≤ cut.card := by
  apply Finset.card_le_card_of_injOn (mainReducedInclude G)
  · intro v hv; exact (Finset.mem_filter.mp hv).2
  · exact (mainReducedInclude G).injective.injOn

/-- Deleting isolated middle roles preserves the actual minimum separator number. -/
theorem main_reduced_separatorNumber_eq (G : PaperShape) :
    (mainIsolatedReducedShape G).toPartiteShape.rightLeftSeparatorNumber =
      G.toPartiteShape.rightLeftSeparatorNumber := by
  let H := (mainIsolatedReducedShape G).toPartiteShape
  apply Nat.le_antisymm
  · have h := H.minimumRightLeftSeparator_isMinimum.2
      (mainPullCut G G.toPartiteShape.minimumRightLeftSeparator)
      (main_separator_pullCut G _ G.toPartiteShape.minimumRightLeftSeparator_isMinimum.1)
    exact h.trans (main_pullCut_card_le G _)
  · have h := G.toPartiteShape.minimumRightLeftSeparator_isMinimum.2
      (mainLiftCut G H.minimumRightLeftSeparator)
      (main_separator_liftCut G _ H.minimumRightLeftSeparator_isMinimum.1)
    simpa [mainLiftCut, PartiteShape.rightLeftSeparatorNumber, H] using h

theorem main_lift_pullCut_eq_inter (G : PaperShape) (cut : Finset (Fin G.roles)) :
    mainLiftCut G (mainPullCut G cut) = cut ∩ coveredRoles G.isolatedMiddleRoles := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hu).2,
      (mainCoveredRoleIso G u).2⟩
  · intro hv
    obtain ⟨hc, hi⟩ := Finset.mem_inter.mp hv
    apply Finset.mem_map.mpr
    refine ⟨mainReducedIndex G v hi, ?_, main_include_index G v hi⟩
    simp [mainPullCut, hc]

theorem main_minSeparator_subset_covered (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    cut ⊆ coveredRoles G.isolatedMiddleRoles := by
  have hs := main_separator_liftCut G _ (main_separator_pullCut G cut hMin.1)
  rw [main_lift_pullCut_eq_inter] at hs
  have he : cut ∩ coveredRoles G.isolatedMiddleRoles = cut :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hMin.2 _ hs)
  rw [← he]
  exact Finset.inter_subset_right

theorem main_liftCut_minimal (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (hMin : (mainIsolatedReducedShape G).toPartiteShape.IsMinimumRightLeftSeparator cut) :
    G.toPartiteShape.IsMinimumRightLeftSeparator (mainLiftCut G cut) := by
  refine ⟨main_separator_liftCut G cut hMin.1, ?_⟩
  intro other ho
  have h := (hMin.2 _ (main_separator_pullCut G other ho)).trans
    (main_pullCut_card_le G other)
  simpa [mainLiftCut] using h

theorem main_pullCut_minimal (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    (mainIsolatedReducedShape G).toPartiteShape.IsMinimumRightLeftSeparator
      (mainPullCut G cut) := by
  refine ⟨main_separator_pullCut G cut hMin.1, ?_⟩
  intro other ho
  have h := hMin.2 _ (main_separator_liftCut G other ho)
  have he : mainLiftCut G (mainPullCut G cut) = cut := by
    rw [main_lift_pullCut_eq_inter,
      Finset.inter_eq_left.mpr (main_minSeparator_subset_covered G cut hMin)]
  have hc := congrArg Finset.card he
  simp only [mainLiftCut, Finset.card_map] at hc h
  exact hc ▸ h

end GraphMatrixReplica
