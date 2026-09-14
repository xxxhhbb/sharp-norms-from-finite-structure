import R6.M1IsolatedReducedShape
import R6.C079DisjointPathLayerCount
import R6.FiniteMengerCertificate

noncomputable section
namespace GraphMatrixReplica
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

def rootReducedInclude (G : PaperShape) :
    Fin (rootIsolatedReducedShape G).roles ↪ Fin G.roles where
  toFun v := ((rootCoveredRoleIso G) v).1
  inj' := fun _ _ h => (rootCoveredRoleIso G).injective (Subtype.ext h)

def rootReducedIndex (G : PaperShape) (v : Fin G.roles)
    (hv : v ∈ coveredRoles G.isolatedMiddleRoles) : Fin (rootIsolatedReducedShape G).roles :=
  (rootCoveredRoleIso G).symm ⟨v, hv⟩

@[simp] theorem root_include_index (G : PaperShape) (v : Fin G.roles)
    (hv : v ∈ coveredRoles G.isolatedMiddleRoles) :
    rootReducedInclude G (rootReducedIndex G v hv) = v := by
  simp [rootReducedInclude, rootReducedIndex]

theorem root_reduced_left_iff (G : PaperShape) (v : Fin (rootIsolatedReducedShape G).roles) :
    v ∈ (rootIsolatedReducedShape G).toPartiteShape.leftBoundary ↔
      rootReducedInclude G v ∈ G.toPartiteShape.leftBoundary := by
  change v ∈ (rootIsolatedReducedShape G).leftBoundaryFinset ↔
    rootReducedInclude G v ∈ G.leftBoundaryFinset
  rw [(rootIsolatedReducedShape G).mem_leftBoundaryFinset_iff v,
    G.mem_leftBoundaryFinset_iff (rootReducedInclude G v)]
  change (∃ i, (rootCoveredRoleIso G).symm ⟨G.left i, _⟩ = v) ↔
    ∃ i, G.left i = ((rootCoveredRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem root_reduced_right_iff (G : PaperShape) (v : Fin (rootIsolatedReducedShape G).roles) :
    v ∈ (rootIsolatedReducedShape G).toPartiteShape.rightBoundary ↔
      rootReducedInclude G v ∈ G.toPartiteShape.rightBoundary := by
  change v ∈ (rootIsolatedReducedShape G).rightBoundaryFinset ↔
    rootReducedInclude G v ∈ G.rightBoundaryFinset
  rw [(rootIsolatedReducedShape G).mem_rightBoundaryFinset_iff v,
    G.mem_rightBoundaryFinset_iff (rootReducedInclude G v)]
  change (∃ i, (rootCoveredRoleIso G).symm ⟨G.right i, _⟩ = v) ↔
    ∃ i, G.right i = ((rootCoveredRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem root_reduced_incident_iff (G : PaperShape) (e : Fin G.edges)
    (v : Fin (rootIsolatedReducedShape G).roles) :
    (rootIsolatedReducedShape G).toPartiteShape.EdgeIncident e v ↔
      G.toPartiteShape.EdgeIncident e (rootReducedInclude G v) := by
  change ((rootCoveredRoleIso G).symm ⟨G.source e, _⟩ = v ∨
      (rootCoveredRoleIso G).symm ⟨G.target e, _⟩ = v) ↔
    G.source e = ((rootCoveredRoleIso G) v).1 ∨ G.target e = ((rootCoveredRoleIso G) v).1
  simp only [OrderIso.symm_apply_eq, Subtype.ext_iff]

theorem root_incident_covered (G : PaperShape) {v : Fin G.roles} (e : Fin G.edges)
    (h : G.toPartiteShape.EdgeIncident e v) : v ∈ coveredRoles G.isolatedMiddleRoles := by
  rcases h with h | h
  · exact h ▸ G.source_mem_coveredRoles_isolatedMiddle e
  · exact h ▸ G.target_mem_coveredRoles_isolatedMiddle e

theorem root_right_covered (G : PaperShape) {v : Fin G.roles}
    (h : v ∈ G.toPartiteShape.rightBoundary) : v ∈ coveredRoles G.isolatedMiddleRoles := by
  obtain ⟨i, rfl⟩ := (G.mem_rightBoundaryFinset_iff v).mp h
  exact root_right_mem_covered G i

def rootLiftPath (G : PaperShape) {v : Fin (rootIsolatedReducedShape G).toPartiteShape.roles}
    (path : (rootIsolatedReducedShape G).toPartiteShape.EdgePathToLeft v) :
    G.toPartiteShape.EdgePathToLeft (rootReducedInclude G v) :=
  match path with
  | .finish v hv => .finish _ ((root_reduced_left_iff G v).mp hv)
  | .step e w hStart hEnd tail => .step e (rootReducedInclude G w)
      ((root_reduced_incident_iff G e _).mp hStart)
      ((root_reduced_incident_iff G e w).mp hEnd) (rootLiftPath G tail)

def rootReducePath (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v) :
    ∀ hv : v ∈ coveredRoles G.isolatedMiddleRoles,
      (rootIsolatedReducedShape G).toPartiteShape.EdgePathToLeft (rootReducedIndex G v hv) := by
  induction path with
  | finish v hLeft =>
      intro hv
      exact .finish _ ((root_reduced_left_iff G _).mpr (by simpa using hLeft))
  | @step v e w hStart hEnd tail ih =>
      intro hv
      exact .step e (rootReducedIndex G w (root_incident_covered G e hEnd))
        ((root_reduced_incident_iff G e _).mpr (by simpa using hStart))
        ((root_reduced_incident_iff G e _).mpr (by simpa using hEnd))
        (ih (root_incident_covered G e hEnd))

theorem root_path_hits_of_occurrence {H : PartiteShape} {v : Fin H.roles}
    (path : H.EdgePathToLeft v) (cut : Finset (Fin H.roles)) :
    ∀ o : Fin path.vertexCount, path.vertexAt o ∈ cut → path.Hits cut := by
  induction path with
  | finish v hv => intro o ho; exact ho
  | @step v e w hStart hEnd tail ih =>
      intro o
      refine Fin.cases ?_ (fun j => ?_) o
      · intro ho; exact Or.inl ho
      · intro ho; exact Or.inr (ih j ho)

def rootLiftCut (G : PaperShape) (cut : Finset (Fin (rootIsolatedReducedShape G).roles)) :
    Finset (Fin G.roles) := cut.map (rootReducedInclude G)

def rootPullCut (G : PaperShape) (cut : Finset (Fin G.roles)) :
    Finset (Fin (rootIsolatedReducedShape G).roles) :=
  Finset.univ.filter fun v => rootReducedInclude G v ∈ cut

@[simp] theorem root_index_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (v : Fin G.roles) (hv : v ∈ coveredRoles G.isolatedMiddleRoles) :
    rootReducedIndex G v hv ∈ cut ↔ v ∈ rootLiftCut G cut := by
  constructor
  · intro h
    exact Finset.mem_map.mpr ⟨rootReducedIndex G v hv, h, root_include_index G v hv⟩
  · intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp h
    have hi : u = rootReducedIndex G v hv :=
      (rootReducedInclude G).injective (he.trans (root_include_index G v hv).symm)
    simpa only [hi] using hu

theorem root_liftPath_hits_pullCut (G : PaperShape)
    {v : Fin (rootIsolatedReducedShape G).toPartiteShape.roles}
    (path : (rootIsolatedReducedShape G).toPartiteShape.EdgePathToLeft v)
    (cut : Finset (Fin G.roles)) :
    (rootLiftPath G path).Hits cut ↔ path.Hits (rootPullCut G cut) := by
  induction path with
  | finish v hv => simp [rootLiftPath, PartiteShape.EdgePathToLeft.Hits, rootPullCut]
  | @step v e w hStart hEnd tail ih =>
      simpa [rootLiftPath, PartiteShape.EdgePathToLeft.Hits, rootPullCut] using
        or_congr Iff.rfl ih

theorem root_reducePath_hits_liftCut (G : PaperShape) {v : Fin G.toPartiteShape.roles}
    (path : G.toPartiteShape.EdgePathToLeft v)
    (hv : v ∈ coveredRoles G.isolatedMiddleRoles)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles)) :
    (rootReducePath G path hv).Hits cut ↔ path.Hits (rootLiftCut G cut) := by
  induction path with
  | finish v hLeft =>
      simpa only [rootReducePath, PartiteShape.EdgePathToLeft.Hits] using
        root_index_mem_liftCut G cut v hv
  | @step v e w hStart hEnd tail ih =>
      simpa only [rootReducePath, PartiteShape.EdgePathToLeft.Hits] using
        or_congr (root_index_mem_liftCut G cut v hv) (ih (root_incident_covered G e hEnd))

theorem root_separator_pullCut (G : PaperShape) (cut : Finset (Fin G.roles))
    (h : G.toPartiteShape.IsRightLeftSeparator cut) :
    (rootIsolatedReducedShape G).toPartiteShape.IsRightLeftSeparator (rootPullCut G cut) := by
  intro v hv path
  obtain ⟨o, ho⟩ := h (rootReducedInclude G v) ((root_reduced_right_iff G v).mp hv)
    (rootLiftPath G path)
  have hh := root_path_hits_of_occurrence (rootLiftPath G path) cut o ho
  exact path.exists_hitOccurrence _ ((root_liftPath_hits_pullCut G path cut).mp hh)

theorem root_separator_liftCut (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (h : (rootIsolatedReducedShape G).toPartiteShape.IsRightLeftSeparator cut) :
    G.toPartiteShape.IsRightLeftSeparator (rootLiftCut G cut) := by
  intro v hv path
  have hCovered := root_right_covered G hv
  have hRight : rootReducedIndex G v hCovered ∈
      (rootIsolatedReducedShape G).toPartiteShape.rightBoundary :=
    (root_reduced_right_iff G _).mpr (by simpa using hv)
  obtain ⟨o, ho⟩ := h _ hRight (rootReducePath G path hCovered)
  have hh := root_path_hits_of_occurrence (rootReducePath G path hCovered) cut o ho
  exact path.exists_hitOccurrence _ ((root_reducePath_hits_liftCut G path hCovered cut).mp hh)

theorem root_pullCut_card_le (G : PaperShape) (cut : Finset (Fin G.roles)) :
    (rootPullCut G cut).card ≤ cut.card := by
  apply Finset.card_le_card_of_injOn (rootReducedInclude G)
  · intro v hv; exact (Finset.mem_filter.mp hv).2
  · exact (rootReducedInclude G).injective.injOn

/-- Deleting isolated middle roles preserves the actual minimum separator number. -/
theorem root_reduced_separatorNumber_eq (G : PaperShape) :
    (rootIsolatedReducedShape G).toPartiteShape.rightLeftSeparatorNumber =
      G.toPartiteShape.rightLeftSeparatorNumber := by
  let H := (rootIsolatedReducedShape G).toPartiteShape
  apply Nat.le_antisymm
  · have h := H.minimumRightLeftSeparator_isMinimum.2
      (rootPullCut G G.toPartiteShape.minimumRightLeftSeparator)
      (root_separator_pullCut G _ G.toPartiteShape.minimumRightLeftSeparator_isMinimum.1)
    exact h.trans (root_pullCut_card_le G _)
  · have h := G.toPartiteShape.minimumRightLeftSeparator_isMinimum.2
      (rootLiftCut G H.minimumRightLeftSeparator)
      (root_separator_liftCut G _ H.minimumRightLeftSeparator_isMinimum.1)
    simpa [rootLiftCut, PartiteShape.rightLeftSeparatorNumber, H] using h

theorem root_lift_pullCut_eq_inter (G : PaperShape) (cut : Finset (Fin G.roles)) :
    rootLiftCut G (rootPullCut G cut) = cut ∩ coveredRoles G.isolatedMiddleRoles := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hu).2,
      (rootCoveredRoleIso G u).2⟩
  · intro hv
    obtain ⟨hc, hi⟩ := Finset.mem_inter.mp hv
    apply Finset.mem_map.mpr
    refine ⟨rootReducedIndex G v hi, ?_, root_include_index G v hi⟩
    simp [rootPullCut, hc]

theorem root_minSeparator_subset_covered (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    cut ⊆ coveredRoles G.isolatedMiddleRoles := by
  have hs := root_separator_liftCut G _ (root_separator_pullCut G cut hMin.1)
  rw [root_lift_pullCut_eq_inter] at hs
  have he : cut ∩ coveredRoles G.isolatedMiddleRoles = cut :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hMin.2 _ hs)
  rw [← he]
  exact Finset.inter_subset_right

theorem root_liftCut_minimal (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (hMin : (rootIsolatedReducedShape G).toPartiteShape.IsMinimumRightLeftSeparator cut) :
    G.toPartiteShape.IsMinimumRightLeftSeparator (rootLiftCut G cut) := by
  refine ⟨root_separator_liftCut G cut hMin.1, ?_⟩
  intro other ho
  have h := (hMin.2 _ (root_separator_pullCut G other ho)).trans
    (root_pullCut_card_le G other)
  simpa [rootLiftCut] using h

theorem root_pullCut_minimal (G : PaperShape) (cut : Finset (Fin G.roles))
    (hMin : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    (rootIsolatedReducedShape G).toPartiteShape.IsMinimumRightLeftSeparator
      (rootPullCut G cut) := by
  refine ⟨root_separator_pullCut G cut hMin.1, ?_⟩
  intro other ho
  have h := hMin.2 _ (root_separator_liftCut G other ho)
  have he : rootLiftCut G (rootPullCut G cut) = cut := by
    rw [root_lift_pullCut_eq_inter,
      Finset.inter_eq_left.mpr (root_minSeparator_subset_covered G cut hMin)]
  have hc := congrArg Finset.card he
  simp only [rootLiftCut, Finset.card_map] at hc h
  exact hc ▸ h

#print axioms rootLiftPath
#print axioms rootReducePath
#print axioms root_separator_pullCut
#print axioms root_separator_liftCut
#print axioms root_reduced_separatorNumber_eq
#print axioms root_minSeparator_subset_covered
#print axioms root_liftCut_minimal
#print axioms root_pullCut_minimal
end GraphMatrixReplica
