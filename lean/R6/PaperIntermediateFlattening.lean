import R6.PaperIntermediateEdgeOrdering

/-! # Role sides of the BLNvH intermediate flattening

The specially ordered edges have already been selected by
`PaperIntermediateEdgeOrdering`.  This file allows an arbitrary assignment of
each selected edge to the row or column side.  Both endpoints of an assigned
edge are placed on that side, while the left boundary is always on the row
side and the right boundary is always on the column side.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica
namespace PartiteShape

/-- An arbitrary row/column assignment of all specially ordered edges.
`false` denotes the row side and `true` the column side. -/
structure IntermediateFlatteningRoleSides
    (G : PartiteShape) {s : ℕ}
    (family : G.BoundaryCleanRightToLeftPaths s) where
  edgeSide : {e : Fin G.edges // e ∈ family.orderingEdges} → Bool

namespace IntermediateFlatteningRoleSides

variable {G : PartiteShape} {s : ℕ}
    {family : G.BoundaryCleanRightToLeftPaths s}

/-- Roles present in the row index: the full left boundary together with
both endpoints of every selected edge assigned to the row side. -/
def rowRoles (D : G.IntermediateFlatteningRoleSides family) :
    Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∈ G.leftBoundary ∨
      ∃ (e : Fin G.edges) (he : e ∈ family.orderingEdges),
        D.edgeSide ⟨e, he⟩ = false ∧ G.EdgeIncident e v

/-- Roles present in the column index: the full right boundary together with
both endpoints of every selected edge assigned to the column side. -/
def colRoles (D : G.IntermediateFlatteningRoleSides family) :
    Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∈ G.rightBoundary ∨
      ∃ (e : Fin G.edges) (he : e ∈ family.orderingEdges),
        D.edgeSide ⟨e, he⟩ = true ∧ G.EdgeIncident e v

theorem leftBoundary_subset_rowRoles
    (D : G.IntermediateFlatteningRoleSides family) :
    G.leftBoundary ⊆ D.rowRoles := by
  classical
  intro v hv
  simp [rowRoles, hv]

theorem rightBoundary_subset_colRoles
    (D : G.IntermediateFlatteningRoleSides family) :
    G.rightBoundary ⊆ D.colRoles := by
  classical
  intro v hv
  simp [colRoles, hv]

theorem incident_mem_rowRoles_of_side_false
    (D : G.IntermediateFlatteningRoleSides family)
    {e : Fin G.edges} (he : e ∈ family.orderingEdges)
    (hSide : D.edgeSide ⟨e, he⟩ = false)
    {v : Fin G.roles} (hv : G.EdgeIncident e v) :
    v ∈ D.rowRoles := by
  classical
  simp only [rowRoles, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨e, he, hSide, hv⟩

theorem incident_mem_colRoles_of_side_true
    (D : G.IntermediateFlatteningRoleSides family)
    {e : Fin G.edges} (he : e ∈ family.orderingEdges)
    (hSide : D.edgeSide ⟨e, he⟩ = true)
    {v : Fin G.roles} (hv : G.EdgeIncident e v) :
    v ∈ D.colRoles := by
  classical
  simp only [colRoles, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨e, he, hSide, hv⟩

/-- Recursive formulation that every edge step of a path belongs to a
selected edge set. -/
def pathEdgesContainedIn
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (edges : Finset (Fin G.edges)) : Prop :=
  match path with
  | .finish _ _ => True
  | .step e _ _ _ tailtail =>
      e ∈ edges ∧ pathEdgesContainedIn tailtail edges

private theorem pathEdgesContainedIn_of_edgeAt_mem
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (edges : Finset (Fin G.edges))
    (hEdges : ∀ o, path.edgeAt o ∈ edges) :
    pathEdgesContainedIn path edges := by
  induction path with
  | finish => trivial
  | step e w hAtStarttail hAtendtail tail ih =>
      constructor
      · exact hEdges ⟨0, by simp [EdgePathToLeft.edgeCount]⟩
      · apply ih
        intro o
        exact hEdges (Fin.succ o)

private theorem path_edgesContainedIn_orderingEdges
    (_D : G.IntermediateFlatteningRoleSides family) (i : Fin s) :
    pathEdgesContainedIn (family.paths.path i) family.orderingEdges := by
  apply pathEdgesContainedIn_of_edgeAt_mem
  intro o
  rw [BoundaryCleanRightToLeftPaths.orderingEdges]
  apply Finset.mem_union_left family.extraEdges
  rw [BoundaryCleanRightToLeftPaths.pathEdges]
  apply Finset.mem_image.2
  exact ⟨⟨i, o⟩, Finset.mem_univ _, rfl⟩

/-- A connected selected path whose head is on the column side and whose
terminal vertex is on the row side must contain a role present on both
sides.  The induction follows the arbitrary R/C edge assignment until its
first transition. -/
private theorem exists_crossingOccurrence
    (D : G.IntermediateFlatteningRoleSides family)
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (hContained : pathEdgesContainedIn path family.orderingEdges)
    (hHeadCol : path.vertexAt path.headOccurrence ∈ D.colRoles)
    (hLastRow : path.vertexAt path.lastOccurrence ∈ D.rowRoles) :
    ∃ o, path.vertexAt o ∈ D.rowRoles ∩ D.colRoles := by
  induction path with
  | finish v hLeft =>
      refine ⟨⟨0, by simp [EdgePathToLeft.vertexCount]⟩,
        Finset.mem_inter.2 ⟨?_, ?_⟩⟩
      · simpa [EdgePathToLeft.vertexAt] using hLastRow
      · simpa [EdgePathToLeft.vertexAt] using hHeadCol
  | @step v e w hAtStart hAtEnd tail ih =>
      have he : e ∈ family.orderingEdges := hContained.1
      have hvCol : v ∈ D.colRoles := by
        rw [EdgePathToLeft.vertexAt_headOccurrence] at hHeadCol
        exact hHeadCol
      by_cases hRow : D.edgeSide ⟨e, he⟩ = false
      · refine ⟨⟨0, by simp [EdgePathToLeft.vertexCount]⟩,
          Finset.mem_inter.2 ⟨?_, ?_⟩⟩
        · exact D.incident_mem_rowRoles_of_side_false he hRow hAtStart
        · exact hvCol
      · have hCol : D.edgeSide ⟨e, he⟩ = true := by
          exact Bool.eq_true_of_not_eq_false hRow
        have hTailHeadCol :
            tail.vertexAt tail.headOccurrence ∈ D.colRoles := by
          rw [tail.vertexAt_headOccurrence]
          exact D.incident_mem_colRoles_of_side_true he hCol hAtEnd
        have hTailLastRow :
            tail.vertexAt tail.lastOccurrence ∈ D.rowRoles := by
          simpa [EdgePathToLeft.lastOccurrence,
            EdgePathToLeft.vertexAt] using hLastRow
        obtain ⟨o, ho⟩ := ih hContained.2 hTailHeadCol hTailLastRow
        exact ⟨Fin.succ o, by
          simpa [EdgePathToLeft.vertexAt] using ho⟩

/-- Every clean path in the certificate family supplies a concrete vertex
occurrence belonging to both flattening sides. -/
theorem exists_pathCrossingOccurrence
    (D : G.IntermediateFlatteningRoleSides family) (i : Fin s) :
    ∃ o, (family.paths.path i).vertexAt o ∈
      D.rowRoles ∩ D.colRoles := by
  let path := family.paths.path i
  have hHeadCol : path.vertexAt path.headOccurrence ∈ D.colRoles := by
    apply D.rightBoundary_subset_colRoles
    simpa [path] using family.paths.startRight i
  have hLastRow : path.vertexAt path.lastOccurrence ∈ D.rowRoles := by
    apply D.leftBoundary_subset_rowRoles
    exact path.vertexAt_lastOccurrence_mem_left
  exact exists_crossingOccurrence D path
    (D.path_edgesContainedIn_orderingEdges i) hHeadCol hLastRow

/-- A chosen crossing occurrence on each path. -/
def pathCrossingOccurrence
    (D : G.IntermediateFlatteningRoleSides family) (i : Fin s) :
    Fin ((family.paths.path i).vertexCount) :=
  Classical.choose (D.exists_pathCrossingOccurrence i)

theorem pathCrossingOccurrence_mem
    (D : G.IntermediateFlatteningRoleSides family) (i : Fin s) :
    (family.paths.path i).vertexAt (D.pathCrossingOccurrence i) ∈
      D.rowRoles ∩ D.colRoles :=
  Classical.choose_spec (D.exists_pathCrossingOccurrence i)

/-- Vertex-disjointness makes the chosen crossing roles for different paths
distinct. -/
theorem pathCrossingRole_injective
    (D : G.IntermediateFlatteningRoleSides family) :
    Function.Injective (fun i : Fin s =>
      (family.paths.path i).vertexAt (D.pathCrossingOccurrence i)) := by
  intro i j hij
  have hOccurrence :
      (⟨i, D.pathCrossingOccurrence i⟩ :
          Σ k : Fin s, Fin ((family.paths.path k).vertexCount)) =
        ⟨j, D.pathCrossingOccurrence j⟩ :=
    family.paths.vertexAt_injective hij
  exact congrArg Sigma.fst hOccurrence

/-- The row/column overlap contains at least one distinct role for every
vertex-disjoint clean path. -/
theorem pathCount_le_card_rowRoles_inter_colRoles
    (D : G.IntermediateFlatteningRoleSides family) :
    s ≤ (D.rowRoles ∩ D.colRoles).card := by
  let hit : Fin s → {v // v ∈ D.rowRoles ∩ D.colRoles} := fun i =>
    ⟨(family.paths.path i).vertexAt (D.pathCrossingOccurrence i),
      D.pathCrossingOccurrence_mem i⟩
  have hHit : Function.Injective hit := by
    intro i j hij
    apply D.pathCrossingRole_injective
    exact congrArg Subtype.val hij
  have hCard := Fintype.card_le_of_injective hit hHit
  simpa only [Fintype.card_fin, Fintype.card_coe] using hCard

/-- Specialization of the preceding bound to a clean Menger certificate:
the overlap has cardinality at least the minimum cut. -/
theorem cut_card_le_card_rowRoles_inter_colRoles
    (certificate : G.BoundaryCleanRightLeftMengerCertificate)
    (D : G.IntermediateFlatteningRoleSides certificate.paths) :
    certificate.cut.card ≤ (D.rowRoles ∩ D.colRoles).card :=
  D.pathCount_le_card_rowRoles_inter_colRoles

/-- Coverage by the selected ordering edges puts every nonisolated middle
role on at least one flattening side, regardless of the R/C assignment. -/
theorem nonisolatedMiddleRoles_subset_rowRoles_union_colRoles
    (D : G.IntermediateFlatteningRoleSides family) :
    G.nonisolatedMiddleRoles ⊆ D.rowRoles ∪ D.colRoles := by
  intro v hv
  obtain ⟨e, he, hIncident⟩ := family.orderingEdges_cover v hv
  cases hSide : D.edgeSide ⟨e, he⟩ with
  | false =>
      exact Finset.mem_union_left _
        (D.incident_mem_rowRoles_of_side_false he hSide hIncident)
  | true =>
      exact Finset.mem_union_right _
        (D.incident_mem_colRoles_of_side_true he hSide hIncident)

/-- Roles missed by both sides can only be isolated middle roles. -/
theorem omittedRoles_subset_isolatedMiddleRoles
    (D : G.IntermediateFlatteningRoleSides family) :
    Finset.univ \ (D.rowRoles ∪ D.colRoles) ⊆
      G.isolatedMiddleRoles := by
  intro v hv
  have hNotUnion := (Finset.mem_sdiff.mp hv).2
  have hNotRow : v ∉ D.rowRoles := fun h =>
    hNotUnion (Finset.mem_union_left _ h)
  have hNotCol : v ∉ D.colRoles := fun h =>
    hNotUnion (Finset.mem_union_right _ h)
  have hNotLeft : v ∉ G.leftBoundary := fun h =>
    hNotRow (D.leftBoundary_subset_rowRoles h)
  have hNotRight : v ∉ G.rightBoundary := fun h =>
    hNotCol (D.rightBoundary_subset_colRoles h)
  by_contra hNotIso
  have hMiddle : v ∈ G.middleRoles := by
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, by
      intro hBoundary
      rcases Finset.mem_union.mp hBoundary with hLeft | hRight
      · exact hNotLeft hLeft
      · exact hNotRight hRight⟩
  have hNonisolated : v ∈ G.nonisolatedMiddleRoles :=
    Finset.mem_sdiff.2 ⟨hMiddle, hNotIso⟩
  exact hNotUnion
    (D.nonisolatedMiddleRoles_subset_rowRoles_union_colRoles hNonisolated)

/-- Equivalently, all non-isolated roles are covered by at least one side. -/
theorem univ_sdiff_isolatedMiddleRoles_subset_rowRoles_union_colRoles
    (D : G.IntermediateFlatteningRoleSides family) :
    Finset.univ \ G.isolatedMiddleRoles ⊆
      D.rowRoles ∪ D.colRoles := by
  intro v hv
  by_cases hLeft : v ∈ G.leftBoundary
  · exact Finset.mem_union_left _ (D.leftBoundary_subset_rowRoles hLeft)
  by_cases hRight : v ∈ G.rightBoundary
  · exact Finset.mem_union_right _ (D.rightBoundary_subset_colRoles hRight)
  have hMiddle : v ∈ G.middleRoles :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ _, by
      intro hBoundary
      rcases Finset.mem_union.mp hBoundary with h | h
      · exact hLeft h
      · exact hRight h⟩
  have hNonisolated : v ∈ G.nonisolatedMiddleRoles :=
    Finset.mem_sdiff.2 ⟨hMiddle, (Finset.mem_sdiff.mp hv).2⟩
  exact D.nonisolatedMiddleRoles_subset_rowRoles_union_colRoles hNonisolated

/-- Twice the ambient role count minus the total number of row/column-side
role occurrences.  This is the numerator of the dimension exponent in the
intermediate flattening estimate. -/
def exponentNumerator
    (D : G.IntermediateFlatteningRoleSides family) : ℕ :=
  2 * G.roles - (D.rowRoles.card + D.colRoles.card)

/-- BLNvH v2 lines 671--678: for any R/C assignment of the selected ordering
edges, path crossings and middle-role coverage give the required exponent
numerator bound. -/
theorem exponentNumerator_le_roles_sub_cut_add_isolated
    (certificate : G.BoundaryCleanRightLeftMengerCertificate)
    (D : G.IntermediateFlatteningRoleSides certificate.paths) :
    D.exponentNumerator ≤
      G.roles - certificate.cut.card + G.isolatedMiddleRoles.card := by
  have hInter := D.cut_card_le_card_rowRoles_inter_colRoles certificate
  have hUnionSubset :=
    D.univ_sdiff_isolatedMiddleRoles_subset_rowRoles_union_colRoles
  have hUnion :
      G.roles - G.isolatedMiddleRoles.card ≤
        (D.rowRoles ∪ D.colRoles).card := by
    have hCard := Finset.card_le_card hUnionSubset
    rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ G.isolatedMiddleRoles)] at hCard
    simpa using hCard
  have hCardIdentity :
      (D.rowRoles ∪ D.colRoles).card +
          (D.rowRoles ∩ D.colRoles).card =
        D.rowRoles.card + D.colRoles.card :=
    Finset.card_union_add_card_inter D.rowRoles D.colRoles
  have hSum := Nat.add_le_add hUnion hInter
  rw [hCardIdentity] at hSum
  have hCutRoles : certificate.cut.card ≤ G.roles := by
    simpa using Finset.card_le_card
      (Finset.subset_univ certificate.cut)
  have hIsoRoles : G.isolatedMiddleRoles.card ≤ G.roles := by
    simpa using Finset.card_le_card
      (Finset.subset_univ G.isolatedMiddleRoles)
  unfold exponentNumerator
  omega

#print axioms IntermediateFlatteningRoleSides.pathCount_le_card_rowRoles_inter_colRoles
#print axioms IntermediateFlatteningRoleSides.cut_card_le_card_rowRoles_inter_colRoles
#print axioms IntermediateFlatteningRoleSides.nonisolatedMiddleRoles_subset_rowRoles_union_colRoles
#print axioms IntermediateFlatteningRoleSides.omittedRoles_subset_isolatedMiddleRoles
#print axioms IntermediateFlatteningRoleSides.exponentNumerator_le_roles_sub_cut_add_isolated

end IntermediateFlatteningRoleSides
end PartiteShape
end GraphMatrixReplica
