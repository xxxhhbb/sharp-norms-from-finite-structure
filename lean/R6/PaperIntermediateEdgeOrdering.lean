import R6.PaperMengerPathTrimming
import R6.PaperToPartiteBridge
import R6.IsolatedMiddleCorrection

/-! # The special intermediate-edge ordering count

This file formalizes the finite coverage count used in BLNvH v2, lines
655--670.  Edges occurring on clean disjoint boundary paths are placed first;
one incident edge is then selected for each still-uncovered nonisolated middle
role.  Both edge collections are finite sets, so repeated edge occurrences and
repeated choices are automatically deduplicated.

The numerical subtraction of the whole common boundary is valid precisely
when every common-boundary role is represented by a singleton path.  We expose
that necessary saturation condition explicitly: it need not hold for an
arbitrary non-maximal path family.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

namespace PartiteShape.EdgePathToLeft

variable {G : PartiteShape}

/-- Number of edge occurrences in an inductively represented path. -/
def edgeCount : {v : Fin G.roles} → G.EdgePathToLeft v → ℕ
  | _, .finish _ _ => 0
  | _, .step _ _ _ _ tail => tail.edgeCount + 1

theorem edgeCount_add_one_eq_vertexCount {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.edgeCount + 1 = path.vertexCount := by
  induction path with
  | finish => rfl
  | step e w hAtStart hAtEnd tail ih =>
      simp only [edgeCount, PartiteShape.EdgePathToLeft.vertexCount]
      omega

/-- Edge at a path-edge occurrence, ordered from the path head. -/
def edgeAt : {v : Fin G.roles} → (path : G.EdgePathToLeft v) →
    Fin path.edgeCount → Fin G.edges
  | _, .finish _ _, o => Fin.elim0 o
  | _, .step e _ _ _ tail, o => Fin.cases e tail.edgeAt o

/-- The vertex occurrence reached by a path-edge occurrence. -/
def edgeEndOccurrence {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (o : Fin path.edgeCount) : Fin path.vertexCount :=
  ⟨o.val + 1, by
    have hCount := path.edgeCount_add_one_eq_vertexCount
    omega⟩

theorem edgeAt_incident_edgeEnd {v : Fin G.roles}
    (path : G.EdgePathToLeft v)
    (o : Fin path.edgeCount) :
    G.EdgeIncident (path.edgeAt o) (path.vertexAt (path.edgeEndOccurrence o)) := by
  induction path with
  | finish v hLeft => exact Fin.elim0 o
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o using Fin.cases with
      | zero =>
          change G.EdgeIncident e (tail.vertexAt tail.headOccurrence)
          simpa using hAtEnd
      | succ o => exact ih o

end PartiteShape.EdgePathToLeft

namespace PartiteShape.BoundaryCleanRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

abbrev EdgeOccurrence (family : G.BoundaryCleanRightToLeftPaths s) :=
  Σ i : Fin s, Fin (family.paths.path i).edgeCount

def edgeOfOccurrence (family : G.BoundaryCleanRightToLeftPaths s) :
    family.EdgeOccurrence → Fin G.edges :=
  fun z => (family.paths.path z.1).edgeAt z.2

/-- Deduplicated set of all edges occurring on the clean paths. -/
def pathEdges (family : G.BoundaryCleanRightToLeftPaths s) :
    Finset (Fin G.edges) := by
  classical
  exact Finset.univ.image family.edgeOfOccurrence

abbrev InteriorOccurrence (family : G.BoundaryCleanRightToLeftPaths s) :=
  Σ i : Fin s, Fin ((family.paths.path i).edgeCount - 1)

private def interiorEdgeIndex (family : G.BoundaryCleanRightToLeftPaths s)
    (z : family.InteriorOccurrence) :
    Fin (family.paths.path z.1).edgeCount :=
  Fin.castLE (by omega) z.2

private def interiorVertexOccurrence
    (family : G.BoundaryCleanRightToLeftPaths s)
    (z : family.InteriorOccurrence) :
    Fin (family.paths.path z.1).vertexCount :=
  (family.paths.path z.1).edgeEndOccurrence (family.interiorEdgeIndex z)

def interiorRole (family : G.BoundaryCleanRightToLeftPaths s) :
    family.InteriorOccurrence → Fin G.roles :=
  fun z => (family.paths.path z.1).vertexAt
    (family.interiorVertexOccurrence z)

/-- Middle roles lying strictly inside one of the clean paths. -/
def pathMiddleRoles (family : G.BoundaryCleanRightToLeftPaths s) :
    Finset (Fin G.roles) := by
  classical
  exact Finset.univ.image family.interiorRole

private theorem interiorVertexOccurrence_val
    (family : G.BoundaryCleanRightToLeftPaths s)
    (z : family.InteriorOccurrence) :
    (family.interiorVertexOccurrence z).val = z.2.val + 1 := rfl

private theorem interiorRole_injective
    (family : G.BoundaryCleanRightToLeftPaths s) :
    Function.Injective family.interiorRole := by
  rintro ⟨i, o⟩ ⟨j, q⟩ hRole
  have hOccurrence :
      (⟨i, family.interiorVertexOccurrence ⟨i, o⟩⟩ :
          Σ k : Fin s, Fin ((family.paths.path k).vertexCount)) =
        ⟨j, family.interiorVertexOccurrence ⟨j, q⟩⟩ :=
    family.paths.vertexAt_injective hRole
  have hij : i = j := congrArg Sigma.fst hOccurrence
  subst j
  have hEnd : family.interiorVertexOccurrence ⟨i, o⟩ =
      family.interiorVertexOccurrence ⟨i, q⟩ :=
    eq_of_heq (Sigma.mk.inj_iff.mp hOccurrence).2
  have hval := congrArg Fin.val hEnd
  have hoq : o = q := by
    apply Fin.ext
    simpa [interiorVertexOccurrence, interiorEdgeIndex,
      PartiteShape.EdgePathToLeft.edgeEndOccurrence] using hval
  subst q
  rfl

theorem card_pathMiddleRoles
    (family : G.BoundaryCleanRightToLeftPaths s) :
    family.pathMiddleRoles.card = Fintype.card family.InteriorOccurrence := by
  classical
  rw [pathMiddleRoles,
    Finset.card_image_iff.mpr family.interiorRole_injective.injOn]
  simp [InteriorOccurrence]

/-- Indices of paths having at least one edge. -/
def activePathIndices (family : G.BoundaryCleanRightToLeftPaths s) :
    Finset (Fin s) :=
  Finset.univ.filter fun i => (family.paths.path i).edgeCount ≠ 0

/-- Indices whose right-boundary start is also in the left boundary.  Clean
paths at these indices are necessarily singletons. -/
def commonSingletonIndices (family : G.BoundaryCleanRightToLeftPaths s) :
    Finset (Fin s) :=
  Finset.univ.filter fun i => family.paths.start i ∈ G.leftBoundary

/-- The exact saturation condition needed for the `|U ∩ V|` saving. -/
def SaturatesCommonBoundary (family : G.BoundaryCleanRightToLeftPaths s) : Prop :=
  family.commonSingletonIndices.card =
    (G.leftBoundary ∩ G.rightBoundary).card

private theorem active_disjoint_common
    (family : G.BoundaryCleanRightToLeftPaths s) :
    Disjoint family.activePathIndices family.commonSingletonIndices := by
  classical
  rw [Finset.disjoint_left]
  intro i hiActive hiCommon
  have hLeft : family.paths.start i ∈ G.leftBoundary := by
    simpa [commonSingletonIndices] using hiCommon
  have hOne := (family.paths.path i).vertexCount_eq_one_of_clean_start_mem_left
    (family.boundary_clean i) hLeft
  have hCount := (family.paths.path i).edgeCount_add_one_eq_vertexCount
  have hEdgeZero : (family.paths.path i).edgeCount = 0 := by omega
  simp [activePathIndices, hEdgeZero] at hiActive

private theorem active_card_le_sub_common
    (family : G.BoundaryCleanRightToLeftPaths s)
    (hSaturates : family.SaturatesCommonBoundary) :
    family.activePathIndices.card ≤
      s - (G.leftBoundary ∩ G.rightBoundary).card := by
  classical
  have hUnion :
      (family.activePathIndices ∪ family.commonSingletonIndices).card ≤ s := by
    simpa using Finset.card_le_card
      (Finset.subset_univ (family.activePathIndices ∪ family.commonSingletonIndices))
  rw [Finset.card_union_of_disjoint family.active_disjoint_common] at hUnion
  rw [hSaturates] at hUnion
  omega

private theorem sum_edgeCount_eq_sum_interior_add_active
    (family : G.BoundaryCleanRightToLeftPaths s) :
    (∑ i : Fin s, (family.paths.path i).edgeCount) =
      (∑ i : Fin s, ((family.paths.path i).edgeCount - 1)) +
        family.activePathIndices.card := by
  classical
  calc
    (∑ i : Fin s, (family.paths.path i).edgeCount) =
        ∑ i : Fin s,
          ((family.paths.path i).edgeCount - 1 +
            if (family.paths.path i).edgeCount = 0 then 0 else 1) := by
          apply Finset.sum_congr rfl
          intro i _
          split <;> omega
    _ = (∑ i : Fin s, ((family.paths.path i).edgeCount - 1)) +
          ∑ i : Fin s,
            if (family.paths.path i).edgeCount = 0 then 0 else 1 := by
          rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      rw [activePathIndices, Finset.card_eq_sum_ones,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : (family.paths.path i).edgeCount = 0 <;> simp [h]

private theorem card_edgeOccurrence
    (family : G.BoundaryCleanRightToLeftPaths s) :
    Fintype.card family.EdgeOccurrence =
      ∑ i : Fin s, (family.paths.path i).edgeCount := by
  simp [EdgeOccurrence]

private theorem card_interiorOccurrence
    (family : G.BoundaryCleanRightToLeftPaths s) :
    Fintype.card family.InteriorOccurrence =
      ∑ i : Fin s, ((family.paths.path i).edgeCount - 1) := by
  simp [InteriorOccurrence]

theorem card_pathEdges_le_common_add_middle
    (family : G.BoundaryCleanRightToLeftPaths s)
    (hSaturates : family.SaturatesCommonBoundary) :
    family.pathEdges.card ≤
      s - (G.leftBoundary ∩ G.rightBoundary).card +
        family.pathMiddleRoles.card := by
  classical
  have hImage : family.pathEdges.card ≤
      Fintype.card family.EdgeOccurrence := by
    simpa [pathEdges] using
      (Finset.card_image_le :
        (Finset.univ.image family.edgeOfOccurrence).card ≤
          (Finset.univ : Finset family.EdgeOccurrence).card)
  have hActive := family.active_card_le_sub_common hSaturates
  rw [family.card_edgeOccurrence,
    family.sum_edgeCount_eq_sum_interior_add_active,
    ← family.card_interiorOccurrence, ← family.card_pathMiddleRoles] at hImage
  omega

end PartiteShape.BoundaryCleanRightToLeftPaths

namespace PartiteShape

/-- All roles outside both boundaries. -/
def middleRoles (G : PartiteShape) : Finset (Fin G.roles) :=
  Finset.univ \ (G.leftBoundary ∪ G.rightBoundary)

/-- Nonisolated middle roles, corresponding to `W \ W_iso`. -/
def nonisolatedMiddleRoles (G : PartiteShape) :
    Finset (Fin G.roles) :=
  G.middleRoles \ G.isolatedMiddleRoles

end PartiteShape

namespace PartiteShape.BoundaryCleanRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

private theorem interiorRole_mem_nonisolatedMiddle
    (family : G.BoundaryCleanRightToLeftPaths s)
    (z : family.InteriorOccurrence) :
    family.interiorRole z ∈ G.nonisolatedMiddleRoles := by
  classical
  let path := family.paths.path z.1
  let edgeIndex := family.interiorEdgeIndex z
  let occurrence := family.interiorVertexOccurrence z
  have hHead : occurrence ≠ path.headOccurrence := by
    intro h
    have hv := congrArg Fin.val h
    simp [occurrence, interiorVertexOccurrence, interiorEdgeIndex,
      PartiteShape.EdgePathToLeft.edgeEndOccurrence,
      PartiteShape.EdgePathToLeft.headOccurrence] at hv
  have hLast : occurrence ≠ path.lastOccurrence := by
    intro h
    have hv := congrArg Fin.val h
    have hLastCount := path.lastOccurrence_val_add_one
    have hEdgeCount := path.edgeCount_add_one_eq_vertexCount
    have hz := z.2.isLt
    have hv' : z.2.val + 1 = path.lastOccurrence.val := by
      simpa [path, occurrence, interiorVertexOccurrence, interiorEdgeIndex,
        PartiteShape.EdgePathToLeft.edgeEndOccurrence] using hv
    have hzEdge : z.2.val + 1 < path.edgeCount := by
      change z.2.val + 1 < (family.paths.path z.1).edgeCount
      omega
    have hLastVal : path.lastOccurrence.val = path.edgeCount := by
      omega
    omega
  have hMiddle := path.clean_interior_not_mem_boundaries
    (family.boundary_clean z.1) occurrence hHead hLast
  have hIncident : G.EdgeIncident (path.edgeAt edgeIndex)
      (family.interiorRole z) := by
    exact path.edgeAt_incident_edgeEnd edgeIndex
  have hNotIso : family.interiorRole z ∉ G.isolatedMiddleRoles := by
    intro hIso
    have h := (G.mem_isolatedMiddleRoles_iff (family.interiorRole z)).1 hIso
    rcases hIncident with hSource | hTarget
    · exact (h.2.2 (path.edgeAt edgeIndex)).1 hSource
    · exact (h.2.2 (path.edgeAt edgeIndex)).2 hTarget
  have hNotUnion : family.interiorRole z ∉
      G.leftBoundary ∪ G.rightBoundary := by
    intro hUnion
    rcases Finset.mem_union.mp hUnion with hLeft | hRight
    · exact hMiddle.2 hLeft
    · exact hMiddle.1 hRight
  exact Finset.mem_sdiff.2
    ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hNotUnion⟩, hNotIso⟩

theorem pathMiddleRoles_subset_nonisolatedMiddle
    (family : G.BoundaryCleanRightToLeftPaths s) :
    family.pathMiddleRoles ⊆ G.nonisolatedMiddleRoles := by
  classical
  intro v hv
  rw [pathMiddleRoles] at hv
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
  exact family.interiorRole_mem_nonisolatedMiddle z

end PartiteShape.BoundaryCleanRightToLeftPaths

namespace PartiteShape

variable {G : PartiteShape} {s : ℕ}

private theorem exists_incident_edge_of_mem_nonisolatedMiddle
    (G : PartiteShape) {v : Fin G.roles}
    (hv : v ∈ G.nonisolatedMiddleRoles) :
    ∃ e : Fin G.edges, G.EdgeIncident e v := by
  classical
  rcases Finset.mem_sdiff.mp hv with ⟨hMiddle, hNotIsoSet⟩
  rcases Finset.mem_sdiff.mp hMiddle with ⟨_, hBoundaries⟩
  have hNotLeft : v ∉ G.leftBoundary := by
    intro h
    exact hBoundaries (Finset.mem_union_left _ h)
  have hNotRight : v ∉ G.rightBoundary := by
    intro h
    exact hBoundaries (Finset.mem_union_right _ h)
  have hNotIso : ¬ G.IsIsolatedMiddle v := fun hIso =>
    hNotIsoSet ((G.mem_isolatedMiddleRoles_iff v).2 hIso)
  by_contra hNoEdge
  apply hNotIso
  refine ⟨hNotLeft, hNotRight, ?_⟩
  intro e
  constructor
  · intro hSource
    exact hNoEdge ⟨e, Or.inl hSource⟩
  · intro hTarget
    exact hNoEdge ⟨e, Or.inr hTarget⟩

private def chosenIncidentEdge (G : PartiteShape)
    (v : {v : Fin G.roles // v ∈ G.nonisolatedMiddleRoles}) :
    Fin G.edges :=
  Classical.choose (G.exists_incident_edge_of_mem_nonisolatedMiddle v.2)

private theorem chosenIncidentEdge_incident (G : PartiteShape)
    (v : {v : Fin G.roles // v ∈ G.nonisolatedMiddleRoles}) :
    G.EdgeIncident (G.chosenIncidentEdge v) v.1 :=
  Classical.choose_spec (G.exists_incident_edge_of_mem_nonisolatedMiddle v.2)

def BoundaryCleanRightToLeftPaths.remainingMiddleRoles
    (family : G.BoundaryCleanRightToLeftPaths s) : Finset (Fin G.roles) :=
  G.nonisolatedMiddleRoles \ family.pathMiddleRoles

private def BoundaryCleanRightToLeftPaths.candidateExtraEdges
    (family : G.BoundaryCleanRightToLeftPaths s) : Finset (Fin G.edges) := by
  classical
  exact family.remainingMiddleRoles.attach.image fun v =>
    G.chosenIncidentEdge
      ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩

/-- Extra selected edges, excluding path edges so the two ordering phases are
disjoint.  A selected edge already on a path needs no second occurrence. -/
def BoundaryCleanRightToLeftPaths.extraEdges
    (family : G.BoundaryCleanRightToLeftPaths s) : Finset (Fin G.edges) :=
  family.candidateExtraEdges \ family.pathEdges

def BoundaryCleanRightToLeftPaths.orderingEdges
    (family : G.BoundaryCleanRightToLeftPaths s) : Finset (Fin G.edges) :=
  family.pathEdges ∪ family.extraEdges

def CoversNonisolatedMiddle (G : PartiteShape)
    (edges : Finset (Fin G.edges)) : Prop :=
  ∀ v ∈ G.nonisolatedMiddleRoles,
    ∃ e ∈ edges, G.EdgeIncident e v

private theorem pathMiddleRole_covered
    (family : G.BoundaryCleanRightToLeftPaths s)
    {v : Fin G.roles} (hv : v ∈ family.pathMiddleRoles) :
    ∃ e ∈ family.pathEdges, G.EdgeIncident e v := by
  classical
  rw [BoundaryCleanRightToLeftPaths.pathMiddleRoles] at hv
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨(family.paths.path z.1).edgeAt (family.interiorEdgeIndex z), ?_, ?_⟩
  · rw [BoundaryCleanRightToLeftPaths.pathEdges]
    apply Finset.mem_image.2
    exact ⟨⟨z.1, family.interiorEdgeIndex z⟩, Finset.mem_univ _, rfl⟩
  · exact (family.paths.path z.1).edgeAt_incident_edgeEnd
      (family.interiorEdgeIndex z)

theorem BoundaryCleanRightToLeftPaths.orderingEdges_cover
    (family : G.BoundaryCleanRightToLeftPaths s) :
    G.CoversNonisolatedMiddle family.orderingEdges := by
  classical
  intro v hv
  by_cases hPath : v ∈ family.pathMiddleRoles
  · obtain ⟨e, he, hIncident⟩ := pathMiddleRole_covered family hPath
    exact ⟨e, Finset.mem_union_left _ he, hIncident⟩
  · have hRemaining : v ∈ family.remainingMiddleRoles :=
      Finset.mem_sdiff.2 ⟨hv, hPath⟩
    let sv : {v : Fin G.roles // v ∈ family.remainingMiddleRoles} :=
      ⟨v, hRemaining⟩
    let nv : {v : Fin G.roles // v ∈ G.nonisolatedMiddleRoles} :=
      ⟨v, hv⟩
    have hCandidate : G.chosenIncidentEdge nv ∈ family.candidateExtraEdges := by
      rw [BoundaryCleanRightToLeftPaths.candidateExtraEdges]
      apply Finset.mem_image.2
      refine ⟨sv, Finset.mem_attach _ _, ?_⟩
      rfl
    by_cases hOld : G.chosenIncidentEdge nv ∈ family.pathEdges
    · exact ⟨G.chosenIncidentEdge nv, Finset.mem_union_left _ hOld,
        G.chosenIncidentEdge_incident nv⟩
    · have hExtra : G.chosenIncidentEdge nv ∈ family.extraEdges :=
        Finset.mem_sdiff.2 ⟨hCandidate, hOld⟩
      exact ⟨G.chosenIncidentEdge nv, Finset.mem_union_right _ hExtra,
        G.chosenIncidentEdge_incident nv⟩

private theorem isolatedMiddleRoles_subset_middleRoles (G : PartiteShape) :
    G.isolatedMiddleRoles ⊆ G.middleRoles := by
  classical
  intro v hv
  have hIso := (G.mem_isolatedMiddleRoles_iff v).1 hv
  exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, by
    intro h
    rcases Finset.mem_union.mp h with hLeft | hRight
    · exact hIso.1 hLeft
    · exact hIso.2.1 hRight⟩

theorem card_nonisolatedMiddleRoles (G : PartiteShape) :
    G.nonisolatedMiddleRoles.card =
      G.middleRoles.card - G.isolatedMiddleRoles.card := by
  classical
  exact Finset.card_sdiff_of_subset G.isolatedMiddleRoles_subset_middleRoles

private theorem card_extraEdges_le_remaining
    (family : G.BoundaryCleanRightToLeftPaths s) :
    family.extraEdges.card ≤ family.remainingMiddleRoles.card := by
  classical
  have hDiff : family.extraEdges.card ≤ family.candidateExtraEdges.card :=
    Finset.card_le_card Finset.sdiff_subset
  have hImage : family.candidateExtraEdges.card ≤
      family.remainingMiddleRoles.attach.card := by
    simpa [BoundaryCleanRightToLeftPaths.candidateExtraEdges] using
      (Finset.card_image_le :
        (family.remainingMiddleRoles.attach.image
          (fun v => G.chosenIncidentEdge
            ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩)).card ≤
          family.remainingMiddleRoles.attach.card)
  simpa using hDiff.trans hImage

/-- The paper's special edge-ordering count.  Here `k1` and `k2` are actual
deduplicated edge-set cardinalities. -/
theorem BoundaryCleanRightToLeftPaths.pathEdges_add_extraEdges_le
    (family : G.BoundaryCleanRightToLeftPaths s)
    (hSaturates : family.SaturatesCommonBoundary) :
    family.pathEdges.card + family.extraEdges.card ≤
      s - (G.leftBoundary ∩ G.rightBoundary).card +
        (G.middleRoles.card - G.isolatedMiddleRoles.card) := by
  classical
  have hPath := family.card_pathEdges_le_common_add_middle hSaturates
  have hMiddle := family.pathMiddleRoles_subset_nonisolatedMiddle
  have hExtra := card_extraEdges_le_remaining family
  have hRemaining : family.remainingMiddleRoles.card =
      G.nonisolatedMiddleRoles.card - family.pathMiddleRoles.card := by
    exact Finset.card_sdiff_of_subset hMiddle
  have hMiddleCard : family.pathMiddleRoles.card ≤
      G.nonisolatedMiddleRoles.card := Finset.card_le_card hMiddle
  have hIsoCard : G.isolatedMiddleRoles.card ≤ G.middleRoles.card :=
    Finset.card_le_card G.isolatedMiddleRoles_subset_middleRoles
  have hCommonCard : (G.leftBoundary ∩ G.rightBoundary).card ≤ s := by
    rw [← hSaturates]
    simpa using Finset.card_le_card
      (Finset.subset_univ family.commonSingletonIndices)
  have hMiddleCancel :
      G.nonisolatedMiddleRoles.card - family.pathMiddleRoles.card +
        family.pathMiddleRoles.card = G.nonisolatedMiddleRoles.card :=
    Nat.sub_add_cancel hMiddleCard
  have hCommonCancel :
      s - (G.leftBoundary ∩ G.rightBoundary).card +
        (G.leftBoundary ∩ G.rightBoundary).card = s :=
    Nat.sub_add_cancel hCommonCard
  have hIsoCancel :
      G.middleRoles.card - G.isolatedMiddleRoles.card +
        G.isolatedMiddleRoles.card = G.middleRoles.card :=
    Nat.sub_add_cancel hIsoCard
  rw [hRemaining, G.card_nonisolatedMiddleRoles] at hExtra
  have hPathMiddleBound : family.pathMiddleRoles.card ≤
      G.middleRoles.card - G.isolatedMiddleRoles.card := by
    rw [← G.card_nonisolatedMiddleRoles]
    exact hMiddleCard
  have hTogether := Nat.add_le_add hPath hExtra
  calc
    family.pathEdges.card + family.extraEdges.card ≤
        (s - (G.leftBoundary ∩ G.rightBoundary).card +
          family.pathMiddleRoles.card) +
          ((G.middleRoles.card - G.isolatedMiddleRoles.card) -
            family.pathMiddleRoles.card) := hTogether
    _ = s - (G.leftBoundary ∩ G.rightBoundary).card +
        (G.middleRoles.card - G.isolatedMiddleRoles.card) := by
      omega

/-- The two phases are disjoint, hence their sum is exactly the number of
edges in the resulting ordering prefix. -/
theorem BoundaryCleanRightToLeftPaths.card_orderingEdges
    (family : G.BoundaryCleanRightToLeftPaths s) :
    family.orderingEdges.card =
      family.pathEdges.card + family.extraEdges.card := by
  classical
  rw [BoundaryCleanRightToLeftPaths.orderingEdges,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.2 fun e hePath heExtra =>
    (Finset.mem_sdiff.mp heExtra).2 hePath

theorem BoundaryCleanRightToLeftPaths.card_orderingEdges_le
    (family : G.BoundaryCleanRightToLeftPaths s)
    (hSaturates : family.SaturatesCommonBoundary) :
    family.orderingEdges.card ≤
      s - (G.leftBoundary ∩ G.rightBoundary).card +
        (G.middleRoles.card - G.isolatedMiddleRoles.card) := by
  rw [family.card_orderingEdges]
  exact family.pathEdges_add_extraEdges_le hSaturates

/-- Every common-boundary role belongs to every right-left separator, because
its singleton path must meet the separator. -/
private theorem commonBoundary_subset_rightLeftSeparator
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (hCut : G.IsRightLeftSeparator cut) :
    G.leftBoundary ∩ G.rightBoundary ⊆ cut := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hLeft, hRight⟩
  obtain ⟨o, ho⟩ := hCut v hRight
    (PartiteShape.EdgePathToLeft.finish v hLeft)
  simpa [PartiteShape.EdgePathToLeft.vertexAt] using ho

/-- A clean Menger certificate automatically contains exactly one singleton
path for every role of `U ∩ V`.  The proof uses the bijection between its
paths and hits in its equally-sized separator. -/
theorem BoundaryCleanRightLeftMengerCertificate.paths_saturateCommonBoundary
    {G : PartiteShape}
    (certificate : G.BoundaryCleanRightLeftMengerCertificate) :
    certificate.paths.SaturatesCommonBoundary := by
  classical
  let hCut : G.IsRightLeftSeparator certificate.cut :=
    certificate.cut_minimum.1
  let hit := certificate.paths.paths.hitVertex certificate.cut hCut
  have hHitInjective : Function.Injective hit :=
    certificate.paths.paths.hitVertex_injective certificate.cut hCut
  have hHitBijective : Function.Bijective hit := by
    apply (Fintype.bijective_iff_injective_and_card hit).2
    refine ⟨hHitInjective, ?_⟩
    simp
  have hStartInjective : Function.Injective certificate.paths.paths.start := by
    intro i j hij
    have hOccurrence :
        (⟨i, (certificate.paths.paths.path i).headOccurrence⟩ :
            Σ k : Fin certificate.cut.card,
              Fin ((certificate.paths.paths.path k).vertexCount)) =
          ⟨j, (certificate.paths.paths.path j).headOccurrence⟩ := by
      apply certificate.paths.paths.vertexAt_injective
      simpa using hij
    exact congrArg Sigma.fst hOccurrence
  have hStarts :
      certificate.paths.commonSingletonIndices.image
          certificate.paths.paths.start =
        G.leftBoundary ∩ G.rightBoundary := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hLeft : certificate.paths.paths.start i ∈ G.leftBoundary := by
        simpa [BoundaryCleanRightToLeftPaths.commonSingletonIndices] using hi
      exact Finset.mem_inter.2
        ⟨hLeft, certificate.paths.paths.startRight i⟩
    · intro hv
      have hvCut : v ∈ certificate.cut :=
        commonBoundary_subset_rightLeftSeparator G certificate.cut hCut hv
      obtain ⟨i, hi⟩ := hHitBijective.2 ⟨v, hvCut⟩
      let o := hCut.hitOccurrence
        (certificate.paths.paths.start i)
        (certificate.paths.paths.startRight i)
        (certificate.paths.paths.path i)
      have hVertex : (certificate.paths.paths.path i).vertexAt o = v := by
        exact congrArg Subtype.val hi
      have hRightAt :
          (certificate.paths.paths.path i).vertexAt o ∈ G.rightBoundary := by
        rw [hVertex]
        exact (Finset.mem_inter.mp hv).2
      have hoHead : o = (certificate.paths.paths.path i).headOccurrence :=
        (certificate.paths.boundary_clean i).1 o |>.1 hRightAt
      have hStart : certificate.paths.paths.start i = v := by
        calc
          certificate.paths.paths.start i =
              (certificate.paths.paths.path i).vertexAt
                (certificate.paths.paths.path i).headOccurrence := by
            symm
            exact (certificate.paths.paths.path i).vertexAt_headOccurrence
          _ = (certificate.paths.paths.path i).vertexAt o := by rw [hoHead]
          _ = v := hVertex
      apply Finset.mem_image.2
      refine ⟨i, ?_, hStart⟩
      simp only [BoundaryCleanRightToLeftPaths.commonSingletonIndices,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hStart]
      exact (Finset.mem_inter.mp hv).1
  rw [BoundaryCleanRightToLeftPaths.SaturatesCommonBoundary]
  rw [← hStarts,
    Finset.card_image_iff.mpr hStartInjective.injOn]

/-- Consequently the paper count and coverage theorem applies directly to
the path family of every clean Menger certificate. -/
theorem BoundaryCleanRightLeftMengerCertificate.card_orderingEdges_le
    {G : PartiteShape}
    (certificate : G.BoundaryCleanRightLeftMengerCertificate) :
    certificate.paths.orderingEdges.card ≤
      certificate.cut.card -
          (G.leftBoundary ∩ G.rightBoundary).card +
        (G.middleRoles.card - G.isolatedMiddleRoles.card) :=
  certificate.paths.card_orderingEdges_le
    certificate.paths_saturateCommonBoundary

#print axioms PartiteShape.BoundaryCleanRightToLeftPaths.orderingEdges_cover
#print axioms PartiteShape.BoundaryCleanRightToLeftPaths.pathEdges_add_extraEdges_le
#print axioms PartiteShape.BoundaryCleanRightToLeftPaths.card_orderingEdges_le
#print axioms PartiteShape.BoundaryCleanRightLeftMengerCertificate.paths_saturateCommonBoundary
#print axioms PartiteShape.BoundaryCleanRightLeftMengerCertificate.card_orderingEdges_le

end PartiteShape

end GraphMatrixReplica
