import R6.C079MaxPackingBoundaryComponent

/-! # Boundary-faithful component seed tree over a maximum path packing -/

noncomputable section
namespace GraphMatrixReplica

/-- A component can receive its prescribed boundary trace matching while
retaining the `2D_C` tree estimate, provided no component meets both
boundaries. The role map prioritizes a trace matching at boundary roles and
uses a canonical matching refinement elsewhere. -/
theorem ReplicaState.exists_boundaryFaithfulComponentSeedTree
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (hNoBoth : ∀ c : G.C079CutComponent family.backboneRoles,
      ¬ ((∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
            v ∈ G.leftBoundary) ∧
          (∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
            v ∈ G.rightBoundary))) :
    ∃ seed : G.C079CutComponent family.backboneRoles →
        C079MatchingPartition (p + 1),
      S.C079BoundaryFaithfulSeed family seed ∧
        Nonempty (S.C079ComponentSeedTreeCertificate family seed) := by
  classical
  let τ : C079MatchingPartition (p + 1) :=
    (leftPerfectMatching p).toC079MatchingPartition
  let η : C079MatchingPartition (p + 1) :=
    (rightPerfectMatching (p + 1)).toC079MatchingPartition
  let σ : Fin G.roles → C079MatchingPartition (p + 1) := fun v =>
    if hL : v ∈ G.leftBoundary then τ
    else if hR : v ∈ G.rightBoundary then η
    else c079CanonicalMatchingRefinement (S.partition v)
      (S.c079_coveredRole_even hCovered v)
  have hRefines : ∀ v : Fin G.roles,
      PartitionCoarsens (S.partition v) (σ v).1 := by
    intro v
    by_cases hL : v ∈ G.leftBoundary
    · simpa only [σ, dif_pos hL, τ,
        PerfectMatching.toC079MatchingPartition] using
        leftTraceCoarsens_partitionCoarsens
          (S.partition v) (S.leftGlue v hL)
    · by_cases hR : v ∈ G.rightBoundary
      · simpa only [σ, dif_neg hL, dif_pos hR, η,
          PerfectMatching.toC079MatchingPartition] using
          rightTraceCoarsens_partitionCoarsens
            (S.partition v) (S.rightGlue v hR)
      · simpa only [σ, dif_neg hL, dif_neg hR] using
          c079CanonicalMatchingRefinement_refines
            (S.partition v) (S.c079_coveredRole_even hCovered v)
  let hLeft (c : G.C079CutComponent family.backboneRoles) : Prop :=
    ∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
      v ∈ G.leftBoundary
  let hRight (c : G.C079CutComponent family.backboneRoles) : Prop :=
    ∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
      v ∈ G.rightBoundary
  let anchor (c : G.C079CutComponent family.backboneRoles) : Fin G.roles :=
    Classical.choose (G.c079ComponentRoles_nonempty family.backboneRoles c)
  have hAnchor (c : G.C079CutComponent family.backboneRoles) :
      anchor c ∈ G.c079ComponentRoles family.backboneRoles c :=
    Classical.choose_spec (G.c079ComponentRoles_nonempty family.backboneRoles c)
  let seed (c : G.C079CutComponent family.backboneRoles) :=
    if hCL : hLeft c then τ
    else if hCR : hRight c then η
    else σ (anchor c)
  refine ⟨seed, ?_, ⟨{
    roleMatching := σ
    roleRefines := hRefines
    seedDistance := ?_
  }⟩⟩
  · constructor
    · intro c hc
      change seed c = τ
      dsimp only [seed]
      rw [dif_pos (show hLeft c from hc)]
    · intro c hc
      have hnL : ¬ hLeft c := by
        intro hL
        exact hNoBoth c ⟨hL, hc⟩
      change seed c = η
      dsimp only [seed]
      rw [dif_neg hnL, dif_pos (show hRight c from hc)]
  · intro c y hy
    by_cases hCL : hLeft c
    · obtain ⟨b, hb, hbL⟩ := hCL
      have hCL' : hLeft c := ⟨b, hb, hbL⟩
      have hσb : σ b = τ := by simp only [σ, dif_pos hbL]
      have hDist := S.c079_componentMatchingDistance_le_two_defect
        family σ hRefines c y b hy hb
      simpa only [seed, dif_pos hCL', hσb] using hDist
    · by_cases hCR : hRight c
      · obtain ⟨b, hb, hbR⟩ := hCR
        have hCR' : hRight c := ⟨b, hb, hbR⟩
        have hbNL : b ∉ G.leftBoundary := by
          intro hbL
          exact hCL ⟨b, hb, hbL⟩
        have hσb : σ b = η := by
          simp only [σ, dif_neg hbNL, dif_pos hbR]
        have hDist := S.c079_componentMatchingDistance_le_two_defect
          family σ hRefines c y b hy hb
        simpa only [seed, dif_neg hCL, dif_pos hCR', hσb] using hDist
      · have hDist := S.c079_componentMatchingDistance_le_two_defect
          family σ hRefines c y (anchor c) hy (hAnchor c)
        simpa only [seed, dif_neg hCL, dif_neg hCR] using hDist

/-- For the internally chosen maximum packing, the necessary no-both
condition follows from strict path-packing maximality. -/
theorem ReplicaState.exists_boundaryFaithfulComponentSeedTree_of_maximumPacking
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    ∃ seed : G.C079CutComponent
        G.maximumRightLeftPathPacking.backboneRoles →
          C079MatchingPartition (p + 1),
      S.C079BoundaryFaithfulSeed G.maximumRightLeftPathPacking seed ∧
        Nonempty (S.C079ComponentSeedTreeCertificate
          G.maximumRightLeftPathPacking seed) := by
  exact S.exists_boundaryFaithfulComponentSeedTree
    G.maximumRightLeftPathPacking hCovered
    (by
      intro c hBoth
      exact (G.maximumPacking_no_bothBoundaryComponent c)
        ⟨hBoth.2, hBoth.1⟩)

#print axioms ReplicaState.exists_boundaryFaithfulComponentSeedTree
#print axioms ReplicaState.exists_boundaryFaithfulComponentSeedTree_of_maximumPacking

end GraphMatrixReplica

