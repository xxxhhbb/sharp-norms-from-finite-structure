import R6.C079BoundaryFaithfulSeedGate
import R6.FinitePathLoopErasure

noncomputable section
namespace GraphMatrixReplica

/-- A walk in the induced cut graph gives a right-to-left edge path all of
whose vertices avoid the deleted set. The walk need not be simple here. -/
private theorem cutWalk_to_avoiding_edgePath
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    {u v : {x : Fin G.roles // x ∉ cut}}
    (walk : (G.c079CutGraph cut).Walk u v)
    (hLeft : v.1 ∈ G.leftBoundary) :
    ∃ path : G.EdgePathToLeft u.1,
      ∀ o : Fin path.vertexCount, path.vertexAt o ∉ cut := by
  revert hLeft
  induction walk with
  | @nil a =>
      intro hLeft
      refine ⟨.finish a.1 hLeft, ?_⟩
      intro o
      simpa [PartiteShape.EdgePathToLeft.vertexAt] using a.2
  | @cons a b c hAdj tail ih =>
      intro hLeft
      obtain ⟨tailPath, hAvoid⟩ := ih hLeft
      change (G.c079RoleGraph).Adj a.1 b.1 at hAdj
      obtain ⟨_, e, ha, hb⟩ := hAdj
      refine ⟨.step e b.1 ha hb tailPath, ?_⟩
      intro o
      cases o using Fin.cases with
      | zero => exact a.2
      | succ o => exact hAvoid o

/-- If a cut component meets both external boundaries, it contains an
entire right-to-left path in the surviving graph. -/
theorem PartiteShape.c079_bothBoundaryComponent_gives_avoidingPath
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (c : G.C079CutComponent cut)
    (hR : ∃ v ∈ G.c079ComponentRoles cut c, v ∈ G.rightBoundary)
    (hL : ∃ v ∈ G.c079ComponentRoles cut c, v ∈ G.leftBoundary) :
    ∃ (v : Fin G.roles) (_hRight : v ∈ G.rightBoundary)
      (path : G.EdgePathToLeft v),
      ∀ o : Fin path.vertexCount, path.vertexAt o ∉ cut := by
  obtain ⟨r, hrComp, hrRight⟩ := hR
  obtain ⟨l, hlComp, hlLeft⟩ := hL
  obtain ⟨hrCut, hrEq⟩ := (G.mem_c079ComponentRoles_iff cut c r).mp hrComp
  obtain ⟨hlCut, hlEq⟩ := (G.mem_c079ComponentRoles_iff cut c l).mp hlComp
  have hReach : (G.c079CutGraph cut).Reachable
      ⟨r, hrCut⟩ ⟨l, hlCut⟩ :=
    SimpleGraph.ConnectedComponent.exact (hrEq.trans hlEq.symm)
  obtain ⟨walk, _⟩ := hReach.exists_isPath
  obtain ⟨path, hAvoid⟩ := cutWalk_to_avoiding_edgePath walk hlLeft
  exact ⟨r, hrRight, path, hAvoid⟩

/-- Maximality in path count, even without a full Menger certificate,
excludes every double-boundary component after deleting all packed roles. -/
theorem PartiteShape.VertexDisjointRightToLeftPaths.no_bothBoundaryComponent_of_noAugmentation
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (hMax : ¬ G.HasRightLeftPathPacking (s + 1))
    (c : G.C079CutComponent family.backboneRoles) :
    ¬ ((∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
          v ∈ G.rightBoundary) ∧
        (∃ v ∈ G.c079ComponentRoles family.backboneRoles c,
          v ∈ G.leftBoundary)) := by
  rintro ⟨hR, hL⟩
  obtain ⟨v, hRight, path, hAvoid⟩ :=
    G.c079_bothBoundaryComponent_gives_avoidingPath
      family.backboneRoles c hR hL
  have hSep : G.IsRightLeftSeparator family.usedRoles :=
    family.usedRoles_isRightLeftSeparator_of_meetEverySimplePath
      (family.usedRoles_meetEverySimplePath_of_no_augmentation hMax)
  obtain ⟨o, hUsed⟩ := hSep v hRight path
  have hEq : family.backboneRoles = family.usedRoles := rfl
  exact hAvoid o (hEq ▸ hUsed)

/-- In particular, the chosen maximum-cardinality family has no cut
component touching both boundaries. -/
theorem PartiteShape.maximumPacking_no_bothBoundaryComponent
    (G : PartiteShape)
    (c : G.C079CutComponent
      G.maximumRightLeftPathPacking.backboneRoles) :
    ¬ ((∃ v ∈ G.c079ComponentRoles
          G.maximumRightLeftPathPacking.backboneRoles c,
          v ∈ G.rightBoundary) ∧
        (∃ v ∈ G.c079ComponentRoles
          G.maximumRightLeftPathPacking.backboneRoles c,
          v ∈ G.leftBoundary)) := by
  apply G.maximumRightLeftPathPacking.no_bothBoundaryComponent_of_noAugmentation
  intro hLarger
  obtain ⟨larger⟩ := hLarger
  have hBound := G.pathCount_le_rightLeftPathPackingNumber larger
  omega

#print axioms PartiteShape.c079_bothBoundaryComponent_gives_avoidingPath
#print axioms PartiteShape.VertexDisjointRightToLeftPaths.no_bothBoundaryComponent_of_noAugmentation
#print axioms PartiteShape.maximumPacking_no_bothBoundaryComponent

end GraphMatrixReplica
