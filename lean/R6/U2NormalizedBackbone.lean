import R6.C079BoundaryFaithfulSeedConstruction

/-! # Legal forward backbone normalization and its merge charge

The existing forward operation coarsens backbone role partitions by seeds of
attached cut components and leaves off-backbone roles unchanged. We prove that
this produces a genuine replica state: edge parity and both trace constraints
survive rolewise coarsening. The charged merge cost is the sum of block losses.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- If both endpoint partitions coarsen one perfect matching, their meet
cells are even. -/
theorem edgeParityCompatible_of_commonMatching
    {q : ℕ} (π σ : ReplicaPartition q) (ρ : PerfectMatching q)
    (hπ : PartitionCoarsens π ρ.partition)
    (hσ : PartitionCoarsens σ ρ.partition) :
    EdgeParityCompatible π σ := by
  classical
  let keyPartition : ReplicaPartition q :=
    equalityPartition (edgeClassKey π σ)
  have hKey : PartitionCoarsens keyPartition ρ.partition := by
    intro a b hab
    change edgeClassKey π σ a = edgeClassKey π σ b
    exact Prod.ext (Quotient.sound (hπ a b hab))
      (Quotient.sound (hσ a b hab))
  have hPairs : PairEquivCoarsens keyPartition ρ.pairingEquiv :=
    (pairEquivCoarsens_iff_partitionCoarsens
      keyPartition ρ.pairingEquiv).2 hKey
  have hEven := pairEquivCoarsens_evenPartition
    keyPartition ρ.pairingEquiv hPairs
  intro a
  have hBlock : partitionBlock keyPartition a =
      partitionMeetCell π σ a := by
    calc
      partitionBlock keyPartition a =
          edgeClassFiber π σ (edgeClassKey π σ a) := by
        ext b
        simp [partitionBlock, keyPartition, edgeClassFiber]
      _ = partitionMeetCell π σ a :=
        edgeClassKey_fiber_eq_meetCell π σ a
  rw [← hBlock]
  exact hEven a

/-- Rademacher edge parity is preserved when both endpoint equality
partitions are coarsened. -/
theorem edgeParityCompatible_of_coarsen_both
    {q : ℕ} (π σ π' σ' : ReplicaPartition q)
    (hEdge : EdgeParityCompatible π σ)
    (hπ : PartitionCoarsens π' π)
    (hσ : PartitionCoarsens σ' σ) :
    EdgeParityCompatible π' σ' := by
  obtain ⟨ρ, hρπ, hρσ⟩ :=
    exists_perfectMatching_coarsened_by_edgeEndpoints π σ hEdge
  exact edgeParityCompatible_of_commonMatching π' σ' ρ
    (fun a b hab => hπ a b (hρπ a b hab))
    (fun a b hab => hσ a b (hρσ a b hab))

/-- A trace gluing constraint survives any coarsening of its partition. -/
theorem leftTraceCoarsens_of_coarsen
    {p : ℕ} (π π' : ReplicaPartition (p + 1))
    (hπ : PartitionCoarsens π' π)
    (hTrace : LeftTraceCoarsens π) :
    LeftTraceCoarsens π' := by
  constructor
  · intro k
    exact hπ _ _ (hTrace.1 k)
  · exact hπ _ _ hTrace.2

theorem rightTraceCoarsens_of_coarsen
    {p : ℕ} (π π' : ReplicaPartition (p + 1))
    (hπ : PartitionCoarsens π' π)
    (hTrace : RightTraceCoarsens π) :
    RightTraceCoarsens π' := by
  intro k
  exact hπ _ _ (hTrace k)

/-- The real forward backbone normalization as a typed, legal replica state.
Off-backbone roles retain their original partitions. -/
def ReplicaState.c079ForwardBackboneNormalizedState
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1)) : ReplicaState G p where
  partition := S.c079ForwardBackbonePartition family seed
  edgeParity := by
    intro e
    exact edgeParityCompatible_of_coarsen_both
      (S.partition (G.source e)) (S.partition (G.target e))
      (S.c079ForwardBackbonePartition family seed (G.source e))
      (S.c079ForwardBackbonePartition family seed (G.target e))
      (S.edgeParity e)
      (S.c079ForwardBackbonePartition_coarsens family seed (G.source e))
      (S.c079ForwardBackbonePartition_coarsens family seed (G.target e))
  leftGlue := by
    intro v hv
    exact leftTraceCoarsens_of_coarsen
      (S.partition v) (S.c079ForwardBackbonePartition family seed v)
      (S.c079ForwardBackbonePartition_coarsens family seed v)
      (S.leftGlue v hv)
  rightGlue := by
    intro v hv
    exact rightTraceCoarsens_of_coarsen
      (S.partition v) (S.c079ForwardBackbonePartition family seed v)
      (S.c079ForwardBackbonePartition_coarsens family seed v)
      (S.rightGlue v hv)

/-- Explicit block-loss charge of the legal normalized state. -/
def ReplicaState.c079ForwardBackboneMergeCost
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1)) : ℕ :=
  (Finset.univ : Finset (Fin G.roles)).sum (fun x =>
    partitionBlockCount (S.partition x) -
      partitionBlockCount
        ((S.c079ForwardBackboneNormalizedState family seed).partition x))

theorem ReplicaState.c079ForwardBackboneMergeCost_le_three_r_D
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (tree : S.C079ComponentSeedTreeCertificate family seed) :
    S.c079ForwardBackboneMergeCost family seed ≤
      3 * G.roles * S.c079OffBackboneDefect family := by
  simpa only [ReplicaState.c079ForwardBackboneMergeCost,
    ReplicaState.c079ForwardBackboneNormalizedState] using
    S.c079_forwardBackbone_totalBlockLoss_le_three_r_D
      family seed (tree.toAttachmentCertificate S family seed)

theorem ReplicaState.c079ForwardBackboneNormalizedState_eq_offBackbone
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) (hx : x ∉ family.backboneRoles) :
    (S.c079ForwardBackboneNormalizedState family seed).partition x =
      S.partition x :=
  S.c079ForwardBackbonePartition_eq_of_offBackbone family seed x hx

/-- At maximum path packing, boundary-faithful seeds give a legal normalized
state whose actual block-loss merge cost is at most `3rD`. -/
theorem ReplicaState.exists_boundaryFaithfulNormalizedState_of_maximumPacking
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    ∃ seed : G.C079CutComponent
        G.maximumRightLeftPathPacking.backboneRoles →
          C079MatchingPartition (p + 1),
      S.C079BoundaryFaithfulSeed G.maximumRightLeftPathPacking seed ∧
        S.c079ForwardBackboneMergeCost
          G.maximumRightLeftPathPacking seed ≤
            3 * G.roles * S.c079OffBackboneDefect
              G.maximumRightLeftPathPacking := by
  obtain ⟨seed, hBoundary, ⟨tree⟩⟩ :=
    S.exists_boundaryFaithfulComponentSeedTree_of_maximumPacking hCovered
  exact ⟨seed, hBoundary,
    S.c079ForwardBackboneMergeCost_le_three_r_D
      G.maximumRightLeftPathPacking seed tree⟩

#print axioms edgeParityCompatible_of_commonMatching
#print axioms edgeParityCompatible_of_coarsen_both
#print axioms ReplicaState.c079ForwardBackboneMergeCost_le_three_r_D
#print axioms ReplicaState.exists_boundaryFaithfulNormalizedState_of_maximumPacking

end GraphMatrixReplica
