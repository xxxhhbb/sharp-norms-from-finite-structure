import R6.U2NormalizedBackbone
/-! # Full C079 normalization: replace each off-backbone component by its seed -/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica

/-- Every seed appearing in an ordered join list is coarsened by the result. -/
theorem c079JoinSeedList_coarsens_seed_of_mem
    {m : ℕ} {κ : Type*} (start : ReplicaPartition m)
    (seed : κ → ReplicaPartition m) (order : List κ)
    (c : κ) (hc : c ∈ order) :
    PartitionCoarsens (c079JoinSeedList start seed order) (seed c) := by
  induction order generalizing start with
  | nil => simp at hc
  | cons d tail ih =>
      rcases List.mem_cons.mp hc with hcd | htail
      · subst d
        change seed c ≤ c079JoinSeedList (start ⊔ seed c) seed tail
        exact le_trans le_sup_right
          (show start ⊔ seed c ≤
            c079JoinSeedList (start ⊔ seed c) seed tail from
            c079JoinSeedList_coarsens _ _ _)
      · exact ih (start ⊔ seed d) htail

theorem ReplicaState.c079ForwardBackbonePartition_coarsens_attachedSeed
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) (c : G.C079CutComponent family.backboneRoles)
    (hc : c ∈ G.c079BackboneAttachmentComponents family x) :
    PartitionCoarsens (S.c079ForwardBackbonePartition family seed x)
      (seed c).1 := by
  exact c079JoinSeedList_coarsens_seed_of_mem
    (S.partition x) (fun d => (seed d).1)
    (G.c079BackboneAttachmentComponents family x).toList c
    (Finset.mem_toList.mpr hc)

/-- The cut-graph component containing an off-backbone role. -/
def PartiteShape.c079OffBackboneComponent
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (y : Fin G.roles) (hy : y ∉ family.backboneRoles) :
    G.C079CutComponent family.backboneRoles :=
  (G.c079CutGraph family.backboneRoles).connectedComponentMk ⟨y, hy⟩

theorem PartiteShape.mem_c079OffBackboneComponent
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (y : Fin G.roles) (hy : y ∉ family.backboneRoles) :
    y ∈ G.c079ComponentRoles family.backboneRoles
      (G.c079OffBackboneComponent family y hy) := by
  apply (G.mem_c079ComponentRoles_iff family.backboneRoles
    (G.c079OffBackboneComponent family y hy) y).2
  exact ⟨hy, rfl⟩

theorem PartiteShape.c079OffBackboneComponent_eq_of_edge
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (y z : Fin G.roles)
    (hy : y ∉ family.backboneRoles)
    (hz : z ∉ family.backboneRoles)
    (e : Fin G.edges)
    (hey : G.EdgeIncident e y)
    (hez : G.EdgeIncident e z) :
    G.c079OffBackboneComponent family y hy =
      G.c079OffBackboneComponent family z hz := by
  have hyComp := G.mem_c079OffBackboneComponent family y hy
  have hzComp := G.c079ComponentRoles_edge_closed_outside_cut
    family.backboneRoles
    (G.c079OffBackboneComponent family y hy)
    hyComp e hey hez hz
  exact (G.mem_c079ComponentRoles_iff family.backboneRoles
    (G.c079OffBackboneComponent family y hy) z).mp hzComp |>.2.symm

/-- A backbone edge endpoint lists the off-backbone endpoint's component
among the seeds adjoined by forward normalization. -/
theorem PartiteShape.offBackboneComponent_mem_attachment_of_edge
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (x y : Fin G.roles)
    (hx : x ∈ family.backboneRoles)
    (hy : y ∉ family.backboneRoles)
    (e : Fin G.edges)
    (hex : G.EdgeIncident e x)
    (hey : G.EdgeIncident e y) :
    G.c079OffBackboneComponent family y hy ∈
      G.c079BackboneAttachmentComponents family x := by
  classical
  simp only [c079BackboneAttachmentComponents,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hx, y, G.mem_c079OffBackboneComponent family y hy,
    e, hex, hey⟩

#print axioms c079JoinSeedList_coarsens_seed_of_mem
#print axioms ReplicaState.c079ForwardBackbonePartition_coarsens_attachedSeed
#print axioms PartiteShape.c079OffBackboneComponent_eq_of_edge
#print axioms PartiteShape.offBackboneComponent_mem_attachment_of_edge

/-- A matching seed makes any two partitions coarsening it edge-compatible. -/
theorem edgeParityCompatible_of_matchingSeed
    {q : ℕ} (π σ : ReplicaPartition q)
    (θ : C079MatchingPartition q)
    (hπ : PartitionCoarsens π θ.1)
    (hσ : PartitionCoarsens σ θ.1) :
    EdgeParityCompatible π σ := by
  obtain ⟨ρ, hρ⟩ := θ.2
  apply edgeParityCompatible_of_commonMatching π σ ρ
  · simpa only [hρ] using hπ
  · simpa only [hρ] using hσ

theorem leftPerfectMatching_leftTrace (p : ℕ) :
    LeftTraceCoarsens (leftPerfectMatching p).partition := by
  have hPair : PairEquivCoarsens
      (leftPerfectMatching p).partition (leftPairEquiv p) :=
    (pairEquivCoarsens_iff_partitionCoarsens
      (leftPerfectMatching p).partition (leftPairEquiv p)).2
        (by intro a b h; exact h)
  constructor
  · intro k
    have hrot : finRotate (p + 1) k.castSucc = k.succ := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last k)]
      rfl
    simpa only [leftPairEquiv_false, leftPairEquiv_true, hrot]
      using hPair k.castSucc
  · simpa only [leftPairEquiv_false, leftPairEquiv_true,
      finRotate_last] using hPair (Fin.last p)

theorem rightPerfectMatching_rightTrace (p : ℕ) :
    RightTraceCoarsens (rightPerfectMatching (p + 1)).partition := by
  intro k
  rfl

/-- Complete rolewise normalization: backbone partitions absorb every
attached component seed, while each off-backbone role is replaced by the
matching seed of its genuine cut-graph component. -/
@[instance_reducible] def ReplicaState.c079FullNormalizedPartition
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) : ReplicaPartition (p + 1) :=
  if hx : x ∈ family.backboneRoles then
    S.c079ForwardBackbonePartition family seed x
  else (seed (G.c079OffBackboneComponent family x hx)).1

theorem ReplicaState.c079FullNormalizedPartition_eq_backbone
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) (hx : x ∈ family.backboneRoles) :
    S.c079FullNormalizedPartition family seed x =
      S.c079ForwardBackbonePartition family seed x := by
  simp only [c079FullNormalizedPartition, dif_pos hx]

theorem ReplicaState.c079FullNormalizedPartition_eq_offBackbone
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) (hx : x ∉ family.backboneRoles) :
    S.c079FullNormalizedPartition family seed x =
      (seed (G.c079OffBackboneComponent family x hx)).1 := by
  simp only [c079FullNormalizedPartition, dif_neg hx]

/-- The complete matching-seed replacement is a legal state when seeds are
faithful to the external boundary traces. -/
def ReplicaState.c079FullNormalizedState
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hBoundary : S.C079BoundaryFaithfulSeed family seed) :
    ReplicaState G p where
  partition := S.c079FullNormalizedPartition family seed
  edgeParity := by
    intro e
    let u := G.source e
    let v := G.target e
    have heu : G.EdgeIncident e u := Or.inl rfl
    have hev : G.EdgeIncident e v := Or.inr rfl
    by_cases hu : u ∈ family.backboneRoles
    · by_cases hv : v ∈ family.backboneRoles
      · rw [S.c079FullNormalizedPartition_eq_backbone family seed u hu,
          S.c079FullNormalizedPartition_eq_backbone family seed v hv]
        exact edgeParityCompatible_of_coarsen_both
          (S.partition u) (S.partition v)
          (S.c079ForwardBackbonePartition family seed u)
          (S.c079ForwardBackbonePartition family seed v)
          (S.edgeParity e)
          (S.c079ForwardBackbonePartition_coarsens family seed u)
          (S.c079ForwardBackbonePartition_coarsens family seed v)
      · let c := G.c079OffBackboneComponent family v hv
        have hAttach := G.offBackboneComponent_mem_attachment_of_edge
          family u v hu hv e heu hev
        have hCoarse := S.c079ForwardBackbonePartition_coarsens_attachedSeed
          family seed u c hAttach
        rw [S.c079FullNormalizedPartition_eq_backbone family seed u hu,
          S.c079FullNormalizedPartition_eq_offBackbone family seed v hv]
        exact edgeParityCompatible_of_matchingSeed
          (S.c079ForwardBackbonePartition family seed u)
          (seed c).1 (seed c) hCoarse
          (by intro a b hab; exact hab)
    · by_cases hv : v ∈ family.backboneRoles
      · let c := G.c079OffBackboneComponent family u hu
        have hAttach := G.offBackboneComponent_mem_attachment_of_edge
          family v u hv hu e hev heu
        have hCoarse := S.c079ForwardBackbonePartition_coarsens_attachedSeed
          family seed v c hAttach
        rw [S.c079FullNormalizedPartition_eq_offBackbone family seed u hu,
          S.c079FullNormalizedPartition_eq_backbone family seed v hv]
        exact edgeParityCompatible_of_matchingSeed
          (seed c).1 (S.c079ForwardBackbonePartition family seed v)
          (seed c) (by intro a b hab; exact hab) hCoarse
      · let cu := G.c079OffBackboneComponent family u hu
        let cv := G.c079OffBackboneComponent family v hv
        have hEq : cu = cv :=
          G.c079OffBackboneComponent_eq_of_edge family u v hu hv e heu hev
        rw [S.c079FullNormalizedPartition_eq_offBackbone family seed u hu,
          S.c079FullNormalizedPartition_eq_offBackbone family seed v hv]
        change EdgeParityCompatible (seed cu).1 (seed cv).1
        rw [← hEq]
        exact edgeParityCompatible_of_matchingSeed
          (seed cu).1 (seed cu).1 (seed cu)
          (by intro a b hab; exact hab)
          (by intro a b hab; exact hab)
  leftGlue := by
    intro x hxL
    by_cases hx : x ∈ family.backboneRoles
    · rw [S.c079FullNormalizedPartition_eq_backbone family seed x hx]
      exact leftTraceCoarsens_of_coarsen
        (S.partition x) (S.c079ForwardBackbonePartition family seed x)
        (S.c079ForwardBackbonePartition_coarsens family seed x)
        (S.leftGlue x hxL)
    · rw [S.c079FullNormalizedPartition_eq_offBackbone family seed x hx]
      let c := G.c079OffBackboneComponent family x hx
      have hSeed : seed c =
          (leftPerfectMatching p).toC079MatchingPartition :=
        hBoundary.1 c ⟨x, G.mem_c079OffBackboneComponent family x hx, hxL⟩
      rw [hSeed]
      exact leftPerfectMatching_leftTrace p
  rightGlue := by
    intro x hxR
    by_cases hx : x ∈ family.backboneRoles
    · rw [S.c079FullNormalizedPartition_eq_backbone family seed x hx]
      exact rightTraceCoarsens_of_coarsen
        (S.partition x) (S.c079ForwardBackbonePartition family seed x)
        (S.c079ForwardBackbonePartition_coarsens family seed x)
        (S.rightGlue x hxR)
    · rw [S.c079FullNormalizedPartition_eq_offBackbone family seed x hx]
      let c := G.c079OffBackboneComponent family x hx
      have hSeed : seed c =
          (rightPerfectMatching (p + 1)).toC079MatchingPartition :=
        hBoundary.2 c ⟨x, G.mem_c079OffBackboneComponent family x hx, hxR⟩
      rw [hSeed]
      exact rightPerfectMatching_rightTrace p

/-- Every off-backbone partition in the complete state is exactly the
matching partition assigned to its genuine cut component. -/
theorem ReplicaState.c079FullNormalizedState_offBackbone_matching
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hBoundary : S.C079BoundaryFaithfulSeed family seed)
    (x : Fin G.roles) (hx : x ∉ family.backboneRoles) :
    (S.c079FullNormalizedState family seed hBoundary).partition x =
      (seed (G.c079OffBackboneComponent family x hx)).1 :=
  S.c079FullNormalizedPartition_eq_offBackbone family seed x hx

/-- The block-loss statistic of the *complete* state. A matching replacement
on Q may split an old block and is therefore not charged by this statistic;
its separate switch/reconstruction code remains a later obligation. -/
def ReplicaState.c079FullNormalizedBlockLoss
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hBoundary : S.C079BoundaryFaithfulSeed family seed) : ℕ :=
  (Finset.univ : Finset (Fin G.roles)).sum (fun x =>
    partitionBlockCount (S.partition x) -
      partitionBlockCount
        ((S.c079FullNormalizedState family seed hBoundary).partition x))

/-- Under role coverage, Q's old block count is at most the matching block
count, so Q contributes zero to block loss. The complete state's block loss
is exactly the previously charged forward backbone cost. -/
theorem ReplicaState.c079FullNormalizedBlockLoss_eq_forwardCost
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hBoundary : S.C079BoundaryFaithfulSeed family seed)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) :
    S.c079FullNormalizedBlockLoss family seed hBoundary =
      S.c079ForwardBackboneMergeCost family seed := by
  classical
  unfold c079FullNormalizedBlockLoss c079ForwardBackboneMergeCost
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ family.backboneRoles
  · have hFull :
        (S.c079FullNormalizedState family seed hBoundary).partition x =
          S.c079ForwardBackbonePartition family seed x :=
      S.c079FullNormalizedPartition_eq_backbone family seed x hx
    simp only [hFull, ReplicaState.c079ForwardBackboneNormalizedState]
  · have hFull :
        partitionBlockCount
          ((S.c079FullNormalizedState family seed hBoundary).partition x) =
            p + 1 := by
      rw [S.c079FullNormalizedState_offBackbone_matching
        family seed hBoundary x hx]
      exact (seed (G.c079OffBackboneComponent family x hx)).blockCount_eq
    have hForward :
        (S.c079ForwardBackboneNormalizedState family seed).partition x =
          S.partition x :=
      S.c079ForwardBackboneNormalizedState_eq_offBackbone
        family seed x hx
    have hOldLe : partitionBlockCount (S.partition x) ≤ p + 1 :=
      S.coveredRole_blockCount_le x (hCovered x)
    rw [hFull, hForward]
    simp [Nat.sub_eq_zero_of_le hOldLe]

theorem ReplicaState.c079FullNormalizedBlockLoss_le_three_r_D
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hBoundary : S.C079BoundaryFaithfulSeed family seed)
    (tree : S.C079ComponentSeedTreeCertificate family seed)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) :
    S.c079FullNormalizedBlockLoss family seed hBoundary ≤
      3 * G.roles * S.c079OffBackboneDefect family := by
  rw [S.c079FullNormalizedBlockLoss_eq_forwardCost
    family seed hBoundary hCovered]
  exact S.c079ForwardBackboneMergeCost_le_three_r_D family seed tree

/-- A maximum path family in a covered shape therefore yields one boundary-
faithful, legal, all-Q-matching normalized state with charged block loss at
most `3rD`. -/
theorem ReplicaState.exists_c079FullNormalizedState_of_maximumPacking
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) :
    ∃ seed : G.C079CutComponent
        G.maximumRightLeftPathPacking.backboneRoles →
          C079MatchingPartition (p + 1),
      ∃ hBoundary : S.C079BoundaryFaithfulSeed
          G.maximumRightLeftPathPacking seed,
        (∀ x : Fin G.roles,
          ∀ hx : x ∉ G.maximumRightLeftPathPacking.backboneRoles,
            (S.c079FullNormalizedState
              G.maximumRightLeftPathPacking seed hBoundary).partition x =
                (seed (G.c079OffBackboneComponent
                  G.maximumRightLeftPathPacking x hx)).1) ∧
        S.c079FullNormalizedBlockLoss
          G.maximumRightLeftPathPacking seed hBoundary ≤
            3 * G.roles * S.c079OffBackboneDefect
              G.maximumRightLeftPathPacking := by
  obtain ⟨seed, hBoundary, ⟨tree⟩⟩ :=
    S.exists_boundaryFaithfulComponentSeedTree_of_maximumPacking hCovered
  refine ⟨seed, hBoundary, ?_, ?_⟩
  · intro x hx
    exact S.c079FullNormalizedState_offBackbone_matching
      G.maximumRightLeftPathPacking seed hBoundary x hx
  · exact S.c079FullNormalizedBlockLoss_le_three_r_D
      G.maximumRightLeftPathPacking seed hBoundary tree hCovered

#print axioms edgeParityCompatible_of_matchingSeed
#print axioms leftPerfectMatching_leftTrace
#print axioms rightPerfectMatching_rightTrace
#print axioms ReplicaState.c079FullNormalizedState
#print axioms ReplicaState.c079FullNormalizedBlockLoss_eq_forwardCost
#print axioms ReplicaState.c079FullNormalizedBlockLoss_le_three_r_D
#print axioms ReplicaState.exists_c079FullNormalizedState_of_maximumPacking

end GraphMatrixReplica

