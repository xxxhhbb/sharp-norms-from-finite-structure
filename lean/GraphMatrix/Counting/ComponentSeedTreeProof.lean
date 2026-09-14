import GraphMatrix.Counting.MergeDefectCharge

/-! # Component seed tree: the covered-role criterion

An arbitrary `ReplicaState` may retain an isolated middle role with an odd
partition. Such a role has no matching refinement, so the tree certificate
cannot be constructed without a role-coverage or parity hypothesis. The
counterexample below has actual off-backbone defect zero.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- One isolated role, no graph edges, and no boundary incidences. -/
def c079IsolatedShape : PartiteShape where
  roles := 1
  edges := 0
  source := Fin.elim0
  target := Fin.elim0
  leftBoundary := ∅
  rightBoundary := ∅

/-- The empty path family is a genuine vertex-disjoint family. -/
def c079IsolatedEmptyFamily :
    c079IsolatedShape.VertexDisjointRightToLeftPaths 0 where
  start := Fin.elim0
  startRight := by intro i; exact Fin.elim0 i
  path := by intro i; exact Fin.elim0 i
  vertexAt_injective := by
    intro z
    exact Fin.elim0 z.1

/-- The isolated role is assigned the discrete two-replica partition. -/
def c079IsolatedDiscreteState : ReplicaState c079IsolatedShape 0 where
  partition := fun _ => ⊥
  edgeParity := by intro e; exact Fin.elim0 e
  leftGlue := by
    intro v hv
    exact False.elim ((Finset.notMem_empty v) hv)
  rightGlue := by
    intro v hv
    exact False.elim ((Finset.notMem_empty v) hv)

def c079IsolatedRole : Fin c079IsolatedShape.roles :=
  ⟨0, by decide⟩

theorem c079IsolatedDiscrete_blockCount :
    partitionBlockCount
      (c079IsolatedDiscreteState.partition c079IsolatedRole) = 2 := by
  classical
  change partitionBlockCount (⊥ : ReplicaPartition 1) = 2
  unfold partitionBlockCount
  calc
    Fintype.card (Quotient (⊥ : ReplicaPartition 1)) =
        Fintype.card (Replica 1) :=
      Fintype.card_congr Setoid.quotientBotEquiv
    _ = 2 := by simp [Replica]

/-- In the counterexample, the actual off-backbone defect is zero. -/
theorem c079IsolatedDiscrete_offBackboneDefect_zero :
    c079IsolatedDiscreteState.c079OffBackboneDefect
      c079IsolatedEmptyFamily = 0 := by
  classical
  have hcard : ∀ v : Fin c079IsolatedShape.roles,
      partitionBlockCount (c079IsolatedDiscreteState.partition v) = 2 := by
    intro v
    have hv : v = c079IsolatedRole := by
      apply Fin.ext
      change v.val = 0
      have hlt : v.val < 1 := by simpa [c079IsolatedShape] using v.isLt
      omega
    rw [hv]
    exact c079IsolatedDiscrete_blockCount
  unfold ReplicaState.c079OffBackboneDefect
  simp [hcard]

/-- `D=0` does not even ensure that all roles have matching refinements. -/
theorem c079IsolatedDiscrete_no_componentSeedTree :
    ¬ Nonempty (c079IsolatedDiscreteState.C079ComponentSeedTreeCertificate
        c079IsolatedEmptyFamily
        (fun _ => (leftPerfectMatching 0).toC079MatchingPartition)) := by
  rintro ⟨tree⟩
  have hrefines := tree.roleRefines c079IsolatedRole
  have hcard := c079_blockCount_le_of_coarsens hrefines
  rw [c079IsolatedDiscrete_blockCount,
    (tree.roleMatching c079IsolatedRole).blockCount_eq] at hcard
  omega

/-- A graph walk whose endpoint metric changes by at most the two endpoint
weights on each edge is charged at most twice the weight of its vertex list.
For a simple path the list has no duplicates. -/
private theorem c079_walk_distance_le_two_support_sum
    {V : Type*} (H : SimpleGraph V)
    (distance : V → V → ℕ) (weight : V → ℕ)
    (hSelf : ∀ u, distance u u = 0)
    (hTriangle : ∀ u v w,
      distance u w ≤ distance u v + distance v w)
    (hEdge : ∀ u v, H.Adj u v →
      distance u v ≤ weight u + weight v)
    {u v : V} (walk : H.Walk u v) :
    distance u v + weight u + weight v ≤
      2 * (walk.support.map weight).sum := by
  induction walk with
  | nil =>
      simp [hSelf]
      omega
  | @cons u v w h tail ih =>
      have hTri := hTriangle u v w
      have hOne := hEdge u v h
      simp only [SimpleGraph.Walk.support_cons, List.map_cons,
        List.sum_cons]
      omega

/-- Coverage gives the parity needed to choose one matching refinement at
every role. This is the exact assumption absent in the isolated counterexample. -/
theorem ReplicaState.c079_coveredRole_even
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (v : Fin G.roles) : IsEvenPartition (S.partition v) := by
  rcases hCovered v with ⟨e, he | he⟩ | hL | hR
  · simpa only [he] using
      edgeParityCompatible_even_left
        (S.partition (G.source e)) (S.partition (G.target e))
        (S.edgeParity e)
  · simpa only [he] using
      edgeParityCompatible_even_right
        (S.partition (G.source e)) (S.partition (G.target e))
        (S.edgeParity e)
  · exact leftTraceCoarsens_evenPartition (S.partition v) (S.leftGlue v hL)
  · exact rightTraceCoarsens_evenPartition (S.partition v) (S.rightGlue v hR)

/-- The matching distance across one actual edge of the cut graph is
charged to its two endpoint partition defects. -/
theorem ReplicaState.c079_cutEdge_matchingDistance_le_defects
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (cut : Finset (Fin G.roles))
    (σ : Fin G.roles → C079MatchingPartition (p + 1))
    (hRefines : ∀ v : Fin G.roles,
      PartitionCoarsens (S.partition v) (σ v).1)
    {u v : {z : Fin G.roles // z ∉ cut}}
    (hAdj : (G.c079CutGraph cut).Adj u v) :
    c079MatchingPartitionDistance (σ u.1) (σ v.1) ≤
      ((p + 1) - partitionBlockCount (S.partition u.1)) +
        ((p + 1) - partitionBlockCount (S.partition v.1)) := by
  change (G.c079RoleGraph).Adj u.1 v.1 at hAdj
  obtain ⟨_, e, hue, hve⟩ := hAdj
  let ξ : C079MatchingPartition (p + 1) :=
    (S.edgePerfectMatching e).toC079MatchingPartition
  have hξu : PartitionCoarsens (S.partition u.1) ξ.1 :=
    S.partition_coarsens_edgePerfectMatching_of_incident e u.1 hue
  have hξv : PartitionCoarsens (S.partition v.1) ξ.1 :=
    S.partition_coarsens_edgePerfectMatching_of_incident e v.1 hve
  calc
    c079MatchingPartitionDistance (σ u.1) (σ v.1) ≤
        c079MatchingPartitionDistance (σ u.1) ξ +
          c079MatchingPartitionDistance ξ (σ v.1) :=
      c079MatchingPartitionDistance_triangle (σ u.1) ξ (σ v.1)
    _ ≤ ((p + 1) - partitionBlockCount (S.partition u.1)) +
          ((p + 1) - partitionBlockCount (S.partition v.1)) :=
      Nat.add_le_add
        (c079MatchingPartitionDistance_le_partitionDefect
          (S.partition u.1) (σ u.1) ξ (hRefines u.1) hξu)
        (c079MatchingPartitionDistance_le_partitionDefect
          (S.partition v.1) ξ (σ v.1) hξv (hRefines v.1))

/-- Any two role matchings in one genuine cut-graph component are within
twice the sum of its actual partition defects. A simple path eliminates
repeated-vertex charges. -/
theorem ReplicaState.c079_componentMatchingDistance_le_two_defect
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (σ : Fin G.roles → C079MatchingPartition (p + 1))
    (hRefines : ∀ v : Fin G.roles,
      PartitionCoarsens (S.partition v) (σ v).1)
    (c : G.C079CutComponent family.backboneRoles)
    (x y : Fin G.roles)
    (hx : x ∈ G.c079ComponentRoles family.backboneRoles c)
    (hy : y ∈ G.c079ComponentRoles family.backboneRoles c) :
    c079MatchingPartitionDistance (σ x) (σ y) ≤
      2 * S.c079ComponentDefect family c := by
  classical
  let cut := family.backboneRoles
  let H := G.c079CutGraph cut
  obtain ⟨hxCut, hxComp⟩ :=
    (G.mem_c079ComponentRoles_iff cut c x).1 hx
  obtain ⟨hyCut, hyComp⟩ :=
    (G.mem_c079ComponentRoles_iff cut c y).1 hy
  have hReach : H.Reachable ⟨x, hxCut⟩ ⟨y, hyCut⟩ :=
    SimpleGraph.ConnectedComponent.exact (hxComp.trans hyComp.symm)
  obtain ⟨walk, hPath⟩ := hReach.exists_isPath
  let distance : {z : Fin G.roles // z ∉ cut} →
      {z : Fin G.roles // z ∉ cut} → ℕ :=
    fun u v => c079MatchingPartitionDistance (σ u.1) (σ v.1)
  let weight : {z : Fin G.roles // z ∉ cut} → ℕ :=
    fun z => (p + 1) - partitionBlockCount (S.partition z.1)
  have hSelf : ∀ u, distance u u = 0 := by
    intro u
    exact (c079MatchingPartitionDistance_eq_zero_iff_eq (σ u.1) (σ u.1)).2 rfl
  have hTriangle : ∀ u v w,
      distance u w ≤ distance u v + distance v w := by
    intro u v w
    exact c079MatchingPartitionDistance_triangle (σ u.1) (σ v.1) (σ w.1)
  have hEdge : ∀ u v, H.Adj u v →
      distance u v ≤ weight u + weight v := by
    intro u v huv
    exact S.c079_cutEdge_matchingDistance_le_defects cut σ hRefines huv
  have hWalk := c079_walk_distance_le_two_support_sum
    H distance weight hSelf hTriangle hEdge walk
  have hSupportIn : ∀ z ∈ walk.support.toFinset,
      z.1 ∈ G.c079ComponentRoles cut c := by
    intro z hz
    have hzList : z ∈ walk.support := by simpa using hz
    have hZReach : H.Reachable ⟨x, hxCut⟩ z :=
      (walk.takeUntil z hzList).reachable
    have hzComp : H.connectedComponentMk z = c :=
      (SimpleGraph.ConnectedComponent.sound hZReach).symm.trans hxComp
    exact (G.mem_c079ComponentRoles_iff cut c z.1).2 ⟨z.2, hzComp⟩
  have hImageSubset : walk.support.toFinset.image Subtype.val ⊆
      G.c079ComponentRoles cut c := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact hSupportIn v hv
  have hSupportSum : (walk.support.map weight).sum ≤
      S.c079ComponentDefect family c := by
    calc
      (walk.support.map weight).sum =
          walk.support.toFinset.sum weight :=
        (List.sum_toFinset weight hPath.support_nodup).symm
      _ = (walk.support.toFinset.image Subtype.val).sum
          (fun v : Fin G.roles =>
            (p + 1) - partitionBlockCount (S.partition v)) := by
        rw [Finset.sum_image]
        exact Subtype.val_injective.injOn
      _ ≤ S.c079ComponentDefect family c := by
        change (walk.support.toFinset.image Subtype.val).sum
          (fun v : Fin G.roles =>
            (p + 1) - partitionBlockCount (S.partition v)) ≤
          (G.c079ComponentRoles cut c).sum
            (fun v : Fin G.roles =>
              (p + 1) - partitionBlockCount (S.partition v))
        exact Finset.sum_le_sum_of_subset hImageSubset
  change distance ⟨x, hxCut⟩ ⟨y, hyCut⟩ ≤
    2 * S.c079ComponentDefect family c
  omega

/-- If every role already has one matching refinement, choose each
component seed at a fixed representative role. The simple-path theorem gives
the complete `2D_C` tree certificate. -/
theorem ReplicaState.exists_c079ComponentSeedTree_of_roleRefinements
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (σ : Fin G.roles → C079MatchingPartition (p + 1))
    (hRefines : ∀ v : Fin G.roles,
      PartitionCoarsens (S.partition v) (σ v).1) :
    ∃ seed : G.C079CutComponent family.backboneRoles →
        C079MatchingPartition (p + 1),
      Nonempty (S.C079ComponentSeedTreeCertificate family seed) := by
  classical
  let anchor (c : G.C079CutComponent family.backboneRoles) : Fin G.roles :=
    Classical.choose (G.c079ComponentRoles_nonempty family.backboneRoles c)
  have hAnchor (c : G.C079CutComponent family.backboneRoles) :
      anchor c ∈ G.c079ComponentRoles family.backboneRoles c :=
    Classical.choose_spec (G.c079ComponentRoles_nonempty family.backboneRoles c)
  let seed (c : G.C079CutComponent family.backboneRoles) := σ (anchor c)
  refine ⟨seed, ⟨{
    roleMatching := σ
    roleRefines := hRefines
    seedDistance := ?_
  }⟩⟩
  intro c y hy
  exact S.c079_componentMatchingDistance_le_two_defect
    family σ hRefines c y (anchor c) hy (hAnchor c)

/-- Coverage is the precise additional hypothesis that excludes the
isolated odd-block obstruction. It supplies canonical role matching
refinements, after which every genuine component receives a seed obeying
the paper's `2D_C` tree-distance bound. -/
theorem ReplicaState.exists_c079ComponentSeedTree_of_covered
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    ∃ seed : G.C079CutComponent family.backboneRoles →
        C079MatchingPartition (p + 1),
      Nonempty (S.C079ComponentSeedTreeCertificate family seed) := by
  let σ : Fin G.roles → C079MatchingPartition (p + 1) := fun v =>
    c079CanonicalMatchingRefinement (S.partition v)
      (S.c079_coveredRole_even hCovered v)
  have hRefines : ∀ v : Fin G.roles,
      PartitionCoarsens (S.partition v) (σ v).1 := by
    intro v
    exact c079CanonicalMatchingRefinement_refines
      (S.partition v) (S.c079_coveredRole_even hCovered v)
  exact S.exists_c079ComponentSeedTree_of_roleRefinements
    family σ hRefines

/-- The covered-state construction closes the previously conditional
forward-backbone merge charge, including ordered role words and decoding. -/
theorem ReplicaState.exists_c079ForwardBackboneMergeWords_of_covered
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    ∃ seed : G.C079CutComponent family.backboneRoles →
        C079MatchingPartition (p + 1),
      ∃ words : Fin G.roles →
          List (Replica (p + 1) × Replica (p + 1)),
        (∀ x : Fin G.roles,
          c079DecodeMergeWord (S.partition x) (words x) =
            S.c079ForwardBackbonePartition family seed x) ∧
        ((Finset.univ : Finset (Fin G.roles)).sum
          (fun x : Fin G.roles => (words x).length)) ≤
            3 * G.roles * S.c079OffBackboneDefect family := by
  obtain ⟨seed, ⟨tree⟩⟩ :=
    S.exists_c079ComponentSeedTree_of_covered family hCovered
  obtain ⟨words, hDecode, hLength⟩ :=
    S.exists_c079ForwardBackboneMergeWords_of_tree family seed tree
  exact ⟨seed, words, hDecode, hLength⟩


end GraphMatrixReplica
