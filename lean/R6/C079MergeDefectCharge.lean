import R6.C079PartitionMergeWord
import R6.C079BackboneDefectSplit
import R6.C079ActiveComponents

/-! # C079 forward-merge charge on genuine off-backbone components

The component defect is the sum of actual partition defects of its roles.
The local seed-distance certificate used in the paper is kept explicit until
its spanning-tree construction has been formalized. No full state encoder or
all-defect count follows from the present charge alone.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Constant-on-block subspaces turn the equivalence closure of two
partitions into intersection. -/
theorem c079_partitionConstantSubspace_sup {m : ℕ}
    (π ρ : ReplicaPartition m) :
    partitionConstantSubspace (K := ℚ) (π ⊔ ρ) =
      partitionConstantSubspace (K := ℚ) π ⊓
        partitionConstantSubspace (K := ℚ) ρ := by
  ext f
  rw [Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨partitionConstantSubspace_mono (K := ℚ)
        (show PartitionCoarsens (π ⊔ ρ) π from by
          change π ≤ π ⊔ ρ
          exact le_sup_left) h,
      partitionConstantSubspace_mono (K := ℚ)
        (show PartitionCoarsens (π ⊔ ρ) ρ from by
          change ρ ≤ π ⊔ ρ
          exact le_sup_right) h⟩
  · rintro ⟨hπ, hρ⟩
    change (π ⊔ ρ) ≤ Setoid.ker f
    apply sup_le
    · exact hπ
    · exact hρ

/-- Coarsening the starting partition cannot increase the block loss of a
subsequent fixed merge. This is the dimension submodularity step. -/
theorem c079_sup_blockLoss_mono {m : ℕ}
    (fine coarse ρ : ReplicaPartition m)
    (h : PartitionCoarsens coarse fine) :
    partitionBlockCount coarse - partitionBlockCount (coarse ⊔ ρ) ≤
      partitionBlockCount fine - partitionBlockCount (fine ⊔ ρ) := by
  let P : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) coarse
  let T : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) fine
  let R : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) ρ
  have hPT : P ≤ T := partitionConstantSubspace_mono h
  have hCross := finrank_inf_add_finrank_inf_le P T R
  have hPinfT : P ⊓ T = P := inf_eq_left.mpr hPT
  rw [hPinfT] at hCross
  have hRank : partitionBlockCount coarse +
      partitionBlockCount (fine ⊔ ρ) ≤
      partitionBlockCount fine +
        partitionBlockCount (coarse ⊔ ρ) := by
    change Module.finrank ℚ P + Module.finrank ℚ ↑(T ⊓ R) ≤
      Module.finrank ℚ T + Module.finrank ℚ ↑(P ⊓ R) at hCross
    rw [finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) coarse,
      finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) fine,
      ← c079_partitionConstantSubspace_sup coarse ρ,
      ← c079_partitionConstantSubspace_sup fine ρ,
      finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) (fine ⊔ ρ),
      finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) (coarse ⊔ ρ)] at hCross
    exact hCross
  have hCoarseSup : partitionBlockCount (coarse ⊔ ρ) ≤
      partitionBlockCount coarse := by
    rw [← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) (coarse ⊔ ρ),
      ← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) coarse]
    exact Submodule.finrank_mono (partitionConstantSubspace_mono
      (show PartitionCoarsens (coarse ⊔ ρ) coarse from by
        change coarse ≤ coarse ⊔ ρ
        exact le_sup_left))
  have hFineSup : partitionBlockCount (fine ⊔ ρ) ≤
      partitionBlockCount fine := by
    rw [← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) (fine ⊔ ρ),
      ← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) fine]
    exact Submodule.finrank_mono (partitionConstantSubspace_mono
      (show PartitionCoarsens (fine ⊔ ρ) fine from by
        change fine ≤ fine ⊔ ρ
        exact le_sup_left))
  omega

/-- A coarsening has no more blocks than the original partition. -/
theorem c079_blockCount_le_of_coarsens {m : ℕ}
    {coarse fine : ReplicaPartition m}
    (h : PartitionCoarsens coarse fine) :
    partitionBlockCount coarse ≤ partitionBlockCount fine := by
  rw [← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) coarse,
    ← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) fine]
  exact Submodule.finrank_mono (partitionConstantSubspace_mono h)

/-- The cost of adjoining one matching seed is bounded by the matching
distance to any matching refinement of the original partition. -/
theorem c079_join_blockLoss_le_matchingDistance {m : ℕ}
    (π : ReplicaPartition m) (ξ ρ : C079MatchingPartition m)
    (hξ : PartitionCoarsens π ξ.1) :
    partitionBlockCount π - partitionBlockCount (π ⊔ ρ.1) ≤
      c079MatchingPartitionDistance ξ ρ := by
  let P : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) π
  let X : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) ξ.1
  let R : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) ρ.1
  have hPX : P ≤ X := partitionConstantSubspace_mono hξ
  have hCross := finrank_inf_add_finrank_inf_le P X R
  rw [inf_eq_left.mpr hPX] at hCross
  have hRank : partitionBlockCount π + Module.finrank ℚ ↑(X ⊓ R) ≤
      m + partitionBlockCount (π ⊔ ρ.1) := by
    change Module.finrank ℚ P + Module.finrank ℚ ↑(X ⊓ R) ≤
      Module.finrank ℚ X + Module.finrank ℚ ↑(P ⊓ R) at hCross
    rw [finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) π,
      ← c079_partitionConstantSubspace_sup π ρ.1,
      finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) (π ⊔ ρ.1),
      finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) ξ.1,
      ξ.blockCount_eq] at hCross
    exact hCross
  have hSup : partitionBlockCount (π ⊔ ρ.1) ≤ partitionBlockCount π :=
    c079_blockCount_le_of_coarsens (by
      change π ≤ π ⊔ ρ.1
      exact le_sup_left)
  have hInf : Module.finrank ℚ ↑(X ⊓ R) ≤ m := by
    calc
      Module.finrank ℚ ↑(X ⊓ R) ≤ Module.finrank ℚ X :=
        Submodule.finrank_mono inf_le_left
      _ = m := by
        change Module.finrank ℚ
          (partitionConstantSubspace (K := ℚ) ξ.1) = m
        rw [finrank_partitionConstantSubspace_eq_blockCount, ξ.blockCount_eq]
  change partitionBlockCount π - partitionBlockCount (π ⊔ ρ.1) ≤
    m - Module.finrank ℚ ↑(X ⊓ R)
  omega

/-- Apply a fixed ordered list of matching seeds to one role partition. -/
@[instance_reducible] def c079JoinSeedList {m : ℕ} {κ : Type*}
    (start : ReplicaPartition m) (seed : κ → ReplicaPartition m)
    (order : List κ) : ReplicaPartition m :=
  order.foldl (fun current c => current ⊔ seed c) start

theorem c079JoinSeedList_coarsens {m : ℕ} {κ : Type*}
    (start : ReplicaPartition m) (seed : κ → ReplicaPartition m)
    (order : List κ) :
    PartitionCoarsens (c079JoinSeedList start seed order) start := by
  induction order generalizing start with
  | nil =>
      change start ≤ start
      exact le_refl _
  | cons c tail ih =>
      change start ≤ c079JoinSeedList (start ⊔ seed c) seed tail
      exact le_trans le_sup_left (show start ⊔ seed c ≤
        c079JoinSeedList (start ⊔ seed c) seed tail from ih _)

/-- Telescoping role charge: every seed's marginal block loss is bounded by
its loss from the original role partition, regardless of previous merges. -/
theorem c079JoinSeedList_blockLoss_le_sum {m : ℕ} {κ : Type*}
    (original : ReplicaPartition m) (seed : κ → ReplicaPartition m)
    (charge : κ → ℕ) (order : List κ)
    (hLocal : ∀ c ∈ order,
      partitionBlockCount original -
        partitionBlockCount (original ⊔ seed c) ≤ charge c) :
    partitionBlockCount original -
      partitionBlockCount (c079JoinSeedList original seed order) ≤
        (order.map charge).sum := by
  have aux : ∀ current : ReplicaPartition m,
      PartitionCoarsens current original →
      ∀ order : List κ,
      (∀ c ∈ order,
        partitionBlockCount original -
          partitionBlockCount (original ⊔ seed c) ≤ charge c) →
      partitionBlockCount current -
        partitionBlockCount (c079JoinSeedList current seed order) ≤
          (order.map charge).sum := by
    intro current hCurrent order
    induction order generalizing current with
    | nil =>
        intro _
        simp [c079JoinSeedList]
    | cons c tail ih =>
        intro hEach
        have hHead := hEach c (by simp)
        have hStep : partitionBlockCount current -
            partitionBlockCount (current ⊔ seed c) ≤ charge c :=
          (c079_sup_blockLoss_mono original current (seed c) hCurrent).trans hHead
        have hNext : PartitionCoarsens (current ⊔ seed c) original := by
          change original ≤ current ⊔ seed c
          exact le_trans hCurrent le_sup_left
        have hTail : ∀ d ∈ tail,
            partitionBlockCount original -
              partitionBlockCount (original ⊔ seed d) ≤ charge d := by
          intro d hd
          exact hEach d (by simp [hd])
        have hRemaining := ih (current ⊔ seed c) hNext hTail
        have hDec1 : partitionBlockCount (current ⊔ seed c) ≤
            partitionBlockCount current :=
          c079_blockCount_le_of_coarsens (by
            change current ≤ current ⊔ seed c
            exact le_sup_left)
        have hDec2 : partitionBlockCount
            (c079JoinSeedList (current ⊔ seed c) seed tail) ≤
            partitionBlockCount (current ⊔ seed c) :=
          c079_blockCount_le_of_coarsens
            (c079JoinSeedList_coarsens _ _ _)
        change partitionBlockCount current -
          partitionBlockCount (c079JoinSeedList
            (current ⊔ seed c) seed tail) ≤
              ((c :: tail).map charge).sum
        simp only [List.map_cons, List.sum_cons]
        omega
  exact aux original (by intro a b h; exact h) order hLocal

/-- The actual defect of one connected component of the graph left after
deleting a fixed disjoint-path backbone. -/
def ReplicaState.c079ComponentDefect {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p) (family : G.VertexDisjointRightToLeftPaths s)
    (c : G.C079CutComponent family.backboneRoles) : ℕ :=
  (G.c079ComponentRoles family.backboneRoles c).sum
    (fun y => (p + 1) - partitionBlockCount (S.partition y))

/-- Genuine graph components partition the off-backbone roles, so their
actual defects sum exactly to the previously defined off-backbone defect. -/
theorem ReplicaState.c079_sum_componentDefects_eq_offBackbone
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) :
    (∑ c : G.C079CutComponent family.backboneRoles,
      S.c079ComponentDefect family c) =
        S.c079OffBackboneDefect family := by
  classical
  let weight : Fin G.roles → ℕ := fun y =>
    (p + 1) - partitionBlockCount (S.partition y)
  have hFiber : ∀ y : Fin G.roles,
      (∑ c : G.C079CutComponent family.backboneRoles,
        if y ∈ G.c079ComponentRoles family.backboneRoles c then weight y else 0) =
          if y ∈ family.offBackboneRoles then weight y else 0 := by
    intro y
    by_cases hy : y ∈ family.backboneRoles
    · have hNone : ∀ c : G.C079CutComponent family.backboneRoles,
          y ∉ G.c079ComponentRoles family.backboneRoles c := by
        intro c hc
        exact ((G.mem_c079ComponentRoles_iff family.backboneRoles c y).1 hc).1 hy
      have hOff : y ∉ family.offBackboneRoles := by
        change y ∉ (Finset.univ \ family.backboneRoles)
        simp [hy]
      simp [hNone, hOff]
    · let c₀ : G.C079CutComponent family.backboneRoles :=
        (G.c079CutGraph family.backboneRoles).connectedComponentMk ⟨y, hy⟩
      have hMem : ∀ c : G.C079CutComponent family.backboneRoles,
          y ∈ G.c079ComponentRoles family.backboneRoles c ↔ c = c₀ := by
        intro c
        rw [G.mem_c079ComponentRoles_iff]
        simp [hy, c₀, eq_comm]
      have hOff : y ∈ family.offBackboneRoles := by
        change y ∈ (Finset.univ \ family.backboneRoles)
        simp [hy]
      simp [hMem, hOff]
  have hEnum :
      (@Finset.univ (G.C079CutComponent family.backboneRoles)
        SetLike.instFintype) =
      (@Finset.univ (G.C079CutComponent family.backboneRoles)
        (G.c079CutGraph family.backboneRoles).instFintypeConnectedComponent) := by
    ext c
    simp
  rw [hEnum]
  calc
    (∑ c : G.C079CutComponent family.backboneRoles,
        S.c079ComponentDefect family c) =
        ∑ c : G.C079CutComponent family.backboneRoles,
          ∑ y : Fin G.roles,
            if y ∈ G.c079ComponentRoles family.backboneRoles c then weight y else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      simp [ReplicaState.c079ComponentDefect, weight]
    _ = ∑ y : Fin G.roles,
          ∑ c : G.C079CutComponent family.backboneRoles,
            if y ∈ G.c079ComponentRoles family.backboneRoles c then weight y else 0 :=
      Finset.sum_comm
    _ = ∑ y : Fin G.roles,
          if y ∈ family.offBackboneRoles then weight y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      exact hFiber y
    _ = S.c079OffBackboneDefect family := by
      simp [ReplicaState.c079OffBackboneDefect, weight]

/-- Components with an actual edge to backbone role `x`, in the fixed
`Finset.toList` order used by the forward merge decoder. -/
def PartiteShape.c079BackboneAttachmentComponents
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (x : Fin G.roles) :
    Finset (G.C079CutComponent family.backboneRoles) := by
  classical
  exact Finset.univ.filter fun c =>
    x ∈ family.backboneRoles ∧
      ∃ y ∈ G.c079ComponentRoles family.backboneRoles c,
        ∃ e : Fin G.edges,
          G.EdgeIncident e x ∧ G.EdgeIncident e y

/-- Forward coarsening of the original backbone role partition by every
matching seed from a genuinely attached off-backbone component. Off-backbone
roles have an empty attachment list and are unchanged by this operation. -/
@[instance_reducible] def ReplicaState.c079ForwardBackbonePartition
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) : ReplicaPartition (p + 1) :=
  c079JoinSeedList (S.partition x) (fun c => (seed c).1)
    (G.c079BackboneAttachmentComponents family x).toList

theorem ReplicaState.c079ForwardBackbonePartition_coarsens
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) :
    PartitionCoarsens (S.c079ForwardBackbonePartition family seed x)
      (S.partition x) :=
  c079JoinSeedList_coarsens _ _ _

theorem ReplicaState.c079ForwardBackbonePartition_eq_of_offBackbone
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (x : Fin G.roles) (hx : x ∉ family.backboneRoles) :
    S.c079ForwardBackbonePartition family seed x = S.partition x := by
  classical
  have hEmpty : G.c079BackboneAttachmentComponents family x = ∅ := by
    ext c
    simp [PartiteShape.c079BackboneAttachmentComponents, hx]
  simp [ReplicaState.c079ForwardBackbonePartition,
    c079JoinSeedList, hEmpty]

/-- This hypothesis is the exact local seed-distance obligation from the
paper's spanning-tree argument. It is not implied by the numerical value of
`D` alone: a component seed must be chosen and transported compatibly. -/
def ReplicaState.C079AttachmentSeedDistanceCertificate
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1)) : Prop :=
  ∀ x : Fin G.roles,
    ∀ c ∈ G.c079BackboneAttachmentComponents family x,
      ∃ ξ : C079MatchingPartition (p + 1),
        PartitionCoarsens (S.partition x) ξ.1 ∧
          c079MatchingPartitionDistance ξ (seed c) ≤
            3 * S.c079ComponentDefect family c

/-- The smaller missing tree certificate: a fixed matching refinement at
each role and, for every actual off-backbone component, a seed within twice
that component's defect of every role matching in the component. -/
structure ReplicaState.C079ComponentSeedTreeCertificate
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1)) where
  roleMatching : Fin G.roles → C079MatchingPartition (p + 1)
  roleRefines : ∀ y : Fin G.roles,
    PartitionCoarsens (S.partition y) (roleMatching y).1
  seedDistance : ∀ c : G.C079CutComponent family.backboneRoles,
    ∀ y ∈ G.c079ComponentRoles family.backboneRoles c,
      c079MatchingPartitionDistance (roleMatching y) (seed c) ≤
        2 * S.c079ComponentDefect family c

/-- Edge parity and the ordinary matching-partition defect bound turn the
tree certificate into the exact attachment certificate needed for `3rD`.
The unproved work is the tree certificate itself, not this local edge step. -/
theorem ReplicaState.C079ComponentSeedTreeCertificate.toAttachmentCertificate
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (tree : S.C079ComponentSeedTreeCertificate family seed) :
    S.C079AttachmentSeedDistanceCertificate family seed := by
  classical
  intro x c hc
  have hAttach := (Finset.mem_filter.mp hc).2
  obtain ⟨_, y, hy, e, hxe, hye⟩ := hAttach
  let ξ : C079MatchingPartition (p + 1) :=
    (S.edgePerfectMatching e).toC079MatchingPartition
  have hξx : PartitionCoarsens (S.partition x) ξ.1 :=
    S.partition_coarsens_edgePerfectMatching_of_incident e x hxe
  have hξy : PartitionCoarsens (S.partition y) ξ.1 :=
    S.partition_coarsens_edgePerfectMatching_of_incident e y hye
  have hEdgeDistance : c079MatchingPartitionDistance ξ (tree.roleMatching y) ≤
      (p + 1) - partitionBlockCount (S.partition y) :=
    c079MatchingPartitionDistance_le_partitionDefect
      (S.partition y) ξ (tree.roleMatching y) hξy (tree.roleRefines y)
  have hRoleDefect : (p + 1) - partitionBlockCount (S.partition y) ≤
      S.c079ComponentDefect family c := by
    unfold ReplicaState.c079ComponentDefect
    exact Finset.single_le_sum
      (s := G.c079ComponentRoles family.backboneRoles c)
      (f := fun z => (p + 1) - partitionBlockCount (S.partition z))
      (fun _ _ => Nat.zero_le _) hy
  have hDistance : c079MatchingPartitionDistance ξ (seed c) ≤
      c079MatchingPartitionDistance ξ (tree.roleMatching y) +
        c079MatchingPartitionDistance (tree.roleMatching y) (seed c) :=
    c079MatchingPartitionDistance_triangle ξ (tree.roleMatching y) (seed c)
  refine ⟨ξ, hξx, ?_⟩
  have hTree := tree.seedDistance c y hy
  omega

/-- The true per-role merge bill is at most three times the defects of its
genuinely attached off-backbone components. -/
theorem ReplicaState.c079_forwardBackboneRole_blockLoss_le
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hSeed : S.C079AttachmentSeedDistanceCertificate family seed)
    (x : Fin G.roles) :
    partitionBlockCount (S.partition x) -
      partitionBlockCount (S.c079ForwardBackbonePartition family seed x) ≤
        (G.c079BackboneAttachmentComponents family x).sum
          (fun c => 3 * S.c079ComponentDefect family c) := by
  have hLocal : ∀ c ∈
      (G.c079BackboneAttachmentComponents family x).toList,
      partitionBlockCount (S.partition x) -
        partitionBlockCount ((S.partition x) ⊔ (seed c).1) ≤
          3 * S.c079ComponentDefect family c := by
    intro c hc
    obtain ⟨ξ, hRefine, hDistance⟩ :=
      hSeed x c (by simpa using hc)
    exact (c079_join_blockLoss_le_matchingDistance
      (S.partition x) ξ (seed c) hRefine).trans hDistance
  have h := c079JoinSeedList_blockLoss_le_sum
    (S.partition x) (fun c => (seed c).1)
    (fun c => 3 * S.c079ComponentDefect family c)
    (G.c079BackboneAttachmentComponents family x).toList hLocal
  simpa only [ReplicaState.c079ForwardBackbonePartition,
    Finset.sum_map_toList] using h

/-- The sum of genuine forward backbone block losses is at most `3rD`,
where `D` is exactly the existing off-backbone defect. -/
theorem ReplicaState.c079_forwardBackbone_totalBlockLoss_le_three_r_D
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hSeed : S.C079AttachmentSeedDistanceCertificate family seed) :
    ((Finset.univ : Finset (Fin G.roles)).sum (fun x : Fin G.roles =>
      partitionBlockCount (S.partition x) -
        partitionBlockCount (S.c079ForwardBackbonePartition family seed x))) ≤
      3 * G.roles * S.c079OffBackboneDefect family := by
  calc
    ((Finset.univ : Finset (Fin G.roles)).sum (fun x : Fin G.roles =>
        partitionBlockCount (S.partition x) -
          partitionBlockCount (S.c079ForwardBackbonePartition family seed x))) ≤
        ∑ x : Fin G.roles,
          (G.c079BackboneAttachmentComponents family x).sum
            (fun c => 3 * S.c079ComponentDefect family c) := by
      exact Finset.sum_le_sum fun x _ =>
        S.c079_forwardBackboneRole_blockLoss_le family seed hSeed x
    _ ≤ ∑ _x : Fin G.roles,
          ∑ c : G.C079CutComponent family.backboneRoles,
            3 * S.c079ComponentDefect family c := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
        (by intro c _ _; positivity)
    _ = 3 * G.roles * S.c079OffBackboneDefect family := by
      rw [← Finset.mul_sum]
      rw [S.c079_sum_componentDefects_eq_offBackbone family]
      simp [Nat.mul_comm, Nat.mul_assoc]

/-- An ordered role-indexed family of genuine point-pair merge words decodes
the forward backbone coarsening and has total length at most `3rD`.
The only conditional input is the named seed-distance certificate above. -/
theorem ReplicaState.exists_c079ForwardBackboneMergeWords
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (hSeed : S.C079AttachmentSeedDistanceCertificate family seed) :
    ∃ words : Fin G.roles →
        List (Replica (p + 1) × Replica (p + 1)),
      (∀ x : Fin G.roles,
        c079DecodeMergeWord (S.partition x) (words x) =
          S.c079ForwardBackbonePartition family seed x) ∧
      ((Finset.univ : Finset (Fin G.roles)).sum
        (fun x : Fin G.roles => (words x).length)) ≤
          3 * G.roles * S.c079OffBackboneDefect family := by
  classical
  have hExists : ∀ x : Fin G.roles,
      ∃ word : List (Replica (p + 1) × Replica (p + 1)),
        c079DecodeMergeWord (S.partition x) word =
            S.c079ForwardBackbonePartition family seed x ∧
          word.length ≤ partitionBlockCount (S.partition x) -
            partitionBlockCount (S.c079ForwardBackbonePartition family seed x) := by
    intro x
    exact exists_c079MergeWord
      (S.c079ForwardBackbonePartition family seed x)
      (S.partition x)
      (S.c079ForwardBackbonePartition_coarsens family seed x)
  let words : Fin G.roles →
      List (Replica (p + 1) × Replica (p + 1)) :=
    fun x => Classical.choose (hExists x)
  have hSpec (x : Fin G.roles) := Classical.choose_spec (hExists x)
  refine ⟨words, (fun x => (hSpec x).1), ?_⟩
  calc
    ((Finset.univ : Finset (Fin G.roles)).sum
        (fun x : Fin G.roles => (words x).length)) ≤
        (Finset.univ : Finset (Fin G.roles)).sum
          (fun x : Fin G.roles =>
            partitionBlockCount (S.partition x) -
              partitionBlockCount
                (S.c079ForwardBackbonePartition family seed x)) := by
      exact Finset.sum_le_sum fun x _ => (hSpec x).2
    _ ≤ 3 * G.roles * S.c079OffBackboneDefect family :=
      S.c079_forwardBackbone_totalBlockLoss_le_three_r_D family seed hSeed

/-- The same role-indexed word bound from the narrower spanning-tree
certificate; this states the remaining construction gate explicitly. -/
theorem ReplicaState.exists_c079ForwardBackboneMergeWords_of_tree
    {G : PartiteShape} {p s : ℕ}
    (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s)
    (seed : G.C079CutComponent family.backboneRoles →
      C079MatchingPartition (p + 1))
    (tree : S.C079ComponentSeedTreeCertificate family seed) :
    ∃ words : Fin G.roles →
        List (Replica (p + 1) × Replica (p + 1)),
      (∀ x : Fin G.roles,
        c079DecodeMergeWord (S.partition x) (words x) =
          S.c079ForwardBackbonePartition family seed x) ∧
      ((Finset.univ : Finset (Fin G.roles)).sum
        (fun x : Fin G.roles => (words x).length)) ≤
          3 * G.roles * S.c079OffBackboneDefect family :=
  S.exists_c079ForwardBackboneMergeWords family seed
    (tree.toAttachmentCertificate S family seed)

#print axioms c079_partitionConstantSubspace_sup
#print axioms c079_sup_blockLoss_mono
#print axioms c079_join_blockLoss_le_matchingDistance
#print axioms c079JoinSeedList_blockLoss_le_sum
#print axioms ReplicaState.c079_sum_componentDefects_eq_offBackbone
#print axioms ReplicaState.c079_forwardBackbone_totalBlockLoss_le_three_r_D
#print axioms ReplicaState.exists_c079ForwardBackboneMergeWords
#print axioms ReplicaState.c079ForwardBackbonePartition_eq_of_offBackbone
#print axioms ReplicaState.C079ComponentSeedTreeCertificate.toAttachmentCertificate
#print axioms ReplicaState.exists_c079ForwardBackboneMergeWords_of_tree

end GraphMatrixReplica
