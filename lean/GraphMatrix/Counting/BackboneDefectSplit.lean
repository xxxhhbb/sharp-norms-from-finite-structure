import GraphMatrix.Counting.ExplicitConstants

/-! # Exact backbone/off-backbone defect split

Appendix D fixes a vertex-disjoint family of boundary-to-boundary paths.
Its vertex occurrences form a true set of graph roles because the family map
is injective.  We split total replica defect over that backbone and its
complement, then identify the paper defect with the sum of the path excesses
and the off-backbone widths.  No path-state count or encoder is used here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The occurrence-to-role map of a fixed disjoint path family. -/
def PartiteShape.VertexDisjointRightToLeftPaths.backboneRoleAt
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (z : Σ i : Fin s, Fin ((family.path i).vertexCount)) :
    Fin G.roles :=
  (family.path z.1).vertexAt z.2

/-- Exactly the roles on the fixed path backbone. -/
def PartiteShape.VertexDisjointRightToLeftPaths.backboneRoles
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s) :
    Finset (Fin G.roles) :=
  Finset.univ.image family.backboneRoleAt

/-- Roles away from the fixed path backbone. -/
def PartiteShape.VertexDisjointRightToLeftPaths.offBackboneRoles
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s) :
    Finset (Fin G.roles) :=
  Finset.univ \ family.backboneRoles

/-- Excess defect on each path, summed over the disjoint family. -/
def ReplicaState.c079OnBackboneDefect
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) : ℕ :=
  ∑ i : Fin s, ((family.path i).vertexDefectSum S - p)

/-- Individual partition widths on the complement of the backbone. -/
def ReplicaState.c079OffBackboneDefect
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) : ℕ :=
  family.offBackboneRoles.sum (fun v =>
    (p + 1) - partitionBlockCount (S.partition v))

/-- Summing over path occurrences is summing over the set of backbone roles,
with no multiplicity because the family is vertex-disjoint. -/
theorem ReplicaState.c079_sum_backboneRoles_eq_sum_pathDefects
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) :
    family.backboneRoles.sum (fun v =>
      (p + 1) - partitionBlockCount (S.partition v)) =
      ∑ i : Fin s, (family.path i).vertexDefectSum S := by
  classical
  let weight : Fin G.roles → ℕ := fun v =>
    (p + 1) - partitionBlockCount (S.partition v)
  calc
    family.backboneRoles.sum (fun v =>
        (p + 1) - partitionBlockCount (S.partition v)) =
        ∑ z : Σ i : Fin s, Fin ((family.path i).vertexCount),
          weight (family.backboneRoleAt z) := by
      unfold PartiteShape.VertexDisjointRightToLeftPaths.backboneRoles
      rw [Finset.sum_image]
      exact family.vertexAt_injective.injOn
    _ = ∑ i : Fin s, ∑ o : Fin (family.path i).vertexCount,
          weight ((family.path i).vertexAt o) := by
      exact Fintype.sum_sigma'
        (fun i o => weight ((family.path i).vertexAt o))
    _ = ∑ i : Fin s, (family.path i).vertexDefectSum S := by
      apply Finset.sum_congr rfl
      intro i _
      exact ((family.path i).vertexDefectSum_eq_sum_occurrences (S := S)).symm

/-- Path defects have the exact baseline `s*p`, not merely a lower bound. -/
theorem ReplicaState.c079_sum_pathDefects_eq_baseline_add_excess
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) :
    (∑ i : Fin s, (family.path i).vertexDefectSum S) =
      s * p + S.c079OnBackboneDefect family := by
  have hEach : ∀ i : Fin s,
      p ≤ (family.path i).vertexDefectSum S :=
    fun i => S.rightToLeftPath_defect_lower_bound
      (family.start i) (family.startRight i) (family.path i)
  calc
    (∑ i : Fin s, (family.path i).vertexDefectSum S) =
        ∑ i : Fin s,
          (p + ((family.path i).vertexDefectSum S - p)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Nat.add_sub_of_le (hEach i)).symm
    _ = (∑ _i : Fin s, p) +
          ∑ i : Fin s, ((family.path i).vertexDefectSum S - p) := by
      rw [Finset.sum_add_distrib]
    _ = s * p + S.c079OnBackboneDefect family := by
      simp [ReplicaState.c079OnBackboneDefect, Nat.mul_comm]

/-- Exact partition of total defect into backbone and off-backbone roles. -/
theorem ReplicaState.c079_totalDefect_eq_backbone_add_offBackbone
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) :
    S.totalDefect =
      family.backboneRoles.sum (fun v =>
        (p + 1) - partitionBlockCount (S.partition v)) +
        S.c079OffBackboneDefect family := by
  classical
  have hDisjoint :
      Disjoint family.backboneRoles family.offBackboneRoles := by
    unfold PartiteShape.VertexDisjointRightToLeftPaths.offBackboneRoles
    apply Finset.disjoint_left.mpr
    intro v hv hOff
    exact (Finset.mem_sdiff.mp hOff).2 hv
  have hUnion :
      family.backboneRoles ∪ family.offBackboneRoles = Finset.univ := by
    unfold PartiteShape.VertexDisjointRightToLeftPaths.offBackboneRoles
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  calc
    S.totalDefect =
        (Finset.univ : Finset (Fin G.roles)).sum (fun v =>
          (p + 1) - partitionBlockCount (S.partition v)) := rfl
    _ = (family.backboneRoles ∪ family.offBackboneRoles).sum (fun v =>
          (p + 1) - partitionBlockCount (S.partition v)) := by rw [hUnion]
    _ = family.backboneRoles.sum (fun v =>
          (p + 1) - partitionBlockCount (S.partition v)) +
          S.c079OffBackboneDefect family := by
      rw [Finset.sum_union hDisjoint]
      rfl

/-- Appendix D equation `delta = delta_on + D`, on an actual covered
admissible replica state and an actual disjoint path family. -/
theorem c079StateDefect_eq_onBackbone_add_offBackbone
    {G : PartiteShape} {p s : ℕ}
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (T : AdmissiblePartitionState G p) :
    c079StateDefect G p s T =
      T.toReplicaState.c079OnBackboneDefect family +
        T.toReplicaState.c079OffBackboneDefect family := by
  have hTotal :=
    T.toReplicaState.c079_totalDefect_eq_backbone_add_offBackbone family
  rw [T.toReplicaState.c079_sum_backboneRoles_eq_sum_pathDefects family,
    T.toReplicaState.c079_sum_pathDefects_eq_baseline_add_excess family] at hTotal
  rw [c079StateDefect_eq_totalDefect_sub_paths hCovered family T, hTotal]
  omega


end GraphMatrixReplica
