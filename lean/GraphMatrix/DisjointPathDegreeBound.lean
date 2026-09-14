import GraphMatrix.CoveredRoleBlockBound
import GraphMatrix.StateBoundaryPathDefect

/-! # Vertex-disjoint path aggregation and the sharp C078 degree bound

Path vertices are represented by a finite occurrence type.  A family is
vertex-disjoint when the map from all indexed occurrences to graph roles is
injective.  This makes summing the one-path defect bounds a finite-sum
argument with no informal multiplicity step.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Number of vertex occurrences in a path. -/
def PartiteShape.EdgePathToLeft.vertexCount
    {G : PartiteShape} {v : Fin G.roles} :
    G.EdgePathToLeft v → ℕ
  | .finish _ _ => 1
  | .step _ _ _ _ tail => tail.vertexCount + 1

/-- The graph role represented by a path-vertex occurrence. -/
def PartiteShape.EdgePathToLeft.vertexAt
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : Fin path.vertexCount → Fin G.roles :=
  match path with
  | .finish v _ => fun _ => v
  | .step (v := v) _ _ _ _ tail =>
      Fin.cases v tail.vertexAt

/-- The distinguished occurrence of the initial vertex. -/
def PartiteShape.EdgePathToLeft.headOccurrence
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : Fin path.vertexCount :=
  ⟨0, by cases path <;> simp [vertexCount]⟩

@[simp] theorem PartiteShape.EdgePathToLeft.vertexAt_headOccurrence
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.vertexAt path.headOccurrence = v := by
  cases path <;> rfl

/-- The recursive path defect sum is exactly the sum over its explicitly
typed vertex occurrences. -/
theorem PartiteShape.EdgePathToLeft.vertexDefectSum_eq_sum_occurrences
    {G : PartiteShape} {p : ℕ} {S : ReplicaState G p} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.vertexDefectSum S =
      (Finset.univ : Finset (Fin path.vertexCount)).sum (fun o =>
        (p + 1) - partitionBlockCount
          (S.partition (PartiteShape.EdgePathToLeft.vertexAt path o))) := by
  induction path with
  | finish v hLeft =>
      change
        (p + 1) - partitionBlockCount (S.partition v) =
          (Finset.univ : Finset (Fin 1)).sum (fun _ =>
            (p + 1) - partitionBlockCount (S.partition v))
      simp
  | @step v e w hAtStart hAtEnd tail ih =>
      rw [vertexDefectSum, ih]
      change
        (p + 1) - partitionBlockCount (S.partition v) +
            (Finset.univ : Finset (Fin tail.vertexCount)).sum (fun o =>
              (p + 1) - partitionBlockCount
                (S.partition (tail.vertexAt o))) =
          (Finset.univ : Finset (Fin (tail.vertexCount + 1))).sum (fun o =>
            (p + 1) - partitionBlockCount
              (S.partition (Fin.cases v tail.vertexAt o)))
      rw [Fin.sum_univ_succ]
      rfl

/-- A family of right-to-left paths with no repeated graph role, either
inside one path or between two different paths. -/
structure PartiteShape.VertexDisjointRightToLeftPaths
    (G : PartiteShape) (s : ℕ) where
  start : Fin s → Fin G.roles
  startRight : ∀ i : Fin s, start i ∈ G.rightBoundary
  path : ∀ i : Fin s, G.EdgePathToLeft (start i)
  vertexAt_injective : Function.Injective
    (fun z : Σ i : Fin s, Fin ((path i).vertexCount) =>
      (path z.1).vertexAt z.2)

/-- An injective reindexing of a nonnegative finite sum cannot exceed the
sum over the whole codomain. -/
theorem sum_comp_le_sum_of_injective
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (weight : β → ℕ) :
    (∑ a : α, weight (f a)) ≤ ∑ b : β, weight b := by
  classical
  calc
    (∑ a : α, weight (f a)) =
        ∑ b ∈ Finset.univ.image f, weight b := by
      rw [Finset.sum_image]
      exact hf.injOn
    _ ≤ ∑ b ∈ (Finset.univ : Finset β), weight b :=
      Finset.sum_le_sum_of_subset (by simp)
    _ = ∑ b : β, weight b := by rfl

/-- Vertex-disjointness implies that the number of paths is at most the
number of graph roles. -/
theorem PartiteShape.VertexDisjointRightToLeftPaths.pathCount_le_roles
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s) :
    s ≤ G.roles := by
  have hInjective : Function.Injective family.start := by
    intro i j hij
    have hOccurrence :
        (⟨i, (family.path i).headOccurrence⟩ :
          Σ k : Fin s, Fin ((family.path k).vertexCount)) =
        ⟨j, (family.path j).headOccurrence⟩ := by
      apply family.vertexAt_injective
      simpa using hij
    exact congrArg Sigma.fst hOccurrence
  simpa using Fintype.card_le_of_injective family.start hInjective

/-- Total partition defect of a replica state. -/
def ReplicaState.totalDefect {G : PartiteShape} {p : ℕ}
    (S : ReplicaState G p) : ℕ :=
  (Finset.univ : Finset (Fin G.roles)).sum (fun v =>
    (p + 1) - partitionBlockCount (S.partition v))

/-- Summing the one-path inequalities over a vertex-disjoint family gives
`s(q-1)` units of total defect. -/
theorem ReplicaState.disjointPaths_totalDefect_lower_bound
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) :
    s * p ≤ S.totalDefect := by
  let weight : Fin G.roles → ℕ := fun v =>
    (p + 1) - partitionBlockCount (S.partition v)
  have hEach : ∀ i : Fin s, p ≤ (family.path i).vertexDefectSum S :=
    fun i => S.rightToLeftPath_defect_lower_bound
      (family.start i) (family.startRight i) (family.path i)
  calc
    s * p = ∑ _i : Fin s, p := by simp
    _ ≤ ∑ i : Fin s, (family.path i).vertexDefectSum S := by
      exact Finset.sum_le_sum fun i _ => hEach i
    _ = ∑ i : Fin s, ∑ o : Fin (family.path i).vertexCount,
          weight ((family.path i).vertexAt o) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (family.path i).vertexDefectSum_eq_sum_occurrences (S := S)
    _ = ∑ z : Σ i : Fin s, Fin ((family.path i).vertexCount),
          weight ((family.path z.1).vertexAt z.2) := by
      exact (Fintype.sum_sigma' fun i o =>
        weight ((family.path i).vertexAt o)).symm
    _ ≤ ∑ v : Fin G.roles, weight v :=
      sum_comp_le_sum_of_injective _ family.vertexAt_injective weight
    _ = S.totalDefect := rfl

/-- When every role is retained, total blocks plus total defect is exactly
`q` times the number of roles. -/
theorem ReplicaState.totalDefect_add_totalBlockCount
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    S.totalDefect + S.totalBlockCount = (p + 1) * G.roles := by
  rw [ReplicaState.totalDefect, ReplicaState.totalBlockCount,
    ← Finset.sum_add_distrib]
  calc
    (Finset.univ : Finset (Fin G.roles)).sum
        (fun v => (p + 1) - partitionBlockCount (S.partition v) +
          partitionBlockCount (S.partition v)) =
        (Finset.univ : Finset (Fin G.roles)).sum (fun _v => p + 1) := by
      apply Finset.sum_congr rfl
      intro v _
      exact Nat.sub_add_cancel (S.coveredRole_blockCount_le v (hCovered v))
    _ = (p + 1) * G.roles := by simp [Nat.mul_comm]

/-- Sharp degree bound in defect form. -/
theorem ReplicaState.totalBlockCount_le_of_disjointPaths
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s) :
    S.totalBlockCount ≤ (p + 1) * G.roles - s * p := by
  have hDefect := S.disjointPaths_totalDefect_lower_bound family
  have hBalance := S.totalDefect_add_totalBlockCount hCovered
  omega

/-- C078's usual presentation `q(r-s)+s`, with `q=p+1`. -/
theorem ReplicaState.totalBlockCount_le_sharp
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s) :
    S.totalBlockCount ≤ (p + 1) * (G.roles - s) + s := by
  have h := S.totalBlockCount_le_of_disjointPaths hCovered family
  have hs : s ≤ G.roles := family.pathCount_le_roles
  calc
    S.totalBlockCount ≤ (p + 1) * G.roles - s * p := h
    _ = (p + 1) * (G.roles - s) + s := by
      have hr : G.roles = (G.roles - s) + s :=
        (Nat.sub_add_cancel hs).symm
      have hmul : (p + 1) * G.roles =
          (p + 1) * (G.roles - s) + s * p + s := by
        calc
          (p + 1) * G.roles = (p + 1) * ((G.roles - s) + s) :=
            congrArg (fun n => (p + 1) * n) hr
          _ = (p + 1) * (G.roles - s) + s * p + s := by ring
      rw [hmul]
      omega


end GraphMatrixReplica
