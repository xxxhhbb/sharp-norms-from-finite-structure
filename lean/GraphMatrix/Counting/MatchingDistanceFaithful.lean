import GraphMatrix.Counting.MatchingPartition

/-! # Zero matching distance distinguishes matching partitions

The linear-algebra intersection distance is used as a matching distance in
C079. This module proves its zero case on the nonredundant partition subtype.
It is the base case for a future distance-to-switch-record construction; it
does not assert that all positive-distance matchings are switch-reachable.
-/

noncomputable section

namespace GraphMatrixReplica

private theorem partition_relation_of_constantSubspace_le
    {p : ℕ} {π ψ : ReplicaPartition p}
    (hsub : partitionConstantSubspace (K := ℚ) π ≤
      partitionConstantSubspace (K := ℚ) ψ)
    {a b : Replica p} (hψ : ψ.r a b) : π.r a b := by
  classical
  let f : Replica p → ℚ := fun x => if π.r a x then 1 else 0
  have hfπ : f ∈ partitionConstantSubspace (K := ℚ) π := by
    rw [mem_partitionConstantSubspace_iff]
    intro x y hxy
    by_cases hax : π.r a x
    · have hay : π.r a y := π.iseqv.trans hax hxy
      simp [f, hax, hay]
    · have hay : ¬ π.r a y := by
        intro hay
        exact hax (π.iseqv.trans hay (π.iseqv.symm hxy))
      simp [f, hax, hay]
  have hfψ := (mem_partitionConstantSubspace_iff ψ f).mp (hsub hfπ)
  have habEq := hfψ a b hψ
  by_contra hn
  simp [f, hn] at habEq

/-- Over `ℚ`, a finite equality partition is determined by its space of
functions constant on blocks. -/
theorem partitionConstantSubspace_injective_rat {p : ℕ}
    {π ψ : ReplicaPartition p}
    (h : partitionConstantSubspace (K := ℚ) π =
      partitionConstantSubspace (K := ℚ) ψ) : π = ψ := by
  apply Setoid.ext
  intro a b
  constructor
  · intro hab
    exact partition_relation_of_constantSubspace_le
      (π := ψ) (ψ := π) (by rw [h]) hab
  · intro hab
    exact partition_relation_of_constantSubspace_le
      (π := π) (ψ := ψ) (by rw [h]) hab

/-- The C079 matching distance vanishes only for the same matching partition.
This is an unconditional `t=0` base case, not the positive-distance switch
construction needed for the full metric-ball count. -/
theorem c079MatchingPartitionDistance_eq_zero_iff_eq {p : ℕ}
    (σ τ : C079MatchingPartition p) :
    c079MatchingPartitionDistance σ τ = 0 ↔ σ = τ := by
  constructor
  · intro hzero
    have hpoint : σ.constantSubspacePoint = τ.constantSubspacePoint :=
      (fixedRankIntersectionDistance_eq_zero_iff p
        σ.constantSubspacePoint τ.constantSubspacePoint).mp hzero
    apply Subtype.ext
    exact partitionConstantSubspace_injective_rat
      (congrArg Subtype.val hpoint)
  · rintro rfl
    exact fixedRankIntersectionDistance_self p σ.constantSubspacePoint


end GraphMatrixReplica
