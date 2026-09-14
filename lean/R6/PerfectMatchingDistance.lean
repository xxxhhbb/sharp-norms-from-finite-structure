import R6.EvenPartitionBlockBound
import R6.PartitionConstantSubspace

/-! # Perfect-matching distance and the local partition-defect bound

A perfect matching is represented by its two-element-block setoid together
with the cached theorem that it has exactly p blocks.  Its constant-vector
subspace therefore has rank p.  Pulling back the fixed-rank intersection
distance gives the matching metric used in C078.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The first partition is coarser: every equivalence of the second partition
is also an equivalence of the first. -/
def PartitionCoarsens {p : ℕ}
    (coarse fine : ReplicaPartition p) : Prop :=
  ∀ a b, fine.r a b → coarse.r a b

theorem partitionConstantSubspace_mono
    {K : Type*} [DivisionRing K] {p : ℕ}
    {coarse fine : ReplicaPartition p}
    (h : PartitionCoarsens coarse fine) :
    partitionConstantSubspace (K := K) coarse ≤
      partitionConstantSubspace (K := K) fine := by
  intro f hf
  intro a b hab
  exact hf a b (h a b hab)

/-- A perfect matching is an identification of the replica set with p
ordered two-point fibers. -/
structure PerfectMatching (p : ℕ) where
  pairingEquiv : Replica p ≃ Replica p

/-- Equality partition into the transported two-point fibers. -/
def PerfectMatching.partition {p : ℕ} (rho : PerfectMatching p) :
    ReplicaPartition p :=
  equalityPartition (fun a => (rho.pairingEquiv.symm a).1)

theorem PerfectMatching.blockCount_eq
    {p : ℕ} (rho : PerfectMatching p) :
    partitionBlockCount rho.partition = p := by
  classical
  let key : Replica p → Fin p := fun a => (rho.pairingEquiv.symm a).1
  have hsurj : Function.Surjective key := by
    intro k
    refine ⟨rho.pairingEquiv (k, false), ?_⟩
    simp [key]
  have hker : equalityPartition key = Setoid.ker key := by
    apply Setoid.ext
    intro a b
    rfl
  unfold partitionBlockCount PerfectMatching.partition
  change Fintype.card (Quotient (equalityPartition key)) = p
  rw [hker]
  calc
    Fintype.card (Quotient (Setoid.ker key)) = Fintype.card (Fin p) :=
      Fintype.card_congr (Setoid.quotientKerEquivOfSurjective key hsurj)
    _ = p := Fintype.card_fin p

/-- The p-dimensional subspace of vectors constant on the matching pairs. -/
def PerfectMatching.constantSubspacePoint
    {p : ℕ} (rho : PerfectMatching p) :
    FixedRankSubmodule ℚ (Replica p → ℚ) p :=
  ⟨partitionConstantSubspace (K := ℚ) rho.partition, by
    rw [finrank_partitionConstantSubspace_eq_blockCount]
    exact rho.blockCount_eq⟩

/-- Linear-algebra matching distance from C078. -/
def matchingIntersectionDistance {p : ℕ}
    (rho sigma : PerfectMatching p) : ℕ :=
  fixedRankIntersectionDistance p rho.constantSubspacePoint
    sigma.constantSubspacePoint

theorem matchingIntersectionDistance_self
    {p : ℕ} (rho : PerfectMatching p) :
    matchingIntersectionDistance rho rho = 0 :=
  fixedRankIntersectionDistance_self p rho.constantSubspacePoint

theorem matchingIntersectionDistance_comm
    {p : ℕ} (rho sigma : PerfectMatching p) :
    matchingIntersectionDistance rho sigma =
      matchingIntersectionDistance sigma rho :=
  fixedRankIntersectionDistance_comm p rho.constantSubspacePoint
    sigma.constantSubspacePoint

theorem matchingIntersectionDistance_eq_zero_iff
    {p : ℕ} (rho sigma : PerfectMatching p) :
    matchingIntersectionDistance rho sigma = 0 ↔
      rho.constantSubspacePoint = sigma.constantSubspacePoint :=
  fixedRankIntersectionDistance_eq_zero_iff p rho.constantSubspacePoint
    sigma.constantSubspacePoint

/-- The matching distance satisfies the triangle inequality. -/
theorem matchingIntersectionDistance_triangle
    {p : ℕ} (rho sigma tau : PerfectMatching p) :
    matchingIntersectionDistance rho tau ≤
      matchingIntersectionDistance rho sigma +
        matchingIntersectionDistance sigma tau :=
  fixedRankIntersectionDistance_triangle p rho.constantSubspacePoint
    sigma.constantSubspacePoint tau.constantSubspacePoint

/-- If a replica partition coarsens both adjacent matchings, their distance is
at most the partition defect p minus its block count. -/
theorem matchingIntersectionDistance_le_partitionDefect
    {p : ℕ} (pi : ReplicaPartition p)
    (rho sigma : PerfectMatching p)
    (hrho : PartitionCoarsens pi rho.partition)
    (hsigma : PartitionCoarsens pi sigma.partition) :
    matchingIntersectionDistance rho sigma ≤
      p - partitionBlockCount pi := by
  let Cpi : Submodule ℚ (Replica p → ℚ) :=
    partitionConstantSubspace (K := ℚ) pi
  let Crho : Submodule ℚ (Replica p → ℚ) :=
    partitionConstantSubspace (K := ℚ) rho.partition
  let Csigma : Submodule ℚ (Replica p → ℚ) :=
    partitionConstantSubspace (K := ℚ) sigma.partition
  have hsub : Cpi ≤ Crho ⊓ Csigma := by
    apply le_inf
    · exact partitionConstantSubspace_mono hrho
    · exact partitionConstantSubspace_mono hsigma
  have hrank :
      partitionBlockCount pi ≤ Module.finrank ℚ ↑(Crho ⊓ Csigma) := by
    rw [← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) pi]
    exact Submodule.finrank_mono hsub
  have hinter :
      Module.finrank ℚ ↑(Crho ⊓ Csigma) ≤ p := by
    calc
      Module.finrank ℚ ↑(Crho ⊓ Csigma) ≤ Module.finrank ℚ Crho :=
        Submodule.finrank_mono inf_le_left
      _ = partitionBlockCount rho.partition := by
        exact finrank_partitionConstantSubspace_eq_blockCount rho.partition
      _ = p := rho.blockCount_eq
  change p - Module.finrank ℚ ↑(Crho ⊓ Csigma) ≤
    p - partitionBlockCount pi
  omega

#print axioms matchingIntersectionDistance_triangle
#print axioms matchingIntersectionDistance_le_partitionDefect

end GraphMatrixReplica
