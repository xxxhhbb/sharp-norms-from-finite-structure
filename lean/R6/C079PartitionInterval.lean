import R6.EdgeParityMatching
import R6.TraceMatchingDistance

/-! # C079 intervals from replica partitions

This module realizes C079's interval endpoints through dimensions of
constant-on-partition subspaces.  For a partition `pi` at trace order `p+1`,
the quantity called `c(pi)` in C079 is the rank of the intersection of the
left-trace matching subspace with the partition subspace.  Thus

* `lower = blockCount(pi) - c(pi)`, and
* `upper = (p+1) - c(pi)`.

The key theorem proves that every perfect matching refined by `pi` has its
left-trace distance inside this interval.  A common matching on a
parity-compatible graph edge therefore proves that the endpoint intervals
intersect.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Linear-algebra realization of C079's join block count `c(pi)`. -/
def c079TraceJoinRank {p : ℕ} (pi : ReplicaPartition (p + 1)) : ℕ :=
  Module.finrank ℚ
    ↑(partitionConstantSubspace (K := ℚ) (leftPerfectMatching p).partition ⊓
      partitionConstantSubspace (K := ℚ) pi)

def c079PartitionLower {p : ℕ} (pi : ReplicaPartition (p + 1)) : ℕ :=
  partitionBlockCount pi - c079TraceJoinRank pi

def c079PartitionUpper {p : ℕ} (pi : ReplicaPartition (p + 1)) : ℕ :=
  (p + 1) - c079TraceJoinRank pi

theorem c079TraceJoinRank_le_blockCount
    {p : ℕ} (pi : ReplicaPartition (p + 1)) :
    c079TraceJoinRank pi ≤ partitionBlockCount pi := by
  unfold c079TraceJoinRank
  rw [← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) pi]
  exact Submodule.finrank_mono inf_le_right

/-- Globally constant replica vectors lie in every partition subspace. -/
theorem universalConstantSubspace_le_partitionConstantSubspace
    {p : ℕ} (pi : ReplicaPartition (p + 1)) :
    partitionConstantSubspace (K := ℚ) (universalReplicaPartition (p + 1)) ≤
      partitionConstantSubspace (K := ℚ) pi := by
  intro f hf
  rw [mem_partitionConstantSubspace_iff] at hf ⊢
  intro a b _
  exact hf a b trivial

/-- The trace-join rank is at least one at every positive trace order. -/
theorem one_le_c079TraceJoinRank
    {p : ℕ} (pi : ReplicaPartition (p + 1)) :
    1 ≤ c079TraceJoinRank pi := by
  have hUniversal :
      partitionConstantSubspace (K := ℚ)
          (universalReplicaPartition (p + 1)) ≤
        partitionConstantSubspace (K := ℚ)
            (leftPerfectMatching p).partition ⊓
          partitionConstantSubspace (K := ℚ) pi := by
    apply le_inf
    · exact universalConstantSubspace_le_partitionConstantSubspace _
    · exact universalConstantSubspace_le_partitionConstantSubspace _
  have hRank := Submodule.finrank_mono hUniversal
  rw [finrank_universalReplicaPartition_eq_one] at hRank
  exact hRank

theorem c079PartitionUpper_le_orderMinusOne
    {p : ℕ} (pi : ReplicaPartition (p + 1)) :
    c079PartitionUpper pi ≤ p := by
  unfold c079PartitionUpper
  have hpos := one_le_c079TraceJoinRank pi
  omega

/-- Exact interval width `upper-lower = order-blockCount`. -/
theorem c079PartitionUpper_sub_lower
    {p : ℕ} (pi : ReplicaPartition (p + 1))
    (hBlocks : partitionBlockCount pi ≤ p + 1) :
    c079PartitionUpper pi - c079PartitionLower pi =
      (p + 1) - partitionBlockCount pi := by
  unfold c079PartitionUpper c079PartitionLower
  have hRank := c079TraceJoinRank_le_blockCount pi
  omega

theorem c079PartitionLower_le_upper
    {p : ℕ} (pi : ReplicaPartition (p + 1))
    (hBlocks : partitionBlockCount pi ≤ p + 1) :
    c079PartitionLower pi ≤ c079PartitionUpper pi := by
  unfold c079PartitionLower c079PartitionUpper
  have hRank := c079TraceJoinRank_le_blockCount pi
  omega

/-- Any perfect matching refined by `pi` has left-trace distance inside the
C079 interval of `pi`. -/
theorem matchingDistance_mem_c079PartitionInterval
    {p : ℕ} (pi : ReplicaPartition (p + 1))
    (rho : PerfectMatching (p + 1))
    (hCoarsens : PartitionCoarsens pi rho.partition) :
    c079PartitionLower pi ≤
        matchingIntersectionDistance (leftPerfectMatching p) rho ∧
      matchingIntersectionDistance (leftPerfectMatching p) rho ≤
        c079PartitionUpper pi := by
  let A := partitionConstantSubspace (K := ℚ)
    (leftPerfectMatching p).partition
  let P := partitionConstantSubspace (K := ℚ) pi
  let B := partitionConstantSubspace (K := ℚ) rho.partition
  have hPB : P ≤ B := partitionConstantSubspace_mono hCoarsens
  have hIntersectMono : A ⊓ P ≤ A ⊓ B :=
    inf_le_inf_left A hPB
  have hRankMono :
      Module.finrank ℚ ↑(A ⊓ P) ≤ Module.finrank ℚ ↑(A ⊓ B) :=
    Submodule.finrank_mono hIntersectMono
  have hCross := finrank_inf_add_finrank_inf_le P B A
  have hPinfB : P ⊓ B = P := inf_eq_left.mpr hPB
  have hBinfA : B ⊓ A = A ⊓ B := inf_comm B A
  have hPinfA : P ⊓ A = A ⊓ P := inf_comm P A
  rw [hPinfB, hBinfA, hPinfA] at hCross
  have hPDim : Module.finrank ℚ P = partitionBlockCount pi := by
    exact finrank_partitionConstantSubspace_eq_blockCount pi
  have hBDim : Module.finrank ℚ B = p + 1 := by
    calc
      Module.finrank ℚ B = partitionBlockCount rho.partition :=
        finrank_partitionConstantSubspace_eq_blockCount rho.partition
      _ = p + 1 := rho.blockCount_eq
  unfold c079PartitionLower c079PartitionUpper c079TraceJoinRank
  unfold matchingIntersectionDistance fixedRankIntersectionDistance
  change
    partitionBlockCount pi - Module.finrank ℚ ↑(A ⊓ P) ≤
        (p + 1) - Module.finrank ℚ ↑(A ⊓ B) ∧
      (p + 1) - Module.finrank ℚ ↑(A ⊓ B) ≤
        (p + 1) - Module.finrank ℚ ↑(A ⊓ P)
  rw [hPDim, hBDim] at hCross
  constructor <;> omega

/-- Edge parity supplies a common matching, so the two C079 intervals
intersect. -/
theorem edgeParity_c079PartitionIntervals_intersect
    {p : ℕ} (pi sigma : ReplicaPartition (p + 1))
    (hEdge : EdgeParityCompatible pi sigma) :
    c079PartitionLower pi ≤ c079PartitionUpper sigma ∧
      c079PartitionLower sigma ≤ c079PartitionUpper pi := by
  obtain ⟨rho, hPi, hSigma⟩ :=
    exists_perfectMatching_coarsened_by_edgeEndpoints pi sigma hEdge
  have hPiInterval :=
    matchingDistance_mem_c079PartitionInterval pi rho hPi
  have hSigmaInterval :=
    matchingDistance_mem_c079PartitionInterval sigma rho hSigma
  exact ⟨hPiInterval.1.trans hSigmaInterval.2,
    hSigmaInterval.1.trans hPiInterval.2⟩

theorem leftTrace_c079PartitionLower_eq_zero
    {p : ℕ} (pi : ReplicaPartition (p + 1))
    (hLeft : LeftTraceCoarsens pi) :
    c079PartitionLower pi = 0 := by
  have hSubspace :
      partitionConstantSubspace (K := ℚ) pi ≤
        partitionConstantSubspace (K := ℚ)
          (leftPerfectMatching p).partition :=
    partitionConstantSubspace_mono
      (leftTraceCoarsens_partitionCoarsens pi hLeft)
  have hInf :
      partitionConstantSubspace (K := ℚ)
            (leftPerfectMatching p).partition ⊓
          partitionConstantSubspace (K := ℚ) pi =
        partitionConstantSubspace (K := ℚ) pi :=
    inf_eq_right.mpr hSubspace
  unfold c079PartitionLower c079TraceJoinRank
  rw [hInf, finrank_partitionConstantSubspace_eq_blockCount]
  omega

theorem rightTrace_c079PartitionUpper_eq_orderMinusOne
    {p : ℕ} (pi : ReplicaPartition (p + 1))
    (hRight : RightTraceCoarsens pi) :
    c079PartitionUpper pi = p := by
  have hInterval := matchingDistance_mem_c079PartitionInterval pi
    (rightPerfectMatching (p + 1))
    (rightTraceCoarsens_partitionCoarsens pi hRight)
  have hDistance :
      matchingIntersectionDistance (leftPerfectMatching p)
          (rightPerfectMatching (p + 1)) = p := by
    rw [matchingIntersectionDistance_comm]
    exact right_left_matchingIntersectionDistance_eq p
  have hUpper := c079PartitionUpper_le_orderMinusOne pi
  rw [hDistance] at hInterval
  omega

#print axioms c079PartitionUpper_sub_lower
#print axioms c079PartitionLower_le_upper
#print axioms matchingDistance_mem_c079PartitionInterval
#print axioms edgeParity_c079PartitionIntervals_intersect
#print axioms leftTrace_c079PartitionLower_eq_zero
#print axioms rightTrace_c079PartitionUpper_eq_orderMinusOne

end GraphMatrixReplica
