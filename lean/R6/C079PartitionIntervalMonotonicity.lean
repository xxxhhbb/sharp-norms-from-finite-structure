import R6.C079ReplicaIntervalLayers

/-! # C079 refinement monotonicity and attachment-layer incidence

These are the two interval facts used before the active-component count in
the paper's C079 argument. `PartitionCoarsens pi theta` means that `theta`
is the finer partition. The interval of the finer partition is contained in
the interval of the coarser one. Hence a layer crossed by a seed constraint
`theta` contains every attachment neighbor whose partition coarsens `theta`.

No component count or `a_*` assertion is made here.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Refinement containment, including both endpoints of the C079 integer
interval. The proof uses the rank inequality for three constant subspaces;
no evenness or matching-refinement hypothesis is required. -/
theorem c079_refinement_interval_contained
    {p : ℕ} (pi theta : ReplicaPartition (p + 1))
    (hCoarsens : PartitionCoarsens pi theta) :
    c079PartitionLower pi ≤ c079PartitionLower theta ∧
      c079PartitionUpper theta ≤ c079PartitionUpper pi := by
  let A : Submodule ℚ (Replica (p + 1) → ℚ) :=
    partitionConstantSubspace (K := ℚ) (leftPerfectMatching p).partition
  let P : Submodule ℚ (Replica (p + 1) → ℚ) :=
    partitionConstantSubspace (K := ℚ) pi
  let T : Submodule ℚ (Replica (p + 1) → ℚ) :=
    partitionConstantSubspace (K := ℚ) theta
  have hPT : P ≤ T := partitionConstantSubspace_mono hCoarsens
  have hRank : c079TraceJoinRank pi ≤ c079TraceJoinRank theta := by
    change Module.finrank ℚ ↑(A ⊓ P) ≤ Module.finrank ℚ ↑(A ⊓ T)
    exact Submodule.finrank_mono (inf_le_inf_left A hPT)
  have hCross := finrank_inf_add_finrank_inf_le P T A
  have hPinfT : P ⊓ T = P := inf_eq_left.mpr hPT
  have hTinfA : T ⊓ A = A ⊓ T := inf_comm T A
  have hPinfA : P ⊓ A = A ⊓ P := inf_comm P A
  rw [hPinfT, hTinfA, hPinfA] at hCross
  have hBlocks :
      partitionBlockCount pi + c079TraceJoinRank theta ≤
        partitionBlockCount theta + c079TraceJoinRank pi := by
    change Module.finrank ℚ P + Module.finrank ℚ ↑(A ⊓ T) ≤
      Module.finrank ℚ T + Module.finrank ℚ ↑(A ⊓ P) at hCross
    rw [finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) pi,
      finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) theta]
      at hCross
    exact hCross
  have hRankPi := c079TraceJoinRank_le_blockCount pi
  have hRankTheta := c079TraceJoinRank_le_blockCount theta
  constructor
  · unfold c079PartitionLower
    omega
  · unfold c079PartitionUpper
    omega

/-- If the seed constraint `theta` crosses layer `k` and refines every
attachment-neighbor partition, all those neighbors belong to the state's
half-open C079 layer. This is precisely the incidence half of the later
active-component argument, without claiming component isolation. -/
theorem c079_refined_seed_neighbors_mem_intervalLayer
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (neighbors : Finset (Fin G.roles))
    (theta : ReplicaPartition (p + 1)) (k : ℕ)
    (hRefines : ∀ x ∈ neighbors,
      PartitionCoarsens (S.partition x) theta)
    (hCrosses : c079PartitionLower theta < k ∧
      k ≤ c079PartitionUpper theta) :
    neighbors ⊆
      c079IntervalLayer
        (fun x => c079PartitionLower (S.partition x))
        (fun x => c079PartitionUpper (S.partition x)) k := by
  intro x hx
  have hContains := c079_refinement_interval_contained
    (S.partition x) theta (hRefines x hx)
  simp only [c079IntervalLayer, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨lt_of_le_of_lt hContains.1 hCrosses.1,
    hCrosses.2.trans hContains.2⟩

/-- The same attachment statement with the actual interval certificate
constructed from a covered fully-partite replica state. -/
theorem ReplicaState.c079_refined_seed_neighbors_mem_layer
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (neighbors : Finset (Fin G.roles))
    (theta : ReplicaPartition (p + 1)) (k : ℕ)
    (hRefines : ∀ x ∈ neighbors,
      PartitionCoarsens (S.partition x) theta)
    (hCrosses : c079PartitionLower theta < k ∧
      k ≤ c079PartitionUpper theta) :
    let C := S.c079IntervalCertificate hCovered
    neighbors ⊆ c079IntervalLayer C.ell C.upper k := by
  change neighbors ⊆
    c079IntervalLayer
      (fun x => c079PartitionLower (S.partition x))
      (fun x => c079PartitionUpper (S.partition x)) k
  exact c079_refined_seed_neighbors_mem_intervalLayer
    S neighbors theta k hRefines hCrosses

#print axioms c079_refinement_interval_contained
#print axioms c079_refined_seed_neighbors_mem_intervalLayer
#print axioms ReplicaState.c079_refined_seed_neighbors_mem_layer

end GraphMatrixReplica
