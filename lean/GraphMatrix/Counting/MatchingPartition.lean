import GraphMatrix.EdgeParityMatching

/-! # Matching partitions without pairing-enumeration multiplicity

`PerfectMatching p` contains an equivalence `Replica p ≃ Fin p × Bool` and
therefore has many encodings for the same two-element-block partition.  The
object counted in the C079 encoding is the partition itself.  Here its
matching property is stored only as a proposition, so reordering pairs or
swapping the points within a pair does not create a new object.

The canonical refinement below is a fixed, noncomputable choice.  It is a
function of the input partition and is sufficient for a lossless *choice of
one refinement*, but it is not the ordered-successor algorithm described in
Appendix D of the paper.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A matching represented by its equality partition, not by a labeled
enumeration of its pairs.  The existence witness is proof-irrelevant. -/
abbrev C079MatchingPartition (p : ℕ) :=
  {σ : ReplicaPartition p // ∃ ρ : PerfectMatching p, ρ.partition = σ}

/-- Forget the redundant pair enumeration of a perfect matching. -/
def PerfectMatching.toC079MatchingPartition {p : ℕ}
    (ρ : PerfectMatching p) : C079MatchingPartition p :=
  ⟨ρ.partition, ρ, rfl⟩

/-- The matching-partition construction is surjective, but not claimed to be
injective: `PerfectMatching` has labeling redundancy. -/
theorem perfectMatching_toC079MatchingPartition_surjective {p : ℕ} :
    Function.Surjective
      (PerfectMatching.toC079MatchingPartition (p := p)) := by
  rintro ⟨σ, ⟨ρ, hρ⟩⟩
  refine ⟨ρ, ?_⟩
  apply Subtype.ext
  exact hρ

/-- Two matching-partition values are equal precisely when their underlying
equality partitions are equal.  There is no `p! 2^p` representation factor. -/
theorem c079MatchingPartition_eq_iff {p : ℕ}
    (σ τ : C079MatchingPartition p) : σ = τ ↔ σ.1 = τ.1 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · exact Subtype.ext

/-- A matching-partition has exactly `p` blocks. -/
theorem C079MatchingPartition.blockCount_eq {p : ℕ}
    (σ : C079MatchingPartition p) : partitionBlockCount σ.1 = p := by
  obtain ⟨ρ, hρ⟩ := σ.2
  rw [← hρ]
  exact ρ.blockCount_eq

/-- Every even replica partition has a matching-partition refinement. -/
theorem exists_c079MatchingPartition_refines_even
    {p : ℕ} (π : ReplicaPartition p) (hEven : IsEvenPartition π) :
    ∃ σ : C079MatchingPartition p, PartitionCoarsens π σ.1 := by
  classical
  let f : Replica p → Quotient π := Quotient.mk''
  have hfiber : ∀ b : Quotient π,
      Even ((Finset.univ.filter fun x : Replica p => f x = b).card) := by
    intro b
    refine Quotient.inductionOn b ?_
    intro a
    rw [quotientFiber_eq_partitionBlock]
    exact hEven a
  obtain ⟨P⟩ := exists_fiberwisePairing_of_even_fibers p f
    (by simp [Replica]) hfiber
  refine ⟨P.toPerfectMatching.toC079MatchingPartition, ?_⟩
  intro a b hab
  have h : (equalityPartition f).r a b :=
    P.mapPartitionCoarsens a b hab
  change (Quotient.mk'' a : Quotient π) = Quotient.mk'' b at h
  exact Quotient.exact h

/-- A fixed choice of one matching refinement for every even partition.
This is deterministic in the logical sense (the same input gives the same
value), but `Classical.choose` does not supply an executable order rule. -/
def c079CanonicalMatchingRefinement {p : ℕ}
    (π : ReplicaPartition p) (hEven : IsEvenPartition π) :
    C079MatchingPartition p :=
  Classical.choose (exists_c079MatchingPartition_refines_even π hEven)

theorem c079CanonicalMatchingRefinement_refines
    {p : ℕ} (π : ReplicaPartition p) (hEven : IsEvenPartition π) :
    PartitionCoarsens π (c079CanonicalMatchingRefinement π hEven).1 :=
  Classical.choose_spec (exists_c079MatchingPartition_refines_even π hEven)

/-- The chosen partition does not depend on which proof of evenness was
supplied.  This is proof-irrelevance, not a computational canonization. -/
theorem c079CanonicalMatchingRefinement_proof_irrel
    {p : ℕ} (π : ReplicaPartition p)
    (h₁ h₂ : IsEvenPartition π) :
    c079CanonicalMatchingRefinement π h₁ =
      c079CanonicalMatchingRefinement π h₂ := by
  have h : h₁ = h₂ := Subsingleton.elim h₁ h₂
  cases h
  rfl

/-- The constant-vector subspace has the required rank `p` directly from
the partition, independent of its `PerfectMatching` enumeration. -/
def C079MatchingPartition.constantSubspacePoint {p : ℕ}
    (σ : C079MatchingPartition p) :
    FixedRankSubmodule ℚ (Replica p → ℚ) p :=
  ⟨partitionConstantSubspace (K := ℚ) σ.1, by
    rw [finrank_partitionConstantSubspace_eq_blockCount]
    exact σ.blockCount_eq⟩

/-- The matching distance descends to the nonredundant partition subtype. -/
def c079MatchingPartitionDistance {p : ℕ}
    (σ τ : C079MatchingPartition p) : ℕ :=
  fixedRankIntersectionDistance p σ.constantSubspacePoint
    τ.constantSubspacePoint

/-- Descending the distance changes no numerical value. -/
theorem c079MatchingPartitionDistance_of_perfectMatching {p : ℕ}
    (ρ η : PerfectMatching p) :
    c079MatchingPartitionDistance
      ρ.toC079MatchingPartition η.toC079MatchingPartition =
      matchingIntersectionDistance ρ η := by
  rfl

theorem c079MatchingPartitionDistance_triangle {p : ℕ}
    (σ τ ξ : C079MatchingPartition p) :
    c079MatchingPartitionDistance σ ξ ≤
      c079MatchingPartitionDistance σ τ +
        c079MatchingPartitionDistance τ ξ :=
  fixedRankIntersectionDistance_triangle p
    σ.constantSubspacePoint τ.constantSubspacePoint ξ.constantSubspacePoint

/-- The existing partition-defect estimate descends exactly through the
quotient of redundant `PerfectMatching` encodings. -/
theorem c079MatchingPartitionDistance_le_partitionDefect
    {p : ℕ} (π : ReplicaPartition p)
    (σ τ : C079MatchingPartition p)
    (hσ : PartitionCoarsens π σ.1)
    (hτ : PartitionCoarsens π τ.1) :
    c079MatchingPartitionDistance σ τ ≤
      p - partitionBlockCount π := by
  obtain ⟨ρ, hρ⟩ := σ.2
  obtain ⟨η, hη⟩ := τ.2
  have hσeq : ρ.toC079MatchingPartition = σ := Subtype.ext hρ
  have hτeq : η.toC079MatchingPartition = τ := Subtype.ext hη
  calc
    c079MatchingPartitionDistance σ τ =
        c079MatchingPartitionDistance
          ρ.toC079MatchingPartition η.toC079MatchingPartition := by
            rw [hσeq, hτeq]
    _ = matchingIntersectionDistance ρ η :=
      c079MatchingPartitionDistance_of_perfectMatching ρ η
    _ ≤ p - partitionBlockCount π :=
      matchingIntersectionDistance_le_partitionDefect π ρ η
        (by simpa only [hρ] using hσ)
        (by simpa only [hη] using hτ)

/-- A parity-compatible edge admits one matching *partition* refining both
endpoint partitions.  This is a witness for legality, not a multiplicity in
the Rademacher moment expansion. -/
theorem exists_c079MatchingPartition_refines_edge
    {p : ℕ} (π ψ : ReplicaPartition p)
    (hEdge : EdgeParityCompatible π ψ) :
    ∃ ξ : C079MatchingPartition p,
      PartitionCoarsens π ξ.1 ∧ PartitionCoarsens ψ ξ.1 := by
  obtain ⟨ρ, hπ, hψ⟩ :=
    exists_perfectMatching_coarsened_by_edgeEndpoints π ψ hEdge
  exact ⟨ρ.toC079MatchingPartition, hπ, hψ⟩

/-- Paper C079's edge matching-distance bound, stated on partition objects
rather than on their redundant pair enumerations. -/
theorem c079MatchingPartitionDistance_le_edgeDefects
    {p : ℕ} (π ψ : ReplicaPartition p)
    (hEdge : EdgeParityCompatible π ψ)
    (σ τ : C079MatchingPartition p)
    (hσ : PartitionCoarsens π σ.1)
    (hτ : PartitionCoarsens ψ τ.1) :
    c079MatchingPartitionDistance σ τ ≤
      (p - partitionBlockCount π) +
        (p - partitionBlockCount ψ) := by
  obtain ⟨ξ, hπξ, hψξ⟩ :=
    exists_c079MatchingPartition_refines_edge π ψ hEdge
  calc
    c079MatchingPartitionDistance σ τ ≤
        c079MatchingPartitionDistance σ ξ +
          c079MatchingPartitionDistance ξ τ :=
      c079MatchingPartitionDistance_triangle σ ξ τ
    _ ≤ (p - partitionBlockCount π) +
        (p - partitionBlockCount ψ) :=
      Nat.add_le_add
        (c079MatchingPartitionDistance_le_partitionDefect π σ ξ hσ hπξ)
        (c079MatchingPartitionDistance_le_partitionDefect ψ ξ τ hψξ hτ)


end GraphMatrixReplica
