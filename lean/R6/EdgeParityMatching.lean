import R6.EdgeParityEvenEndpoint
import R6.EvenFiberPairing

/-! # An edge-compatible perfect matching

Rademacher parity says that every common equality cell of the two endpoint
partitions is even.  Pairing separately inside those cells produces a
perfect matching refined by both endpoint partitions.  This closes the
local existence step implicit in the C078 matching-path argument.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The pair of quotient classes recording the meet cell of a replica. -/
def edgeClassKey {q : ℕ} (pi sigma : ReplicaPartition q) (a : Replica q) :
    Quotient pi × Quotient sigma :=
  (Quotient.mk'' a, Quotient.mk'' a)

/-- A finite fiber of the quotient-pair map. -/
def edgeClassFiber {q : ℕ} (pi sigma : ReplicaPartition q)
    (b : Quotient pi × Quotient sigma) : Finset (Replica q) := by
  classical
  exact Finset.univ.filter fun x => edgeClassKey pi sigma x = b

/-- A fiber of `edgeClassKey` through `a` is its meet cell. -/
theorem edgeClassKey_fiber_eq_meetCell
    {q : ℕ} (pi sigma : ReplicaPartition q) (a : Replica q) :
    edgeClassFiber pi sigma (edgeClassKey pi sigma a) =
        partitionMeetCell pi sigma a := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    edgeClassFiber, edgeClassKey, Prod.mk.injEq, partitionMeetCell]
  constructor
  · rintro ⟨hpi, hsigma⟩
    exact ⟨Quotient.eq''.mp hpi, Quotient.eq''.mp hsigma⟩
  · rintro ⟨hpi, hsigma⟩
    exact ⟨Quotient.sound hpi, Quotient.sound hsigma⟩

/-- Edge parity is precisely enough to make every quotient-pair fiber even,
including the empty fibers. -/
theorem edgeClassKey_even_fibers
    {q : ℕ} (pi sigma : ReplicaPartition q)
    (hEdge : EdgeParityCompatible pi sigma) :
    ∀ b : Quotient pi × Quotient sigma,
      Even (edgeClassFiber pi sigma b).card := by
  classical
  intro b
  by_cases hNonempty : (edgeClassFiber pi sigma b).Nonempty
  · obtain ⟨a, ha⟩ := hNonempty
    have haKey : edgeClassKey pi sigma a = b :=
      (Finset.mem_filter.mp ha).2
    rw [← haKey, edgeClassKey_fiber_eq_meetCell]
    exact hEdge a
  · have hEmpty : edgeClassFiber pi sigma b = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hNonempty
    rw [hEmpty]
    exact Even.zero

theorem firstPartition_coarsens_edgeClassKey
    {q : ℕ} (pi sigma : ReplicaPartition q) :
    PartitionCoarsens pi (equalityPartition (edgeClassKey pi sigma)) := by
  intro a b hab
  exact Quotient.eq''.mp (congrArg Prod.fst hab)

theorem secondPartition_coarsens_edgeClassKey
    {q : ℕ} (pi sigma : ReplicaPartition q) :
    PartitionCoarsens sigma (equalityPartition (edgeClassKey pi sigma)) := by
  intro a b hab
  exact Quotient.eq''.mp (congrArg Prod.snd hab)

/-- Every parity-compatible edge admits a perfect matching whose pair
partition is refined by both endpoint partitions. -/
theorem exists_perfectMatching_coarsened_by_edgeEndpoints
    {q : ℕ} (pi sigma : ReplicaPartition q)
    (hEdge : EdgeParityCompatible pi sigma) :
    ∃ rho : PerfectMatching q,
      PartitionCoarsens pi rho.partition ∧
        PartitionCoarsens sigma rho.partition := by
  classical
  have hcard : Fintype.card (Replica q) = q * 2 := by
    simp [Replica]
  obtain ⟨P⟩ := exists_fiberwisePairing_of_even_fibers q
    (edgeClassKey pi sigma) hcard
    (by
      intro b
      simpa [edgeClassFiber] using edgeClassKey_even_fibers pi sigma hEdge b)
  refine ⟨P.toPerfectMatching, ?_, ?_⟩
  · intro a b hab
    exact firstPartition_coarsens_edgeClassKey pi sigma a b
      (P.mapPartitionCoarsens a b hab)
  · intro a b hab
    exact secondPartition_coarsens_edgeClassKey pi sigma a b
      (P.mapPartitionCoarsens a b hab)

/-- A fixed compatible matching chosen for each edge of a replica state. -/
def ReplicaState.edgePerfectMatching
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (e : Fin G.edges) : PerfectMatching (p + 1) :=
  Classical.choose
    (exists_perfectMatching_coarsened_by_edgeEndpoints
      (S.partition (G.source e)) (S.partition (G.target e))
      (S.edgeParity e))

theorem ReplicaState.sourcePartition_coarsens_edgePerfectMatching
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (e : Fin G.edges) :
    PartitionCoarsens (S.partition (G.source e))
      (S.edgePerfectMatching e).partition :=
  (Classical.choose_spec
    (exists_perfectMatching_coarsened_by_edgeEndpoints
      (S.partition (G.source e)) (S.partition (G.target e))
      (S.edgeParity e))).1

theorem ReplicaState.targetPartition_coarsens_edgePerfectMatching
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (e : Fin G.edges) :
    PartitionCoarsens (S.partition (G.target e))
      (S.edgePerfectMatching e).partition :=
  (Classical.choose_spec
    (exists_perfectMatching_coarsened_by_edgeEndpoints
      (S.partition (G.source e)) (S.partition (G.target e))
      (S.edgeParity e))).2

#print axioms edgeClassKey_fiber_eq_meetCell
#print axioms edgeClassKey_even_fibers
#print axioms exists_perfectMatching_coarsened_by_edgeEndpoints
#print axioms ReplicaState.sourcePartition_coarsens_edgePerfectMatching
#print axioms ReplicaState.targetPartition_coarsens_edgePerfectMatching

end GraphMatrixReplica
