import R6.PairCoarseningEvenPartition
import R6.PerfectMatchingDistance

/-! # Standard trace matchings and their endpoint distance

The right matching is the adjacent pairing, while the left matching is its
cyclic transport.  Their constant-vector subspaces intersect exactly in the
one-dimensional space of globally constant replica vectors, so their distance
at moment order q = p+1 is q-1 = p.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The perfect matching obtained by transporting the standard pairs with an
equivalence of the replica set. -/
def perfectMatchingOfEquiv {q : ℕ}
    (e : Replica q ≃ Replica q) : PerfectMatching q :=
  ⟨e⟩

/-- Coarsening the transported pairs is equivalent to coarsening their exact
two-point equality partition. -/
theorem pairEquivCoarsens_iff_partitionCoarsens
    {q : ℕ} (pi : ReplicaPartition q) (e : Replica q ≃ Replica q) :
    PairEquivCoarsens pi e ↔
      PartitionCoarsens pi (perfectMatchingOfEquiv e).partition := by
  constructor
  · intro hpair a b hab
    unfold perfectMatchingOfEquiv PerfectMatching.partition at hab
    change (e.symm a).1 = (e.symm b).1 at hab
    cases ha : e.symm a with
    | mk ka ba =>
      cases hb : e.symm b with
      | mk kb bb =>
        have hkeys : ka = kb := by
          simpa only [ha, hb] using hab
        subst kb
        have hae : e (ka, ba) = a := by
          calc
            e (ka, ba) = e (e.symm a) := by rw [ha]
            _ = a := e.apply_symm_apply a
        have hbe : e (ka, bb) = b := by
          calc
            e (ka, bb) = e (e.symm b) := by rw [hb]
            _ = b := e.apply_symm_apply b
        rw [← hae, ← hbe]
        cases ba <;> cases bb
        · exact pi.iseqv.refl _
        · exact hpair ka
        · exact pi.iseqv.symm (hpair ka)
        · exact pi.iseqv.refl _
  · intro h k
    apply h
    change (e.symm (e (k, false))).1 = (e.symm (e (k, true))).1
    simp

/-- Adjacent-pair matching used at the right trace boundary. -/
def rightPerfectMatching (q : ℕ) : PerfectMatching q :=
  perfectMatchingOfEquiv (Equiv.refl (Replica q))

/-- Cyclic matching used at the left trace boundary. -/
def leftPerfectMatching (p : ℕ) : PerfectMatching (p + 1) :=
  perfectMatchingOfEquiv (leftPairEquiv p)

theorem rightTraceCoarsens_partitionCoarsens
    {p : ℕ} (pi : ReplicaPartition (p + 1))
    (hR : RightTraceCoarsens pi) :
    PartitionCoarsens pi (rightPerfectMatching (p + 1)).partition := by
  apply (pairEquivCoarsens_iff_partitionCoarsens pi
    (Equiv.refl (Replica (p + 1)))).1
  intro k
  exact hR k

theorem leftTraceCoarsens_partitionCoarsens
    {p : ℕ} (pi : ReplicaPartition (p + 1))
    (hL : LeftTraceCoarsens pi) :
    PartitionCoarsens pi (leftPerfectMatching p).partition := by
  apply (pairEquivCoarsens_iff_partitionCoarsens pi (leftPairEquiv p)).1
  exact leftTraceCoarsens_pairEquiv pi hL

/-- Universal one-block partition. -/
def universalReplicaPartition (q : ℕ) : ReplicaPartition q where
  r := fun _ _ => True
  iseqv := {
    refl := fun _ => trivial
    symm := fun _ => trivial
    trans := fun _ _ => trivial
  }

theorem universalReplicaPartition_blockCount_eq_one (p : ℕ) :
    partitionBlockCount (universalReplicaPartition (p + 1)) = 1 := by
  apply common_trace_coarsening_blockCount_eq_one
  · constructor
    · intro _
      trivial
    · trivial
  · intro _
    trivial

theorem finrank_universalReplicaPartition_eq_one (p : ℕ) :
    Module.finrank ℚ
      (partitionConstantSubspace (K := ℚ)
        (universalReplicaPartition (p + 1))) = 1 := by
  rw [finrank_partitionConstantSubspace_eq_blockCount]
  exact universalReplicaPartition_blockCount_eq_one p

/-- A function lies in a partition's constant subspace exactly when its
equality partition coarsens that partition. -/
theorem mem_constantSubspace_iff_equalityPartition_coarsens
    {q : ℕ} (pi : ReplicaPartition q) (f : Replica q → ℚ) :
    f ∈ partitionConstantSubspace (K := ℚ) pi ↔
      PartitionCoarsens (equalityPartition f) pi := by
  rfl

/-- The right and left trace matching subspaces meet only in globally constant
vectors. -/
theorem right_inf_left_constantSubspace_eq_universal (p : ℕ) :
    partitionConstantSubspace (K := ℚ)
        (rightPerfectMatching (p + 1)).partition ⊓
      partitionConstantSubspace (K := ℚ)
        (leftPerfectMatching p).partition =
      partitionConstantSubspace (K := ℚ)
        (universalReplicaPartition (p + 1)) := by
  ext f
  constructor
  · intro hf
    have hRightCoarsens :
        PartitionCoarsens (equalityPartition f)
          (rightPerfectMatching (p + 1)).partition :=
      (mem_constantSubspace_iff_equalityPartition_coarsens _ f).1 hf.1
    have hLeftCoarsens :
        PartitionCoarsens (equalityPartition f)
          (leftPerfectMatching p).partition :=
      (mem_constantSubspace_iff_equalityPartition_coarsens _ f).1 hf.2
    have hR : RightTraceCoarsens (equalityPartition f) := by
      have hpair := (pairEquivCoarsens_iff_partitionCoarsens
        (equalityPartition f) (Equiv.refl (Replica (p + 1)))).2
          hRightCoarsens
      intro k
      exact hpair k
    have hL : LeftTraceCoarsens (equalityPartition f) := by
      have hpair := (pairEquivCoarsens_iff_partitionCoarsens
        (equalityPartition f) (leftPairEquiv p)).2 hLeftCoarsens
      constructor
      · intro k
        simpa [leftPairEquiv_false, leftPairEquiv_true] using
          hpair k.castSucc
      · simpa [leftPairEquiv_false, leftPairEquiv_true, finRotate_last] using
          hpair (Fin.last p)
    have hall := common_trace_coarsening_universal
      (equalityPartition f) hL hR
    intro a b _
    exact hall a b
  · intro hf
    constructor
    · intro a b _
      exact hf a b trivial
    · intro a b _
      exact hf a b trivial

/-- Exact endpoint value d(tau_R,tau_L)=q-1 at q=p+1. -/
theorem right_left_matchingIntersectionDistance_eq (p : ℕ) :
    matchingIntersectionDistance (rightPerfectMatching (p + 1))
      (leftPerfectMatching p) = p := by
  unfold matchingIntersectionDistance fixedRankIntersectionDistance
  change (p + 1) -
      Module.finrank ℚ
        ↑(partitionConstantSubspace (K := ℚ)
            (rightPerfectMatching (p + 1)).partition ⊓
          partitionConstantSubspace (K := ℚ)
            (leftPerfectMatching p).partition) = p
  rw [right_inf_left_constantSubspace_eq_universal]
  rw [finrank_universalReplicaPartition_eq_one]
  omega

#print axioms pairEquivCoarsens_iff_partitionCoarsens
#print axioms right_inf_left_constantSubspace_eq_universal
#print axioms right_left_matchingIntersectionDistance_eq

end GraphMatrixReplica
