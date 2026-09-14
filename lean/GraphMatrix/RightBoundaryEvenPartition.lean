import GraphMatrix.EdgeParityEvenEndpoint

/-! # Even blocks from the right trace matching

An isolated right-boundary role has no incident edge from which to inherit
parity.  Instead its equality partition coarsens the adjacent-pair trace
matching.  Each block is therefore a union of two-element fibers.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The two replicas in the right trace pair indexed by `k`. -/
def rightPair {p : ℕ} (k : Fin (p + 1)) : Finset (Replica (p + 1)) :=
  {(k, false), (k, true)}

/-- If a partition coarsens the right trace matching, then every partition
block is even. -/
theorem rightTraceCoarsens_evenPartition
    {p : ℕ} (π : ReplicaPartition (p + 1))
    (hR : RightTraceCoarsens π) : IsEvenPartition π := by
  classical
  intro a
  let fiber : Fin (p + 1) → Finset (Replica (p + 1)) := fun k =>
    (partitionBlock π a).filter fun x => x.1 = k
  have hFiberEven : ∀ k : Fin (p + 1), Even (fiber k).card := by
    intro k
    by_cases hk : (fiber k).Nonempty
    · have hFalse : (k, false) ∈ partitionBlock π a := by
        by_contra hnot
        obtain ⟨x, hx⟩ := hk
        have hxBlock := (Finset.mem_filter.mp hx).1
        have hxKey := (Finset.mem_filter.mp hx).2
        rcases x with ⟨j, b⟩
        change j = k at hxKey
        subst j
        cases b with
        | false => exact hnot hxBlock
        | true =>
            have hTrueRel : π.r (k, true) a := by
              simpa only [partitionBlock, Finset.mem_filter,
                Finset.mem_univ, true_and] using hxBlock
            have hFalseRel : π.r (k, false) a :=
              π.iseqv.trans (hR k) hTrueRel
            exact hnot (by
              simpa only [partitionBlock, Finset.mem_filter,
                Finset.mem_univ, true_and])
      have hTrue : (k, true) ∈ partitionBlock π a := by
        have hFalseRel : π.r (k, false) a := by
          simpa only [partitionBlock, Finset.mem_filter,
            Finset.mem_univ, true_and] using hFalse
        have hTrueRel : π.r (k, true) a :=
          π.iseqv.trans (π.iseqv.symm (hR k)) hFalseRel
        simpa only [partitionBlock, Finset.mem_filter,
          Finset.mem_univ, true_and]
      have hFiberEq : fiber k = rightPair k := by
        ext x
        constructor
        · intro hx
          have hxKey := (Finset.mem_filter.mp hx).2
          rcases x with ⟨j, b⟩
          change j = k at hxKey
          subst j
          cases b <;> simp [rightPair]
        · intro hx
          simp only [rightPair, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hFalse, rfl⟩
          · exact Finset.mem_filter.mpr ⟨hTrue, rfl⟩
      rw [hFiberEq]
      simp [rightPair]
    · have hEmpty : fiber k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hk
      rw [hEmpty]
      exact Even.zero
  have hCard :
      (partitionBlock π a).card = ∑ k : Fin (p + 1), (fiber k).card := by
    simpa [fiber] using Finset.card_eq_sum_card_fiberwise
      (f := fun x : Replica (p + 1) => x.1)
      (s := partitionBlock π a) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  choose half hHalf using hFiberEven
  refine ⟨∑ k : Fin (p + 1), half k, ?_⟩
  rw [hCard]
  simp_rw [hHalf]
  rw [Finset.sum_add_distrib]

/-- Hence an isolated right-boundary role also obeys the C078 block bound. -/
theorem rightTraceCoarsens_blockCount_le
    {p : ℕ} (π : ReplicaPartition (p + 1))
    (hR : RightTraceCoarsens π) : partitionBlockCount π ≤ p + 1 :=
  evenPartition_blockCount_le π (rightTraceCoarsens_evenPartition π hR)


end GraphMatrixReplica
