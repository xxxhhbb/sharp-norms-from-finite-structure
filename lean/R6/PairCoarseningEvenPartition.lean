import R6.RightBoundaryEvenPartition

/-! # Even partitions from an arbitrary paired gluing

The left trace matching is a cyclic reindexing of the adjacent right
matching.  We first prove the parity statement for any explicit equivalence
from `q × Bool` to the replica set, then instantiate it with that cyclic
reindexing.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A partition coarsens the pairs transported by `e`. -/
def PairEquivCoarsens {q : ℕ} (π : ReplicaPartition q)
    (e : Replica q ≃ Replica q) : Prop :=
  ∀ k : Fin q, π.r (e (k, false)) (e (k, true))

def pairUnderEquiv {q : ℕ} (e : Replica q ≃ Replica q) (k : Fin q) :
    Finset (Replica q) :=
  {e (k, false), e (k, true)}

/-- Coarsening any transported perfect pairing forces all equality blocks
to have even cardinality. -/
theorem pairEquivCoarsens_evenPartition
    {q : ℕ} (π : ReplicaPartition q) (e : Replica q ≃ Replica q)
    (hPair : PairEquivCoarsens π e) : IsEvenPartition π := by
  classical
  intro a
  let fiber : Fin q → Finset (Replica q) := fun k =>
    (partitionBlock π a).filter fun x => (e.symm x).1 = k
  have hFiberEven : ∀ k : Fin q, Even (fiber k).card := by
    intro k
    by_cases hk : (fiber k).Nonempty
    · have hFalse : e (k, false) ∈ partitionBlock π a := by
        by_contra hnot
        obtain ⟨x, hx⟩ := hk
        have hxBlock := (Finset.mem_filter.mp hx).1
        have hxKey := (Finset.mem_filter.mp hx).2
        have hSymm : e.symm x = (k, (e.symm x).2) := by
          exact Prod.ext hxKey rfl
        have hxEq : x = e (k, (e.symm x).2) := by
          calc
            x = e (e.symm x) := (e.apply_symm_apply x).symm
            _ = e (k, (e.symm x).2) := congrArg e hSymm
        cases hb : (e.symm x).2 with
        | false =>
            simp only [hb] at hxEq
            rw [hxEq] at hxBlock
            exact hnot hxBlock
        | true =>
            simp only [hb] at hxEq
            rw [hxEq] at hxBlock
            have hTrueRel : π.r (e (k, true)) a := by
              simpa only [partitionBlock, Finset.mem_filter,
                Finset.mem_univ, true_and] using hxBlock
            have hFalseRel : π.r (e (k, false)) a :=
              π.iseqv.trans (hPair k) hTrueRel
            exact hnot (by
              simpa only [partitionBlock, Finset.mem_filter,
                Finset.mem_univ, true_and])
      have hTrue : e (k, true) ∈ partitionBlock π a := by
        have hFalseRel : π.r (e (k, false)) a := by
          simpa only [partitionBlock, Finset.mem_filter,
            Finset.mem_univ, true_and] using hFalse
        have hTrueRel : π.r (e (k, true)) a :=
          π.iseqv.trans (π.iseqv.symm (hPair k)) hFalseRel
        simpa only [partitionBlock, Finset.mem_filter,
          Finset.mem_univ, true_and]
      have hFiberEq : fiber k = pairUnderEquiv e k := by
        ext x
        constructor
        · intro hx
          have hxKey := (Finset.mem_filter.mp hx).2
          have hSymm : e.symm x = (k, (e.symm x).2) :=
            Prod.ext hxKey rfl
          have hxEq : x = e (k, (e.symm x).2) := by
            calc
              x = e (e.symm x) := (e.apply_symm_apply x).symm
              _ = e (k, (e.symm x).2) := congrArg e hSymm
          cases hb : (e.symm x).2 with
          | false => simp only [hb] at hxEq; simp [pairUnderEquiv, hxEq]
          | true => simp only [hb] at hxEq; simp [pairUnderEquiv, hxEq]
        · intro hx
          simp only [pairUnderEquiv, Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hFalse, by simp⟩
          · exact Finset.mem_filter.mpr ⟨hTrue, by simp⟩
      rw [hFiberEq]
      simp [pairUnderEquiv]
    · have hEmpty : fiber k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hk
      rw [hEmpty]
      exact Even.zero
  have hCard :
      (partitionBlock π a).card = ∑ k : Fin q, (fiber k).card := by
    simpa [fiber] using Finset.card_eq_sum_card_fiberwise
      (f := fun x : Replica q => (e.symm x).1)
      (s := partitionBlock π a) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  choose half hHalf using hFiberEven
  refine ⟨∑ k : Fin q, half k, ?_⟩
  rw [hCard]
  simp_rw [hHalf]
  rw [Finset.sum_add_distrib]

/-- Reindex the adjacent pairs into the cyclic left trace pairs. -/
def leftPairEquiv (p : ℕ) : Replica (p + 1) ≃ Replica (p + 1) where
  toFun x := if x.2 then (finRotate (p + 1) x.1, false) else (x.1, true)
  invFun x := if x.2 then (x.1, false)
    else ((finRotate (p + 1)).symm x.1, true)
  left_inv := by
    rintro ⟨k, b⟩
    cases b <;> simp
  right_inv := by
    rintro ⟨k, b⟩
    cases b <;> simp

@[simp] theorem leftPairEquiv_false (p : ℕ) (k : Fin (p + 1)) :
    leftPairEquiv p (k, false) = (k, true) := by
  rfl

@[simp] theorem leftPairEquiv_true (p : ℕ) (k : Fin (p + 1)) :
    leftPairEquiv p (k, true) = (finRotate (p + 1) k, false) := by
  rfl

/-- The explicit C078 cyclic gluing coarsens the pairs transported by
`leftPairEquiv`. -/
theorem leftTraceCoarsens_pairEquiv
    {p : ℕ} (π : ReplicaPartition (p + 1))
    (hL : LeftTraceCoarsens π) : PairEquivCoarsens π (leftPairEquiv p) := by
  intro k
  simp only [leftPairEquiv_false, leftPairEquiv_true]
  by_cases hk : k = Fin.last p
  · subst k
    simpa [finRotate_last] using hL.2
  · have hklt : (k : ℕ) < p := Fin.val_lt_last hk
    let j : Fin p := ⟨k, hklt⟩
    have hcast : j.castSucc = k := Fin.ext rfl
    have hrotate : finRotate (p + 1) k = j.succ := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last hk]
      rfl
    simpa only [hcast, hrotate] using hL.1 j

/-- An isolated left-boundary role also has an even partition. -/
theorem leftTraceCoarsens_evenPartition
    {p : ℕ} (π : ReplicaPartition (p + 1))
    (hL : LeftTraceCoarsens π) : IsEvenPartition π :=
  pairEquivCoarsens_evenPartition π (leftPairEquiv p)
    (leftTraceCoarsens_pairEquiv π hL)

theorem leftTraceCoarsens_blockCount_le
    {p : ℕ} (π : ReplicaPartition (p + 1))
    (hL : LeftTraceCoarsens π) : partitionBlockCount π ≤ p + 1 :=
  evenPartition_blockCount_le π (leftTraceCoarsens_evenPartition π hL)

#print axioms pairEquivCoarsens_evenPartition
#print axioms leftTraceCoarsens_pairEquiv
#print axioms leftTraceCoarsens_evenPartition
#print axioms leftTraceCoarsens_blockCount_le

end GraphMatrixReplica
