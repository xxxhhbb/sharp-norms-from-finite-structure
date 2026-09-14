import R6.U3RecordSemantics

/-!
U3: a block-loss budget for EVERY forward code, not just encoder outputs.
This is needed because actual_fiber_card_le quantifies over all forward codes.
This module has not been executed in Lean in the return environment.
-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U3
open C079U2

open Classical in
attribute [local instance] propDecidable

variable {G : PartiteShape} {p s : ℕ}

theorem mergePoints_eq_self_of_rel {m : ℕ} (π : ReplicaPartition m)
    (a b : Replica m) (hab : π.r a b) : c079MergePoints π a b = π := by
  apply Setoid.ext
  intro x y
  rw [mergePoints_rel_iff]
  constructor
  · rintro (h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · exact h
    · exact π.iseqv.trans hxa (π.iseqv.trans hab (π.iseqv.symm hyb))
    · exact π.iseqv.trans hxb (π.iseqv.trans (π.iseqv.symm hab) (π.iseqv.symm hya))
  · exact Or.inl

theorem mergePoints_loss_le_one {m : ℕ} (π : ReplicaPartition m)
    (a b : Replica m) :
    partitionBlockCount π ≤ partitionBlockCount (c079MergePoints π a b) + 1 := by
  by_cases hab : π.r a b
  · rw [mergePoints_eq_self_of_rel π a b hab]
    omega
  · exact (mergePoints_blockCount π a b hab).symm.le

theorem mergeBlock_loss_le_one {m : ℕ} (π : ReplicaPartition m)
    (ij : Fin m × Fin m) :
    partitionBlockCount π ≤ partitionBlockCount (mergeBlock π ij) + 1 := by
  unfold mergeBlock
  split <;> try omega
  exact mergePoints_loss_le_one π _ _

theorem decodeBlockWord_coarsens {m : ℕ} (π : ReplicaPartition m)
    (word : List (Fin m × Fin m)) :
    PartitionCoarsens (decodeBlockWord π word) π := by
  induction word generalizing π with
  | nil => exact fun _ _ h => h
  | cons ij rest ih =>
      intro a b hab
      exact ih (mergeBlock π ij) a b (mergeBlock_coarsens π ij a b hab)

theorem decodeBlockWord_count_balance {m : ℕ} (π : ReplicaPartition m)
    (word : List (Fin m × Fin m)) :
    partitionBlockCount π ≤
      partitionBlockCount (decodeBlockWord π word) + word.length := by
  induction word generalizing π with
  | nil => simp [decodeBlockWord]
  | cons ij rest ih =>
      have hOne := mergeBlock_loss_le_one π ij
      have hRest := ih (mergeBlock π ij)
      simp only [decodeBlockWord, List.length_cons]
      omega

theorem decodeBlockWord_loss_le_length {m : ℕ} (π : ReplicaPartition m)
    (word : List (Fin m × Fin m)) :
    partitionBlockCount π - partitionBlockCount (decodeBlockWord π word) ≤ word.length := by
  have h := decodeBlockWord_count_balance π word
  omega

/-- Each non-null tagged letter is charged to exactly one role. -/
theorem sum_roleWord_lengths_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (word : List (ForwardLetter ι m)) :
    (∑ x : ι, (roleWord x word).length) ≤ word.length := by
  induction word with
  | nil => simp [roleWord]
  | cons letter rest ih =>
      cases letter with
      | none =>
          change (∑ x : ι, (roleWord x rest).length) ≤ rest.length + 1
          exact ih.trans (Nat.le_succ rest.length)
      | some yij =>
          rcases yij with ⟨y, ij⟩
          have hEach (x : ι) :
              (roleWord x (some (y, ij) :: rest)).length =
                (if x = y then 1 else 0) + (roleWord x rest).length := by
            by_cases hxy : x = y <;> simp [roleWord, extractLetter, hxy, Nat.add_comm]
          simp only [hEach, Finset.sum_add_distrib, List.length_cons]
          have hOne : (∑ x : ι, if x = y then (1 : ℕ) else 0) = 1 := by simp
          rw [hOne]
          omega

/-- No assumption says that the code came from exists_forward_code. -/
theorem decodeForward_total_loss_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m b : ℕ}
    (original : ι → ReplicaPartition m) (code : ForwardCode ι m b) :
    (∑ x : ι, (partitionBlockCount (original x) -
      partitionBlockCount (decodeForward original code x))) ≤ b := by
  calc
    _ ≤ ∑ x : ι, (roleWord x (List.ofFn code)).length :=
      Finset.sum_le_sum (fun x _ => decodeBlockWord_loss_le_length
        (original x) (roleWord x (List.ofFn code)))
    _ ≤ (List.ofFn code).length := sum_roleWord_lengths_le _
    _ = b := by simp

def forwardLoss
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) : ℕ :=
  family.backboneRoles.sum fun x =>
    partitionBlockCount (originalPrefix B.1 x) -
      partitionBlockCount (repairedAt B forward x)

theorem forwardLoss_le
    {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) :
    forwardLoss B forward ≤ 3 * G.roles * offDefect family d := by
  unfold forwardLoss repairedAt
  calc
    _ ≤ ∑ x : Fin G.roles,
        (partitionBlockCount (originalPrefix B.1 x) -
          partitionBlockCount (decodeForward (originalPrefix B.1) forward x)) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ _ := decodeForward_total_loss_le _ _

#print axioms decodeBlockWord_coarsens
#print axioms decodeForward_total_loss_le
#print axioms forwardLoss_le
end GraphMatrixReplica.C079U3
