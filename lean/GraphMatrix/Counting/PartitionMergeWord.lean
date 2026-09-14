import GraphMatrix.Counting.MatchingDistanceFaithful

/-! # Arbitrary partition merges for one replica role

This proves a one-role partition-coarsening word. It does not identify that
word with the paper's ordered `3rD` encoding or establish a global `hCount`.
-/

noncomputable section

namespace GraphMatrixReplica

private def collapseKey {α : Type*} [DecidableEq α]
    (a b x : α) : α := if x = b then a else x

private theorem collapseKey_eq_iff {α : Type*} [DecidableEq α]
    (a b x y : α) :
    collapseKey a b x = collapseKey a b y ↔
      x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  by_cases hxb : x = b
  · subst x
    by_cases hyb : y = b
    · subst y
      simp [collapseKey]
    · have hby : b ≠ y := Ne.symm hyb
      simp [collapseKey, hyb, hby]
      exact eq_comm
  · by_cases hyb : y = b
    · subst y
      have hbx : b ≠ x := Ne.symm hxb
      simp [collapseKey, hxb]
    · simp [collapseKey, hxb, hyb]

/-- Collapse the old block of `b` onto the old block of `a`. -/
def c079MergeKey {m : ℕ} (π : ReplicaPartition m)
    (a b x : Replica m) : Quotient π :=
  by classical exact
    collapseKey (Quotient.mk'' a) (Quotient.mk'' b) (Quotient.mk'' x)

/-- A single merge, with an intrinsic result partition. -/
abbrev c079MergePoints {m : ℕ} (π : ReplicaPartition m)
    (a b : Replica m) : ReplicaPartition m :=
  equalityPartition (c079MergeKey π a b)

/-- Exact relation decoded from one merge: the old relation plus cross
relations between the two selected old blocks. -/
theorem mergePoints_rel_iff {m : ℕ} (π : ReplicaPartition m)
    (a b x y : Replica m) :
    (c079MergePoints π a b).r x y ↔
      π.r x y ∨ (π.r x a ∧ π.r y b) ∨ (π.r x b ∧ π.r y a) := by
  classical
  change c079MergeKey π a b x = c079MergeKey π a b y ↔ _
  unfold c079MergeKey
  rw [collapseKey_eq_iff]
  simp only [Quotient.eq]

/-- A genuine merge removes exactly one block. -/
theorem mergePoints_blockCount {m : ℕ} (π : ReplicaPartition m)
    (a b : Replica m) (hab : ¬ π.r a b) :
    partitionBlockCount (c079MergePoints π a b) + 1 =
      partitionBlockCount π := by
  classical
  let qa : Quotient π := Quotient.mk'' a
  let qb : Quotient π := Quotient.mk'' b
  let f : Replica m → Quotient π := c079MergeKey π a b
  have hqa : qa ≠ qb := by
    intro h
    exact hab (Quotient.exact h)
  have hrange : Set.range f = {q | q ≠ qb} := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      change collapseKey qa qb (Quotient.mk'' x) ≠ qb
      by_cases hx : (Quotient.mk'' x : Quotient π) = qb
      · simp [collapseKey, hx, hqa]
      · simp [collapseKey, hx]
    · intro hq
      obtain ⟨x, rfl⟩ := Quotient.mk''_surjective q
      refine ⟨x, ?_⟩
      change (Quotient.mk'' x : Quotient π) ≠ qb at hq
      change collapseKey qa qb (Quotient.mk'' x) = Quotient.mk'' x
      simp [collapseKey, hq]
  have hker : c079MergePoints π a b = Setoid.ker f := by
    apply Setoid.ext
    intro x y
    rfl
  have hcard : Fintype.card (Set.range f) + 1 = Fintype.card (Quotient π) := by
    calc
      Fintype.card (Set.range f) + 1 =
          Fintype.card {q : Quotient π // q ≠ qb} + 1 := by
            rw [Fintype.card_congr (Equiv.setCongr hrange)]
            rfl
      _ = Fintype.card (Quotient π) := by
        simp [Fintype.card_subtype_compl]
        have hpos : 0 < Fintype.card (Quotient π) :=
          Fintype.card_pos_iff.mpr ⟨qb⟩
        omega
  change Fintype.card (Quotient (c079MergePoints π a b)) + 1 =
    Fintype.card (Quotient π)
  rw [hker]
  rw [Fintype.card_congr (Setoid.quotientKerEquivRange f)]
  exact hcard


/-- The old equivalences survive the merge. -/
theorem mergePoints_coarsens {m : ℕ} (π : ReplicaPartition m)
    (a b : Replica m) :
    PartitionCoarsens (c079MergePoints π a b) π := by
  intro x y hxy
  exact (mergePoints_rel_iff π a b x y).2 (Or.inl hxy)

/-- This is the least coarsening that identifies the selected two blocks. -/
theorem mergePoints_least {m : ℕ} (π τ : ReplicaPartition m)
    (a b : Replica m) (hτ : PartitionCoarsens τ π)
    (hab : τ.r a b) :
    PartitionCoarsens τ (c079MergePoints π a b) := by
  intro x y hxy
  rcases (mergePoints_rel_iff π a b x y).1 hxy with h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · exact hτ x y h
  · exact τ.iseqv.trans (τ.iseqv.trans (hτ x a hxa) hab)
      (τ.iseqv.symm (hτ y b hyb))
  · exact τ.iseqv.trans (τ.iseqv.trans (hτ x b hxb) (τ.iseqv.symm hab))
      (τ.iseqv.symm (hτ y a hya))

/-- Outside the two selected old blocks, a merge creates no new relations. -/
theorem mergePoints_unchanged_outside {m : ℕ} (π : ReplicaPartition m)
    (a b x y : Replica m) (hxa : ¬ π.r x a) (hxb : ¬ π.r x b) :
    (c079MergePoints π a b).r x y ↔ π.r x y := by
  constructor
  · intro h
    rcases (mergePoints_rel_iff π a b x y).1 h with h | h | h
    · exact h
    · exact False.elim (hxa h.1)
    · exact False.elim (hxb h.1)
  · intro h
    exact (mergePoints_rel_iff π a b x y).2 (Or.inl h)

/-- Decode a word of merges from its starting partition. -/
@[instance_reducible] def c079DecodeMergeWord {m : ℕ} (σ : ReplicaPartition m) :
    List (Replica m × Replica m) → ReplicaPartition m
  | [] => σ
  | (a, b) :: word => c079DecodeMergeWord (c079MergePoints σ a b) word

/-- A coarsening of a finite replica partition is obtained by a word of
genuine two-block merges.  The length is bounded by the exact block gap. -/
theorem exists_c079MergeWord {m : ℕ} (π σ : ReplicaPartition m)
    (hπσ : PartitionCoarsens π σ) :
    ∃ word : List (Replica m × Replica m),
      c079DecodeMergeWord σ word = π ∧
        word.length ≤ partitionBlockCount σ - partitionBlockCount π := by
  have haux : ∀ n : ℕ, ∀ τ : ReplicaPartition m,
      partitionBlockCount τ = n → PartitionCoarsens π τ →
      ∃ word : List (Replica m × Replica m),
        c079DecodeMergeWord τ word = π ∧
          word.length ≤ n - partitionBlockCount π := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro τ hn hπτ
      by_cases heq : τ = π
      · refine ⟨[], ?_, ?_⟩
        · simp [c079DecodeMergeWord, heq]
        · simp
      · have hdiff : ∃ a b : Replica m, π.r a b ∧ ¬ τ.r a b := by
          by_contra h
          have hreverse : PartitionCoarsens τ π := by
            intro a b hab
            by_contra hnab
            exact h ⟨a, b, hab, hnab⟩
          apply heq
          apply Setoid.ext
          intro a b
          exact ⟨hπτ a b, hreverse a b⟩
        obtain ⟨a, b, habπ, habτ⟩ := hdiff
        let μ := c079MergePoints τ a b
        have hμ : partitionBlockCount μ + 1 = n := by
          simpa only [μ, hn] using mergePoints_blockCount τ a b habτ
        have hlt : partitionBlockCount μ < n := by omega
        have hπμ : PartitionCoarsens π μ :=
          mergePoints_least τ π a b hπτ habπ
        obtain ⟨word, hdecode, hlength⟩ :=
          ih (partitionBlockCount μ) hlt μ rfl hπμ
        have hπle : partitionBlockCount π ≤ partitionBlockCount μ := by
          rw [← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) π,
            ← finrank_partitionConstantSubspace_eq_blockCount (K := ℚ) μ]
          exact Submodule.finrank_mono (partitionConstantSubspace_mono hπμ)
        refine ⟨(a, b) :: word, ?_, ?_⟩
        · exact hdecode
        · simp only [List.length_cons]
          omega
  exact haux (partitionBlockCount σ) σ rfl hπσ


end GraphMatrixReplica
