import R6.PaperRademacherBlockRowSandwich
import R6.PaperRademacherNoncrossingContribution

/-! # Sharp bounds for genuine Catalan matching contributions

This file connects the recursive open-word estimate to the genuine
alternating coefficient-cycle contribution wherever the finite-index
reindexing has been established.  The entire adjacent (row-canonical)
Catalan class is connected unconditionally.  For an arbitrary Catalan tree,
the one remaining statement is exposed as the exact trace bridge rather than
being hidden inside an analytic assumption.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The adjacent Catalan matching `(0,1),(2,3),...`. -/
def rademacherAdjacentCatalan :
    (n : ℕ) → RademacherNoncrossingMatching n
  | 0 => .empty
  | n + 1 =>
      (congrArg (fun z : ℕ => z + 1) (Nat.zero_add n)) ▸
        RademacherNoncrossingMatching.node .empty
          (rademacherAdjacentCatalan n)

/-- The recursive pair list of the adjacent Catalan tree consists exactly
of adjacent even/odd positions. -/
theorem mem_pairList_rademacherAdjacentCatalan_iff
    {n i j : ℕ} :
    (i, j) ∈ (rademacherAdjacentCatalan n).pairList ↔
      ∃ t : ℕ, t < n ∧ i = t * 2 ∧ j = t * 2 + 1 := by
  induction n generalizing i j with
  | zero => simp [rademacherAdjacentCatalan,
      RademacherNoncrossingMatching.pairList]
  | succ n ih =>
      have hpair : (rademacherAdjacentCatalan (n + 1)).pairList =
          (0, 1) :: (rademacherAdjacentCatalan n).pairList.map
            (fun z => (z.1 + 2, z.2 + 2)) := by
        simp [rademacherAdjacentCatalan,
          RademacherNoncrossingMatching.pairList_cast,
          RademacherNoncrossingMatching.pairList]
      rw [hpair]
      simp only [List.mem_cons, List.mem_map]
      constructor
      · intro h
        rcases h with hroot | htail
        · injection hroot with hi hj
          subst i
          subst j
          exact ⟨0, by omega, by omega, by omega⟩
        · obtain ⟨⟨i', j'⟩, hp, hij⟩ := htail
          injection hij with hi hj
          subst i
          subst j
          obtain ⟨t, ht, rfl, rfl⟩ := ih.mp hp
          exact ⟨t + 1, by omega, by omega, by omega⟩
      · rintro ⟨t, ht, rfl, rfl⟩
        by_cases hzero : t = 0
        · subst t
          exact Or.inl rfl
        · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
          apply Or.inr
          refine ⟨(u * 2, u * 2 + 1), ih.mpr ?_, ?_⟩
          · exact ⟨u, Nat.lt_of_succ_lt_succ ht, rfl, rfl⟩
          · apply Prod.ext <;> dsimp <;> omega

/-- Compatibility for the adjacent Catalan tree is exactly diagonal choice
at every Gram-cycle position. -/
theorem rademacherNoncrossingCompatible_adjacent_iff
    {ε : Type} {n : ℕ} (choice : Fin n → ε × ε) :
    RademacherNoncrossingCompatible (rademacherAdjacentCatalan n) choice ↔
      ∀ t : Fin n, (choice t).1 = (choice t).2 := by
  constructor
  · intro h t
    have hp : (t.1 * 2, t.1 * 2 + 1) ∈
        (rademacherAdjacentCatalan n).pairList :=
      mem_pairList_rademacherAdjacentCatalan_iff.mpr
        ⟨t.1, t.2, by omega, by omega⟩
    have heq := h (t.1 * 2) (t.1 * 2 + 1) hp
    simpa only [rademacherNatEdgeLabel_even,
      rademacherNatEdgeLabel_odd] using heq
  · intro h i j hp
    obtain ⟨t, ht, rfl, rfl⟩ :=
      mem_pairList_rademacherAdjacentCatalan_iff.mp hp
    let tf : Fin n := ⟨t, ht⟩
    have heven := rademacherNatEdgeLabel_even choice tf
    have hodd := rademacherNatEdgeLabel_odd choice tf
    simpa only [tf] using heven.trans ((h tf).trans hodd.symm)

/-- The genuine contribution selected by the adjacent Catalan tree is the
previously normalized canonical perfect-matching contribution. -/
theorem rademacherNoncrossingMatchingContribution_adjacent_eq_canonical
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {n : ℕ} (A : ε → Matrix ι κ ℝ) :
    rademacherNoncrossingMatchingContribution A
        (rademacherAdjacentCatalan n) =
      rademacherCanonicalMatchingContribution (r := n) A := by
  classical
  unfold rademacherNoncrossingMatchingContribution
  unfold rademacherCanonicalMatchingContribution
  apply Finset.sum_congr rfl
  intro rows hrows
  apply Finset.sum_congr rfl
  intro cols hcols
  apply Finset.sum_congr rfl
  intro choice hchoice
  simp only [rademacherNoncrossingCompatible_adjacent_iff]

@[simp]
theorem rademacherRowOpenWord_cast
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n m : ℕ} (h : n = m)
    (M : RademacherNoncrossingMatching n) :
    rademacherRowOpenWord A (h ▸ M) = rademacherRowOpenWord A M := by
  subst m
  rfl

/-- The row open word of the adjacent Catalan tree is the corresponding
power of the row variance. -/
theorem rademacherRowOpenWord_adjacent_eq_rowVariance_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ) :
    rademacherRowOpenWord A (rademacherAdjacentCatalan n) =
      rademacherRowVariance A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rademacherAdjacentCatalan, rademacherRowOpenWord_cast,
        rademacherRowOpenWord, rademacherColumnOpenWord,
        rademacherRowSandwich_one, ih]
      rw [pow_succ']

/-- For positive order, the genuine adjacent Catalan contribution is exactly
the trace of its recursive row open word. -/
theorem rademacherNoncrossingMatchingContribution_adjacent_eq_trace_openWord
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ) (hn : 0 < n) :
    rademacherNoncrossingMatchingContribution A
        (rademacherAdjacentCatalan n) =
      Matrix.trace (rademacherRowOpenWord A
        (rademacherAdjacentCatalan n)) := by
  rw [rademacherNoncrossingMatchingContribution_adjacent_eq_canonical,
    rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow A n hn,
    rademacherRowOpenWord_adjacent_eq_rowVariance_pow]

/-- The exact finite reindexing statement still required for a general
Catalan tree.  It mentions the genuine cycle sum on the left and the typed
recursive matrix word on the right. -/
def RademacherCatalanContributionTraceBridge
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {n : ℕ} (A : ε → Matrix ι κ ℝ)
    (M : RademacherNoncrossingMatching n) : Prop :=
  rademacherNoncrossingMatchingContribution A M =
    Matrix.trace (rademacherRowOpenWord A M)

/-- Once the exact reindexing bridge is known, the sharp sandwich theorem
immediately bounds the genuine contribution by `dimension × variance^n`. -/
theorem abs_rademacherNoncrossingMatchingContribution_le_of_traceBridge
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n)
    (hbridge : RademacherCatalanContributionTraceBridge A M) :
    |rademacherNoncrossingMatchingContribution A M| ≤
      (Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ n := by
  rw [hbridge]
  exact (abs_matrix_trace_le_card_mul_l2_opNorm
    (rademacherRowOpenWord A M)).trans
      (mul_le_mul_of_nonneg_left
        (rademacherOpenWords_norm_le_varianceNormMax_pow A M).1
        (Nat.cast_nonneg _))

/-- The sharp genuine bound is unconditional for the full adjacent Catalan
class. -/
theorem abs_rademacherNoncrossingMatchingContribution_adjacent_le
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ) (hn : 0 < n) :
    |rademacherNoncrossingMatchingContribution A
        (rademacherAdjacentCatalan n)| ≤
      (Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ n := by
  apply abs_rademacherNoncrossingMatchingContribution_le_of_traceBridge
  exact rademacherNoncrossingMatchingContribution_adjacent_eq_trace_openWord
    A n hn

#print axioms mem_pairList_rademacherAdjacentCatalan_iff
#print axioms rademacherNoncrossingCompatible_adjacent_iff
#print axioms
  rademacherNoncrossingMatchingContribution_adjacent_eq_trace_openWord
#print axioms
  abs_rademacherNoncrossingMatchingContribution_le_of_traceBridge
#print axioms
  abs_rademacherNoncrossingMatchingContribution_adjacent_le

end GraphMatrixReplica
