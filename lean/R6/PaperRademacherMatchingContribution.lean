import R6.PaperRademacherEvenWordPairing

/-! # Contributions associated with edge-word matchings

This file begins the matrix-algebra layer after the even-word matching cover.
It first isolates the canonical matching, which pairs the two edge choices at
each Gram-cycle position.  Its full coefficient contribution is exactly a
trace power of the row-variance matrix.  No estimate for arbitrary crossing
matchings, and no noncommutative Khintchine inequality, is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The canonical encoding pairs the two adjacent positions contributed by
each Gram-cycle location. -/
def rademacherCanonicalMatching (r : ℕ) :
    Fin r × Bool ≃ Fin (r * 2) :=
  ((Equiv.refl (Fin r)).prodCongr finTwoEquiv.symm).trans finProdFinEquiv

@[simp] theorem rademacherCanonicalMatching_false
    {r : ℕ} (t : Fin r) :
    rademacherCanonicalMatching r (t, false) =
      ⟨t.1 * 2, by omega⟩ := by
  apply Fin.ext
  simp [rademacherCanonicalMatching, finProdFinEquiv, finTwoEquiv]
  omega

@[simp] theorem rademacherCanonicalMatching_true
    {r : ℕ} (t : Fin r) :
    rademacherCanonicalMatching r (t, true) =
      ⟨t.1 * 2 + 1, by omega⟩ := by
  apply Fin.ext
  simp [rademacherCanonicalMatching, finProdFinEquiv, finTwoEquiv]
  omega

/-- Normalize an arbitrary matching encoding relative to the canonical one.
The result is a permutation of the `2r` word positions. -/
def rademacherMatchingPositionPermutation {r : ℕ}
    (matching : Fin r × Bool ≃ Fin (r * 2)) :
    Equiv.Perm (Fin (r * 2)) :=
  (rademacherCanonicalMatching r).symm.trans matching

/-- Every matching encoding is the canonical encoding followed by its unique
normalizing position permutation. -/
@[simp] theorem rademacherMatchingPositionPermutation_apply_canonical
    {r : ℕ} (matching : Fin r × Bool ≃ Fin (r * 2))
    (position : Fin r × Bool) :
    rademacherMatchingPositionPermutation matching
        (rademacherCanonicalMatching r position) =
      matching position := by
  simp [rademacherMatchingPositionPermutation]

/-- Conversely, a position permutation recovers the corresponding matching
encoding by postcomposition with the canonical matching. -/
theorem rademacherMatching_eq_positionPermutation_trans_canonical
    {r : ℕ} (matching : Fin r × Bool ≃ Fin (r * 2)) :
    matching = (rademacherCanonicalMatching r).trans
      (rademacherMatchingPositionPermutation matching) := by
  ext position
  simp

/-- Canonical-compatible choices are exactly diagonal choices.  This explicit
equivalence is the normalization used below. -/
def canonicalRademacherChoiceEquiv
    {ε : Type} {r : ℕ} :
    (Fin r → ε) ≃
      {choice : Fin r → ε × ε // ∀ t, (choice t).1 = (choice t).2} where
  toFun edges := ⟨fun t => (edges t, edges t), fun _ => rfl⟩
  invFun choice t := (choice.1 t).1
  left_inv _ := rfl
  right_inv choice := by
    apply Subtype.ext
    funext t
    apply Prod.ext
    · rfl
    · exact choice.property t

/-- Summing a function over a pair constrained to the diagonal is the same
as summing over its single free edge label. -/
theorem sum_edgePairs_if_eq
    {ε : Type} [Fintype ε] [DecidableEq ε]
    (F : ε → ε → ℝ) :
    (∑ z : ε × ε, if z.1 = z.2 then F z.1 z.2 else 0) =
      ∑ e : ε, F e e := by
  rw [Fintype.sum_prod_type]
  simp

/-- Product-factorization form of canonical-choice normalization. -/
theorem sum_canonicalChoices_eq_prod_diagonal
    {ε : Type} [Fintype ε] [DecidableEq ε] {r : ℕ}
    (term : Fin r → ε → ε → ℝ) :
    (∑ choice : Fin r → ε × ε,
      if ∀ t, (choice t).1 = (choice t).2 then
        ∏ t, term t (choice t).1 (choice t).2 else 0) =
      ∏ t : Fin r, ∑ e : ε, term t e e := by
  classical
  calc
    _ = ∑ choice : Fin r → ε × ε,
          ∏ t : Fin r,
            if (choice t).1 = (choice t).2 then
              term t (choice t).1 (choice t).2 else 0 := by
      apply Finset.sum_congr rfl
      intro choice _
      by_cases h : ∀ t, (choice t).1 = (choice t).2
      · simp [h]
      · simp only [if_neg h]
        push Not at h
        obtain ⟨t, ht⟩ := h
        symm
        apply (Finset.prod_eq_zero (Finset.mem_univ t))
        simp [ht]
    _ = ∏ t : Fin r, ∑ z : ε × ε,
          if z.1 = z.2 then term t z.1 z.2 else 0 := by
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro t _
      exact sum_edgePairs_if_eq (term t)

/-- The row-side variance matrix associated with the coefficient family. -/
def rademacherRowVariance
    {ε ι κ : Type} [Fintype ε] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  ∑ e : ε, A e * (A e).transpose

/-- The row-variance matrix is positive semidefinite. -/
theorem rademacherRowVariance_posSemidef
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) :
    (rademacherRowVariance A).PosSemidef := by
  classical
  unfold rademacherRowVariance
  apply Matrix.posSemidef_sum
  intro e _
  simpa using Matrix.posSemidef_self_mul_conjTranspose (A e)

/-- The full coefficient-cycle contribution covered by the canonical
adjacent-position matching. -/
def rademacherCanonicalMatchingContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) : ℝ :=
  ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
    ∑ choice : Fin r → ε × ε,
      if ∀ t, (choice t).1 = (choice t).2 then
        rademacherGramCycleCoefficient A rows cols choice else 0

/-- Canonical compatibility eliminates one of the two edge labels at every
cycle position. -/
theorem rademacherCanonicalMatchingContribution_eq_diagonalEdges
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) :
    rademacherCanonicalMatchingContribution (r := r) A =
      ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
        ∏ t : Fin r, ∑ e : ε,
          A e (rows t) (cols t) *
            A e (rows (finRotate r t)) (cols t) := by
  classical
  unfold rademacherCanonicalMatchingContribution
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro cols _
  simpa only [rademacherGramCycleCoefficient] using
    (sum_canonicalChoices_eq_prod_diagonal
      (fun t e₁ e₂ =>
        A e₁ (rows t) (cols t) *
          A e₂ (rows (finRotate r t)) (cols t)))

/-- After summing the column-cycle coordinates, the canonical contribution
is the ordinary cycle expansion of the row-variance matrix. -/
theorem rademacherCanonicalMatchingContribution_eq_rowVarianceCycles
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) :
    rademacherCanonicalMatchingContribution (r := r) A =
      ∑ rows : Fin r → ι,
        ∏ t : Fin r,
          rademacherRowVariance A (rows t) (rows (finRotate r t)) := by
  classical
  rw [rademacherCanonicalMatchingContribution_eq_diagonalEdges]
  apply Finset.sum_congr rfl
  intro rows _
  calc
    (∑ cols : Fin r → κ,
        ∏ t : Fin r, ∑ e : ε,
          A e (rows t) (cols t) *
            A e (rows (finRotate r t)) (cols t)) =
        ∏ t : Fin r, ∑ col : κ, ∑ e : ε,
          A e (rows t) col *
            A e (rows (finRotate r t)) col := by
      rw [Fintype.prod_sum]
    _ = ∏ t : Fin r,
          rademacherRowVariance A (rows t) (rows (finRotate r t)) := by
      apply Finset.prod_congr rfl
      intro t _
      simp only [rademacherRowVariance, Matrix.sum_apply, Matrix.mul_apply,
        Matrix.transpose_apply]
      rw [Finset.sum_comm]

/-- The canonical perfect-matching contribution is exactly the trace power
of the row-variance matrix. -/
theorem rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    rademacherCanonicalMatchingContribution (r := r) A =
      Matrix.trace ((rademacherRowVariance A) ^ r) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [rademacherCanonicalMatchingContribution_eq_rowVarianceCycles]
  exact (matrix_trace_pow_succ_eq_sum_cycleProducts
    (rademacherRowVariance A) q).symm

/-- In particular, every dyadic canonical contribution is nonnegative. -/
theorem rademacherCanonicalMatchingContribution_dyadic_nonneg
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (q : ℕ) :
    0 ≤ rademacherCanonicalMatchingContribution (r := 2 ^ q) A := by
  rw [rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow
    A (2 ^ q) (by positivity)]
  exact (matrix_posSemidef_pow_two_pow
    (rademacherRowVariance A) (rademacherRowVariance_posSemidef A) q).trace_nonneg

#print axioms sum_canonicalChoices_eq_prod_diagonal
#print axioms rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow
#print axioms rademacherCanonicalMatchingContribution_dyadic_nonneg

end GraphMatrixReplica
