import R6.PaperRademacherMatrixFourthMoment
import R6.PaperTraceCycleIdentity

/-! # Arbitrary dyadic Rademacher matrix moments

This file provides the exact finite expansion underlying every dyadic Gram
trace moment of a Rademacher matrix sum.  It proves no NCK inequality: after
the norm-to-trace step, all identities are finite distributive expansions and
the standard even-multiplicity Rademacher rule.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The unconditional dyadic norm-to-Gram-trace bound after uniform averaging
over all independent `Bool` signs. -/
theorem paperMean_rademacherMatrix_l2_opNorm_dyadic_le_gramTrace
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (q : ℕ) :
    paperMean (fun w : ε → Bool =>
      ‖paperRademacherMatrixSum A w‖ ^ (2 * 2 ^ q)) ≤
      paperMean (fun w : ε → Bool =>
        Matrix.trace ((paperRademacherMatrixSum A w *
          (paperRademacherMatrixSum A w).transpose) ^ (2 ^ q))) := by
  apply paperMean_mono
  intro w
  exact matrix_l2_opNorm_pow_dyadic_le_gramTrace
    (paperRademacherMatrixSum A w) q

/-- Row/column cycle expansion of a positive Gram power for an arbitrary
finite real matrix. -/
theorem matrix_gramTrace_pow_eq_sum_rowColCycles
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (X : Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    Matrix.trace ((X * X.transpose) ^ r) =
      ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
        ∏ t : Fin r,
          X (rows t) (cols t) *
            X (rows (finRotate r t)) (cols t) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  calc
    Matrix.trace ((X * X.transpose) ^ (q + 1)) =
        ∑ rows : Fin (q + 1) → ι,
          ∏ t : Fin (q + 1),
            ∑ col : κ,
              X (rows t) col * X (rows (finRotate (q + 1) t)) col := by
      simpa only [Matrix.mul_apply, Matrix.transpose_apply] using
        (matrix_trace_pow_succ_eq_sum_cycleProducts
          (X * X.transpose) q)
    _ = ∑ rows : Fin (q + 1) → ι, ∑ cols : Fin (q + 1) → κ,
          ∏ t : Fin (q + 1),
            X (rows t) (cols t) *
              X (rows (finRotate (q + 1) t)) (cols t) := by
      apply Finset.sum_congr rfl
      intro rows _
      rw [Fintype.prod_sum]

/-- The length-`2r` edge word associated with choosing two coefficient
matrices at every Gram-cycle position. -/
def rademacherPairEdgeWord
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) : List ε :=
  (List.ofFn choice).flatMap fun z => [z.1, z.2]

/-- The product of signs along the paired edge word is the product of the two
chosen signs at each cycle position. -/
theorem rademacherPairEdgeWord_signProduct
    {ε : Type} [Fintype ε] {r : ℕ}
    (choice : Fin r → ε × ε) (w : ε → Bool) :
    ((rademacherPairEdgeWord choice).map
      (fun e => paperSign (w e))).prod =
      ∏ t : Fin r,
        paperSign (w (choice t).1) * paperSign (w (choice t).2) := by
  classical
  induction r with
  | zero => simp [rademacherPairEdgeWord]
  | succ r ih =>
      rw [Fin.prod_univ_succ]
      simp only [rademacherPairEdgeWord, List.ofFn_succ, List.flatMap_cons,
        List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      have hTail := ih (fun i => choice i.succ)
      unfold rademacherPairEdgeWord at hTail
      rw [hTail]

/-- Rademacher parity for an arbitrary paired Gram-cycle edge word. -/
theorem paperMean_rademacherPairEdgeWord_mul_const
    {ε : Type} [Fintype ε] [DecidableEq ε] {r : ℕ}
    (choice : Fin r → ε × ε) (c : ℝ) :
    paperMean (fun w : ε → Bool =>
      ((rademacherPairEdgeWord choice).map
        (fun e => paperSign (w e))).prod * c) =
      if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then c else 0 := by
  calc
    paperMean (fun w : ε → Bool =>
        ((rademacherPairEdgeWord choice).map
          (fun e => paperSign (w e))).prod * c) =
        c * paperMean (fun w : ε → Bool =>
          ((rademacherPairEdgeWord choice).map
            (fun e => paperSign (w e))).prod) := by
      simpa only [mul_comm] using
        (paperMean_const_mul c (fun w : ε → Bool =>
          ((rademacherPairEdgeWord choice).map
            (fun e => paperSign (w e))).prod))
    _ = if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
          c else 0 := by
      rw [paperMean_sign_word]
      split_ifs <;> simp

/-- The deterministic coefficient attached to a row/column cycle and a
choice of two coefficient matrices at each cycle position. -/
def rademacherGramCycleCoefficient
    {ε ι κ : Type} {r : ℕ}
    (A : ε → Matrix ι κ ℝ) (rows : Fin r → ι) (cols : Fin r → κ)
    (choice : Fin r → ε × ε) : ℝ :=
  ∏ t : Fin r,
    A (choice t).1 (rows t) (cols t) *
      A (choice t).2 (rows (finRotate r t)) (cols t)

/-- Pointwise finite edge-word expansion of a positive Gram trace power. -/
theorem rademacherMatrix_gramTrace_pow_eq_sum_edgeWords
    {ε ι κ : Type} [Fintype ε]
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (w : ε → Bool)
    (r : ℕ) (hr : 0 < r) :
    Matrix.trace ((paperRademacherMatrixSum A w *
      (paperRademacherMatrixSum A w).transpose) ^ r) =
      ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
        ∑ choice : Fin r → ε × ε,
          ((rademacherPairEdgeWord choice).map
            (fun e => paperSign (w e))).prod *
              rademacherGramCycleCoefficient A rows cols choice := by
  rw [matrix_gramTrace_pow_eq_sum_rowColCycles _ r hr]
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro cols _
  calc
    (∏ t : Fin r,
        paperRademacherMatrixSum A w (rows t) (cols t) *
          paperRademacherMatrixSum A w
            (rows (finRotate r t)) (cols t)) =
        ∏ t : Fin r, ∑ z : ε × ε,
          (paperSign (w z.1) * A z.1 (rows t) (cols t)) *
            (paperSign (w z.2) *
              A z.2 (rows (finRotate r t)) (cols t)) := by
      apply Finset.prod_congr rfl
      intro t _
      rw [Fintype.sum_prod_type]
      simpa only [paperRademacherMatrixSum] using
        (Fintype.sum_mul_sum
          (fun e : ε => paperSign (w e) * A e (rows t) (cols t))
          (fun e : ε => paperSign (w e) *
            A e (rows (finRotate r t)) (cols t)))
    _ = ∑ choice : Fin r → ε × ε, ∏ t : Fin r,
          (paperSign (w (choice t).1) *
            A (choice t).1 (rows t) (cols t)) *
          (paperSign (w (choice t).2) *
            A (choice t).2 (rows (finRotate r t)) (cols t)) := by
      rw [Fintype.prod_sum]
    _ = ∑ choice : Fin r → ε × ε,
          ((rademacherPairEdgeWord choice).map
            (fun e => paperSign (w e))).prod *
              rademacherGramCycleCoefficient A rows cols choice := by
      apply Finset.sum_congr rfl
      intro choice _
      rw [rademacherPairEdgeWord_signProduct]
      unfold rademacherGramCycleCoefficient
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro t _
      ring

/-- Uniform averaging deletes precisely the edge words having an odd
multiplicity. -/
theorem paperMean_rademacherMatrix_gramTrace_pow_eq_evenEdgeWords
    {ε ι κ : Type} [Fintype ε] [DecidableEq ε]
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    paperMean (fun w : ε → Bool =>
      Matrix.trace ((paperRademacherMatrixSum A w *
        (paperRademacherMatrixSum A w).transpose) ^ r)) =
      ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
        ∑ choice : Fin r → ε × ε,
          if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
            rademacherGramCycleCoefficient A rows cols choice else 0 := by
  simp_rw [rademacherMatrix_gramTrace_pow_eq_sum_edgeWords A _ r hr]
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro rows _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro cols _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro choice _
  exact paperMean_rademacherPairEdgeWord_mul_const choice _

/-- Dyadic specialization of the exact even-edge-word trace expansion. -/
theorem paperMean_rademacherMatrix_dyadicGramTrace_eq_evenEdgeWords
    {ε ι κ : Type} [Fintype ε] [DecidableEq ε]
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (q : ℕ) :
    paperMean (fun w : ε → Bool =>
      Matrix.trace ((paperRademacherMatrixSum A w *
        (paperRademacherMatrixSum A w).transpose) ^ (2 ^ q))) =
      ∑ rows : Fin (2 ^ q) → ι, ∑ cols : Fin (2 ^ q) → κ,
        ∑ choice : Fin (2 ^ q) → ε × ε,
          if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
            rademacherGramCycleCoefficient A rows cols choice else 0 := by
  exact paperMean_rademacherMatrix_gramTrace_pow_eq_evenEdgeWords
    A (2 ^ q) (by positivity)

/-- The general dyadic norm moment is bounded by the exact finite sum over
even edge words.  No NCK estimate of that sum is asserted. -/
theorem paperMean_rademacherMatrix_l2_opNorm_dyadic_le_evenEdgeWords
    {ε ι κ : Type} [Fintype ε] [DecidableEq ε]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (q : ℕ) :
    paperMean (fun w : ε → Bool =>
      ‖paperRademacherMatrixSum A w‖ ^ (2 * 2 ^ q)) ≤
      ∑ rows : Fin (2 ^ q) → ι, ∑ cols : Fin (2 ^ q) → κ,
        ∑ choice : Fin (2 ^ q) → ε × ε,
          if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
            rademacherGramCycleCoefficient A rows cols choice else 0 := by
  calc
    paperMean (fun w : ε → Bool =>
        ‖paperRademacherMatrixSum A w‖ ^ (2 * 2 ^ q)) ≤
        paperMean (fun w : ε → Bool =>
          Matrix.trace ((paperRademacherMatrixSum A w *
            (paperRademacherMatrixSum A w).transpose) ^ (2 ^ q))) :=
      paperMean_rademacherMatrix_l2_opNorm_dyadic_le_gramTrace A q
    _ = _ := paperMean_rademacherMatrix_dyadicGramTrace_eq_evenEdgeWords A q

#print axioms paperMean_rademacherMatrix_l2_opNorm_dyadic_le_gramTrace
#print axioms matrix_gramTrace_pow_eq_sum_rowColCycles
#print axioms rademacherPairEdgeWord_signProduct
#print axioms paperMean_rademacherPairEdgeWord_mul_const
#print axioms rademacherMatrix_gramTrace_pow_eq_sum_edgeWords
#print axioms paperMean_rademacherMatrix_gramTrace_pow_eq_evenEdgeWords
#print axioms paperMean_rademacherMatrix_dyadicGramTrace_eq_evenEdgeWords
#print axioms paperMean_rademacherMatrix_l2_opNorm_dyadic_le_evenEdgeWords

end GraphMatrixReplica
