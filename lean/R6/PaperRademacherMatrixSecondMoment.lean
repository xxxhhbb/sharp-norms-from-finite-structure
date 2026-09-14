import R6.PaperNCKEndpoint
import R6.PaperSparseFlatteningNorm

/-! # The matrix Rademacher second-moment identity

This file proves the `p = 2` orthogonality base case for a finite family of
real matrices with independent uniform `Bool` signs.  It is not an iterated
noncommutative Khintchine inequality: only the entrywise/Frobenius second
moment and the deterministic operator-norm-to-Frobenius comparison are used.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Two independent Rademacher coordinates are orthogonal in the finite
uniform mean. -/
theorem paperMean_paperSign_mul_paperSign
    {ε : Type} [Fintype ε] [DecidableEq ε] (e e' : ε) :
    paperMean (fun w : ε → Bool => paperSign (w e) * paperSign (w e')) =
      if e = e' then 1 else 0 := by
  by_cases he : e = e'
  · subst e'
    have hEven : ∀ i : ε, Even ([e, e].count i) := by
      intro i
      by_cases hi : i = e
      · subst i
        norm_num
      · have hei : e ≠ i := Ne.symm hi
        simp [hei]
    simpa [hEven] using (paperMean_sign_word (ι := ε) [e, e])
  · have hNotEven : ¬ ∀ i : ε, Even ([e, e'].count i) := by
      intro hAll
      have hAtE := hAll e
      simp [he] at hAtE
    simpa [he, hNotEven] using
      (paperMean_sign_word (ι := ε) [e, e'])

/-- Orthogonality with fixed scalar coefficients pulled outside the mean. -/
theorem paperMean_weighted_paperSign_pair
    {ε : Type} [Fintype ε] [DecidableEq ε]
    (a : ε → ℝ) (e e' : ε) :
    paperMean (fun w : ε → Bool =>
      (paperSign (w e) * a e) * (paperSign (w e') * a e')) =
      if e = e' then a e ^ 2 else 0 := by
  calc
    paperMean (fun w : ε → Bool =>
        (paperSign (w e) * a e) * (paperSign (w e') * a e')) =
        (a e * a e') * paperMean (fun w : ε → Bool =>
          paperSign (w e) * paperSign (w e')) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (paperMean_const_mul (a e * a e')
          (fun w : ε → Bool => paperSign (w e) * paperSign (w e')))
    _ = if e = e' then a e ^ 2 else 0 := by
      rw [paperMean_paperSign_mul_paperSign]
      split_ifs with he
      · subst e'
        rw [pow_two]
        ring
      · simp

/-- Scalar Rademacher second-moment orthogonality. -/
theorem paperMean_rademacher_sum_sq
    {ε : Type} [Fintype ε] [DecidableEq ε] (a : ε → ℝ) :
    paperMean (fun w : ε → Bool =>
      (∑ e, paperSign (w e) * a e) ^ 2) =
      ∑ e, a e ^ 2 := by
  have hExpand :
      (fun w : ε → Bool => (∑ e, paperSign (w e) * a e) ^ 2) =
        (fun w : ε → Bool =>
          ∑ e, ∑ e',
            (paperSign (w e) * a e) * (paperSign (w e') * a e')) := by
    funext w
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
  rw [hExpand, paperMean_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [paperMean_sum]
  simp_rw [paperMean_weighted_paperSign_pair a e]
  simp

/-- The entrywise Rademacher matrix sum. -/
def paperRademacherMatrixSum
    {ε ι κ : Type} [Fintype ε]
    (A : ε → Matrix ι κ ℝ) (w : ε → Bool) : Matrix ι κ ℝ :=
  fun i j => ∑ e, paperSign (w e) * A e i j

/-- Matrix-level Frobenius second-moment identity. -/
theorem paperMean_rademacherMatrix_sum_entry_sq
    {ε ι κ : Type} [Fintype ε] [DecidableEq ε]
    [Fintype ι] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) :
    paperMean (fun w : ε → Bool =>
      ∑ i, ∑ j, paperRademacherMatrixSum A w i j ^ 2) =
      ∑ e, ∑ i, ∑ j, A e i j ^ 2 := by
  rw [paperMean_sum]
  calc
    (∑ i, paperMean (fun w : ε → Bool =>
        ∑ j, paperRademacherMatrixSum A w i j ^ 2)) =
        ∑ i, ∑ j, paperMean (fun w : ε → Bool =>
          paperRademacherMatrixSum A w i j ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [paperMean_sum]
    _ = ∑ i, ∑ j, ∑ e, A e i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa [paperRademacherMatrixSum] using
        (paperMean_rademacher_sum_sq (fun e => A e i j))
    _ =
        ∑ i, ∑ e, ∑ j, A e i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ e, ∑ i, ∑ j, A e i j ^ 2 := by
      rw [Finset.sum_comm]

/-- The expected squared `L2` operator norm is at most the deterministic sum
of the squared Frobenius norms of the coefficient matrices.  This is exactly
the `p = 2` base case and contains no higher-moment NCK assertion. -/
theorem paperMean_rademacherMatrix_l2_opNorm_sq_le_sum_entry_sq
    {ε ι κ : Type} [Fintype ε] [DecidableEq ε]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    paperMean (fun w : ε → Bool => ‖paperRademacherMatrixSum A w‖ ^ 2) ≤
      ∑ e, ∑ i, ∑ j, A e i j ^ 2 := by
  calc
    paperMean (fun w : ε → Bool =>
        ‖paperRademacherMatrixSum A w‖ ^ 2) ≤
        paperMean (fun w : ε → Bool =>
          ∑ i, ∑ j, paperRademacherMatrixSum A w i j ^ 2) := by
      apply paperMean_mono
      intro w
      exact matrix_l2_opNorm_sq_le_sum_entry_sq
        (paperRademacherMatrixSum A w)
    _ = ∑ e, ∑ i, ∑ j, A e i j ^ 2 :=
      paperMean_rademacherMatrix_sum_entry_sq A

#print axioms paperMean_paperSign_mul_paperSign
#print axioms paperMean_weighted_paperSign_pair
#print axioms paperMean_rademacher_sum_sq
#print axioms paperMean_rademacherMatrix_sum_entry_sq
#print axioms paperMean_rademacherMatrix_l2_opNorm_sq_le_sum_entry_sq

end GraphMatrixReplica
