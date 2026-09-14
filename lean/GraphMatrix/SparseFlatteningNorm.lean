import GraphMatrix.TraceNormBridge

/-! # Deterministic sparse flattening norm bounds

This file records the unconditional Frobenius endpoint available from the
current Mathlib L2-operator-norm API.  It retains actual row and column
support cardinalities.  The stronger Schur estimate depending on the product
of maximum row and column degrees would remove the ambient dimension factor;
that interpolation step is deliberately not postulated here.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Nonzero columns in a fixed row. -/
def matrixRowSupport
    {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (i : ι) : Finset κ := by
  classical
  exact Finset.univ.filter fun j => A i j ≠ 0

/-- Nonzero rows in a fixed column. -/
def matrixColSupport
    {ι κ : Type*} [Fintype ι]
    (A : Matrix ι κ ℝ) (j : κ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => A i j ≠ 0

/-- A uniformly bounded finite scalar family has squared sum at most its
support cardinality times the squared entry bound. -/
theorem sum_sq_le_support_card_mul_sq
    {α : Type*} [Fintype α]
    (f : α → ℝ) (w : ℝ) (_hw : 0 ≤ w)
    (hEntry : ∀ a, |f a| ≤ w) :
    (∑ a, f a ^ 2) ≤
      ((Finset.univ.filter fun a => f a ≠ 0).card : ℝ) * w ^ 2 := by
  classical
  calc
    (∑ a, f a ^ 2) =
        ∑ a, if f a ≠ 0 then f a ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a = 0 <;> simp [ha]
    _ = (∑ a ∈ (Finset.univ.filter fun a => f a ≠ 0),
          f a ^ 2) := by
      rw [Finset.sum_filter]
    _ ≤ (∑ _a ∈ (Finset.univ.filter fun a => f a ≠ 0),
          w ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      have hsq : |f a| ^ 2 ≤ w ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) (hEntry a) 2
      simpa [sq_abs] using hsq
    _ = ((Finset.univ.filter fun a => f a ≠ 0).card : ℝ) *
          w ^ 2 := by
      simp

/-- The trace of the real Gram matrix is the entrywise sum of squares. -/
theorem matrix_trace_transpose_mul_self_eq_sum_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    Matrix.trace (A.transpose * A) =
      ∑ i, ∑ j, A i j ^ 2 := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, pow_two]
  rw [Finset.sum_comm]

/-- The squared Euclidean operator norm is bounded by the entrywise sum of
squares.  This is the Frobenius bound, proved through the positive
semidefinite Gram trace rather than by changing matrix norm instances. -/
theorem matrix_l2_opNorm_sq_le_sum_entry_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) :
    ‖A‖ ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := by
  have hGram : (A.transpose * A).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self A
  have hNorm : ‖A.transpose * A‖ = ‖A‖ * ‖A‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose_mul_self A
  calc
    ‖A‖ ^ 2 = ‖A.transpose * A‖ := by
      rw [pow_two, hNorm]
    _ ≤ Matrix.trace (A.transpose * A) :=
      matrix_l2_opNorm_le_trace_of_posSemidef _ hGram
    _ = ∑ i, ∑ j, A i j ^ 2 :=
      matrix_trace_transpose_mul_self_eq_sum_sq A

/-- Frobenius bound using a uniform entry bound and maximum row degree. -/
theorem matrix_l2_opNorm_sq_le_rows_mul_rowDegree_mul_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (w : ℝ) (r : ℕ)
    (hw : 0 ≤ w) (hEntry : ∀ i j, |A i j| ≤ w)
    (hRow : ∀ i, (matrixRowSupport A i).card ≤ r) :
    ‖A‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * (r : ℝ) * w ^ 2 := by
  refine (matrix_l2_opNorm_sq_le_sum_entry_sq A).trans ?_
  calc
    (∑ i, ∑ j, A i j ^ 2) ≤
        ∑ i, ((matrixRowSupport A i).card : ℝ) * w ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa [matrixRowSupport] using
        sum_sq_le_support_card_mul_sq (fun j => A i j) w hw
          (hEntry i)
    _ ≤ ∑ _i : ι, (r : ℝ) * w ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact_mod_cast hRow i
    _ = (Fintype.card ι : ℝ) * (r : ℝ) * w ^ 2 := by
      simp [mul_assoc]

/-- Transposed Frobenius bound using maximum column degree. -/
theorem matrix_l2_opNorm_sq_le_cols_mul_colDegree_mul_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (w : ℝ) (c : ℕ)
    (hw : 0 ≤ w) (hEntry : ∀ i j, |A i j| ≤ w)
    (hCol : ∀ j, (matrixColSupport A j).card ≤ c) :
    ‖A‖ ^ 2 ≤
      (Fintype.card κ : ℝ) * (c : ℝ) * w ^ 2 := by
  refine (matrix_l2_opNorm_sq_le_sum_entry_sq A).trans ?_
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, A i j ^ 2) ≤
        ∑ j, ((matrixColSupport A j).card : ℝ) * w ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa [matrixColSupport] using
        sum_sq_le_support_card_mul_sq (fun i => A i j) w hw
          (fun i => hEntry i j)
    _ ≤ ∑ _j : κ, (c : ℝ) * w ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      gcongr
      exact_mod_cast hCol j
    _ = (Fintype.card κ : ℝ) * (c : ℝ) * w ^ 2 := by
      simp [mul_assoc]

/-- Using both sparse-degree hypotheses gives the minimum of the two valid
Frobenius estimates.  Unlike the desired Schur bound `w²*r*c`, this still
contains an ambient row or column cardinality. -/
theorem matrix_l2_opNorm_sq_le_min_dimension_degree_mul_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (w : ℝ) (r c : ℕ)
    (hw : 0 ≤ w) (hEntry : ∀ i j, |A i j| ≤ w)
    (hRow : ∀ i, (matrixRowSupport A i).card ≤ r)
    (hCol : ∀ j, (matrixColSupport A j).card ≤ c) :
    ‖A‖ ^ 2 ≤ min
      ((Fintype.card ι : ℝ) * (r : ℝ) * w ^ 2)
      ((Fintype.card κ : ℝ) * (c : ℝ) * w ^ 2) := by
  exact le_min
    (matrix_l2_opNorm_sq_le_rows_mul_rowDegree_mul_sq
      A w r hw hEntry hRow)
    (matrix_l2_opNorm_sq_le_cols_mul_colDegree_mul_sq
      A w c hw hEntry hCol)


end GraphMatrixReplica
