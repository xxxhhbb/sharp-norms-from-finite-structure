import GraphMatrix.SparseFlatteningNorm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Finite Schur test for the L2 matrix operator norm

This is the dimension-free deterministic norm estimate needed by sparse
nearly-combinatorial flattenings.  The proof is finite throughout: a weighted
Cauchy--Schwarz inequality controls each row, the double sum is exchanged,
and the resulting vector estimate is promoted to the continuous-linear-map
operator norm used by Mathlib's matrix L2 norm.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Absolute row sum. -/
def matrixAbsRowSum
    {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (i : ι) : ℝ :=
  ∑ j, |A i j|

/-- Absolute column sum. -/
def matrixAbsColSum
    {ι κ : Type*} [Fintype ι]
    (A : Matrix ι κ ℝ) (j : κ) : ℝ :=
  ∑ i, |A i j|

/-- Weighted finite Cauchy--Schwarz in the exact form used for one matrix
row. -/
theorem sum_mul_sq_le_abs_sum_mul_weighted_sq
    {κ : Type*} [Fintype κ]
    (a x : κ → ℝ) :
    (∑ j, a j * x j) ^ 2 ≤
      (∑ j, |a j|) * ∑ j, |a j| * x j ^ 2 := by
  classical
  have hTriangle :
      |∑ j, a j * x j| ≤ ∑ j, |a j * x j| :=
    Finset.abs_sum_le_sum_abs _ _
  have hTriangleSq :
      (∑ j, a j * x j) ^ 2 ≤ (∑ j, |a j * x j|) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hTriangle 2
    simpa [sq_abs] using h
  refine hTriangleSq.trans ?_
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _
    exact abs_nonneg _
  · intro j _
    exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
  · intro j _
    rw [abs_mul, mul_pow, sq_abs]
    nlinarith [sq_abs (a j), sq_abs (x j)]

/-- Vector-level Schur estimate.  This is the analytic core, independent of
any norm-identification API. -/
theorem matrix_mulVec_sum_sq_le_rowColSum_mul_sum_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (R C : ℝ)
    (hR : 0 ≤ R) (_hC : 0 ≤ C)
    (hRow : ∀ i, matrixAbsRowSum A i ≤ R)
    (hCol : ∀ j, matrixAbsColSum A j ≤ C)
    (x : κ → ℝ) :
    (∑ i, (Matrix.mulVec A x) i ^ 2) ≤
      R * C * ∑ j, x j ^ 2 := by
  classical
  calc
    (∑ i, (Matrix.mulVec A x) i ^ 2) =
        ∑ i, (∑ j, A i j * x j) ^ 2 := by
      simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ i, matrixAbsRowSum A i *
          (∑ j, |A i j| * x j ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_mul_sq_le_abs_sum_mul_weighted_sq (A i) x
    _ ≤ ∑ i, R * (∑ j, |A i j| * x j ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact hRow i
    _ = R * ∑ i, ∑ j, |A i j| * x j ^ 2 := by
      rw [Finset.mul_sum]
    _ = R * ∑ j, ∑ i, |A i j| * x j ^ 2 := by
      rw [Finset.sum_comm]
    _ = R * ∑ j, matrixAbsColSum A j * x j ^ 2 := by
      simp only [matrixAbsColSum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ R * ∑ j, C * x j ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hR
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hCol j) (sq_nonneg _)
    _ = R * C * ∑ j, x j ^ 2 := by
      rw [← Finset.mul_sum]
      ring

/-- Finite real Schur test for Mathlib's Euclidean (`L2`) matrix operator
norm. -/
theorem matrix_l2_opNorm_sq_le_absRowSum_mul_absColSum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (R C : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hRow : ∀ i, matrixAbsRowSum A i ≤ R)
    (hCol : ∀ j, matrixAbsColSum A j ≤ C) :
    ‖A‖ ^ 2 ≤ R * C := by
  let T : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := ι) (n := κ)).trans
      LinearMap.toContinuousLinearMap A
  have hRC : 0 ≤ R * C := mul_nonneg hR hC
  have hApply : ∀ x : EuclideanSpace ℝ κ,
      ‖T x‖ ≤ Real.sqrt (R * C) * ‖x‖ := by
    intro x
    have hVector := matrix_mulVec_sum_sq_le_rowColSum_mul_sum_sq
      A R C hR hC hRow hCol (WithLp.ofLp x)
    have hSquare : ‖T x‖ ^ 2 ≤
        (Real.sqrt (R * C) * ‖x‖) ^ 2 := by
      calc
        ‖T x‖ ^ 2 = ∑ i, (Matrix.mulVec A (WithLp.ofLp x)) i ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          rfl
        _ ≤ R * C * ∑ j, (WithLp.ofLp x j) ^ 2 := hVector
        _ = R * C * ‖x‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
        _ = (Real.sqrt (R * C) * ‖x‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hRC]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
      (Real.sqrt_nonneg _) (norm_nonneg _))).mp hSquare
  have hOp : ‖T‖ ≤ Real.sqrt (R * C) :=
    T.opNorm_le_bound (Real.sqrt_nonneg _) hApply
  have hMatrix : ‖A‖ ≤ Real.sqrt (R * C) := by
    exact hOp
  calc
    ‖A‖ ^ 2 ≤ (Real.sqrt (R * C)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hMatrix 2
    _ = R * C := Real.sq_sqrt hRC

/-- Absolute sum of a bounded scalar family is controlled by the size of its
nonzero support. -/
theorem sum_abs_le_support_card_mul
    {α : Type*} [Fintype α]
    (f : α → ℝ) (w : ℝ)
    (hEntry : ∀ a, |f a| ≤ w) :
    (∑ a, |f a|) ≤
      ((Finset.univ.filter fun a => f a ≠ 0).card : ℝ) * w := by
  classical
  calc
    (∑ a, |f a|) =
        ∑ a, if f a ≠ 0 then |f a| else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a = 0 <;> simp [ha]
    _ = (∑ a ∈ (Finset.univ.filter fun a => f a ≠ 0),
          |f a|) := by
      rw [Finset.sum_filter]
    _ ≤ (∑ _a ∈ (Finset.univ.filter fun a => f a ≠ 0), w) := by
      exact Finset.sum_le_sum fun a _ => hEntry a
    _ = ((Finset.univ.filter fun a => f a ≠ 0).card : ℝ) * w := by
      simp

/-- Sparse Schur corollary: bounded entries and maximum row/column nonzero
degrees give the dimension-free product bound required by the flattening
argument. -/
theorem matrix_l2_opNorm_sq_le_entry_sq_mul_rowDegree_mul_colDegree
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (w : ℝ) (r c : ℕ)
    (hw : 0 ≤ w) (hEntry : ∀ i j, |A i j| ≤ w)
    (hRow : ∀ i, (matrixRowSupport A i).card ≤ r)
    (hCol : ∀ j, (matrixColSupport A j).card ≤ c) :
    ‖A‖ ^ 2 ≤ w ^ 2 * (r : ℝ) * (c : ℝ) := by
  have hAbsRow : ∀ i, matrixAbsRowSum A i ≤ (r : ℝ) * w := by
    intro i
    have hSupport : matrixAbsRowSum A i ≤
        ((matrixRowSupport A i).card : ℝ) * w := by
      simpa [matrixAbsRowSum, matrixRowSupport] using
        sum_abs_le_support_card_mul (fun j => A i j) w (hEntry i)
    refine hSupport.trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hRow i) hw
  have hAbsCol : ∀ j, matrixAbsColSum A j ≤ (c : ℝ) * w := by
    intro j
    have hSupport : matrixAbsColSum A j ≤
        ((matrixColSupport A j).card : ℝ) * w := by
      simpa [matrixAbsColSum, matrixColSupport] using
        sum_abs_le_support_card_mul (fun i => A i j) w
          (fun i => hEntry i j)
    refine hSupport.trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCol j) hw
  have hSchur := matrix_l2_opNorm_sq_le_absRowSum_mul_absColSum
    A ((r : ℝ) * w) ((c : ℝ) * w)
      (mul_nonneg (Nat.cast_nonneg _) hw)
      (mul_nonneg (Nat.cast_nonneg _) hw) hAbsRow hAbsCol
  calc
    ‖A‖ ^ 2 ≤ ((r : ℝ) * w) * ((c : ℝ) * w) := hSchur
    _ = w ^ 2 * (r : ℝ) * (c : ℝ) := by ring


end GraphMatrixReplica
