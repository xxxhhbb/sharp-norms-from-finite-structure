import R6.PaperRademacherOpenWordContraction
import Mathlib.Data.Matrix.Block

/-! # Block-row factorization of Rademacher sandwich maps

The row sandwich is factored as `B · diag(X) · Bᵀ`, where `B` concatenates
the coefficient matrices.  The Gram factor is exactly the row variance.
This reduces the sharp completely-positive-map norm bound to the single
direct-sum norm inequality for a constant block diagonal matrix.
-/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/- The C-star matrix type-copy exports a higher-priority heterogeneous
multiplication instance definitionally overlapping `Matrix`.  Pin the native
matrix product in this block-factorization file. -/
def nativeMatrixMul {l m n α : Type} [Fintype m] [Mul α] [AddCommMonoid α]
    (A : Matrix l m α) (B : Matrix m n α) : Matrix l n α :=
  fun i k => ∑ j, A i j * B j k

/-- Horizontal concatenation of all coefficient matrices. -/
def rademacherRowBlockMatrix
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) : Matrix ι (κ × ε) ℝ :=
  fun i ke => A ke.2 i ke.1

/-- One copy of `X` on each edge-label block. -/
def rademacherRepeatedBlockDiagonal
    {ε κ : Type} [DecidableEq ε]
    (X : Matrix κ κ ℝ) : Matrix (κ × ε) (κ × ε) ℝ :=
  Matrix.blockDiagonal (fun _ : ε => X)

/-- The `e`-th Euclidean slice of a vector indexed by `κ × ε`. -/
def rademacherBlockSlice
    {ε κ : Type} [Fintype κ]
    (x : EuclideanSpace ℝ (κ × ε)) (e : ε) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 fun k => x (k, e)

@[simp]
theorem rademacherBlockSlice_apply
    {ε κ : Type} [Fintype κ]
    (x : EuclideanSpace ℝ (κ × ε)) (e : ε) (k : κ) :
    rademacherBlockSlice x e k = x (k, e) := by
  rfl

/-- A repeated block diagonal acts independently on every Euclidean slice. -/
theorem rademacherRepeatedBlockDiagonal_mulVec_apply
    {ε κ : Type} [Fintype ε] [Fintype κ] [DecidableEq ε]
    (X : Matrix κ κ ℝ) (x : EuclideanSpace ℝ (κ × ε))
    (k : κ) (e : ε) :
    (rademacherRepeatedBlockDiagonal (ε := ε) X *ᵥ x) (k, e) =
      (X *ᵥ rademacherBlockSlice x e) k := by
  classical
  simp [rademacherRepeatedBlockDiagonal, Matrix.mulVec,
    Matrix.blockDiagonal_apply, rademacherBlockSlice,
    dotProduct, Fintype.sum_prod_type]

/-- Pythagoras for the edge-label slices of a product-indexed Euclidean
vector. -/
theorem sum_rademacherBlockSlice_norm_sq
    {ε κ : Type} [Fintype ε] [Fintype κ]
    (x : EuclideanSpace ℝ (κ × ε)) :
    ∑ e, ‖rademacherBlockSlice x e‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  simp only [rademacherBlockSlice_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The block-row Gram matrix is exactly the row variance. -/
theorem rademacherRowBlockMatrix_mul_transpose
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    rademacherRowBlockMatrix A * (rademacherRowBlockMatrix A).transpose =
      rademacherRowVariance A := by
  classical
  ext i j
  simp only [rademacherRowBlockMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, rademacherRowVariance, Matrix.sum_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Exact block factorization of the row sandwich. -/
theorem rademacherRowBlock_factorization
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix κ κ ℝ) :
    nativeMatrixMul
      (nativeMatrixMul (rademacherRowBlockMatrix A)
        (rademacherRepeatedBlockDiagonal X))
      (rademacherRowBlockMatrix A).transpose =
      rademacherRowSandwich A X := by
  classical
  ext i j
  simp [nativeMatrixMul, rademacherRowBlockMatrix,
    rademacherRepeatedBlockDiagonal, Matrix.blockDiagonal_apply,
    Matrix.transpose_apply, rademacherRowSandwich, Matrix.sum_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Squared block-row norm is the row-variance norm. -/
theorem rademacherRowBlock_norm_sq
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    ‖rademacherRowBlockMatrix A‖ * ‖rademacherRowBlockMatrix A‖ =
      ‖rademacherRowVariance A‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self
    (rademacherRowBlockMatrix A).transpose
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    rademacherRowBlockMatrix_mul_transpose] at h
  have ht : ‖(rademacherRowBlockMatrix A).transpose‖ =
      ‖rademacherRowBlockMatrix A‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose (rademacherRowBlockMatrix A)
  simpa [ht] using h.symm

/-- Minimal remaining direct-sum norm statement. -/
def RademacherRepeatedBlockDiagonalNormBound : Prop :=
  ∀ {ε κ : Type} [Fintype ε] [Fintype κ]
      [DecidableEq ε] [DecidableEq κ] (X : Matrix κ κ ℝ),
    ‖rademacherRepeatedBlockDiagonal (ε := ε) X‖ ≤ ‖X‖

/-- The operator norm of a constant finite block diagonal is bounded by the
norm of its common block.  This includes the empty edge-label type. -/
theorem rademacherRepeatedBlockDiagonal_norm_le
    {ε κ : Type} [Fintype ε] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ] (X : Matrix κ κ ℝ) :
    ‖rademacherRepeatedBlockDiagonal (ε := ε) X‖ ≤ ‖X‖ := by
  let D := rademacherRepeatedBlockDiagonal (ε := ε) X
  let T := Matrix.toEuclideanCLM (n := κ × ε) (𝕜 := ℝ) D
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine T.opNorm_le_bound (norm_nonneg X) fun x => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg X)
    (norm_nonneg x))).mp ?_
  simp only [(T x).norm_sq_eq, Matrix.ofLp_toEuclideanCLM, T, D]
  calc
    ∑ ke, ‖(rademacherRepeatedBlockDiagonal (ε := ε) X *ᵥ x) ke‖ ^ 2 =
        ∑ e, ‖(EuclideanSpace.equiv κ ℝ).symm
          (X *ᵥ rademacherBlockSlice x e)‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro k hk
      rw [rademacherRepeatedBlockDiagonal_mulVec_apply]
      rfl
    _ ≤ ∑ e, (‖X‖ * ‖rademacherBlockSlice x e‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg X) (norm_nonneg _))).mpr
          (Matrix.l2_opNorm_mulVec X (rademacherBlockSlice x e))
    _ = ‖X‖ ^ 2 * ∑ e, ‖rademacherBlockSlice x e‖ ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ = ‖X‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [sum_rademacherBlockSlice_norm_sq]
    _ = (‖X‖ * ‖x‖) ^ 2 := by ring

/-- The direct-sum norm obligation used by the block-row factorization is
unconditional. -/
theorem rademacherRepeatedBlockDiagonalNormBound_holds :
    RademacherRepeatedBlockDiagonalNormBound := by
  intro ε κ _ _ _ _ X
  exact rademacherRepeatedBlockDiagonal_norm_le X

/-- The block factorization yields the sharp row sandwich estimate from the
single repeated-block-diagonal norm bound. -/
theorem rademacherRowSandwich_norm_le_rowVariance_mul_of_blockDiagonal
    (hblock : RademacherRepeatedBlockDiagonalNormBound)
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix κ κ ℝ) :
    ‖rademacherRowSandwich A X‖ ≤ ‖rademacherRowVariance A‖ * ‖X‖ := by
  let B := rademacherRowBlockMatrix A
  let D := rademacherRepeatedBlockDiagonal (ε := ε) X
  have hfactor : nativeMatrixMul (nativeMatrixMul B D) B.transpose =
      rademacherRowSandwich A X :=
    rademacherRowBlock_factorization A X
  have ht : ‖B.transpose‖ = ‖B‖ := by
    simpa [B] using Matrix.l2_opNorm_conjTranspose B
  calc
    ‖rademacherRowSandwich A X‖ =
        ‖nativeMatrixMul (nativeMatrixMul B D) B.transpose‖ := by
      rw [hfactor]
    _ ≤ ‖nativeMatrixMul B D‖ * ‖B.transpose‖ := by
      change ‖@HMul.hMul _ _ _
        Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
        (@HMul.hMul _ _ _
          Matrix.instHMulOfFintypeOfMulOfAddCommMonoid B D)
        B.transpose‖ ≤ _
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (‖B‖ * ‖D‖) * ‖B.transpose‖ := by
      gcongr
      change ‖@HMul.hMul _ _ _
        Matrix.instHMulOfFintypeOfMulOfAddCommMonoid B D‖ ≤ ‖B‖ * ‖D‖
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ (‖B‖ * ‖X‖) * ‖B.transpose‖ := by
      gcongr
      exact hblock X
    _ = (‖B‖ * ‖B‖) * ‖X‖ := by rw [ht]; ring
    _ = ‖rademacherRowVariance A‖ * ‖X‖ := by
      rw [rademacherRowBlock_norm_sq A]

/-- The column sharp estimate follows by applying the row factorization to
the transposed coefficient family. -/
theorem rademacherColumnSandwich_norm_le_columnVariance_mul_of_blockDiagonal
    (hblock : RademacherRepeatedBlockDiagonalNormBound)
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix ι ι ℝ) :
    ‖rademacherColumnSandwich A X‖ ≤
      ‖rademacherColumnVariance A‖ * ‖X‖ := by
  simpa [rademacherColumnSandwich, rademacherRowSandwich,
    rademacherRowVariance_transposeFamily] using
    (rademacherRowSandwich_norm_le_rowVariance_mul_of_blockDiagonal
      hblock (fun e => (A e).transpose) X)

/-- Conditional assembly of the desired common sharp sandwich interface. -/
theorem rademacherSandwichNormBound_varianceNormMax_of_blockDiagonal
    (hblock : RademacherRepeatedBlockDiagonalNormBound)
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    RademacherSandwichNormBound A (rademacherVarianceNormMax A) := by
  constructor
  · intro X
    exact (rademacherRowSandwich_norm_le_rowVariance_mul_of_blockDiagonal
      hblock A X).trans (mul_le_mul_of_nonneg_right
        (rowVariance_l2_opNorm_le_varianceNormMax A) (norm_nonneg X))
  · intro X
    exact (rademacherColumnSandwich_norm_le_columnVariance_mul_of_blockDiagonal
      hblock A X).trans (mul_le_mul_of_nonneg_right
        (columnVariance_l2_opNorm_le_varianceNormMax A) (norm_nonneg X))

/-- Sharp row completely-positive sandwich bound. -/
theorem rademacherRowSandwich_norm_le_rowVariance_mul
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix κ κ ℝ) :
    ‖rademacherRowSandwich A X‖ ≤ ‖rademacherRowVariance A‖ * ‖X‖ :=
  rademacherRowSandwich_norm_le_rowVariance_mul_of_blockDiagonal
    rademacherRepeatedBlockDiagonalNormBound_holds A X

/-- Sharp column completely-positive sandwich bound. -/
theorem rademacherColumnSandwich_norm_le_columnVariance_mul
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix ι ι ℝ) :
    ‖rademacherColumnSandwich A X‖ ≤
      ‖rademacherColumnVariance A‖ * ‖X‖ :=
  rademacherColumnSandwich_norm_le_columnVariance_mul_of_blockDiagonal
    rademacherRepeatedBlockDiagonalNormBound_holds A X

/-- The row and column sandwich maps have the common sharp variance-max
constant required by the open-word recursion. -/
theorem rademacherSandwichNormBound_varianceNormMax
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    RademacherSandwichNormBound A (rademacherVarianceNormMax A) :=
  rademacherSandwichNormBound_varianceNormMax_of_blockDiagonal
    rademacherRepeatedBlockDiagonalNormBound_holds A

/-- Unconditional sharp Catalan endpoint: every noncrossing open word loses
exactly one factor of the maximum row/column variance norm per matched pair. -/
theorem rademacherOpenWords_norm_le_varianceNormMax_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ)
    {n : ℕ} (M : RademacherNoncrossingMatching n) :
    ‖rademacherRowOpenWord A M‖ ≤ rademacherVarianceNormMax A ^ n ∧
      ‖rademacherColumnOpenWord A M‖ ≤
        rademacherVarianceNormMax A ^ n :=
  rademacherOpenWords_norm_le_varianceNormMax_pow_of_sharpSandwich A
    (rademacherSandwichNormBound_varianceNormMax A) M

#print axioms rademacherRowBlockMatrix_mul_transpose
#print axioms rademacherRowBlock_factorization
#print axioms rademacherRowBlock_norm_sq
#print axioms rademacherRepeatedBlockDiagonal_norm_le
#print axioms rademacherRepeatedBlockDiagonalNormBound_holds
#print axioms
  rademacherSandwichNormBound_varianceNormMax_of_blockDiagonal
#print axioms rademacherRowSandwich_norm_le_rowVariance_mul
#print axioms rademacherColumnSandwich_norm_le_columnVariance_mul
#print axioms rademacherSandwichNormBound_varianceNormMax
#print axioms rademacherOpenWords_norm_le_varianceNormMax_pow

end GraphMatrixReplica
