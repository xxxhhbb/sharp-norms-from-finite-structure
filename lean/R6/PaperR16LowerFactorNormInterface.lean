import R6.PaperR16LowerFactorRawExactFactorization
import R6.PaperPartialNCKStageReindexIsometry
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Deterministic L2 operator-norm interface for exact factor preprocessing

This module promotes the proven pointwise raw factorization to a
finite matrix identity and an L2 operator-norm identity. The core matrix is
indexed by the original row and column tuples through canonicalRow/Col.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.PaperR16.RawFactorShape

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

def rawOperatorMatrix (ξ : S.RawSample) :
    Matrix (S.RawBoundaryTuple S.leftBoundary)
      (S.RawBoundaryTuple S.rightBoundary) ℝ :=
  fun row col => S.rawMatrix ξ row col

def coreOperatorMatrixOnRawBoundary (ξ : S.RawSample) :
    Matrix (S.RawBoundaryTuple S.leftBoundary)
      (S.RawBoundaryTuple S.rightBoundary) ℝ :=
  fun row col =>
    (S.canonicalPreprocessedShape).coreMatrix
      (S.canonicalSample ξ) (S.canonicalRow row) (S.canonicalCol col)

def coreOperatorMatrixNative (ξ : S.RawSample) :
    Matrix
      ((S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).leftBoundary)
      ((S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).rightBoundary) ℝ :=
  fun row col =>
    (S.canonicalPreprocessedShape).coreMatrix (S.canonicalSample ξ) row col

def exactPreprocessingScalar (ξ : S.RawSample) : ℝ :=
  (S.canonicalPreprocessedShape).unusedScalar *
    ∏ j : S.DetachedComponent,
      (S.canonicalPreprocessedShape).detachedScalar
        (S.canonicalSample ξ) j

/-- Recover an original row label from a canonical core row label. -/
def canonicalRowInverse
    (row : (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).leftBoundary) :
    S.RawBoundaryTuple S.leftBoundary := by
  classical
  intro w
  have hSub : S.leftBoundary ⊆ S.boundary := Finset.subset_union_left
  exact row ⟨⟨w.1, S.core_of_mem_boundary (hSub w.2)⟩, by
    simp [RawFactorShape.canonicalPreprocessedShape, w.2]⟩

theorem canonicalRowInverse_canonicalRow
    (row : S.RawBoundaryTuple S.leftBoundary) :
    S.canonicalRowInverse (S.canonicalRow row) = row := by
  classical
  funext w
  rfl

theorem canonicalRow_canonicalRowInverse
    (row : (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).leftBoundary) :
    S.canonicalRow (S.canonicalRowInverse row) = row := by
  classical
  funext c
  rfl

/-- Canonical preprocessing preserves every row coordinate, including
boundary roles not read by any factor. -/
def canonicalRowEquiv :
    S.RawBoundaryTuple S.leftBoundary ≃
      (S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).leftBoundary where
  toFun := S.canonicalRow
  invFun := S.canonicalRowInverse
  left_inv := S.canonicalRowInverse_canonicalRow
  right_inv := S.canonicalRow_canonicalRowInverse

/-- Recover an original column label from a canonical core column label. -/
def canonicalColInverse
    (col : (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).rightBoundary) :
    S.RawBoundaryTuple S.rightBoundary := by
  classical
  intro w
  have hSub : S.rightBoundary ⊆ S.boundary := Finset.subset_union_right
  exact col ⟨⟨w.1, S.core_of_mem_boundary (hSub w.2)⟩, by
    simp [RawFactorShape.canonicalPreprocessedShape, w.2]⟩

theorem canonicalColInverse_canonicalCol
    (col : S.RawBoundaryTuple S.rightBoundary) :
    S.canonicalColInverse (S.canonicalCol col) = col := by
  classical
  funext w
  rfl

theorem canonicalCol_canonicalColInverse
    (col : (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).rightBoundary) :
    S.canonicalCol (S.canonicalColInverse col) = col := by
  classical
  funext c
  rfl

/-- Canonical preprocessing preserves every column coordinate. -/
def canonicalColEquiv :
    S.RawBoundaryTuple S.rightBoundary ≃
      (S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).rightBoundary where
  toFun := S.canonicalCol
  invFun := S.canonicalColInverse
  left_inv := S.canonicalColInverse_canonicalCol
  right_inv := S.canonicalCol_canonicalColInverse

theorem coreOperatorMatrixOnRawBoundary_eq_reindex
    (ξ : S.RawSample) :
    S.coreOperatorMatrixOnRawBoundary ξ =
      Matrix.reindex S.canonicalRowEquiv.symm S.canonicalColEquiv.symm
        (S.coreOperatorMatrixNative ξ) := by
  classical
  ext row col
  rfl

theorem rawOperatorMatrix_eq_scalar_smul_coreOnRawBoundary
    (ξ : S.RawSample) :
    S.rawOperatorMatrix ξ =
      S.exactPreprocessingScalar ξ • S.coreOperatorMatrixOnRawBoundary ξ := by
  classical
  ext row col
  change S.rawMatrix ξ row col =
    S.exactPreprocessingScalar ξ *
      (S.canonicalPreprocessedShape).coreMatrix
        (S.canonicalSample ξ) (S.canonicalRow row) (S.canonicalCol col)
  exact S.rawMatrix_eq_unused_mul_detached_mul_core ξ row col

theorem rawOperatorMatrix_l2_opNorm_eq
    (ξ : S.RawSample) :
    ‖S.rawOperatorMatrix ξ‖ =
      |S.exactPreprocessingScalar ξ| *
        ‖S.coreOperatorMatrixOnRawBoundary ξ‖ := by
  rw [S.rawOperatorMatrix_eq_scalar_smul_coreOnRawBoundary, norm_smul]
  simp only [Real.norm_eq_abs]

theorem rawOperatorMatrix_l2_opNorm_eq_reindexed_core
    (ξ : S.RawSample) :
    ‖S.rawOperatorMatrix ξ‖ =
      |S.exactPreprocessingScalar ξ| *
        ‖Matrix.reindex S.canonicalRowEquiv.symm
          S.canonicalColEquiv.symm (S.coreOperatorMatrixNative ξ)‖ := by
  rw [S.rawOperatorMatrix_l2_opNorm_eq,
    S.coreOperatorMatrixOnRawBoundary_eq_reindex]

/-- The exact pointwise preprocessing identity also gives the paper's
deterministic L2 operator-norm identity, with the core on its native index
types. The row and column equivalences preserve the operator norm. -/
theorem rawOperatorMatrix_l2_opNorm_eq_native_core
    (ξ : S.RawSample) :
    ‖S.rawOperatorMatrix ξ‖ =
      |S.exactPreprocessingScalar ξ| *
        ‖S.coreOperatorMatrixNative ξ‖ := by
  classical
  rw [S.rawOperatorMatrix_l2_opNorm_eq_reindexed_core]
  rw [GraphMatrixReplica.paper_l2_opNorm_reindex
    S.canonicalRowEquiv.symm S.canonicalColEquiv.symm
    (S.coreOperatorMatrixNative ξ)]

#print axioms RawFactorShape.rawOperatorMatrix_eq_scalar_smul_coreOnRawBoundary
#print axioms RawFactorShape.rawOperatorMatrix_l2_opNorm_eq
#print axioms RawFactorShape.canonicalRowEquiv
#print axioms RawFactorShape.canonicalColEquiv
#print axioms RawFactorShape.coreOperatorMatrixOnRawBoundary_eq_reindex
#print axioms RawFactorShape.rawOperatorMatrix_l2_opNorm_eq_reindexed_core
#print axioms RawFactorShape.rawOperatorMatrix_l2_opNorm_eq_native_core

end GraphMatrixReplica.PaperR16.RawFactorShape
