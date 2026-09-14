import R6.PaperR16LowerFactorRawMatrixBridge

/-!
# Exact preprocessing of the original independent-occurrence factor matrix

The original raw Cartesian matrix has the canonical unused-role dimension,
detached-component partition functions, and core matrix as exact factors.
The construction retains the original factor occurrence indices and arrays.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.PaperR16.RawFactorShape

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

/-- Exact factorization of the original unpartitioned finite factor matrix.
No core/unused/detached partition is assumed: it is extracted canonically
from the raw factor scopes and boundary roles. Equal scopes retain separate
occurrence labels and arrays. -/
theorem rawMatrix_eq_unused_mul_detached_mul_core
    (ξ : S.RawSample)
    (row : S.RawBoundaryTuple S.leftBoundary)
    (col : S.RawBoundaryTuple S.rightBoundary) :
    S.rawMatrix ξ row col =
      (S.canonicalPreprocessedShape).unusedScalar *
        (∏ j : S.DetachedComponent,
          (S.canonicalPreprocessedShape).detachedScalar
            (S.canonicalSample ξ) j) *
        (S.canonicalPreprocessedShape).coreMatrix
          (S.canonicalSample ξ) (S.canonicalRow row)
          (S.canonicalCol col) := by
  rw [S.rawMatrix_eq_canonicalFullMatrix]
  exact (S.canonicalPreprocessedShape).fullMatrix_eq_unused_mul_detached_mul_core
    (S.canonicalSample ξ) (S.canonicalRow row) (S.canonicalCol col)

#print axioms RawFactorShape.rawMatrix_eq_unused_mul_detached_mul_core

end GraphMatrixReplica.PaperR16.RawFactorShape
