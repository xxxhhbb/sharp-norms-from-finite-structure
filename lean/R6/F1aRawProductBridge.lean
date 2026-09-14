import R6.PaperR16LowerFactorProbabilityFactors

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory
namespace GraphMatrixReplica.PaperR16.RawFactorShape
variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

/-- The actual raw model has the same integral as its proved coordinate reindex.
This is a consequence of the pushforward theorem, not an independence premise. -/
theorem integral_raw_reindex
    (ν : E → Measure ℝ) [∀ e, IsProbabilityMeasure (ν e)]
    (F : (∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) → ℝ) :
    (∫ x, F (S.rawFlatToBlocksMeasurableEquiv x) ∂S.rawPrimitiveLaw ν) =
      ∫ blocks, F blocks ∂S.groupedPrimitiveLaw ν := by
  rw [← S.map_rawPrimitiveLaw_eq_groupedPrimitiveLaw ν]
  exact (integral_map_equiv S.rawFlatToBlocksMeasurableEquiv F).symm

/-- Exact expectation factorization for the actual canonical core matrix and
detached scalar sums, evaluated directly in the original primitive sample. -/
theorem integral_raw_actual_core_detached_tests
    (ν : E → Measure ℝ) [∀ e, IsProbabilityMeasure (ν e)]
    (fc : Matrix
      (S.canonicalPreprocessedShape.BoundaryTuple S.canonicalPreprocessedShape.leftBoundary)
      (S.canonicalPreprocessedShape.BoundaryTuple S.canonicalPreprocessedShape.rightBoundary) ℝ → ℝ)
    (fj : ∀ j : S.DetachedComponent, ℝ → ℝ) :
    (∫ x,
      fc (S.coreOperatorMatrixNative (S.unflattenRawSample x)) *
        ∏ j : S.DetachedComponent,
          fj j (S.canonicalPreprocessedShape.detachedScalar
            (S.canonicalSample (S.unflattenRawSample x)) j)
      ∂S.rawPrimitiveLaw ν) =
      (∫ x, fc (S.coreMatrixFromBlock x) ∂S.oneBlockLaw ν (Sum.inl ())) *
        ∏ j : S.DetachedComponent,
          ∫ x, fj j (S.detachedScalarFromBlock j x) ∂S.oneBlockLaw ν (Sum.inr j) := by
  classical
  rw [← S.integral_actual_core_detached_tests ν fc fj,
    ← S.integral_raw_reindex ν]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [S.coreOperatorMatrixNative_eq_fromBlock]
  simp only [S.canonical_detachedScalar_eq_fromBlock]
  congr 1
  · congr 2
    funext p
    exact (S.rawFlatToBlocksMeasurableEquiv_apply x (Sum.inl ()) p).symm
  · apply Finset.prod_congr rfl
    intro j hj
    congr 2
    funext p
    exact (S.rawFlatToBlocksMeasurableEquiv_apply x (Sum.inr j) p).symm

#print axioms integral_raw_reindex
#print axioms integral_raw_actual_core_detached_tests
end GraphMatrixReplica.PaperR16.RawFactorShape
