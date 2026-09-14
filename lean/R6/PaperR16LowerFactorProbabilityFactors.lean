import R6.PaperR16LowerFactorProbabilityReindex
import Mathlib.Tactic.Measurability

/-!
# F1a: actual canonical factors as functions of the probability blocks

This companion draft connects the primitive-coordinate probability reindex to
`canonicalSample`, the actual detached scalar sums, and the native core matrix.
It does not replace the model by freshly sampled independent factors: every
function below is built from the original occurrence-labelled primitive
coordinates.

Execution status in the return package: NOT RUN LOCALLY.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory

namespace GraphMatrixReplica.PaperR16.RawFactorShape

local instance {m n : Type*} : MeasurableSpace (Matrix m n ℝ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℝ))
local instance {m n : Type*} [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℝ) :=
  inferInstanceAs (BorelSpace (m → n → ℝ))

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

/-- The actual core occurrence product, written directly as a polynomial in
primitive coordinates from the core block. -/
def coreAmplitudeFromBlock
    (x : S.CorePrimitiveCoord → ℝ)
    (a : (S.canonicalPreprocessedShape).CoreTuple) : ℝ :=
  ∏ e : S.CanonicalCoreOccurrence,
    x ⟨⟨e.1, fun w => a ⟨w.1, e.2 w.1 w.2⟩⟩, e.2⟩

/-- The actual core entry, with exactly the boundary tests from
`PreprocessedFactorShape.coreEntry`. -/
def coreEntryFromBlock
    (x : S.CorePrimitiveCoord → ℝ)
    (row : (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).leftBoundary)
    (col : (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).rightBoundary)
    (a : (S.canonicalPreprocessedShape).CoreTuple) : ℝ :=
  if (∀ c : {c : S.CanonicalCore //
        c ∈ (S.canonicalPreprocessedShape).leftBoundary},
        a c.1 = row c) ∧
      (∀ c : {c : S.CanonicalCore //
        c ∈ (S.canonicalPreprocessedShape).rightBoundary},
        a c.1 = col c) then
    S.coreAmplitudeFromBlock x a
  else 0

/-- Native core matrix as a function of the core primitive block alone. -/
def coreMatrixFromBlock (x : S.CorePrimitiveCoord → ℝ) :
    Matrix
      ((S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).leftBoundary)
      ((S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).rightBoundary) ℝ :=
  fun row col =>
    ∑ a : (S.canonicalPreprocessedShape).CoreTuple,
      S.coreEntryFromBlock x row col a

/-- The actual detached occurrence product in component `j`, expressed only
in primitive coordinates assigned to `j`. -/
def detachedAmplitudeFromBlock
    (j : S.DetachedComponent)
    (x : S.DetachedPrimitiveCoord j → ℝ)
    (a : (S.canonicalPreprocessedShape).DetachedTuple j) : ℝ :=
  ∏ e : S.CanonicalDetachedOccurrence j,
    x ⟨⟨e.1, fun w => a ⟨w.1, e.2 w.1 w.2⟩⟩, e.2⟩

/-- The actual detached scalar sum `Z_j`, expressed as a polynomial of the
primitive coordinates in component `j` only. -/
def detachedScalarFromBlock
    (j : S.DetachedComponent)
    (x : S.DetachedPrimitiveCoord j → ℝ) : ℝ :=
  ∑ a : (S.canonicalPreprocessedShape).DetachedTuple j,
    S.detachedAmplitudeFromBlock j x a

/-- The source `canonicalSample` core amplitude agrees with the block
polynomial. -/
theorem canonical_coreAmplitude_eq_fromBlock
    (ξ : S.RawSample)
    (a : (S.canonicalPreprocessedShape).CoreTuple) :
    (S.canonicalPreprocessedShape).coreAmplitude (S.canonicalSample ξ) a =
      S.coreAmplitudeFromBlock (S.rawCoreBlock ξ) a := by
  classical
  unfold PreprocessedFactorShape.coreAmplitude coreAmplitudeFromBlock
  apply Fintype.prod_congr
  intro e
  rfl

/-- The source `canonicalSample` detached amplitude agrees with the block
polynomial. -/
theorem canonical_detachedAmplitude_eq_fromBlock
    (ξ : S.RawSample) (j : S.DetachedComponent)
    (a : (S.canonicalPreprocessedShape).DetachedTuple j) :
    (S.canonicalPreprocessedShape).detachedAmplitude
        (S.canonicalSample ξ) j a =
      S.detachedAmplitudeFromBlock j (S.rawDetachedBlock ξ j) a := by
  classical
  unfold PreprocessedFactorShape.detachedAmplitude detachedAmplitudeFromBlock
  apply Fintype.prod_congr
  intro e
  rfl

/-- The actual detached scalar in the deterministic preprocessing theorem is
exactly the function of its own primitive block defined above. -/
theorem canonical_detachedScalar_eq_fromBlock
    (ξ : S.RawSample) (j : S.DetachedComponent) :
    (S.canonicalPreprocessedShape).detachedScalar
        (S.canonicalSample ξ) j =
      S.detachedScalarFromBlock j (S.rawDetachedBlock ξ j) := by
  classical
  unfold PreprocessedFactorShape.detachedScalar detachedScalarFromBlock
  apply Fintype.sum_congr
  intro a
  exact S.canonical_detachedAmplitude_eq_fromBlock ξ j a

/-- The actual native core matrix is exactly the function of the core
primitive block defined above. -/
theorem coreOperatorMatrixNative_eq_fromBlock (ξ : S.RawSample) :
    S.coreOperatorMatrixNative ξ =
      S.coreMatrixFromBlock (S.rawCoreBlock ξ) := by
  classical
  ext row col
  unfold coreOperatorMatrixNative PreprocessedFactorShape.coreMatrix
    PreprocessedFactorShape.coreEntry coreMatrixFromBlock coreEntryFromBlock
  apply Fintype.sum_congr
  intro a
  split_ifs with h
  · exact S.canonical_coreAmplitude_eq_fromBlock ξ a
  · rfl

/-- Coordinate evaluation on a product measurable space is measurable. -/
theorem measurable_coreAmplitudeFromBlock
    (a : (S.canonicalPreprocessedShape).CoreTuple) :
    Measurable (fun x : S.CorePrimitiveCoord → ℝ =>
      S.coreAmplitudeFromBlock x a) := by
  classical
  unfold coreAmplitudeFromBlock
  fun_prop

/-- Each entry of the core matrix is a finite sum of finite products of
coordinate evaluations, hence Borel measurable. -/
theorem measurable_coreMatrixFromBlock :
    Measurable S.coreMatrixFromBlock := by
  classical
  change Measurable (fun x => fun row col => _)
  apply measurable_pi_lambda
  intro row
  apply measurable_pi_lambda
  intro col
  unfold coreMatrixFromBlock coreEntryFromBlock coreAmplitudeFromBlock
  apply Finset.measurable_sum
  intro a ha
  split_ifs <;> fun_prop

/-- Every detached amplitude is a finite product of coordinate evaluations. -/
theorem measurable_detachedAmplitudeFromBlock
    (j : S.DetachedComponent)
    (a : (S.canonicalPreprocessedShape).DetachedTuple j) :
    Measurable (fun x : S.DetachedPrimitiveCoord j → ℝ =>
      S.detachedAmplitudeFromBlock j x a) := by
  classical
  unfold detachedAmplitudeFromBlock
  fun_prop

/-- Every actual detached scalar is a finite sum of those products. -/
theorem measurable_detachedScalarFromBlock (j : S.DetachedComponent) :
    Measurable (S.detachedScalarFromBlock j) := by
  classical
  unfold detachedScalarFromBlock detachedAmplitudeFromBlock
  fun_prop

/-- The native finite matrix operator norm is continuous/measurable after the
matrix-valued core polynomial. -/
theorem measurable_coreNormFromBlock :
    Measurable (fun x : S.CorePrimitiveCoord → ℝ =>
      ‖S.coreMatrixFromBlock x‖) := by
  exact (S.measurable_coreMatrixFromBlock.norm)

/-- Absolute detached factors are measurable. -/
theorem measurable_abs_detachedScalarFromBlock
    (j : S.DetachedComponent) :
    Measurable (fun x : S.DetachedPrimitiveCoord j → ℝ =>
      |S.detachedScalarFromBlock j x|) := by
  exact (S.measurable_detachedScalarFromBlock j).abs

/-- The required bounded-Borel test identity for the actual native core
matrix and actual detached scalar sums, on the grouped product law.  The
functions `fc` and `fj` are arbitrary here because Mathlib's finite-product
integral identity is unconditional; bounded Borel tests are the intended
probabilistic specialization. -/
theorem integral_actual_core_detached_tests
    (ν : E → Measure ℝ) [∀ e : E, IsProbabilityMeasure (ν e)]
    (fc : Matrix
      ((S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).leftBoundary)
      ((S.canonicalPreprocessedShape).BoundaryTuple
        (S.canonicalPreprocessedShape).rightBoundary) ℝ → ℝ)
    (fj : ∀ j : S.DetachedComponent, ℝ → ℝ) :
    (∫ blocks,
        fc (S.coreMatrixFromBlock (blocks (Sum.inl ()))) *
          ∏ j : S.DetachedComponent,
            fj j (S.detachedScalarFromBlock j (blocks (Sum.inr j)))
      ∂S.groupedPrimitiveLaw ν) =
      (∫ x,
          fc (S.coreMatrixFromBlock x)
        ∂S.oneBlockLaw ν (Sum.inl ())) *
        ∏ j : S.DetachedComponent,
          ∫ x,
            fj j (S.detachedScalarFromBlock j x)
          ∂S.oneBlockLaw ν (Sum.inr j) := by
  classical
  simpa using S.integral_core_mul_detached_eq ν
    (fun x => fc (S.coreMatrixFromBlock x))
    (fun j x => fj j (S.detachedScalarFromBlock j x))

/-- In particular, the nonnegative factors that occur in the pointwise
operator-norm identity have an exact expectation product on the grouped law. -/
theorem integral_coreNorm_mul_absDetached_eq
    (ν : E → Measure ℝ) [∀ e : E, IsProbabilityMeasure (ν e)] :
    (∫ blocks,
        ‖S.coreMatrixFromBlock (blocks (Sum.inl ()))‖ *
          ∏ j : S.DetachedComponent,
            |S.detachedScalarFromBlock j (blocks (Sum.inr j))|
      ∂S.groupedPrimitiveLaw ν) =
      (∫ x, ‖S.coreMatrixFromBlock x‖
        ∂S.oneBlockLaw ν (Sum.inl ())) *
        ∏ j : S.DetachedComponent,
          ∫ x, |S.detachedScalarFromBlock j x|
            ∂S.oneBlockLaw ν (Sum.inr j) := by
  classical
  simpa using S.integral_actual_core_detached_tests ν
    (fun M => ‖M‖) (fun _ z => |z|)

/-- Reconstruct an actual `RawSample` from a grouped primitive sample by the
inverse measurable coordinate reindex. -/
def rawSampleOfBlocks
    (blocks : ∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) : S.RawSample :=
  S.unflattenRawSample (S.rawFlatToBlocksMeasurableEquiv.symm blocks)

/-- The reconstructed raw sample has exactly the prescribed core block. -/
theorem rawCoreBlock_rawSampleOfBlocks
    (blocks : ∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) :
    S.rawCoreBlock (S.rawSampleOfBlocks blocks) = blocks (Sum.inl ()) := by
  classical
  funext p
  have h := congrFun
    (congrFun
      (S.rawFlatToBlocksMeasurableEquiv.apply_symm_apply blocks)
      (Sum.inl ())) p
  change S.BlockCoord (Sum.inl ()) at p
  change S.rawFlatToBlocksMeasurableEquiv (S.rawFlatToBlocksMeasurableEquiv.symm blocks) (Sum.inl ()) p = _ at h
  rw [rawFlatToBlocksMeasurableEquiv_apply] at h
  exact h

/-- The reconstructed raw sample has exactly the prescribed detached block. -/
theorem rawDetachedBlock_rawSampleOfBlocks
    (blocks : ∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ)
    (j : S.DetachedComponent) :
    S.rawDetachedBlock (S.rawSampleOfBlocks blocks) j =
      blocks (Sum.inr j) := by
  classical
  funext p
  have h := congrFun
    (congrFun
      (S.rawFlatToBlocksMeasurableEquiv.apply_symm_apply blocks)
      (Sum.inr j)) p
  change S.BlockCoord (Sum.inr j) at p
  change S.rawFlatToBlocksMeasurableEquiv (S.rawFlatToBlocksMeasurableEquiv.symm blocks) (Sum.inr j) p = _ at h
  rw [rawFlatToBlocksMeasurableEquiv_apply] at h
  exact h

/-- Pointwise operator-norm factorization expressed on the grouped primitive
sample.  This uses the already-proved deterministic theorem; no probability
claim is hidden in this step. -/
theorem rawOperatorNorm_ofBlocks_eq
    (blocks : ∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) :
    ‖S.rawOperatorMatrix (S.rawSampleOfBlocks blocks)‖ =
      |(S.canonicalPreprocessedShape).unusedScalar *
          ∏ j : S.DetachedComponent,
            S.detachedScalarFromBlock j (blocks (Sum.inr j))| *
        ‖S.coreMatrixFromBlock (blocks (Sum.inl ()))‖ := by
  classical
  rw [S.rawOperatorMatrix_l2_opNorm_eq_native_core]
  unfold exactPreprocessingScalar
  rw [S.coreOperatorMatrixNative_eq_fromBlock]
  rw [S.rawCoreBlock_rawSampleOfBlocks]
  congr 2
  congr 1
  apply Fintype.prod_congr
  intro j
  rw [S.canonical_detachedScalar_eq_fromBlock]
  rw [S.rawDetachedBlock_rawSampleOfBlocks]

/-- The unused-middle scalar is nonnegative because it is a finite product of
natural cardinalities cast to `ℝ`. -/
theorem unusedScalar_nonneg :
    0 ≤ (S.canonicalPreprocessedShape).unusedScalar := by
  classical
  unfold PreprocessedFactorShape.unusedScalar
  positivity

/-- A form of the pointwise norm identity with all random scalar factors
made nonnegative.  This is the exact input for the `q = 1` expectation
factorization and for the general finite-q moment calculation. -/
theorem rawOperatorNorm_ofBlocks_eq_nonneg
    (blocks : ∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) :
    ‖S.rawOperatorMatrix (S.rawSampleOfBlocks blocks)‖ =
      (S.canonicalPreprocessedShape).unusedScalar *
        (∏ j : S.DetachedComponent,
          |S.detachedScalarFromBlock j (blocks (Sum.inr j))|) *
        ‖S.coreMatrixFromBlock (blocks (Sum.inl ()))‖ := by
  classical
  rw [S.rawOperatorNorm_ofBlocks_eq]
  rw [abs_mul, abs_of_nonneg S.unusedScalar_nonneg]
  rw [Finset.abs_prod]

#print axioms RawFactorShape.canonical_detachedScalar_eq_fromBlock
#print axioms RawFactorShape.coreOperatorMatrixNative_eq_fromBlock
#print axioms RawFactorShape.measurable_coreMatrixFromBlock
#print axioms RawFactorShape.measurable_detachedScalarFromBlock
#print axioms RawFactorShape.integral_actual_core_detached_tests
#print axioms RawFactorShape.rawOperatorNorm_ofBlocks_eq_nonneg

end GraphMatrixReplica.PaperR16.RawFactorShape
