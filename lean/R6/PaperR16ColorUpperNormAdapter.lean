import R6.PaperR16ColorFiberTypedBridge
import R6.PaperR16FixedColorExpectedNorm
import R6.PaperR16GlobalColorL1

/-! # Direct R16 color upper transfer at expected operator norm

Each ambient coloring determines possibly empty role fibers.  The actual
colored paper matrix is their zero-padded typed matrix.  Its expected norm is
bounded by the independent-edge typed expected norm for those exact fiber
sizes.  Combining this with the finite color sum gives a direct, unbalanced
fiber average upper bound.  No balanced-dimension comparison is asserted.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Pointwise norm comparison for the actual full-size colored paper matrix. -/
theorem paperR16_coloredNorm_le_fiberPartite
    (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (color : Fin n → Fin G.roles) :
    ‖paperR16ColoredGraphMatrix G n w color‖ ≤
      ‖c027PartiteBoundaryMatrixReal G
        (paperR16ColorClassDimension G n color)
        ((paperR16ColorClassRoleColoring G n color).readJointEdgeSignSample w)‖ := by
  let C := paperR16ColorClassRoleColoring G n color
  let dimension := paperR16ColorClassDimension G n color
  calc
    ‖paperR16ColoredGraphMatrix G n w color‖ =
        ‖C.zeroPaddedBoundaryMatrix
          (paperRoleColoredBoundaryMatrix G dimension n C w)‖ := by
      rw [paperR16ColoredGraphMatrix_eq_fiber_zeroPadded]
    _ ≤ ‖paperRoleColoredBoundaryMatrix G dimension n C w‖ :=
      C.zeroPaddedBoundaryMatrix_norm_le _
    _ = ‖c027PartiteBoundaryMatrixReal G dimension
          (C.readJointEdgeSignSample w)‖ := by
      rw [C.coloredBoundaryMatrix_eq_readTyped w]
      rfl

/-- Fixed ambient coloring: the colored paper matrix has no larger expected
operator norm than its independent-edge typed fiber model. -/
theorem paperR16_coloredExpectedNorm_le_fiberPartite
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles) :
    paperMean (fun w : PaperNoise n =>
      ‖paperR16ColoredGraphMatrix G n w color‖) ≤
        c027PartiteExpectedOperatorNorm G
          (paperR16ColorClassDimension G n color) := by
  let C := paperR16ColorClassRoleColoring G n color
  let dimension := paperR16ColorClassDimension G n color
  calc
    paperMean (fun w : PaperNoise n =>
        ‖paperR16ColoredGraphMatrix G n w color‖) ≤
        paperMean (fun w : PaperNoise n =>
          ‖paperRoleColoredBoundaryMatrix G dimension n C w‖) := by
      apply paperMean_mono
      intro w
      rw [paperR16ColoredGraphMatrix_eq_fiber_zeroPadded]
      exact C.zeroPaddedBoundaryMatrix_norm_le _
    _ = c027PartiteExpectedOperatorNorm G dimension :=
      C.paperMean_coloredBoundaryNorm_eq_partite

/-- Direct R16 expected-norm upper reduction: the global model is bounded
by the finite sum of typed independent-edge models over all color-fiber
size vectors, with the exact retention-multiplicity coefficient. -/
theorem paperR16_globalExpectedNorm_le_sum_fiberPartite
    (G : PaperShape) (n : ℕ) (hroles : 0 < G.roles) :
    c027PaperExpectedOperatorNorm G n ≤
      ((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹ *
        ∑ color : Fin n → Fin G.roles,
          c027PartiteExpectedOperatorNorm G
            (paperR16ColorClassDimension G n color) := by
  unfold c027PaperExpectedOperatorNorm
  calc
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        ((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹ *
          ∑ color : Fin n → Fin G.roles,
            paperMean (fun w : PaperNoise n =>
              ‖paperR16ColoredGraphMatrix G n w color‖) :=
      paperR16_globalExpectedNorm_le_sum_colored G n hroles
    _ ≤ ((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹ *
          ∑ color : Fin n → Fin G.roles,
            c027PartiteExpectedOperatorNorm G
              (paperR16ColorClassDimension G n color) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro color _
        exact paperR16_coloredExpectedNorm_le_fiberPartite G n color
      · positivity

#print axioms paperR16_coloredNorm_le_fiberPartite
#print axioms paperR16_coloredExpectedNorm_le_fiberPartite
#print axioms paperR16_globalExpectedNorm_le_sum_fiberPartite

end GraphMatrixReplica
