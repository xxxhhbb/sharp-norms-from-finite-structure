import R6.PaperEdgeOrientationDecomposition
import R6.PaperTraceNormBridge
import Mathlib.Algebra.Order.Chebyshev

/-! # The unconditional orientation endpoint before NCK

This file isolates the analytic loss caused by the BLNvH orientation
decomposition.  It proves the operator-norm triangle inequality, its finite
noise average, and the corresponding power-moment inequality.  No
noncommutative Khintchine estimate is assumed: the final conditional lemmas
take any proposed per-piece estimate as an explicit hypothesis.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Pointwise operator-norm triangle inequality for the exact orientation
decomposition of the original globally injective paper matrix. -/
theorem paperGraphMatrix_l2_opNorm_le_sum_oriented
    (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    ‖paperGraphMatrix G n w‖ ≤
      ∑ orientation : Fin G.edges → Bool,
        ‖paperOrientedGraphMatrix G n orientation w‖ := by
  rw [← paperSum_orientedGraphMatrix_eq G n w]
  exact norm_sum_le _ _

/-- The same orientation triangle inequality after finite uniform averaging
over the paper noise. -/
theorem paperGraphMatrix_l2_opNorm_mean_le_sum_orientedMean
    (G : PaperShape) (n : ℕ) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      ∑ orientation : Fin G.edges → Bool,
        paperMean (fun w : PaperNoise n =>
          ‖paperOrientedGraphMatrix G n orientation w‖) := by
  calc
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        paperMean (fun w : PaperNoise n =>
          ∑ orientation : Fin G.edges → Bool,
            ‖paperOrientedGraphMatrix G n orientation w‖) := by
      apply paperMean_mono
      exact fun w => paperGraphMatrix_l2_opNorm_le_sum_oriented G n w
    _ = ∑ orientation : Fin G.edges → Bool,
          paperMean (fun w : PaperNoise n =>
            ‖paperOrientedGraphMatrix G n orientation w‖) :=
      paperMean_sum _

/-- Multiplication by a fixed nonnegative or signed scalar commutes with the
finite uniform average. -/
theorem paperMean_const_mul
    {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    paperMean (fun a => c * f a) = c * paperMean f := by
  unfold paperMean
  rw [← Finset.mul_sum]
  ring

/-- Raising the orientation triangle bound to the positive integer power
`p + 1` costs at most `number_of_orientations ^ p`.  This is the finite
Jensen/Hölder loss, with no probabilistic or NCK input. -/
theorem paperGraphMatrix_l2_opNorm_pow_le_oriented_sum
    (G : PaperShape) (n p : ℕ) (w : PaperNoise n) :
    ‖paperGraphMatrix G n w‖ ^ (p + 1) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) ^ p *
        ∑ orientation : Fin G.edges → Bool,
          ‖paperOrientedGraphMatrix G n orientation w‖ ^ (p + 1) := by
  calc
    ‖paperGraphMatrix G n w‖ ^ (p + 1) ≤
        (∑ orientation : Fin G.edges → Bool,
          ‖paperOrientedGraphMatrix G n orientation w‖) ^ (p + 1) := by
      gcongr
      exact paperGraphMatrix_l2_opNorm_le_sum_oriented G n w
    _ ≤ (Fintype.card (Fin G.edges → Bool) : ℝ) ^ p *
          ∑ orientation : Fin G.edges → Bool,
            ‖paperOrientedGraphMatrix G n orientation w‖ ^ (p + 1) := by
      simpa using
        (pow_sum_le_card_mul_sum_pow
          (s := Finset.univ)
          (f := fun orientation : Fin G.edges → Bool =>
            ‖paperOrientedGraphMatrix G n orientation w‖)
          (fun orientation _ => norm_nonneg
            (paperOrientedGraphMatrix G n orientation w)) p)

/-- Finite-noise averaged form of the powered orientation reduction. -/
theorem paperGraphMatrix_l2_opNorm_pow_mean_le_orientedMomentSum
    (G : PaperShape) (n p : ℕ) :
    paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix G n w‖ ^ (p + 1)) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) ^ p *
        ∑ orientation : Fin G.edges → Bool,
          paperMean (fun w : PaperNoise n =>
            ‖paperOrientedGraphMatrix G n orientation w‖ ^ (p + 1)) := by
  calc
    paperMean (fun w : PaperNoise n =>
        ‖paperGraphMatrix G n w‖ ^ (p + 1)) ≤
        paperMean (fun w : PaperNoise n =>
          (Fintype.card (Fin G.edges → Bool) : ℝ) ^ p *
            ∑ orientation : Fin G.edges → Bool,
              ‖paperOrientedGraphMatrix G n orientation w‖ ^ (p + 1)) := by
      apply paperMean_mono
      exact fun w => paperGraphMatrix_l2_opNorm_pow_le_oriented_sum G n p w
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) ^ p *
          paperMean (fun w : PaperNoise n =>
            ∑ orientation : Fin G.edges → Bool,
              ‖paperOrientedGraphMatrix G n orientation w‖ ^ (p + 1)) := by
      exact paperMean_const_mul _ _
    _ = (Fintype.card (Fin G.edges → Bool) : ℝ) ^ p *
          ∑ orientation : Fin G.edges → Bool,
            paperMean (fun w : PaperNoise n =>
              ‖paperOrientedGraphMatrix G n orientation w‖ ^ (p + 1)) := by
      rw [paperMean_sum]

/-- A transparent interface for any future piecewise NCK or flattening
estimate.  Such an estimate is not hidden here: it must be supplied, one
orientation at a time, as the explicit hypothesis `hPiece`. -/
theorem paperGraphMatrix_l2_opNorm_pow_mean_le_of_orientedMomentBounds
    (G : PaperShape) (n p : ℕ)
    (bound : (Fin G.edges → Bool) → ℝ)
    (hPiece : ∀ orientation,
      paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖ ^ (p + 1)) ≤
        bound orientation) :
    paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix G n w‖ ^ (p + 1)) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) ^ p *
        ∑ orientation, bound orientation := by
  refine (paperGraphMatrix_l2_opNorm_pow_mean_le_orientedMomentSum
    G n p).trans ?_
  gcongr with orientation
  exact hPiece orientation

/-- At dyadic even moments, each oriented piece can unconditionally be
replaced by its matching Gram trace moment.  This is the exact handoff point
at which a genuine iterated NCK/flattening theorem would need to improve the
right-hand side. -/
theorem paperGraphMatrix_l2_opNorm_dyadicMoment_mean_le_orientedTraceSum
    (G : PaperShape) (n q : ℕ) :
    paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix G n w‖ ^ (2 * 2 ^ q)) ≤
      (Fintype.card (Fin G.edges → Bool) : ℝ) ^ (2 * 2 ^ q - 1) *
        ∑ orientation : Fin G.edges → Bool,
          paperMean (fun w : PaperNoise n =>
            Matrix.trace ((paperOrientedGraphMatrix G n orientation w *
              (paperOrientedGraphMatrix G n orientation w).transpose) ^
                (2 ^ q))) := by
  have hmoment : 2 * 2 ^ q - 1 + 1 = 2 * 2 ^ q := by
    have hpos : 0 < 2 * 2 ^ q := by positivity
    omega
  have horient :
      paperMean (fun w : PaperNoise n =>
        ‖paperGraphMatrix G n w‖ ^ (2 * 2 ^ q)) ≤
        (Fintype.card (Fin G.edges → Bool) : ℝ) ^ (2 * 2 ^ q - 1) *
          ∑ orientation : Fin G.edges → Bool,
            paperMean (fun w : PaperNoise n =>
              ‖paperOrientedGraphMatrix G n orientation w‖ ^
                (2 * 2 ^ q)) := by
    simpa [hmoment] using
      (paperGraphMatrix_l2_opNorm_pow_mean_le_orientedMomentSum
        G n (2 * 2 ^ q - 1))
  refine horient.trans ?_
  gcongr with orientation
  apply paperMean_mono
  intro w
  exact matrix_l2_opNorm_pow_dyadic_le_gramTrace
    (paperOrientedGraphMatrix G n orientation w) q

#print axioms paperGraphMatrix_l2_opNorm_le_sum_oriented
#print axioms paperGraphMatrix_l2_opNorm_mean_le_sum_orientedMean
#print axioms paperMean_const_mul
#print axioms paperGraphMatrix_l2_opNorm_pow_le_oriented_sum
#print axioms paperGraphMatrix_l2_opNorm_pow_mean_le_orientedMomentSum
#print axioms
  paperGraphMatrix_l2_opNorm_pow_mean_le_of_orientedMomentBounds
#print axioms
  paperGraphMatrix_l2_opNorm_dyadicMoment_mean_le_orientedTraceSum

end GraphMatrixReplica
