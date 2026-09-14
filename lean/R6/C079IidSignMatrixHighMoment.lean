import R6.PaperRademacherMatrixDyadicMoment
import R6.PaperR16AnyOrderTraceDomination

/-! # The iid sign matrix: exact finite Gram moments

The missing high-moment inequality is reduced here to an exact count of
closed bipartite walks with even edge multiplicities.  The count estimate
needed for the dimension-free constant is a separate, open combinatorial
step; this file does not assert it.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The real iid `m × m` sign matrix, indexed by its independent bits. -/
def c079IidSignMatrix (m : ℕ) (w : Fin m × Fin m → Bool) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => paperSign (w (i, j))

/-- The two bipartite edges traversed at each position of a Gram cycle. -/
def c079IidWalkChoice {m q : ℕ}
    (rows cols : Fin q → Fin m) :
    Fin q → (Fin m × Fin m) × (Fin m × Fin m) :=
  fun t => ((rows t, cols t), (rows (finRotate q t), cols t))

/-- Exact count of even-edge closed Gram walks. -/
def c079IidEvenWalkCount (m q : ℕ) : ℝ :=
  by
    classical
    letI : BEq (Fin m × Fin m) := instBEqOfDecidableEq
    exact ∑ rows : Fin q → Fin m, ∑ cols : Fin q → Fin m,
      if ∀ e : Fin m × Fin m,
        Even ((rademacherPairEdgeWord (c079IidWalkChoice rows cols)).count e)
      then 1 else 0

/-- Independence removes precisely the Gram walks containing an edge an
odd number of times.  This identity also covers dimension zero. -/
theorem c079IidSignMatrix_gramTrace_mean_eq_evenWalkCount
    (m q : ℕ) (hq : 0 < q) :
    paperMean (fun w : Fin m × Fin m → Bool =>
      Matrix.trace ((c079IidSignMatrix m w *
        (c079IidSignMatrix m w).transpose) ^ q)) =
      c079IidEvenWalkCount m q := by
  classical
  simp_rw [matrix_gramTrace_pow_eq_sum_rowColCycles
    (c079IidSignMatrix m _) q hq]
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro rows _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro cols _
  simp only [c079IidSignMatrix]
  calc
    paperMean (fun w : Fin m × Fin m → Bool =>
        ∏ t : Fin q, paperSign (w (rows t, cols t)) *
          paperSign (w (rows (finRotate q t), cols t))) =
        paperMean (fun w : Fin m × Fin m → Bool =>
          ((rademacherPairEdgeWord (c079IidWalkChoice rows cols)).map
            (fun e => paperSign (w e))).prod * (1 : ℝ)) := by
      congr 1
      funext w
      simpa only [mul_one, c079IidWalkChoice] using
        (rademacherPairEdgeWord_signProduct
          (c079IidWalkChoice rows cols) w).symm
    _ = _ := by
      simpa only [] using
        (paperMean_rademacherPairEdgeWord_mul_const
          (c079IidWalkChoice rows cols) (1 : ℝ))

/-- The arbitrary-order operator-norm moment is at most the exact even-walk
count.  Bounding that count is the remaining high-moment gate. -/
theorem c079IidSignMatrix_normMoment_le_evenWalkCount
    (m q : ℕ) (hq : 0 < q) :
    paperMean (fun w : Fin m × Fin m → Bool =>
      ‖c079IidSignMatrix m w‖ ^ (2 * q)) ≤
      c079IidEvenWalkCount m q := by
  classical
  calc
    _ ≤ paperMean (fun w : Fin m × Fin m → Bool =>
        Matrix.trace ((c079IidSignMatrix m w *
          (c079IidSignMatrix m w).transpose) ^ q)) := by
      apply paperMean_mono
      intro w
      exact paperR16_matrix_l2_opNorm_pow_le_gramTrace
        (c079IidSignMatrix m w) q hq
    _ = _ := c079IidSignMatrix_gramTrace_mean_eq_evenWalkCount m q hq

/-- Exact remaining finite counting gate at the C079 dimension.  The
hypothesis is a combinatorial assertion about even closed walks, independent
of any operator norm. -/
theorem c079IidSignMatrix_highMoment_of_evenWalkCount_bound
    (q : ℕ) (hq : 0 < q)
    (hcount : c079IidEvenWalkCount (2 * q ^ 2) q ≤
      (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q)) :
    paperMean (fun w : Fin (2 * q ^ 2) × Fin (2 * q ^ 2) → Bool =>
      ‖c079IidSignMatrix (2 * q ^ 2) w‖ ^ (2 * q)) ≤
      (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q) :=
  (c079IidSignMatrix_normMoment_le_evenWalkCount
    (2 * q ^ 2) q hq).trans hcount

#print axioms c079IidSignMatrix_gramTrace_mean_eq_evenWalkCount
#print axioms c079IidSignMatrix_normMoment_le_evenWalkCount
#print axioms c079IidSignMatrix_highMoment_of_evenWalkCount_bound

end GraphMatrixReplica
