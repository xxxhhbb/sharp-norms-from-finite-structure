import GraphMatrix.RademacherMatchingContribution
import GraphMatrix.PairCoarseningEvenPartition

/-! # Column-canonical Rademacher matching contributions

Transposing every coefficient matrix exchanges the row and column variance
contractions.  We use that exact symmetry to define and evaluate the
column-canonical matching class.  Only the row- and column-canonical classes
are treated; no assertion is made about arbitrary crossing matchings.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- On a nonempty cycle, pair the second occurrence at `k` with the first
occurrence at the next position.  Composing with the adjacent-position
encoding makes this a perfect matching of the `2(p+1)` word positions. -/
def rademacherColumnCanonicalMatching (p : ℕ) :
    Fin (p + 1) × Bool ≃ Fin ((p + 1) * 2) :=
  (leftPairEquiv p).trans (rademacherCanonicalMatching (p + 1))

@[simp] theorem rademacherColumnCanonicalMatching_false
    {p : ℕ} (t : Fin (p + 1)) :
    rademacherColumnCanonicalMatching p (t, false) =
      rademacherCanonicalMatching (p + 1) (t, true) := by
  simp [rademacherColumnCanonicalMatching, leftPairEquiv_false]

@[simp] theorem rademacherColumnCanonicalMatching_true
    {p : ℕ} (t : Fin (p + 1)) :
    rademacherColumnCanonicalMatching p (t, true) =
      rademacherCanonicalMatching (p + 1)
        (finRotate (p + 1) t, false) := by
  simp [rademacherColumnCanonicalMatching, leftPairEquiv_true]

/-- The column-side variance matrix. -/
def rademacherColumnVariance
    {ε ι κ : Type} [Fintype ε] [Fintype ι]
    (A : ε → Matrix ι κ ℝ) : Matrix κ κ ℝ :=
  ∑ e : ε, (A e).transpose * A e

/-- Column variance is row variance after transposing every coefficient. -/
theorem rademacherRowVariance_transposeFamily
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) :
    rademacherRowVariance (fun e => (A e).transpose) =
      rademacherColumnVariance A := by
  classical
  simp [rademacherRowVariance, rademacherColumnVariance]

/-- The column-variance matrix is positive semidefinite. -/
theorem rademacherColumnVariance_posSemidef
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) :
    (rademacherColumnVariance A).PosSemidef := by
  rw [← rademacherRowVariance_transposeFamily]
  exact rademacherRowVariance_posSemidef (fun e => (A e).transpose)

/-- The column-canonical coefficient contribution, defined by the exact
row/column transpose symmetry of the Gram-cycle expansion. -/
def rademacherColumnCanonicalMatchingContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) : ℝ :=
  rademacherCanonicalMatchingContribution (r := r)
    (fun e => (A e).transpose)

/-- The column-canonical contribution is exactly the trace power of the
column-variance matrix. -/
theorem rademacherColumnCanonicalMatchingContribution_eq_trace_columnVariance_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    rademacherColumnCanonicalMatchingContribution (r := r) A =
      Matrix.trace ((rademacherColumnVariance A) ^ r) := by
  unfold rademacherColumnCanonicalMatchingContribution
  rw [rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow
    (fun e => (A e).transpose) r hr]
  rw [rademacherRowVariance_transposeFamily]

/-- Every dyadic column-canonical contribution is nonnegative. -/
theorem rademacherColumnCanonicalMatchingContribution_dyadic_nonneg
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (q : ℕ) :
    0 ≤ rademacherColumnCanonicalMatchingContribution (r := 2 ^ q) A := by
  rw [rademacherColumnCanonicalMatchingContribution_eq_trace_columnVariance_pow
    A (2 ^ q) (by positivity)]
  exact (matrix_posSemidef_pow_two_pow
    (rademacherColumnVariance A)
    (rademacherColumnVariance_posSemidef A) q).trace_nonneg

/-- The two canonical classes are summarized by the larger of their two
variance trace moments. -/
theorem max_rowColumnCanonicalContributions_eq_maxVarianceTraces
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    max (rademacherCanonicalMatchingContribution (r := r) A)
        (rademacherColumnCanonicalMatchingContribution (r := r) A) =
      max (Matrix.trace ((rademacherRowVariance A) ^ r))
        (Matrix.trace ((rademacherColumnVariance A) ^ r)) := by
  rw [rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow A r hr,
    rademacherColumnCanonicalMatchingContribution_eq_trace_columnVariance_pow
      A r hr]

/-- Each of the two proven canonical classes is bounded by the common
max-variance trace endpoint. -/
theorem rowCanonicalContribution_le_maxVarianceTrace
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    rademacherCanonicalMatchingContribution (r := r) A ≤
      max (Matrix.trace ((rademacherRowVariance A) ^ r))
        (Matrix.trace ((rademacherColumnVariance A) ^ r)) := by
  rw [rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow A r hr]
  exact le_max_left _ _

theorem columnCanonicalContribution_le_maxVarianceTrace
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    rademacherColumnCanonicalMatchingContribution (r := r) A ≤
      max (Matrix.trace ((rademacherRowVariance A) ^ r))
        (Matrix.trace ((rademacherColumnVariance A) ^ r)) := by
  rw [rademacherColumnCanonicalMatchingContribution_eq_trace_columnVariance_pow
    A r hr]
  exact le_max_right _ _

/-- The standard row/column variance norm endpoint appearing in matrix
Khintchine estimates.  This definition itself contains no Khintchine claim. -/
def rademacherVarianceNormMax
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) : ℝ :=
  max ‖rademacherRowVariance A‖ ‖rademacherColumnVariance A‖

theorem rowVariance_l2_opNorm_le_varianceNormMax
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    ‖rademacherRowVariance A‖ ≤ rademacherVarianceNormMax A :=
  le_max_left _ _

theorem columnVariance_l2_opNorm_le_varianceNormMax
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    ‖rademacherColumnVariance A‖ ≤ rademacherVarianceNormMax A :=
  le_max_right _ _

theorem rademacherVarianceNormMax_nonneg
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    0 ≤ rademacherVarianceNormMax A :=
  (norm_nonneg _).trans (rowVariance_l2_opNorm_le_varianceNormMax A)


end GraphMatrixReplica
