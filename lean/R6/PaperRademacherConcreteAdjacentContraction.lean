import R6.PaperRademacherAdjacentContraction

/-! # Concrete variance envelopes for adjacent contraction

This file proves the spectral contraction inequality needed by the two
canonical coefficient-cycle contributions.  The resulting row and column
trace envelopes satisfy the abstract adjacent-deletion interface for every
recursive noncrossing matching.  They are deliberately named envelopes: the
identification of a general recursive matching with its original nested
coefficient-cycle contribution is a separate combinatorial-matrix theorem.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- A canonical witness in every Catalan order, used only to instantiate
matching-independent trace envelopes. -/
def rademacherFullyAdjacentNoncrossing :
  ∀ n : ℕ, RademacherNoncrossingMatching n
  | 0 => .empty
  | n + 1 => by
      simpa using RademacherNoncrossingMatching.node .empty
        (rademacherFullyAdjacentNoncrossing n)

/-- Spectral formula for every natural trace power of a real positive
semidefinite matrix. -/
theorem trace_pow_eq_sum_eigenvalues_pow_of_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (n : ℕ) :
    Matrix.trace (S ^ n) =
      ∑ i : ι, (hS.isHermitian.eigenvalues i) ^ n := by
  let U := hS.isHermitian.eigenvectorUnitary
  let eigen := hS.isHermitian.eigenvalues
  have hdiag : S = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
      (Matrix.diagonal eigen) := by
    simpa [U, eigen] using hS.isHermitian.spectral_theorem
  calc
    Matrix.trace (S ^ n) = Matrix.trace
        ((Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
          (Matrix.diagonal eigen)) ^ n) := by rw [hdiag]
    _ = Matrix.trace (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
          ((Matrix.diagonal eigen) ^ n)) := by rw [map_pow]
    _ = Matrix.trace ((Matrix.diagonal eigen) ^ n) := by
      rw [Unitary.conjStarAlgAut_apply, ← Matrix.trace_mul_cycle]
      simp only [mul_assoc, Unitary.coe_star_mul_self, mul_one]
    _ = ∑ i : ι, eigen i ^ n := by
      rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
      simp only [Pi.pow_apply]
    _ = ∑ i : ι, (hS.isHermitian.eigenvalues i) ^ n := by rfl

/-- Multiplying a positive semidefinite trace power by one further copy costs
at most one Euclidean operator-norm factor. -/
theorem trace_posSemidef_pow_succ_le_norm_mul_trace_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (n : ℕ) :
    Matrix.trace (S ^ (n + 1)) ≤ ‖S‖ * Matrix.trace (S ^ n) := by
  rw [trace_pow_eq_sum_eigenvalues_pow_of_posSemidef S hS,
    trace_pow_eq_sum_eigenvalues_pow_of_posSemidef S hS]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hlam : 0 ≤ hS.isHermitian.eigenvalues i := hS.eigenvalues_nonneg i
  have hlamnorm : hS.isHermitian.eigenvalues i ≤ ‖S‖ := by
    have hdiagNorm : ‖Matrix.diagonal hS.isHermitian.eigenvalues‖ = ‖S‖ := by
      let U := hS.isHermitian.eigenvectorUnitary
      have hdiag : S = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
          (Matrix.diagonal hS.isHermitian.eigenvalues) := by
        simpa [U] using hS.isHermitian.spectral_theorem
      calc
        ‖Matrix.diagonal hS.isHermitian.eigenvalues‖ =
            ‖Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
              (Matrix.diagonal hS.isHermitian.eigenvalues)‖ := by
          rw [Unitary.conjStarAlgAut_apply]
          simp only [← Unitary.coe_star,
            CStarRing.norm_mul_coe_unitary,
            CStarRing.norm_coe_unitary_mul]
        _ = ‖S‖ := congrArg norm hdiag.symm
    calc
      hS.isHermitian.eigenvalues i = ‖hS.isHermitian.eigenvalues i‖ := by
        exact (Real.norm_of_nonneg hlam).symm
      _ ≤ ‖hS.isHermitian.eigenvalues‖ :=
        norm_le_pi_norm hS.isHermitian.eigenvalues i
      _ = ‖Matrix.diagonal hS.isHermitian.eigenvalues‖ := by
        symm
        exact Matrix.l2_opNorm_diagonal _
      _ = ‖S‖ := hdiagNorm
  calc
    hS.isHermitian.eigenvalues i ^ (n + 1) =
        hS.isHermitian.eigenvalues i *
          hS.isHermitian.eigenvalues i ^ n := by rw [pow_succ']
    _ ≤ ‖S‖ * hS.isHermitian.eigenvalues i ^ n :=
      mul_le_mul_of_nonneg_right hlamnorm (pow_nonneg hlam n)

/-- The row-variance trace envelope.  It is independent of the recursive
matching because it is the canonical comparison quantity, not an assertion
that all matching contributions are equal. -/
def rademacherRowTraceEnvelope
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (n : ℕ)
    (_M : RademacherNoncrossingMatching n) : ℝ :=
  Matrix.trace ((rademacherRowVariance A) ^ n)

/-- The row trace envelope obeys the concrete adjacent contraction interface. -/
theorem rademacherRowTraceEnvelope_adjacentContractionBound
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) :
    RademacherAdjacentContractionBound (rademacherRowTraceEnvelope A)
      ‖rademacherRowVariance A‖ := by
  intro n m i M M' hdelete
  have hn : n = m + 1 := hdelete.pairCount
  subst n
  simpa [rademacherRowTraceEnvelope] using
    (trace_posSemidef_pow_succ_le_norm_mul_trace_pow
    (rademacherRowVariance A) (rademacherRowVariance_posSemidef A) m
    )

/-- Hence every recursive noncrossing index has the same rigorous row
variance envelope bound. -/
theorem rademacherRowTraceEnvelope_le_card_mul_norm_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    rademacherRowTraceEnvelope A n M ≤
      ‖rademacherRowVariance A‖ ^ n * Fintype.card ι := by
  apply noncrossingContribution_le_variance_pow
    (rademacherRowTraceEnvelope A) ‖rademacherRowVariance A‖
      (Fintype.card ι)
  · exact norm_nonneg _
  · simp [rademacherRowTraceEnvelope, Matrix.trace]
  · exact rademacherRowTraceEnvelope_adjacentContractionBound A

/-- For positive order, the row envelope is exactly the already-expanded
row-canonical coefficient-cycle contribution. -/
theorem rademacherCanonicalMatchingContribution_eq_rowTraceEnvelope
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (n : ℕ) (hn : 0 < n)
    (M : RademacherNoncrossingMatching n) :
    rademacherCanonicalMatchingContribution (r := n) A =
      rademacherRowTraceEnvelope A n M := by
  simpa [rademacherRowTraceEnvelope] using
    (rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow
      A n hn)

/-- The actual positive-order row-canonical coefficient-cycle contribution,
with the mathematically necessary dimension-valued zeroth term.  The raw
empty coefficient cycle has value `1`, whereas the trace-power envelope has
zeroth term `trace I = card ι`; the padding makes that distinction explicit. -/
def rademacherPaddedRowCanonicalContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (n : ℕ)
    (_M : RademacherNoncrossingMatching n) : ℝ :=
  if n = 0 then Fintype.card ι
  else rademacherCanonicalMatchingContribution (r := n) A

theorem rademacherPaddedRowCanonicalContribution_eq_traceEnvelope
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    rademacherPaddedRowCanonicalContribution A n M =
      rademacherRowTraceEnvelope A n M := by
  cases n with
  | zero =>
      simp [rademacherPaddedRowCanonicalContribution,
        rademacherRowTraceEnvelope, Matrix.trace]
  | succ n =>
      simp only [rademacherPaddedRowCanonicalContribution, Nat.succ_ne_zero,
        ↓reduceIte]
      exact rademacherCanonicalMatchingContribution_eq_rowTraceEnvelope
        A (n + 1) (by omega) M

/-- A concrete `RademacherAdjacentContractionBound` for the padded actual
row-canonical coefficient-cycle family. -/
theorem rademacherPaddedRowCanonical_adjacentContractionBound
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) :
    RademacherAdjacentContractionBound
      (rademacherPaddedRowCanonicalContribution A)
      ‖rademacherRowVariance A‖ := by
  intro n m i M M' hdelete
  rw [rademacherPaddedRowCanonicalContribution_eq_traceEnvelope,
    rademacherPaddedRowCanonicalContribution_eq_traceEnvelope]
  exact rademacherRowTraceEnvelope_adjacentContractionBound A hdelete

/-- Column-side counterpart of the canonical trace envelope. -/
def rademacherColumnTraceEnvelope
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ)
    (_M : RademacherNoncrossingMatching n) : ℝ :=
  Matrix.trace ((rademacherColumnVariance A) ^ n)

theorem rademacherColumnTraceEnvelope_adjacentContractionBound
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    RademacherAdjacentContractionBound (rademacherColumnTraceEnvelope A)
      ‖rademacherColumnVariance A‖ := by
  intro n m i M M' hdelete
  have hn : n = m + 1 := hdelete.pairCount
  subst n
  exact trace_posSemidef_pow_succ_le_norm_mul_trace_pow
    (rademacherColumnVariance A) (rademacherColumnVariance_posSemidef A) m

theorem rademacherColumnTraceEnvelope_le_card_mul_norm_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    rademacherColumnTraceEnvelope A n M ≤
      ‖rademacherColumnVariance A‖ ^ n * Fintype.card κ := by
  apply noncrossingContribution_le_variance_pow
    (rademacherColumnTraceEnvelope A) ‖rademacherColumnVariance A‖
      (Fintype.card κ)
  · exact norm_nonneg _
  · simp [rademacherColumnTraceEnvelope, Matrix.trace]
  · exact rademacherColumnTraceEnvelope_adjacentContractionBound A

theorem rademacherColumnCanonicalMatchingContribution_eq_columnTraceEnvelope
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ) (hn : 0 < n)
    (M : RademacherNoncrossingMatching n) :
    rademacherColumnCanonicalMatchingContribution (r := n) A =
      rademacherColumnTraceEnvelope A n M := by
  simpa [rademacherColumnTraceEnvelope] using
    (rademacherColumnCanonicalMatchingContribution_eq_trace_columnVariance_pow
      A n hn)

def rademacherPaddedColumnCanonicalContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ)
    (_M : RademacherNoncrossingMatching n) : ℝ :=
  if n = 0 then Fintype.card κ
  else rademacherColumnCanonicalMatchingContribution (r := n) A

theorem rademacherPaddedColumnCanonicalContribution_eq_traceEnvelope
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    rademacherPaddedColumnCanonicalContribution A n M =
      rademacherColumnTraceEnvelope A n M := by
  cases n with
  | zero =>
      simp [rademacherPaddedColumnCanonicalContribution,
        rademacherColumnTraceEnvelope, Matrix.trace]
  | succ n =>
      simp only [rademacherPaddedColumnCanonicalContribution,
        Nat.succ_ne_zero, ↓reduceIte]
      exact rademacherColumnCanonicalMatchingContribution_eq_columnTraceEnvelope
        A (n + 1) (by omega) M

theorem rademacherPaddedColumnCanonical_adjacentContractionBound
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    RademacherAdjacentContractionBound
      (rademacherPaddedColumnCanonicalContribution A)
      ‖rademacherColumnVariance A‖ := by
  intro n m i M M' hdelete
  rw [rademacherPaddedColumnCanonicalContribution_eq_traceEnvelope,
    rademacherPaddedColumnCanonicalContribution_eq_traceEnvelope]
  exact rademacherColumnTraceEnvelope_adjacentContractionBound A hdelete

/-- Both canonical coefficient-cycle classes are controlled by the common
row/column variance norm endpoint, with only the appropriate ambient trace
dimension remaining. -/
theorem rowCanonicalContribution_le_varianceNormMax_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ) (hn : 0 < n) :
    rademacherCanonicalMatchingContribution (r := n) A ≤
      rademacherVarianceNormMax A ^ n * Fintype.card ι := by
  let M : RademacherNoncrossingMatching n :=
    rademacherFullyAdjacentNoncrossing n
  rw [rademacherCanonicalMatchingContribution_eq_rowTraceEnvelope A n hn M]
  refine (rademacherRowTraceEnvelope_le_card_mul_norm_pow A M).trans ?_
  gcongr
  exact rowVariance_l2_opNorm_le_varianceNormMax A

theorem columnCanonicalContribution_le_varianceNormMax_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (n : ℕ) (hn : 0 < n) :
    rademacherColumnCanonicalMatchingContribution (r := n) A ≤
      rademacherVarianceNormMax A ^ n * Fintype.card κ := by
  let M : RademacherNoncrossingMatching n :=
    rademacherFullyAdjacentNoncrossing n
  rw [rademacherColumnCanonicalMatchingContribution_eq_columnTraceEnvelope
    A n hn M]
  refine (rademacherColumnTraceEnvelope_le_card_mul_norm_pow A M).trans ?_
  gcongr
  exact columnVariance_l2_opNorm_le_varianceNormMax A

#print axioms trace_posSemidef_pow_succ_le_norm_mul_trace_pow
#print axioms rademacherRowTraceEnvelope_adjacentContractionBound
#print axioms rademacherRowTraceEnvelope_le_card_mul_norm_pow
#print axioms rademacherColumnTraceEnvelope_adjacentContractionBound
#print axioms rademacherPaddedRowCanonical_adjacentContractionBound
#print axioms rademacherPaddedColumnCanonical_adjacentContractionBound
#print axioms rowCanonicalContribution_le_varianceNormMax_pow
#print axioms columnCanonicalContribution_le_varianceNormMax_pow

end GraphMatrixReplica
