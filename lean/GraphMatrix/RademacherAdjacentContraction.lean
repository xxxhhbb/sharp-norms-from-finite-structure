import GraphMatrix.RademacherNoncrossingMatching

/-! # Adjacent-pair contraction for noncrossing matchings

The two local identities below are the matrix contractions produced by the
two possible adjacent positions in the alternating Gram word.  The final
theorems isolate the sole product-law statement for a full contribution
argument: prove that deleting the adjacent pair bounds (or equals) the source
contribution by one variance factor times the reduced contribution.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Summing an adjacent pair that shares its column coordinate contracts to
one entry of the row-variance matrix. -/
theorem sum_adjacentRowPair_mul_const
    {ε ι κ : Type} [Fintype ε] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) (i j : ι) (z : ℝ) :
    (∑ col : κ, ∑ e : ε,
      (A e i col * A e j col) * z) =
      rademacherRowVariance A i j * z := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp [rademacherRowVariance, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Summing an adjacent pair that shares its row coordinate contracts to one
entry of the column-variance matrix. -/
theorem sum_adjacentColumnPair_mul_const
    {ε ι κ : Type} [Fintype ε] [Fintype ι]
    (A : ε → Matrix ι κ ℝ) (i j : κ) (z : ℝ) :
    (∑ row : ι, ∑ e : ε,
      (A e row i * A e row j) * z) =
      rademacherColumnVariance A i j * z := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp [rademacherColumnVariance, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Minimal one-step interface required to contract a concrete contribution
along an adjacent-pair deletion certificate. -/
def RademacherAdjacentContractionBound
    (contribution : ∀ n, RademacherNoncrossingMatching n → ℝ)
    (varianceFactor : ℝ) : Prop :=
  ∀ {n m i : ℕ}
    {M : RademacherNoncrossingMatching n}
    {M' : RademacherNoncrossingMatching m},
    M.DeletesAdjacent i M' →
      contribution n M ≤ varianceFactor * contribution m M'

/-- The equality-strength version of the adjacent contraction interface. -/
def RademacherAdjacentContractionExact
    (contribution : ∀ n, RademacherNoncrossingMatching n → ℝ)
    (varianceFactor : ℝ) : Prop :=
  ∀ {n m i : ℕ}
    {M : RademacherNoncrossingMatching n}
    {M' : RademacherNoncrossingMatching m},
    M.DeletesAdjacent i M' →
      contribution n M = varianceFactor * contribution m M'

/-- Iterating a one-step adjacent-pair contraction bounds every recursively
noncrossing contribution by one variance factor per pair. -/
theorem noncrossingContribution_le_variance_pow
    (contribution : ∀ n, RademacherNoncrossingMatching n → ℝ)
    (varianceFactor baseBound : ℝ)
    (hvariance : 0 ≤ varianceFactor)
    (hbase : contribution 0 .empty ≤ baseBound)
    (hcontract : RademacherAdjacentContractionBound contribution varianceFactor)
    {n : ℕ} (M : RademacherNoncrossingMatching n) :
    contribution n M ≤ varianceFactor ^ n * baseBound := by
  induction n with
  | zero =>
      cases M
      simpa using hbase
  | succ n ih =>
      obtain ⟨i, M', hdelete, -, -⟩ :=
        RademacherNoncrossingMatching.exists_adjacentMatchedPair_and_delete M
      have hstep : contribution (Nat.succ n) M ≤
          varianceFactor * contribution n M' :=
        hcontract hdelete
      have hind : varianceFactor * contribution n M' ≤
          varianceFactor * (varianceFactor ^ n * baseBound) :=
        mul_le_mul_of_nonneg_left (ih M') hvariance
      calc
        contribution (Nat.succ n) M ≤
            varianceFactor * contribution n M' := hstep
        _ ≤ varianceFactor * (varianceFactor ^ n * baseBound) := hind
        _ = varianceFactor ^ (Nat.succ n) * baseBound := by
          rw [pow_succ']
          ring

/-- If every adjacent deletion is an equality, the whole noncrossing
contribution is exactly the corresponding power of the variance factor. -/
theorem noncrossingContribution_eq_variance_pow
    (contribution : ∀ n, RademacherNoncrossingMatching n → ℝ)
    (varianceFactor baseValue : ℝ)
    (hbase : contribution 0 .empty = baseValue)
    (hcontract : RademacherAdjacentContractionExact contribution varianceFactor)
    {n : ℕ} (M : RademacherNoncrossingMatching n) :
    contribution n M = varianceFactor ^ n * baseValue := by
  induction n with
  | zero =>
      cases M
      simpa using hbase
  | succ n ih =>
      obtain ⟨i, M', hdelete, -, -⟩ :=
        RademacherNoncrossingMatching.exists_adjacentMatchedPair_and_delete M
      calc
        contribution (Nat.succ n) M =
            varianceFactor * contribution n M' := hcontract hdelete
        _ = varianceFactor * (varianceFactor ^ n * baseValue) := by rw [ih M']
        _ = varianceFactor ^ (Nat.succ n) * baseValue := by
          rw [pow_succ']
          ring

/-- Exact deletion automatically provides the weak one-step interface. -/
theorem adjacentContractionBound_of_exact
    (contribution : ∀ n, RademacherNoncrossingMatching n → ℝ)
    (varianceFactor : ℝ)
    (h : RademacherAdjacentContractionExact contribution varianceFactor) :
    RademacherAdjacentContractionBound contribution varianceFactor := by
  intro n m i M M' hdelete
  exact (h hdelete).le


end GraphMatrixReplica
