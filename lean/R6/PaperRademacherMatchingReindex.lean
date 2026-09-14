import R6.PaperRademacherColumnMatchingContribution

/-! # Explicit reindexing of canonical Rademacher matching contributions

This file reindexes the original row/column/edge-choice cycle sum for the
column-canonical matching.  It uses only finite equivalences and cyclic
permutations.  No statement about arbitrary crossing matchings is made.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The original edge-choice condition imposed by the column-canonical
matching: the second label at `t` equals the first label at the next cycle
position. -/
def RademacherColumnCanonicalChoice
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) : Prop :=
  ∀ t, (choice t).2 = (choice (finRotate r t)).1

instance instDecidableRademacherColumnCanonicalChoice
    {ε : Type} [DecidableEq ε] {r : ℕ}
    (choice : Fin r → ε × ε) :
    Decidable (RademacherColumnCanonicalChoice choice) := by
  unfold RademacherColumnCanonicalChoice
  infer_instance

/-- A column-compatible edge choice has one free label per cycle position. -/
def columnCanonicalChoiceEquiv
    {ε : Type} {r : ℕ} :
    (Fin r → ε) ≃
      {choice : Fin r → ε × ε // RademacherColumnCanonicalChoice choice} where
  toFun edges :=
    ⟨fun t => (edges t, edges (finRotate r t)), fun _ => rfl⟩
  invFun choice t := (choice.1 t).1
  left_inv _ := rfl
  right_inv choice := by
    apply Subtype.ext
    funext t
    apply Prod.ext
    · rfl
    · exact (choice.property t).symm

/-- Explicitly reindex a sum over constrained pair choices by its one free
edge label at each cycle position. -/
theorem sum_if_columnCanonicalChoice_eq_sum_edges
    {ε : Type} [Fintype ε] [DecidableEq ε] {r : ℕ}
    (F : (Fin r → ε × ε) → ℝ) :
    (∑ choice : Fin r → ε × ε,
      if RademacherColumnCanonicalChoice choice then F choice else 0) =
      ∑ edges : Fin r → ε,
        F (fun t => (edges t, edges (finRotate r t))) := by
  classical
  calc
    _ = ∑ choice :
          {choice : Fin r → ε × ε //
            RademacherColumnCanonicalChoice choice}, F choice.1 := by
      rw [← Finset.sum_filter]
      simpa using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (Fin r → ε × ε))) F
          (p := RademacherColumnCanonicalChoice)).symm
    _ = _ := by
      symm
      exact Fintype.sum_equiv columnCanonicalChoiceEquiv
        (fun edges : Fin r → ε =>
          F (fun t => (edges t, edges (finRotate r t))))
        (fun choice => F choice.1) (fun _ => rfl)

/-- The column-canonical contribution written directly in the original
row/column/paired-edge coordinates of the Gram-cycle expansion. -/
def rademacherOriginalColumnMatchingContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) : ℝ :=
  ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
    ∑ choice : Fin r → ε × ε,
      if RademacherColumnCanonicalChoice choice then
        rademacherGramCycleCoefficient A rows cols choice else 0

/-- Eliminate the constrained second edge label in the original contribution.
This is the first explicit reindexing step. -/
theorem rademacherOriginalColumnMatchingContribution_eq_edgeAssignments
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) :
    rademacherOriginalColumnMatchingContribution (r := r) A =
      ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
        ∑ edges : Fin r → ε,
          ∏ t : Fin r,
            A (edges t) (rows t) (cols t) *
              A (edges (finRotate r t))
                (rows (finRotate r t)) (cols t) := by
  classical
  unfold rademacherOriginalColumnMatchingContribution
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro cols _
  simpa [rademacherGramCycleCoefficient] using
    (sum_if_columnCanonicalChoice_eq_sum_edges
      (fun choice => rademacherGramCycleCoefficient A rows cols choice))

/-- Reindexing one factor of a product by a permutation does not change the
product. -/
theorem prod_mul_comp_perm_eq
    {α : Type} [Fintype α] (σ : Equiv.Perm α)
    (f g : α → ℝ) :
    (∏ t : α, f t * g (σ t)) = ∏ t : α, f t * g t := by
  have hg : (∏ t : α, g (σ t)) = ∏ t : α, g t :=
    Fintype.prod_equiv σ _ _ (fun _ => rfl)
  simp only [Finset.prod_mul_distrib]
  rw [hg]

/-- Rotate the second occurrence back to the same free edge/row coordinate.
This exposes the predecessor column coordinate. -/
theorem rademacherColumnEdgeProduct_reindex
    {ε ι κ : Type} {r : ℕ}
    (A : ε → Matrix ι κ ℝ) (edges : Fin r → ε)
    (rows : Fin r → ι) (cols : Fin r → κ) :
    (∏ t : Fin r,
      A (edges t) (rows t) (cols t) *
        A (edges (finRotate r t))
          (rows (finRotate r t)) (cols t)) =
      ∏ t : Fin r,
        A (edges t) (rows t) (cols t) *
          A (edges t) (rows t) (cols ((finRotate r).symm t)) := by
  simpa only [Equiv.symm_apply_apply] using
    prod_mul_comp_perm_eq (finRotate r)
    (fun t => A (edges t) (rows t) (cols t))
    (fun t =>
      A (edges t) (rows t) (cols ((finRotate r).symm t)))

/-- Summing the original row and edge coordinates after the cyclic reindexing
produces the column-variance kernel at every cycle position. -/
theorem rademacherOriginalColumnMatchingContribution_eq_predecessorCycles
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) :
    rademacherOriginalColumnMatchingContribution (r := r) A =
      ∑ cols : Fin r → κ,
        ∏ t : Fin r,
          rademacherColumnVariance A (cols t)
            (cols ((finRotate r).symm t)) := by
  classical
  rw [rademacherOriginalColumnMatchingContribution_eq_edgeAssignments]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cols _
  rw [Finset.sum_comm]
  simp_rw [rademacherColumnEdgeProduct_reindex]
  calc
    (∑ edges : Fin r → ε, ∑ rows : Fin r → ι,
        ∏ t : Fin r,
          A (edges t) (rows t) (cols t) *
            A (edges t) (rows t) (cols ((finRotate r).symm t))) =
        ∏ t : Fin r, ∑ e : ε, ∑ row : ι,
          A e row (cols t) *
            A e row (cols ((finRotate r).symm t)) := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro edges _
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro t _
      simp [rademacherColumnVariance, Matrix.sum_apply,
        Matrix.mul_apply, Matrix.transpose_apply]

/-- The real column-variance kernel is symmetric. -/
theorem rademacherColumnVariance_apply_comm
    {ε ι κ : Type} [Fintype ε] [Fintype ι]
    (A : ε → Matrix ι κ ℝ) (i j : κ) :
    rademacherColumnVariance A i j =
      rademacherColumnVariance A j i := by
  classical
  simp only [rademacherColumnVariance, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro row _
  exact mul_comm _ _

/-- Reversal of a cyclic product with a symmetric kernel changes predecessor
edges into successor edges. -/
theorem prod_symmetricKernel_predecessor_eq_successor
    {α β : Type} [Fintype α] {r : ℕ}
    (K : α → α → β) [CommMonoid β]
    (hK : ∀ i j, K i j = K j i) (cycle : Fin r → α) :
    (∏ t : Fin r, K (cycle t) (cycle ((finRotate r).symm t))) =
      ∏ t : Fin r, K (cycle t) (cycle (finRotate r t)) := by
  have hrotate :
      (∏ t : Fin r,
        K (cycle (finRotate r t))
          (cycle ((finRotate r).symm (finRotate r t)))) =
        ∏ t : Fin r,
          K (cycle t) (cycle ((finRotate r).symm t)) :=
    Fintype.prod_equiv (finRotate r) _ _ (fun _ => rfl)
  rw [← hrotate]
  apply Finset.prod_congr rfl
  intro t _
  rw [Equiv.symm_apply_apply]
  exact hK _ _

/-- The predecessor-cycle expression is the standard successor-cycle trace
word for column variance. -/
theorem rademacherOriginalColumnMatchingContribution_eq_columnVarianceCycles
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) :
    rademacherOriginalColumnMatchingContribution (r := r) A =
      ∑ cols : Fin r → κ,
        ∏ t : Fin r,
          rademacherColumnVariance A (cols t) (cols (finRotate r t)) := by
  rw [rademacherOriginalColumnMatchingContribution_eq_predecessorCycles]
  apply Finset.sum_congr rfl
  intro cols _
  exact prod_symmetricKernel_predecessor_eq_successor
    (rademacherColumnVariance A)
    (rademacherColumnVariance_apply_comm A) cols

/-- Direct evaluation of the original column-canonical nested coefficient
sum, without defining the contribution by transposition. -/
theorem rademacherOriginalColumnMatchingContribution_eq_trace_columnVariance_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    rademacherOriginalColumnMatchingContribution (r := r) A =
      Matrix.trace ((rademacherColumnVariance A) ^ r) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [rademacherOriginalColumnMatchingContribution_eq_columnVarianceCycles]
  exact (matrix_trace_pow_succ_eq_sum_cycleProducts
    (rademacherColumnVariance A) q).symm

/-- The direct original-coordinate contribution agrees with the earlier
transpose-symmetry packaging. -/
theorem rademacherOriginalColumnMatchingContribution_eq_transposeContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    rademacherOriginalColumnMatchingContribution (r := r) A =
      rademacherColumnCanonicalMatchingContribution (r := r) A := by
  rw [rademacherOriginalColumnMatchingContribution_eq_trace_columnVariance_pow
    A r hr]
  exact (rademacherColumnCanonicalMatchingContribution_eq_trace_columnVariance_pow
    A r hr).symm

#print axioms sum_if_columnCanonicalChoice_eq_sum_edges
#print axioms rademacherColumnEdgeProduct_reindex
#print axioms
  rademacherOriginalColumnMatchingContribution_eq_trace_columnVariance_pow

end GraphMatrixReplica
