import GraphMatrix.RademacherMatrixSecondMoment

/-! # The first nontrivial Rademacher matrix moment

For `X = ∑ₑ εₑ Aₑ`, this file expands
`E trace ((X Xᵀ)^2)` and removes exactly those edge-index quadruples having
an odd multiplicity.  This is a verified fourth-moment layer, not a general
noncommutative Khintchine theorem.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

local instance rademacherMatrixFourthMoment_propDecidable {P : Prop} : Decidable P :=
  Classical.propDecidable P

/-- Every edge index occurs an even number of times in a quadruple. -/
def RademacherEvenQuadruple
    {ε : Type} [DecidableEq ε] (e₁ e₂ e₃ e₄ : ε) : Prop :=
  ∀ e, Even ([e₁, e₂, e₃, e₄].count e)

/-- Exact parity rule for four Rademacher coordinates. -/
theorem paperMean_four_paperSigns
    {ε : Type} [Fintype ε] [DecidableEq ε]
    (e₁ e₂ e₃ e₄ : ε) :
    paperMean (fun w : ε → Bool =>
      paperSign (w e₁) * paperSign (w e₂) *
      paperSign (w e₃) * paperSign (w e₄)) =
      if RademacherEvenQuadruple e₁ e₂ e₃ e₄ then 1 else 0 := by
  have h := paperMean_sign_word (ι := ε) [e₁, e₂, e₃, e₄]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one] at h
  by_cases hEven : RademacherEvenQuadruple e₁ e₂ e₃ e₄
  · simp only [hEven, if_true]
    have hEven' : ∀ i : ε, Even ([e₁, e₂, e₃, e₄].count i) := by
      simpa [RademacherEvenQuadruple] using hEven
    rw [if_pos hEven'] at h
    simpa [mul_assoc] using h
  · simp only [hEven, if_false]
    have hNotEven' : ¬ ∀ i : ε,
        Even ([e₁, e₂, e₃, e₄].count i) := by
      simpa [RademacherEvenQuadruple] using hEven
    rw [if_neg hNotEven'] at h
    simpa [mul_assoc] using h

/-- The parity rule after multiplying by a deterministic coefficient. -/
theorem paperMean_four_paperSigns_mul_const
    {ε : Type} [Fintype ε] [DecidableEq ε]
    (e₁ e₂ e₃ e₄ : ε) (c : ℝ) :
    paperMean (fun w : ε → Bool =>
      paperSign (w e₁) * paperSign (w e₂) *
        paperSign (w e₃) * paperSign (w e₄) * c) =
      if RademacherEvenQuadruple e₁ e₂ e₃ e₄ then c else 0 := by
  calc
    paperMean (fun w : ε → Bool =>
        paperSign (w e₁) * paperSign (w e₂) *
          paperSign (w e₃) * paperSign (w e₄) * c) =
        c * paperMean (fun w : ε → Bool =>
          paperSign (w e₁) * paperSign (w e₂) *
            paperSign (w e₃) * paperSign (w e₄)) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (paperMean_const_mul c (fun w : ε → Bool =>
          paperSign (w e₁) * paperSign (w e₂) *
            paperSign (w e₃) * paperSign (w e₄)))
    _ = if RademacherEvenQuadruple e₁ e₂ e₃ e₄ then c else 0 := by
      rw [paperMean_four_paperSigns]
      split_ifs <;> simp

/-- Four-linear scalar Rademacher expansion, with all odd-multiplicity
quadruples deleted by an explicit `if`. -/
theorem paperMean_four_rademacher_sums
    {ε : Type} [Fintype ε] [DecidableEq ε]
    (a₁ a₂ a₃ a₄ : ε → ℝ) :
    paperMean (fun w : ε → Bool =>
      (∑ e, paperSign (w e) * a₁ e) *
      (∑ e, paperSign (w e) * a₂ e) *
      (∑ e, paperSign (w e) * a₃ e) *
      (∑ e, paperSign (w e) * a₄ e)) =
      ∑ e₁, ∑ e₂, ∑ e₃, ∑ e₄,
        if RademacherEvenQuadruple e₁ e₂ e₃ e₄ then
          a₁ e₁ * a₂ e₂ * a₃ e₃ * a₄ e₄ else 0 := by
  have hExpand :
      (fun w : ε → Bool =>
        (∑ e, paperSign (w e) * a₁ e) *
        (∑ e, paperSign (w e) * a₂ e) *
        (∑ e, paperSign (w e) * a₃ e) *
        (∑ e, paperSign (w e) * a₄ e)) =
      (fun w : ε → Bool =>
        ∑ e₁, ∑ e₂, ∑ e₃, ∑ e₄,
          paperSign (w e₁) * paperSign (w e₂) *
            paperSign (w e₃) * paperSign (w e₄) *
              (a₁ e₁ * a₂ e₂ * a₃ e₃ * a₄ e₄)) := by
    funext w
    calc
      (∑ e, paperSign (w e) * a₁ e) *
          (∑ e, paperSign (w e) * a₂ e) *
          (∑ e, paperSign (w e) * a₃ e) *
          (∑ e, paperSign (w e) * a₄ e) =
          (∑ e, paperSign (w e) * a₁ e) *
            ((∑ e, paperSign (w e) * a₂ e) *
              ((∑ e, paperSign (w e) * a₃ e) *
                (∑ e, paperSign (w e) * a₄ e))) := by ring
      _ = ∑ e₁, (paperSign (w e₁) * a₁ e₁) *
            ((∑ e, paperSign (w e) * a₂ e) *
              ((∑ e, paperSign (w e) * a₃ e) *
                (∑ e, paperSign (w e) * a₄ e))) := by
          rw [Finset.sum_mul]
      _ = ∑ e₁, ∑ e₂,
            (paperSign (w e₁) * a₁ e₁) *
              ((paperSign (w e₂) * a₂ e₂) *
                ((∑ e, paperSign (w e) * a₃ e) *
                  (∑ e, paperSign (w e) * a₄ e))) := by
          apply Finset.sum_congr rfl
          intro e₁ _
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ e₁, ∑ e₂, ∑ e₃,
            (paperSign (w e₁) * a₁ e₁) *
              ((paperSign (w e₂) * a₂ e₂) *
                ((paperSign (w e₃) * a₃ e₃) *
                  (∑ e, paperSign (w e) * a₄ e))) := by
          apply Finset.sum_congr rfl
          intro e₁ _
          apply Finset.sum_congr rfl
          intro e₂ _
          rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ e₁, ∑ e₂, ∑ e₃, ∑ e₄,
            paperSign (w e₁) * paperSign (w e₂) *
              paperSign (w e₃) * paperSign (w e₄) *
                (a₁ e₁ * a₂ e₂ * a₃ e₃ * a₄ e₄) := by
          apply Finset.sum_congr rfl
          intro e₁ _
          apply Finset.sum_congr rfl
          intro e₂ _
          apply Finset.sum_congr rfl
          intro e₃ _
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e₄ _
          ring
  rw [hExpand, paperMean_sum]
  apply Finset.sum_congr rfl
  intro e₁ _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro e₂ _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro e₃ _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro e₄ _
  exact paperMean_four_paperSigns_mul_const e₁ e₂ e₃ e₄ _

/-- Entrywise form of the fourth Gram trace. -/
theorem matrix_trace_gram_sq_eq_four_entry_sum
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (X : Matrix ι κ ℝ) :
    Matrix.trace ((X * X.transpose) ^ 2) =
      ∑ i, ∑ j, ∑ a, ∑ b,
        X i a * X j a * X j b * X i b := by
  have hSymm : (X * X.transpose).transpose = X * X.transpose := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    Matrix.trace ((X * X.transpose) ^ 2) =
        Matrix.trace ((X * X.transpose).transpose *
          (X * X.transpose)) := by rw [pow_two, hSymm]
    _ = ∑ i, ∑ j, (X * X.transpose) i j ^ 2 :=
      matrix_trace_transpose_mul_self_eq_sum_sq (X * X.transpose)
    _ = ∑ i, ∑ j, ∑ a, ∑ b,
          X i a * X j a * X j b * X i b := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Exact fourth-moment expansion for the finite Rademacher matrix sum.
Only edge-index quadruples satisfying `RademacherEvenQuadruple` remain. -/
theorem paperMean_rademacherMatrix_gramTrace_sq_eq_evenQuadruples
    {ε ι κ : Type} [Fintype ε] [DecidableEq ε]
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) :
    paperMean (fun w : ε → Bool =>
      Matrix.trace ((paperRademacherMatrixSum A w *
        (paperRademacherMatrixSum A w).transpose) ^ 2)) =
      ∑ i, ∑ j, ∑ a, ∑ b,
        ∑ e₁, ∑ e₂, ∑ e₃, ∑ e₄,
          if RademacherEvenQuadruple e₁ e₂ e₃ e₄ then
            A e₁ i a * A e₂ j a * A e₃ j b * A e₄ i b else 0 := by
  simp_rw [matrix_trace_gram_sq_eq_four_entry_sum]
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro b _
  simpa [paperRademacherMatrixSum] using
    (paperMean_four_rademacher_sums
      (fun e => A e i a) (fun e => A e j a)
      (fun e => A e j b) (fun e => A e i b))

/-- A coarse unconditional bound obtained by forgetting the parity filter
and taking absolute values of every fourth-order coefficient. -/
theorem paperMean_rademacherMatrix_gramTrace_sq_le_sum_abs_coefficients
    {ε ι κ : Type} [Fintype ε] [DecidableEq ε]
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) :
    paperMean (fun w : ε → Bool =>
      Matrix.trace ((paperRademacherMatrixSum A w *
        (paperRademacherMatrixSum A w).transpose) ^ 2)) ≤
      ∑ i, ∑ j, ∑ a, ∑ b,
        ∑ e₁, ∑ e₂, ∑ e₃, ∑ e₄,
          |A e₁ i a * A e₂ j a * A e₃ j b * A e₄ i b| := by
  rw [paperMean_rademacherMatrix_gramTrace_sq_eq_evenQuadruples]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro e₁ _
  apply Finset.sum_le_sum
  intro e₂ _
  apply Finset.sum_le_sum
  intro e₃ _
  apply Finset.sum_le_sum
  intro e₄ _
  by_cases hEven : RademacherEvenQuadruple e₁ e₂ e₃ e₄
  · simpa [hEven] using
      (le_abs_self (A e₁ i a * A e₂ j a * A e₃ j b * A e₄ i b))
  · simp only [hEven, if_false]
    positivity


end GraphMatrixReplica
