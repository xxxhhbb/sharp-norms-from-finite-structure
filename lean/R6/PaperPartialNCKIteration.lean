import R6.PaperMomentToMean

/-! # Pure iteration bookkeeping for a future partial NCK argument

The results here do not prove a noncommutative Khintchine inequality.  They
only propagate an explicitly supplied one-step estimate and normalize the
resulting powers.  Thus the analytic NCK input remains visible as `hStep`.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Iteration of a one-step multiplicative bound.  Nonnegativity of `c` is
the only order hypothesis needed for propagation. -/
theorem sequence_le_geometric_of_step
    (B : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ i, B (i + 1) ≤ c * B i) (k : ℕ) :
    B k ≤ c ^ k * B 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        B (k + 1) ≤ c * B k := hStep k
        _ ≤ c * (c ^ k * B 0) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (k + 1) * B 0 := by rw [pow_succ]; ring

/-- If at each stage one may use a row or a column estimate, bounding the
two multipliers by their maximum gives a single geometric recurrence. -/
theorem sequence_le_geometric_of_row_col_steps
    (B : ℕ → ℝ) (cRow cCol : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hcRow : 0 ≤ cRow) (_hcCol : 0 ≤ cCol)
    (hStep : ∀ i,
      B (i + 1) ≤ max (cRow * B i) (cCol * B i)) (k : ℕ) :
    B k ≤ (max cRow cCol) ^ k * B 0 := by
  apply sequence_le_geometric_of_step B (max cRow cCol)
    (by positivity) _ k
  intro i
  refine (hStep i).trans ?_
  apply max_le
  · exact mul_le_mul_of_nonneg_right (le_max_left cRow cCol) (hB i)
  · exact mul_le_mul_of_nonneg_right (le_max_right cRow cCol) (hB i)

/-- The squared-scale multiplier produced by one NCK step with constant `C`
and moment parameter `p`. -/
def partialNCKSquaredStepFactor (C : ℝ) (p : ℕ) : ℝ :=
  C ^ 2 * (p : ℝ)

/-- `k` squared-scale NCK steps followed by an initial squared bound `D²`.
This is a definition only; a future NCK theorem must supply the recurrence. -/
def partialNCKIteratedSquaredScale (C : ℝ) (p k : ℕ) (D : ℝ) : ℝ :=
  partialNCKSquaredStepFactor C p ^ k * D ^ 2

theorem partialNCKSquaredStepFactor_nonneg
    (C : ℝ) (p : ℕ) :
    0 ≤ partialNCKSquaredStepFactor C p := by
  unfold partialNCKSquaredStepFactor
  positivity

/-- Explicit squared bookkeeping after `k` supplied NCK steps. -/
theorem sequence_le_partialNCKIteratedSquaredScale
    (B : ℕ → ℝ) (C : ℝ) (p k : ℕ) (D : ℝ)
    (hInit : B 0 ≤ D ^ 2)
    (hStep : ∀ i,
      B (i + 1) ≤ partialNCKSquaredStepFactor C p * B i) :
    B k ≤ partialNCKIteratedSquaredScale C p k D := by
  calc
    B k ≤ partialNCKSquaredStepFactor C p ^ k * B 0 :=
      sequence_le_geometric_of_step B _
        (partialNCKSquaredStepFactor_nonneg C p) hStep k
    _ ≤ partialNCKSquaredStepFactor C p ^ k * D ^ 2 := by
      exact mul_le_mul_of_nonneg_left hInit
        (pow_nonneg (partialNCKSquaredStepFactor_nonneg C p) k)
    _ = partialNCKIteratedSquaredScale C p k D := rfl

/-- Algebraic normalization of the squared scale.  It displays the exact
`C^(2k) p^k` loss before taking a square root. -/
theorem partialNCKIteratedSquaredScale_eq
    (C : ℝ) (p k : ℕ) (D : ℝ) :
    partialNCKIteratedSquaredScale C p k D =
      C ^ (2 * k) * (p : ℝ) ^ k * D ^ 2 := by
  unfold partialNCKIteratedSquaredScale partialNCKSquaredStepFactor
  rw [mul_pow, ← pow_mul]
 

/-- Taking the square root converts the accumulated `p^k` squared loss into
the exact factor `sqrt (p^k)`.  Replacing it by notation such as `p^(k/2)`
requires either even `k` (proved below) or real-exponent bookkeeping. -/
theorem sqrt_partialNCKIteratedSquaredScale
    (C : ℝ) (p k : ℕ) (D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Real.sqrt (partialNCKIteratedSquaredScale C p k D) =
      C ^ k * Real.sqrt ((p : ℝ) ^ k) * D := by
  have hRewrite :
      partialNCKIteratedSquaredScale C p k D =
        (C ^ k * D) ^ 2 * (p : ℝ) ^ k := by
    rw [partialNCKIteratedSquaredScale_eq]
    ring
  rw [hRewrite, Real.sqrt_mul (sq_nonneg (C ^ k * D)),
    Real.sqrt_sq (mul_nonneg (pow_nonneg hC k) hD)]
  ring

/-- For an even number of iterations, the square-root loss is literally the
integer power `p^(k/2)`. -/
theorem sqrt_natCast_pow_of_even
    (p k : ℕ) (hk : Even k) :
    Real.sqrt ((p : ℝ) ^ k) = (p : ℝ) ^ (k / 2) := by
  obtain ⟨t, rfl⟩ := hk
  have hdiv : (t + t) / 2 = t := by omega
  rw [hdiv, pow_add, ← pow_two, Real.sqrt_sq]
  positivity

/-- Moment-to-mean endpoint at the exact square-root scale accumulated by
`k` NCK steps.  The entire analytic burden is the explicit hypothesis
`hMoment`; this theorem only takes the positive even-moment root. -/
theorem paperMean_le_sqrt_partialNCKScale_of_evenMoment
    {α : Type} [Fintype α]
    (f : α → ℝ) (C : ℝ) (p k m : ℕ) (D : ℝ)
    (hm : 0 < m) (hf : ∀ a, 0 ≤ f a)
    (hMoment : paperMean (fun a => f a ^ (2 * m)) ≤
      partialNCKIteratedSquaredScale C p k D ^ m) :
    paperMean f ≤
      Real.sqrt (partialNCKIteratedSquaredScale C p k D) := by
  have hScale : 0 ≤ partialNCKIteratedSquaredScale C p k D := by
    unfold partialNCKIteratedSquaredScale partialNCKSquaredStepFactor
    positivity
  apply paperMean_le_of_mean_pow_le_pow f (2 * m)
    (Real.sqrt (partialNCKIteratedSquaredScale C p k D))
    (by omega) hf (Real.sqrt_nonneg _) ?_
  calc
    paperMean (fun a => f a ^ (2 * m)) ≤
        partialNCKIteratedSquaredScale C p k D ^ m := hMoment
    _ = Real.sqrt (partialNCKIteratedSquaredScale C p k D) ^ (2 * m) := by
      rw [pow_mul, Real.sq_sqrt hScale]

/-- The preceding endpoint with the square root expanded.  This is the
precise finite-uniform form of the `C^k p^(k/2) D` ledger. -/
theorem paperMean_le_partialNCKScale_of_evenMoment
    {α : Type} [Fintype α]
    (f : α → ℝ) (C : ℝ) (p k m : ℕ) (D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hm : 0 < m) (hf : ∀ a, 0 ≤ f a)
    (hMoment : paperMean (fun a => f a ^ (2 * m)) ≤
      partialNCKIteratedSquaredScale C p k D ^ m) :
    paperMean f ≤ C ^ k * Real.sqrt ((p : ℝ) ^ k) * D := by
  rw [← sqrt_partialNCKIteratedSquaredScale C p k D hC hD]
  exact paperMean_le_sqrt_partialNCKScale_of_evenMoment
    f C p k m D hm hf hMoment

/-- When the iteration count is even, the preceding conclusion has the
literal integer exponent `k / 2` on `p`. -/
theorem paperMean_le_partialNCKScale_of_evenMoment_evenIterations
    {α : Type} [Fintype α]
    (f : α → ℝ) (C : ℝ) (p k m : ℕ) (D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hk : Even k)
    (hm : 0 < m) (hf : ∀ a, 0 ≤ f a)
    (hMoment : paperMean (fun a => f a ^ (2 * m)) ≤
      partialNCKIteratedSquaredScale C p k D ^ m) :
    paperMean f ≤ C ^ k * (p : ℝ) ^ (k / 2) * D := by
  rw [← sqrt_natCast_pow_of_even p k hk]
  exact paperMean_le_partialNCKScale_of_evenMoment
    f C p k m D hC hD hm hf hMoment

/-- Fully composed recurrence-to-mean interface.  Here `hStep` is precisely
the still-unproved NCK input: once it is supplied, the remaining iteration,
squaring, and positive moment root are automatic. -/
theorem paperMean_le_of_partialNCKSquaredRecurrence
    {α : Type} [Fintype α]
    (f : α → ℝ) (B : ℕ → ℝ) (C : ℝ) (p k m : ℕ) (D : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hInit : B 0 ≤ D ^ 2)
    (hStep : ∀ i,
      B (i + 1) ≤ partialNCKSquaredStepFactor C p * B i)
    (hm : 0 < m) (hf : ∀ a, 0 ≤ f a)
    (hMomentAtEnd : paperMean (fun a => f a ^ (2 * m)) ≤ B k ^ m) :
    paperMean f ≤
      Real.sqrt (partialNCKIteratedSquaredScale C p k D) := by
  apply paperMean_le_sqrt_partialNCKScale_of_evenMoment
    f C p k m D hm hf
  exact hMomentAtEnd.trans
    (pow_le_pow_left₀ (hB k)
      (sequence_le_partialNCKIteratedSquaredScale
        B C p k D hInit hStep) m)

/-- Operator-norm specialization of the iterated moment-to-mean endpoint. -/
theorem matrix_l2_opNorm_paperMean_le_partialNCKScale_of_evenMoment
    {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : α → Matrix ι κ ℝ) (C : ℝ) (p k m : ℕ) (D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hm : 0 < m)
    (hMoment : paperMean (fun a => ‖A a‖ ^ (2 * m)) ≤
      partialNCKIteratedSquaredScale C p k D ^ m) :
    paperMean (fun a => ‖A a‖) ≤
      C ^ k * Real.sqrt ((p : ℝ) ^ k) * D := by
  exact paperMean_le_partialNCKScale_of_evenMoment
    (fun a => ‖A a‖) C p k m D hC hD hm
    (fun a => norm_nonneg (A a)) hMoment

#print axioms sequence_le_geometric_of_step
#print axioms sequence_le_geometric_of_row_col_steps
#print axioms sequence_le_partialNCKIteratedSquaredScale
#print axioms partialNCKIteratedSquaredScale_eq
#print axioms sqrt_partialNCKIteratedSquaredScale
#print axioms sqrt_natCast_pow_of_even
#print axioms paperMean_le_sqrt_partialNCKScale_of_evenMoment
#print axioms paperMean_le_partialNCKScale_of_evenMoment
#print axioms paperMean_le_partialNCKScale_of_evenMoment_evenIterations
#print axioms paperMean_le_of_partialNCKSquaredRecurrence
#print axioms matrix_l2_opNorm_paperMean_le_partialNCKScale_of_evenMoment

end GraphMatrixReplica
