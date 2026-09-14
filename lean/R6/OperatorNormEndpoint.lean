import R6.HighMomentTailMarkov
import Mathlib.Analysis.MeanInequalitiesPow

/-! # Operator-norm high-probability endpoint

This module is the downstream endpoint for a C078/C079-style trace budget.
It performs only Markov's inequality, logarithmic moment-order selection, and
the deterministic norm-to-Gram-trace comparison.  The upstream trace estimate
is always an explicit hypothesis.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The integer trace order chosen in R16, Proposition `prop:core-upper`.
It handles the whole `L^q` window, unlike the dyadic order used below for a
separate high-probability corollary. -/
def paperCoreTraceOrder (n q : ℕ) : ℕ :=
  max 2 (max (⌈Real.log (2 * (n : ℝ))⌉₊) (⌈(q : ℝ) / 2⌉₊))

theorem paperCoreTraceOrder_ge_two (n q : ℕ) :
    2 ≤ paperCoreTraceOrder n q := le_max_left _ _

theorem paperCoreTraceOrder_covers_q (n q : ℕ) :
    q ≤ 2 * paperCoreTraceOrder n q := by
  have hq : (q : ℝ) / 2 ≤ (⌈(q : ℝ) / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hceil : ⌈(q : ℝ) / 2⌉₊ ≤ paperCoreTraceOrder n q :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hceilR : (⌈(q : ℝ) / 2⌉₊ : ℝ) ≤
      (paperCoreTraceOrder n q : ℝ) := by exact_mod_cast hceil
  exact_mod_cast (show (q : ℝ) ≤ 2 * (paperCoreTraceOrder n q : ℝ) by
    linarith)

/-- The third member of R16's `max` choice is the ceiling of `log(2n)`. -/
theorem paperCoreTraceOrder_covers_log (n q : ℕ) :
    Real.log (2 * (n : ℝ)) ≤ (paperCoreTraceOrder n q : ℝ) := by
  have hceil : ⌈Real.log (2 * (n : ℝ))⌉₊ ≤ paperCoreTraceOrder n q := by
    unfold paperCoreTraceOrder
    exact (le_max_left _ _).trans (le_max_right _ _)
  calc
    Real.log (2 * (n : ℝ)) ≤ (⌈Real.log (2 * (n : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (paperCoreTraceOrder n q : ℝ) := by
      exact_mod_cast hceil

/-- Finite-uniform Lyapunov inequality in the form needed for the paper's
`L^q` endpoint.  This covers every integer `1 ≤ q ≤ m`, without requiring
dyadic divisibility. -/
theorem paperMean_lowerMoment_le_of_higherMoment_budget
    {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (q m : ℕ) (B : ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hq : 0 < q) (hqm : q ≤ m) (hB : 0 ≤ B)
    (hMoment : paperMean (fun ω => f ω ^ m) ≤ B ^ m) :
    paperMean (fun ω => f ω ^ q) ≤ B ^ q := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl hEmpty =>
      letI := hEmpty
      simp [paperMean, pow_nonneg hB]
  | inr hNonempty =>
      letI := hNonempty
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hq hqm)
      have hqmR : (q : ℝ) ≤ m := by exact_mod_cast hqm
      let t : ℝ := (m : ℝ) / (q : ℝ)
      have ht : 1 ≤ t := by
        dsimp [t]
        exact (one_le_div hqR).2 hqmR
      have htPos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have hWeightNonneg :
          ∀ ω ∈ (Finset.univ : Finset Ω),
            0 ≤ (Fintype.card Ω : ℝ)⁻¹ := by
        intro _ _
        positivity
      have hWeightSum :
          ∑ _ω : Ω, (Fintype.card Ω : ℝ)⁻¹ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      have hJensen :=
        Real.rpow_arith_mean_le_arith_mean_rpow
          (s := (Finset.univ : Finset Ω))
          (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹)
          (fun ω => f ω ^ q) hWeightNonneg hWeightSum
          (fun ω _ => pow_nonneg (hf ω) q) ht
      have hJ :
          (paperMean (fun ω => f ω ^ q)) ^ t ≤
            paperMean (fun ω => (f ω ^ q) ^ t) := by
        simpa only [Finset.mul_sum, paperMean] using hJensen
      have hPow : ∀ ω, (f ω ^ q) ^ t = f ω ^ m := by
        intro ω
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hf ω)]
        have hqt : (q : ℝ) * t = (m : ℝ) := by
          dsimp [t]
          field_simp
        rw [hqt, Real.rpow_natCast]
      simp_rw [hPow] at hJ
      have hMeanNonneg : 0 ≤ paperMean (fun ω => f ω ^ q) := by
        have hZero : paperMean (fun _ : Ω => (0 : ℝ)) = 0 := paperMean_zero
        rw [← hZero]
        exact paperMean_mono (fun ω => pow_nonneg (hf ω) q)
      have hBq : 0 ≤ B ^ q := pow_nonneg hB q
      apply (Real.rpow_le_rpow_iff hMeanNonneg hBq htPos).mp
      have hBpow : (B ^ q) ^ t = B ^ m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
        have hqt : (q : ℝ) * t = (m : ℝ) := by
          dsimp [t]
          field_simp
        rw [hqt, Real.rpow_natCast]
      rw [hBpow]
      exact hJ.trans hMoment

/-- The finite-uniform `L^q` norm used by the R16 core upper endpoint.
The operator norm is nonnegative, so no absolute value is needed. -/
def finiteUniformOperatorLpNorm
    {Ω ι κ : Type} [Fintype Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Ω → Matrix ι κ ℝ) (q : ℕ) : ℝ :=
  (paperMean (fun ω => ‖M ω‖ ^ q)) ^ (1 / (q : ℝ))

/-- Conditional arbitrary-order Gram-trace endpoint.  The deterministic
norm-to-trace bridge and the upstream trace budget are separate hypotheses;
neither is supplied by the existing dyadic endpoint. -/
theorem finiteUniformOperatorLpNorm_le_of_generalTraceBudget
    {Ω ι κ : Type} [Fintype Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Ω → Matrix ι κ ℝ) (q p : ℕ) (B : ℝ)
    (hq : 0 < q) (hqp : q ≤ 2 * p) (hB : 0 ≤ B)
    (hNormTrace : ∀ ω,
      ‖M ω‖ ^ (2 * p) ≤
        Matrix.trace ((M ω * (M ω).transpose) ^ p))
    (hTrace : paperMean (fun ω =>
      Matrix.trace ((M ω * (M ω).transpose) ^ p)) ≤ B ^ (2 * p)) :
    finiteUniformOperatorLpNorm M q ≤ B := by
  have hMoment : paperMean (fun ω => ‖M ω‖ ^ q) ≤ B ^ q :=
    paperMean_lowerMoment_le_of_higherMoment_budget
      (fun ω => ‖M ω‖) q (2 * p) B
      (fun _ => norm_nonneg _) hq hqp hB
      ((paperMean_mono hNormTrace).trans hTrace)
  have hMeanNonneg : 0 ≤ paperMean (fun ω => ‖M ω‖ ^ q) := by
    have hZero : paperMean (fun _ : Ω => (0 : ℝ)) = 0 := paperMean_zero
    rw [← hZero]
    exact paperMean_mono (fun ω => pow_nonneg (norm_nonneg _) q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold finiteUniformOperatorLpNorm
  calc
    (paperMean (fun ω => ‖M ω‖ ^ q)) ^ (1 / (q : ℝ)) ≤
        (B ^ q) ^ (1 / (q : ℝ)) :=
      Real.rpow_le_rpow hMeanNonneg hMoment (by positivity)
    _ = B := by
      calc
        (B ^ q) ^ (1 / (q : ℝ)) =
            B ^ ((q : ℝ) * (1 / (q : ℝ))) := by
          rw [Real.rpow_mul hB, Real.rpow_natCast]
        _ = B ^ (1 : ℝ) := by
          congr 1
          field_simp [ne_of_gt hqR]
        _ = B := Real.rpow_one B

/-- R16's exact integer-order choice is now visible in the interface.
The upper window `q ≤ C₀ log(2n)`, the scale's graph exponents, and the
eventual large-`n` ratio condition belong to the explicit upstream budget. -/
theorem finiteUniformOperatorLpNorm_le_at_paperCoreTraceOrder
    {Ω ι κ : Type} [Fintype Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Ω → Matrix ι κ ℝ) (n q : ℕ) (B : ℝ)
    (hq : 0 < q) (hB : 0 ≤ B)
    (hNormTrace : ∀ ω,
      ‖M ω‖ ^ (2 * paperCoreTraceOrder n q) ≤
        Matrix.trace ((M ω * (M ω).transpose) ^ paperCoreTraceOrder n q))
    (hTrace : paperMean (fun ω =>
      Matrix.trace ((M ω * (M ω).transpose) ^ paperCoreTraceOrder n q)) ≤
        B ^ (2 * paperCoreTraceOrder n q)) :
    finiteUniformOperatorLpNorm M q ≤ B := by
  exact finiteUniformOperatorLpNorm_le_of_generalTraceBudget
    M q (paperCoreTraceOrder n q) B hq
    (paperCoreTraceOrder_covers_q n q) hB hNormTrace hTrace

/-- The least natural moment order above the requested logarithmic budget. -/
def logarithmicMomentOrder (A : ℝ) (n : ℕ) : ℕ :=
  ⌈A * Real.log (n : ℝ)⌉₊

/-- The selected order really pays the full `A log n` exponent. -/
theorem le_logarithmicMomentOrder (A : ℝ) (n : ℕ) :
    A * Real.log (n : ℝ) ≤ (logarithmicMomentOrder A n : ℝ) := by
  exact Nat.le_ceil _

/-- A dyadic trace order can be selected within a factor two of any logarithmic
target at least one.  This is the order optimization needed by the existing
dyadic norm-to-trace bridge. -/
theorem exists_dyadic_logarithmicMomentOrder
    (A : ℝ) (n : ℕ) (hScale : 1 ≤ A * Real.log (n : ℝ)) :
    ∃ q : ℕ,
      A * Real.log (n : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) ∧
      ((2 ^ q : ℕ) : ℝ) ≤ 2 * (A * Real.log (n : ℝ)) := by
  obtain ⟨a, haLower, haUpper⟩ :=
    exists_nat_pow_near hScale (by norm_num : (1 : ℝ) < 2)
  refine ⟨a + 1, ?_, ?_⟩
  · simpa [Nat.cast_pow] using le_of_lt haUpper
  · calc
      (((2 ^ (a + 1) : ℕ) : ℝ)) = 2 * (2 : ℝ) ^ a := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤ 2 * (A * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left haLower (by norm_num)

/-- A dyadic Gram-trace order can be selected so that its corresponding norm
moment `2 * 2^q` lies above the logarithmic target, while the trace power
`2^q` lies below it.  Thus the norm moment is within a factor two of the
target. -/
theorem exists_dyadic_gramMomentOrder
    (A : ℝ) (n : ℕ) (hScale : 1 ≤ A * Real.log (n : ℝ)) :
    ∃ q : ℕ,
      A * Real.log (n : ℝ) ≤ ((2 * 2 ^ q : ℕ) : ℝ) ∧
      ((2 ^ q : ℕ) : ℝ) ≤ A * Real.log (n : ℝ) := by
  obtain ⟨q, hqLower, hqUpper⟩ :=
    exists_nat_pow_near hScale (by norm_num : (1 : ℝ) < 2)
  refine ⟨q, ?_, ?_⟩
  · calc
      A * Real.log (n : ℝ) ≤ (2 : ℝ) ^ (q + 1) := le_of_lt hqUpper
      _ = ((2 * 2 ^ q : ℕ) : ℝ) := by
        push_cast
        rw [pow_succ]
        ring
  · simpa [Nat.cast_pow] using hqLower

/-- An exponential tail at any order above `A log n` is at most `n^{-A}`.
The conclusion uses real powers, so `A` need not be an integer. -/
theorem exp_neg_natCast_le_rpow_neg_of_logOrder
    (n m : ℕ) (A : ℝ) (hn : 0 < n)
    (hOrder : A * Real.log (n : ℝ) ≤ (m : ℝ)) :
    Real.exp (-(m : ℝ)) ≤ Real.rpow (n : ℝ) (-A) := by
  calc
    Real.exp (-(m : ℝ)) ≤
        Real.exp (-(A * Real.log (n : ℝ))) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hOrder)
    _ = Real.rpow (n : ℝ) (-A) := by
      symm
      calc
        Real.rpow (n : ℝ) (-A) =
            Real.exp (Real.log (n : ℝ) * (-A)) :=
          Real.rpow_def_of_pos (by exact_mod_cast hn) (-A)
        _ = Real.exp (-(A * Real.log (n : ℝ))) := by
          congr 1
          ring

/-- Generic logarithmic-order endpoint: an `m`-th moment bound by `B^m`
implies an `n^{-A}` failure probability at threshold `e B`. -/
theorem highMomentTail_le_rpow_neg_of_logOrder
    {Ω : Type} [Fintype Ω]
    (X : Ω → ℝ) (B A : ℝ) (n m : ℕ)
    (hX : ∀ ω, 0 ≤ X ω) (hB : 0 < B) (hn : 0 < n)
    (hOrder : A * Real.log (n : ℝ) ≤ (m : ℝ))
    (hMoment : paperMean (fun ω => X ω ^ m) ≤ B ^ m) :
    finiteUniformProbability (fun ω => Real.exp 1 * B < X ω) ≤
      Real.rpow (n : ℝ) (-A) := by
  exact (finiteUniformProbability_le_exp_neg_nat_of_moment_le_pow
    X B m hX hB hMoment).trans
      (exp_neg_natCast_le_rpow_neg_of_logOrder n m A hn hOrder)

/-- The canonical ceiling choice discharges the logarithmic order condition. -/
theorem highMomentTail_le_rpow_neg_at_logarithmicMomentOrder
    {Ω : Type} [Fintype Ω]
    (X : Ω → ℝ) (B A : ℝ) (n : ℕ)
    (hX : ∀ ω, 0 ≤ X ω) (hB : 0 < B) (hn : 0 < n)
    (hMoment : paperMean (fun ω =>
      X ω ^ logarithmicMomentOrder A n) ≤
        B ^ logarithmicMomentOrder A n) :
    finiteUniformProbability (fun ω => Real.exp 1 * B < X ω) ≤
      Real.rpow (n : ℝ) (-A) := by
  exact highMomentTail_le_rpow_neg_of_logOrder
    X B A n (logarithmicMomentOrder A n) hX hB hn
      (le_logarithmicMomentOrder A n) hMoment

/-- Operator-norm specialization for an arbitrary finite matrix family. -/
theorem operatorNormEndpoint_of_momentBudget
    {Ω ι κ : Type} [Fintype Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Ω → Matrix ι κ ℝ) (B A : ℝ) (n m : ℕ)
    (hB : 0 < B) (hn : 0 < n)
    (hOrder : A * Real.log (n : ℝ) ≤ (m : ℝ))
    (hMoment : paperMean (fun ω => ‖M ω‖ ^ m) ≤ B ^ m) :
    finiteUniformProbability (fun ω =>
      Real.exp 1 * B < ‖M ω‖) ≤ Real.rpow (n : ℝ) (-A) := by
  exact highMomentTail_le_rpow_neg_of_logOrder
    (fun ω => ‖M ω‖) B A n m (fun ω => norm_nonneg (M ω))
      hB hn hOrder hMoment

/-- Abstract C078/C079 handoff.  A dyadic Gram-trace estimate at order `p=2^q`
is sufficient for the final operator-norm probability bound.  No counting
claim is assumed beyond the explicit hypothesis `hTrace`. -/
theorem operatorNormEndpoint_of_dyadicTraceBudget
    {Ω ι κ : Type} [Fintype Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Ω → Matrix ι κ ℝ) (B A : ℝ) (n q : ℕ)
    (hB : 0 < B) (hn : 0 < n)
    (hOrder : A * Real.log (n : ℝ) ≤ ((2 * 2 ^ q : ℕ) : ℝ))
    (hTrace : paperMean (fun ω =>
      Matrix.trace ((M ω * (M ω).transpose) ^ (2 ^ q))) ≤
        B ^ (2 * 2 ^ q)) :
    finiteUniformProbability (fun ω =>
      Real.exp 1 * B < ‖M ω‖) ≤ Real.rpow (n : ℝ) (-A) := by
  apply operatorNormEndpoint_of_momentBudget
    M B A n (2 * 2 ^ q) hB hn hOrder
  exact (paperMean_mono (fun ω =>
    matrix_l2_opNorm_pow_dyadic_le_gramTrace (M ω) q)).trans hTrace

/-- Exact specialization of the trace-budget interface to the globally
injective paper graph matrix and its finite Rademacher noise space. -/
theorem paperGraphMatrix_operatorNormEndpoint_of_dyadicTraceBudget
    (G : PaperShape) (B A : ℝ) (n q : ℕ)
    (hB : 0 < B) (hn : 0 < n)
    (hOrder : A * Real.log (n : ℝ) ≤ ((2 * 2 ^ q : ℕ) : ℝ))
    (hTrace : paperMean (fun w : PaperNoise n =>
      Matrix.trace ((paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) ^ (2 ^ q))) ≤
          B ^ (2 * 2 ^ q)) :
    finiteUniformProbability (fun w : PaperNoise n =>
      Real.exp 1 * B < ‖paperGraphMatrix G n w‖) ≤
        Real.rpow (n : ℝ) (-A) := by
  exact operatorNormEndpoint_of_dyadicTraceBudget
    (fun w : PaperNoise n => paperGraphMatrix G n w)
      B A n q hB hn hOrder hTrace

/-- Internally select a dyadic logarithmic trace order.  The upstream provider
only has to prove its trace budget throughout the explicit factor-two window;
the endpoint chooses one admissible order and returns the final probability
bound. -/
theorem exists_operatorNormEndpoint_of_dyadicLogWindow
    {Ω ι κ : Type} [Fintype Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Ω → Matrix ι κ ℝ) (B A : ℝ) (n : ℕ)
    (hB : 0 < B) (hn : 0 < n)
    (hScale : 1 ≤ A * Real.log (n : ℝ))
    (hTrace : ∀ q : ℕ,
      A * Real.log (n : ℝ) ≤ ((2 * 2 ^ q : ℕ) : ℝ) →
      ((2 ^ q : ℕ) : ℝ) ≤ A * Real.log (n : ℝ) →
      paperMean (fun ω =>
        Matrix.trace ((M ω * (M ω).transpose) ^ (2 ^ q))) ≤
          B ^ (2 * 2 ^ q)) :
    ∃ q : ℕ,
      A * Real.log (n : ℝ) ≤ ((2 * 2 ^ q : ℕ) : ℝ) ∧
      ((2 ^ q : ℕ) : ℝ) ≤ A * Real.log (n : ℝ) ∧
      finiteUniformProbability (fun ω =>
        Real.exp 1 * B < ‖M ω‖) ≤ Real.rpow (n : ℝ) (-A) := by
  obtain ⟨q, hMomentLower, hTraceUpper⟩ :=
    exists_dyadic_gramMomentOrder A n hScale
  refine ⟨q, hMomentLower, hTraceUpper, ?_⟩
  apply operatorNormEndpoint_of_dyadicTraceBudget M B A n q hB hn
  · exact hMomentLower
  · exact hTrace q hMomentLower hTraceUpper

#print axioms le_logarithmicMomentOrder
#print axioms exists_dyadic_logarithmicMomentOrder
#print axioms exists_dyadic_gramMomentOrder
#print axioms exp_neg_natCast_le_rpow_neg_of_logOrder
#print axioms highMomentTail_le_rpow_neg_of_logOrder
#print axioms highMomentTail_le_rpow_neg_at_logarithmicMomentOrder
#print axioms operatorNormEndpoint_of_momentBudget
#print axioms operatorNormEndpoint_of_dyadicTraceBudget
#print axioms paperGraphMatrix_operatorNormEndpoint_of_dyadicTraceBudget
#print axioms exists_operatorNormEndpoint_of_dyadicLogWindow

end GraphMatrixReplica
