import GraphMatrix.RademacherCatalanClosedCycleWeightProof
import GraphMatrix.MomentToMean
import GraphMatrix.RademacherPerfectMatchingCount

/-! # The remaining crossing-matching reduction

The Catalan contribution bound is now unconditional.  This file separates
what it proves about an arbitrary pairing from the genuinely new crossing
inequality.  In particular, relabelling/orienting the pairs does not turn a
crossing pairing into a Catalan one, so no invalid uncrossing monotonicity is
asserted.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Contribution cut out by an arbitrary labelled and oriented perfect
matching of the `2*r` occurrence positions. -/
def rademacherPerfectMatchingContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ} (A : ε → Matrix ι κ ℝ)
    (matching : Fin r × Bool ≃ Fin (r * 2)) : ℝ :=
  ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
    ∑ choice : Fin r → ε × ε,
      if RademacherWordMatchingCompatible choice matching then
        rademacherGramCycleCoefficient A rows cols choice else 0

/-- If two matching presentations select exactly the same edge words, their
coefficient-cycle contributions agree.  This is the precise invariance needed
to forget pair labels and pair orientations. -/
theorem rademacherPerfectMatchingContribution_eq_of_compatible_iff
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ} (A : ε → Matrix ι κ ℝ)
    (m₁ m₂ : Fin r × Bool ≃ Fin (r * 2))
    (h : ∀ choice : Fin r → ε × ε,
      RademacherWordMatchingCompatible choice m₁ ↔
        RademacherWordMatchingCompatible choice m₂) :
    rademacherPerfectMatchingContribution A m₁ =
      rademacherPerfectMatchingContribution A m₂ := by
  unfold rademacherPerfectMatchingContribution
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro cols _
  apply Finset.sum_congr rfl
  intro choice _
  rw [if_congr (h choice) rfl rfl]

/-- A concrete perfect-matching encoding which selects the same words as a
Catalan matching inherits the sharp Catalan estimate. -/
theorem abs_rademacherPerfectMatchingContribution_le_of_catalan
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {r : ℕ} (A : ε → Matrix ι κ ℝ)
    (M : RademacherNoncrossingMatching r) (hr : 0 < r)
    (matching : Fin r × Bool ≃ Fin (r * 2))
    (h : ∀ choice : Fin r → ε × ε,
      RademacherWordMatchingCompatible choice matching ↔
        RademacherNoncrossingCompatible M choice) :
    |rademacherPerfectMatchingContribution A matching| ≤
      (Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ r := by
  have heq : rademacherPerfectMatchingContribution A matching =
      rademacherNoncrossingMatchingContribution A M := by
    unfold rademacherPerfectMatchingContribution
    unfold rademacherNoncrossingMatchingContribution
    apply Finset.sum_congr rfl
    intro rows _
    apply Finset.sum_congr rfl
    intro cols _
    apply Finset.sum_congr rfl
    intro choice _
    rw [if_congr (h choice) rfl rfl]
  rw [heq]
  cases M with
  | empty => omega
  | @node a b inside outside =>
      simpa using
        (abs_rademacherNoncrossingMatchingContribution_le_catalan
          A inside outside)

/-- The exact even-edge trace sum at order `r`. -/
def rademacherEvenEdgeTraceSum
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] (A : ε → Matrix ι κ ℝ) (r : ℕ) : ℝ :=
  ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
    ∑ choice : Fin r → ε × ε,
      if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
        rademacherGramCycleCoefficient A rows cols choice else 0

theorem paperMean_rademacherMatrix_gramTrace_pow_eq_evenEdgeTraceSum
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r) :
    paperMean (fun w : ε → Bool =>
      Matrix.trace ((paperRademacherMatrixSum A w *
        (paperRademacherMatrixSum A w).transpose) ^ r)) =
      rademacherEvenEdgeTraceSum A r := by
  exact paperMean_rademacherMatrix_gramTrace_pow_eq_evenEdgeWords A r hr

/-- The minimal unresolved crossing statement.  It says that the exact
Rademacher parity sum is controlled by the number of actual (unlabelled,
unoriented) pairings times the sharp single-pairing variance envelope. -/
def RademacherCrossingMatchingReduction
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) : Prop :=
  rademacherEvenEdgeTraceSum A r ≤
    (rademacherPerfectMatchingCount r : ℝ) *
      ((Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ r)

/-- Abstract but fully proved double-factorial accounting.  It is enough to
construct an actual-pairing decomposition with at most `(2*r-1)‼` terms and
bound every term in absolute value by the sharp variance envelope. -/
theorem sum_le_perfectMatchingCount_mul_of_decomposition
    {β : Type} [Fintype β] (r : ℕ) (term : β → ℝ) (S E : ℝ)
    (hE : 0 ≤ E) (hcard : Fintype.card β ≤ rademacherPerfectMatchingCount r)
    (hsum : S = ∑ x, term x) (hterm : ∀ x, |term x| ≤ E) :
    S ≤ (rademacherPerfectMatchingCount r : ℝ) * E := by
  rw [hsum]
  calc
    (∑ x, term x) ≤ ∑ x, |term x| := by
      apply Finset.sum_le_sum
      intro x _
      exact le_abs_self (term x)
    _ ≤ ∑ _x : β, E := by
      apply Finset.sum_le_sum
      intro x _
      exact hterm x
    _ = (Fintype.card β : ℝ) * E := by
      simp [nsmul_eq_mul]
    _ ≤ (rademacherPerfectMatchingCount r : ℝ) * E := by
      gcongr

/-- A double-factorial decomposition with the sharp per-pairing estimate
implies the isolated crossing reduction. -/
theorem rademacherCrossingMatchingReduction_of_decomposition
    {ε ι κ β : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [Fintype β] [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (term : β → ℝ)
    (hcard : Fintype.card β ≤ rademacherPerfectMatchingCount r)
    (hsum : rademacherEvenEdgeTraceSum A r = ∑ x, term x)
    (hterm : ∀ x, |term x| ≤
      (Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ r) :
    RademacherCrossingMatchingReduction A r := by
  unfold RademacherCrossingMatchingReduction
  apply sum_le_perfectMatchingCount_mul_of_decomposition r term _ _
  · exact mul_nonneg (by positivity) (pow_nonneg
      (rademacherVarianceNormMax_nonneg A) r)
  · exact hcard
  · exact hsum
  · exact hterm

/-- Conditional dyadic moment endpoint.  This is the exact place where the
crossing reduction plugs into the already verified trace expansion. -/
theorem paperMean_rademacherMatrix_l2_opNorm_dyadic_le_of_crossingReduction
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (q : ℕ)
    (hcross : RademacherCrossingMatchingReduction A (2 ^ q)) :
    paperMean (fun w : ε → Bool =>
      ‖paperRademacherMatrixSum A w‖ ^ (2 * 2 ^ q)) ≤
      (rademacherPerfectMatchingCount (2 ^ q) : ℝ) *
        ((Fintype.card ι : ℝ) *
          rademacherVarianceNormMax A ^ (2 ^ q)) := by
  unfold RademacherCrossingMatchingReduction at hcross
  exact (paperMean_rademacherMatrix_l2_opNorm_dyadic_le_evenEdgeWords
    A q).trans hcross

/-- The standard correct-scale coarse form: the pairing count costs at most
`(2r)^r`, whose `2r`-th root is of order `sqrt r`. -/
theorem paperMean_rademacherMatrix_l2_opNorm_dyadic_le_pairingPower
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (q : ℕ)
    (hcross : RademacherCrossingMatchingReduction A (2 ^ q)) :
    paperMean (fun w : ε → Bool =>
      ‖paperRademacherMatrixSum A w‖ ^ (2 * 2 ^ q)) ≤
      (((2 * (2 ^ q)) ^ (2 ^ q) : ℕ) : ℝ) *
        ((Fintype.card ι : ℝ) *
          rademacherVarianceNormMax A ^ (2 ^ q)) := by
  let r := 2 ^ q
  let E := (Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ r
  calc
    paperMean (fun w : ε → Bool =>
        ‖paperRademacherMatrixSum A w‖ ^ (2 * 2 ^ q)) ≤
        (rademacherPerfectMatchingCount r : ℝ) * E := by
      exact paperMean_rademacherMatrix_l2_opNorm_dyadic_le_of_crossingReduction
        A q hcross
    _ ≤ (((2 * r) ^ r : ℕ) : ℝ) * E := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast rademacherPerfectMatchingCount_le r
      · exact mul_nonneg (by positivity)
          (pow_nonneg (rademacherVarianceNormMax_nonneg A) r)

/-- Unconditioned `L¹` endpoint.  A numerical `2r`-th-root bound can
be supplied independently without committing the usual Nat/Real exponent
confusion. -/
theorem paperMean_rademacherMatrix_l2_opNorm_le_of_crossingReduction
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (q : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hcross : RademacherCrossingMatchingReduction A (2 ^ q))
    (hnumeric :
      (rademacherPerfectMatchingCount (2 ^ q) : ℝ) *
          ((Fintype.card ι : ℝ) *
            rademacherVarianceNormMax A ^ (2 ^ q)) ≤
        B ^ (2 * 2 ^ q)) :
    paperMean (fun w : ε → Bool =>
      ‖paperRademacherMatrixSum A w‖) ≤ B := by
  apply matrix_l2_opNorm_paperMean_le_of_moment_le_pow
    (fun w : ε → Bool => paperRademacherMatrixSum A w)
    (2 * 2 ^ q) B (by positivity) hB
  exact (paperMean_rademacherMatrix_l2_opNorm_dyadic_le_of_crossingReduction
    A q hcross).trans hnumeric


end GraphMatrixReplica
