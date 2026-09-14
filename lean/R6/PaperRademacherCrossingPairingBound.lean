import R6.PaperRademacherCrossingMatchingReduction

/-! # Unconditional bounds for an arbitrary crossing pairing

The first bound below is deliberately finite-dimensional: it applies to every
pairing, crossing or not, without using an unproved uncrossing operation.  The
sharp variance bound is then named separately, making the exact remaining
noncommutative Cauchy--Schwarz obligation visible.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Entrywise `ℓ¹` mass of the coefficient family. -/
def rademacherCoefficientEntryL1
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) : ℝ :=
  ∑ e, ∑ i, ∑ j, |A e i j|

theorem rademacherCoefficientEntryL1_nonneg
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) :
    0 ≤ rademacherCoefficientEntryL1 A := by
  unfold rademacherCoefficientEntryL1
  positivity

theorem abs_entry_le_rademacherCoefficientEntryL1
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (e : ε) (i : ι) (j : κ) :
    |A e i j| ≤ rademacherCoefficientEntryL1 A := by
  unfold rademacherCoefficientEntryL1
  calc
    |A e i j| ≤ ∑ j' : κ, |A e i j'| :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j' : κ => |A e i j'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : ι, ∑ j' : κ, |A e i' j'| :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun i' : ι => ∑ j' : κ, |A e i' j'|)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    _ ≤ ∑ e' : ε, ∑ i' : ι, ∑ j' : κ, |A e' i' j'| :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun e' : ε => ∑ i' : ι, ∑ j' : κ, |A e' i' j'|)
        (fun _ _ => by positivity) (Finset.mem_univ e)

/-- Every concrete coefficient cycle is bounded by the `2r`-th power of the
entrywise mass. -/
theorem abs_rademacherGramCycleCoefficient_le_entryL1_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {r : ℕ}
    (rows : Fin r → ι) (cols : Fin r → κ)
    (choice : Fin r → ε × ε) :
    |rademacherGramCycleCoefficient A rows cols choice| ≤
      rademacherCoefficientEntryL1 A ^ (2 * r) := by
  unfold rademacherGramCycleCoefficient
  rw [Finset.abs_prod]
  calc
    (∏ t : Fin r,
      |A (choice t).1 (rows t) (cols t) *
        A (choice t).2 (rows (finRotate r t)) (cols t)|) ≤
        ∏ _t : Fin r, rademacherCoefficientEntryL1 A ^ 2 := by
      apply Finset.prod_le_prod
      · intro t _
        positivity
      · intro t _
        rw [abs_mul, pow_two]
        exact mul_le_mul
          (abs_entry_le_rademacherCoefficientEntryL1
            A (choice t).1 (rows t) (cols t))
          (abs_entry_le_rademacherCoefficientEntryL1
            A (choice t).2 (rows (finRotate r t)) (cols t))
          (abs_nonneg _) (rademacherCoefficientEntryL1_nonneg A)
    _ = (rademacherCoefficientEntryL1 A ^ 2) ^ r := by simp
    _ = rademacherCoefficientEntryL1 A ^ (2 * r) := by rw [pow_mul]

/-- Fully unconditional arbitrary-pairing bound.  It is intentionally crude:
the price is the number of row, column, and unconstrained edge choices.  Its
role is to prove finiteness and provide a rigorous fallback, not to claim the
dimension-free NCK exponent. -/
theorem abs_rademacherPerfectMatchingContribution_le_entryL1
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {r : ℕ}
    (matching : Fin r × Bool ≃ Fin (r * 2)) :
    |rademacherPerfectMatchingContribution A matching| ≤
      ((Fintype.card ι : ℝ) ^ r * (Fintype.card κ : ℝ) ^ r) *
        ((Fintype.card ε : ℝ) ^ (2 * r) *
          rademacherCoefficientEntryL1 A ^ (2 * r)) := by
  unfold rademacherPerfectMatchingContribution
  calc
    |∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
        ∑ choice : Fin r → ε × ε,
          if RademacherWordMatchingCompatible choice matching then
            rademacherGramCycleCoefficient A rows cols choice else 0| ≤
      ∑ rows : Fin r → ι, |∑ cols : Fin r → κ,
        ∑ choice : Fin r → ε × ε,
          if RademacherWordMatchingCompatible choice matching then
            rademacherGramCycleCoefficient A rows cols choice else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _rows : Fin r → ι, ∑ cols : Fin r → κ,
        |∑ choice : Fin r → ε × ε,
          if RademacherWordMatchingCompatible choice matching then
            rademacherGramCycleCoefficient A _rows cols choice else 0| := by
      apply Finset.sum_le_sum
      intro rows _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _rows : Fin r → ι, ∑ _cols : Fin r → κ,
        ∑ choice : Fin r → ε × ε,
          |if RademacherWordMatchingCompatible choice matching then
            rademacherGramCycleCoefficient A _rows _cols choice else 0| := by
      apply Finset.sum_le_sum
      intro rows _
      apply Finset.sum_le_sum
      intro cols _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _rows : Fin r → ι, ∑ _cols : Fin r → κ,
        ∑ _choice : Fin r → ε × ε,
          rademacherCoefficientEntryL1 A ^ (2 * r) := by
      apply Finset.sum_le_sum
      intro rows _
      apply Finset.sum_le_sum
      intro cols _
      apply Finset.sum_le_sum
      intro choice _
      split_ifs
      · exact abs_rademacherGramCycleCoefficient_le_entryL1_pow
          A rows cols choice
      · rw [abs_zero]
        exact pow_nonneg (rademacherCoefficientEntryL1_nonneg A) _
    _ = ((Fintype.card ι : ℝ) ^ r * (Fintype.card κ : ℝ) ^ r) *
        ((Fintype.card ε : ℝ) ^ (2 * r) *
          rademacherCoefficientEntryL1 A ^ (2 * r)) := by
      simp [Fintype.card_fun, Fintype.card_prod, pow_mul]
      ring

/-- The sharp single-pairing inequality still required for NCK.  Unlike an
uncrossing assertion, this statement is valid for the original crossing
contribution and contains no change of pairing. -/
def RademacherCrossingPairingSharpBound
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {r : ℕ}
    (matching : Fin r × Bool ≃ Fin (r * 2)) : Prop :=
  |rademacherPerfectMatchingContribution A matching| ≤
    (Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ r

theorem rademacherCrossingPairingSharpBound_of_catalan
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {r : ℕ}
    (M : RademacherNoncrossingMatching r) (hr : 0 < r)
    (matching : Fin r × Bool ≃ Fin (r * 2))
    (h : ∀ choice : Fin r → ε × ε,
      RademacherWordMatchingCompatible choice matching ↔
        RademacherNoncrossingCompatible M choice) :
    RademacherCrossingPairingSharpBound A matching :=
  abs_rademacherPerfectMatchingContribution_le_of_catalan
    A M hr matching h

#print axioms rademacherCoefficientEntryL1_nonneg
#print axioms abs_entry_le_rademacherCoefficientEntryL1
#print axioms abs_rademacherGramCycleCoefficient_le_entryL1_pow
#print axioms abs_rademacherPerfectMatchingContribution_le_entryL1
#print axioms rademacherCrossingPairingSharpBound_of_catalan

end GraphMatrixReplica
