import GraphMatrix.RademacherCrossingPairingBound

/-! # Canonical finite decomposition of even Rademacher words

The decomposition below never compares signed summands term by term.  An
even word is assigned to one matching code, and the exact trace sum is then
partitioned into disjoint code classes.  Consequently triangle inequality is
applied only after the exact partition.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

set_option maxHeartbeats 1600000

/-- A concrete enumeration of unlabelled perfect matchings by the recursive
odd-double-factorial code.  `complete` is precisely the remaining pure finite
decoder/coverage obligation. -/
structure RademacherPerfectMatchingEnumeration (r : ℕ) where
  matching : RademacherPerfectMatchingCode r →
    (Fin r × Bool ≃ Fin (r * 2))
  complete : ∀ {epsilon : Type} [Fintype epsilon] [DecidableEq epsilon]
      (choice : Fin r → epsilon × epsilon),
    (∀ e, Even ((rademacherPairEdgeWord choice).count e)) →
      ∃ code : RademacherPerfectMatchingCode r,
        RademacherWordMatchingCompatible choice (matching code)

/-- A default recursive matching code, used only for non-even words which do
not contribute to the trace sum. -/
def defaultRademacherPerfectMatchingCode :
    ∀ r : ℕ, RademacherPerfectMatchingCode r
  | 0 => PUnit.unit
  | r + 1 => (⟨0, by omega⟩, defaultRademacherPerfectMatchingCode r)

/-- Canonically choose one compatible matching code for an even word.  The
choice is made once; later class sums are therefore disjoint. -/
def rademacherEvenWordCanonicalCode
    {epsilon : Type} [Fintype epsilon] [DecidableEq epsilon]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (choice : Fin r → epsilon × epsilon) :
    RademacherPerfectMatchingCode r :=
  if hEven : ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
    Classical.choose (enumeration.complete choice hEven)
  else
    defaultRademacherPerfectMatchingCode r

theorem rademacherEvenWordCanonicalCode_compatible
    {epsilon : Type} [Fintype epsilon] [DecidableEq epsilon]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (choice : Fin r → epsilon × epsilon)
    (hEven : ∀ e, Even ((rademacherPairEdgeWord choice).count e)) :
    RademacherWordMatchingCompatible choice
      (enumeration.matching
        (rademacherEvenWordCanonicalCode enumeration choice)) := by
  unfold rademacherEvenWordCanonicalCode
  rw [dif_pos hEven]
  exact Classical.choose_spec (enumeration.complete choice hEven)

/-- Contribution of one disjoint canonical pairing class.  Membership uses
both evenness and equality with the single selected code. -/
def rademacherCanonicalPairingClassContribution
    {epsilon rows cols : Type}
    [Fintype epsilon] [Fintype rows] [Fintype cols]
    [DecidableEq epsilon]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (A : epsilon → Matrix rows cols ℝ)
    (code : RademacherPerfectMatchingCode r) : ℝ :=
  ∑ rowValues : Fin r → rows, ∑ colValues : Fin r → cols,
    ∑ choice : Fin r → epsilon × epsilon,
      if (∀ e, Even ((rademacherPairEdgeWord choice).count e)) ∧
          rademacherEvenWordCanonicalCode enumeration choice = code then
        rademacherGramCycleCoefficient A rowValues colValues choice
      else 0

/-- Every even word occurs in exactly one canonical code class.  This is an
exact equality and is valid for signed cycle coefficients. -/
theorem rademacherEvenEdgeTraceSum_eq_sum_canonicalPairingClasses
    {epsilon rows cols : Type}
    [Fintype epsilon] [Fintype rows] [Fintype cols]
    [DecidableEq epsilon]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (A : epsilon → Matrix rows cols ℝ) :
    rademacherEvenEdgeTraceSum A r =
      ∑ code : RademacherPerfectMatchingCode r,
        rademacherCanonicalPairingClassContribution enumeration A code := by
  classical
  unfold rademacherEvenEdgeTraceSum
    rademacherCanonicalPairingClassContribution
  calc
    (∑ rowValues : Fin r → rows, ∑ colValues : Fin r → cols,
      ∑ choice : Fin r → epsilon × epsilon,
        if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
          rademacherGramCycleCoefficient A rowValues colValues choice else 0) =
      ∑ rowValues : Fin r → rows, ∑ colValues : Fin r → cols,
        ∑ choice : Fin r → epsilon × epsilon,
          ∑ code : RademacherPerfectMatchingCode r,
            if (∀ e, Even ((rademacherPairEdgeWord choice).count e)) ∧
                rademacherEvenWordCanonicalCode enumeration choice = code then
              rademacherGramCycleCoefficient A rowValues colValues choice
            else 0 := by
      apply Finset.sum_congr rfl
      intro rowValues _
      apply Finset.sum_congr rfl
      intro colValues _
      apply Finset.sum_congr rfl
      intro choice _
      by_cases hEven : ∀ e,
          Even ((rademacherPairEdgeWord choice).count e)
      · simp [hEven]
      · simp [hEven]
    _ = ∑ code : RademacherPerfectMatchingCode r,
        ∑ rowValues : Fin r → rows, ∑ colValues : Fin r → cols,
          ∑ choice : Fin r → epsilon × epsilon,
            if (∀ e, Even ((rademacherPairEdgeWord choice).count e)) ∧
                rademacherEvenWordCanonicalCode enumeration choice = code then
              rademacherGramCycleCoefficient A rowValues colValues choice
            else 0 := by
      calc
        _ = ∑ rowValues : Fin r → rows,
            ∑ colValues : Fin r → cols,
              ∑ code : RademacherPerfectMatchingCode r,
                ∑ choice : Fin r → epsilon × epsilon,
                  if (∀ e, Even ((rademacherPairEdgeWord choice).count e)) ∧
                      rademacherEvenWordCanonicalCode enumeration choice = code then
                    rademacherGramCycleCoefficient A rowValues colValues choice
                  else 0 := by
          apply Finset.sum_congr rfl
          intro rowValues _
          apply Finset.sum_congr rfl
          intro colValues _
          exact Finset.sum_comm
        _ = ∑ rowValues : Fin r → rows,
            ∑ code : RademacherPerfectMatchingCode r,
              ∑ colValues : Fin r → cols,
                ∑ choice : Fin r → epsilon × epsilon,
                  if (∀ e, Even ((rademacherPairEdgeWord choice).count e)) ∧
                      rademacherEvenWordCanonicalCode enumeration choice = code then
                    rademacherGramCycleCoefficient A rowValues colValues choice
                  else 0 := by
          apply Finset.sum_congr rfl
          intro rowValues _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

/-- Sharp bound on one disjoint canonical pairing class. -/
def RademacherCanonicalPairingClassSharpBound
    {epsilon rows cols : Type}
    [Fintype epsilon] [Fintype rows] [Fintype cols]
    [DecidableEq epsilon] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (A : epsilon → Matrix rows cols ℝ)
    (code : RademacherPerfectMatchingCode r) : Prop :=
  |rademacherCanonicalPairingClassContribution enumeration A code| ≤
    (Fintype.card rows : ℝ) * rademacherVarianceNormMax A ^ r

/-- Exact canonical decomposition plus a sharp bound for each disjoint class
implies the crossing-matching reduction with the exact double-factorial
count. -/
theorem rademacherCrossingMatchingReduction_of_canonicalClasses
    {epsilon rows cols : Type}
    [Fintype epsilon] [Fintype rows] [Fintype cols]
    [DecidableEq epsilon] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (A : epsilon → Matrix rows cols ℝ)
    (hSharp : ∀ code,
      RademacherCanonicalPairingClassSharpBound enumeration A code) :
    RademacherCrossingMatchingReduction A r := by
  unfold RademacherCrossingMatchingReduction
  rw [rademacherEvenEdgeTraceSum_eq_sum_canonicalPairingClasses enumeration A]
  let E := (Fintype.card rows : ℝ) * rademacherVarianceNormMax A ^ r
  calc
    (∑ code : RademacherPerfectMatchingCode r,
        rademacherCanonicalPairingClassContribution enumeration A code) ≤
      ∑ code : RademacherPerfectMatchingCode r,
        |rademacherCanonicalPairingClassContribution enumeration A code| := by
      apply Finset.sum_le_sum
      intro code _
      exact le_abs_self _
    _ ≤ ∑ _code : RademacherPerfectMatchingCode r, E := by
      apply Finset.sum_le_sum
      intro code _
      simpa [RademacherCanonicalPairingClassSharpBound, E] using hSharp code
    _ = (rademacherPerfectMatchingCount r : ℝ) * E := by
      rw [← card_rademacherPerfectMatchingCode]
      simp [E, nsmul_eq_mul]

/-- The precise extra cancellation/positivity statement needed to pass from
the already named full compatible-matching contribution to a disjoint
canonical subsum.  It is not silently assumed by the decomposition. -/
def RademacherCanonicalClassSubsumDomination
    {epsilon rows cols : Type}
    [Fintype epsilon] [Fintype rows] [Fintype cols]
    [DecidableEq epsilon] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (A : epsilon → Matrix rows cols ℝ) : Prop :=
  ∀ code : RademacherPerfectMatchingCode r,
    |rademacherCanonicalPairingClassContribution enumeration A code| ≤
      |rademacherPerfectMatchingContribution A (enumeration.matching code)|

/-- With the explicit subsum-domination statement, sharp bounds for the full
matching contributions imply the crossing reduction. -/
theorem rademacherCrossingMatchingReduction_of_pairingSharpBounds
    {epsilon rows cols : Type}
    [Fintype epsilon] [Fintype rows] [Fintype cols]
    [DecidableEq epsilon] [DecidableEq rows] [DecidableEq cols]
    {r : ℕ} (enumeration : RademacherPerfectMatchingEnumeration r)
    (A : epsilon → Matrix rows cols ℝ)
    (hSubsum : RademacherCanonicalClassSubsumDomination enumeration A)
    (hPairing : ∀ code : RademacherPerfectMatchingCode r,
      RademacherCrossingPairingSharpBound A (enumeration.matching code)) :
    RademacherCrossingMatchingReduction A r := by
  apply rademacherCrossingMatchingReduction_of_canonicalClasses enumeration A
  intro code
  exact (hSubsum code).trans (hPairing code)


end GraphMatrixReplica
