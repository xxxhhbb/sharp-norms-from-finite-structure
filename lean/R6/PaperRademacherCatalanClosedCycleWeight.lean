import R6.PaperRademacherCatalanClosedCycleEquiv

/-! # Closed-cycle coefficient transport

The coordinate equivalence is now concrete.  This file records the exact
occurrence-product identity and isolates the remaining scalar compatibility
with the recursively nested coordinate weight.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica

theorem rademacherGramCycleCoefficient_eq_occurrenceProduct
    {ε ι κ : Type} [Fintype ε] {n : ℕ}
    (A : ε → Matrix ι κ ℝ) (rows : Fin n → ι)
    (cols : Fin n → κ) (choice : Fin n → ε × ε) :
    rademacherGramCycleCoefficient A rows cols choice =
      ∏ s : Fin (2 * n),
        rademacherAlternatingOccurrenceFactor A rows cols choice s :=
  (prod_rademacherAlternatingOccurrenceFactor A rows cols choice).symm

/-- For a compatible word, the original choice has disappeared completely:
the coefficient is the product of the word label and the literal cycle
coordinates at every occurrence. -/
theorem rademacherGramCycleCoefficient_eq_compatibleWordProduct
    {ε ι κ : Type} [Fintype ε] {n : ℕ}
    (A : ε → Matrix ι κ ℝ) (M : RademacherNoncrossingMatching n)
    (word : RademacherCompatibleOccurrenceWord ε M)
    (rows : Fin n → ι) (cols : Fin n → κ) :
    let choiceData :=
      (rademacherCompatibleChoiceOccurrenceWordEquiv M).symm word
    rademacherGramCycleCoefficient A rows cols choiceData.1 =
      ∏ s : Fin (2 * n), A (word.1 s)
        (rademacherCycleOccurrenceRow rows s)
        (rademacherCycleOccurrenceCol cols s) := by
  dsimp only
  let E := rademacherCompatibleChoiceOccurrenceWordEquiv (ε := ε) M
  let choiceData := E.symm word
  have hw : rademacherChoiceOccurrenceWordEquiv ε n choiceData.1 = word.1 := by
    exact congrArg Subtype.val (E.apply_symm_apply word)
  rw [rademacherGramCycleCoefficient_eq_occurrenceProduct]
  apply Finset.prod_congr rfl
  intro s _
  rw [rademacherAlternatingOccurrenceFactor_eq_extracted]
  rw [← rademacherChoiceOccurrenceWordEquiv_apply]
  exact congrArg
    (fun w => A (w s) (rademacherCycleOccurrenceRow rows s)
      (rademacherCycleOccurrenceCol cols s)) hw

/-- The sole pointwise scalar identity left after all coordinate and edge
equivalences have been constructed.  Both sides are explicit finite products;
there is no analytic or matching assumption hidden here. -/
def RademacherCatalanClosedCycleWeightCompatibility
    {ε ι κ : Type} [Fintype ε] {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) : Prop :=
  ∀ (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    (coordinates :
      (Fin (a + b + 1) → ι) × (Fin (a + b + 1) → κ)),
    (∏ s : Fin (2 * (a + b + 1)),
      A (word.1 s)
        (rademacherCycleOccurrenceRow coordinates.1 s)
        (rademacherCycleOccurrenceCol coordinates.2 s)) =
      rademacherRowCoordinateWeight A word
        (rademacherClosedCycleCoordinateDecorationEquiv
          inside outside coordinates).2

/-- A proof of the explicit scalar compatibility completes the exact cycle
coordinate interface. -/
def rademacherCatalanCycleCoordinateEquiv_of_closedCycleWeight
    {ε ι κ : Type} [Fintype ε] {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (h : RademacherCatalanClosedCycleWeightCompatibility A inside outside) :
    RademacherCatalanCycleCoordinateEquiv A inside outside where
  toEquiv := rademacherClosedCycleCoordinateDecorationEquiv inside outside
  weight_eq := by
    intro word coordinates
    dsimp only
    rw [rademacherGramCycleCoefficient_eq_compatibleWordProduct
      A (.node inside outside) word coordinates.1 coordinates.2]
    exact h word coordinates

def rademacherCatalanAssignmentOccurrenceEquiv_of_closedCycleWeight
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (h : RademacherCatalanClosedCycleWeightCompatibility A inside outside) :
    RademacherCatalanAssignmentOccurrenceEquiv A inside outside :=
  rademacherCatalanAssignmentOccurrenceEquiv_of_coordinate A inside outside
    ((rademacherCatalanCycleCoordinateEquiv_of_closedCycleWeight
      A inside outside h).toCoordinateWeightEquiv A inside outside)

theorem rademacherCatalanContributionTraceBridge_of_closedCycleWeight
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (h : RademacherCatalanClosedCycleWeightCompatibility A inside outside) :
    RademacherCatalanContributionTraceBridge A (.node inside outside) :=
  rademacherCatalanContributionTraceBridge_of_assignmentEquiv A inside outside
    (rademacherCatalanAssignmentOccurrenceEquiv_of_closedCycleWeight
      A inside outside h)

theorem abs_rademacherNoncrossingMatchingContribution_le_of_closedCycleWeight
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (h : RademacherCatalanClosedCycleWeightCompatibility A inside outside) :
    |rademacherNoncrossingMatchingContribution A (.node inside outside)| ≤
      (Fintype.card ι : ℝ) *
        rademacherVarianceNormMax A ^ (a + b + 1) :=
  abs_rademacherNoncrossingMatchingContribution_le_of_assignmentEquiv
    A inside outside
      (rademacherCatalanAssignmentOccurrenceEquiv_of_closedCycleWeight
        A inside outside h)

#print axioms rademacherGramCycleCoefficient_eq_occurrenceProduct
#print axioms rademacherGramCycleCoefficient_eq_compatibleWordProduct
#print axioms rademacherCatalanCycleCoordinateEquiv_of_closedCycleWeight
#print axioms rademacherCatalanContributionTraceBridge_of_closedCycleWeight
#print axioms abs_rademacherNoncrossingMatchingContribution_le_of_closedCycleWeight

end GraphMatrixReplica
