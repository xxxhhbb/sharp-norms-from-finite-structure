import GraphMatrix.RademacherCatalanOccurrenceBridge

/-! # The explicit assignment-to-occurrence interface

This file packages the exact remaining finite equivalence.  Its source is
the genuine row/column/coefficient assignment subtype selected by node
compatibility; its target is the closed typed occurrence decoration.  The
finite-sum consequences of a weight-preserving equivalence are proved here,
so the only combinatorial task left is the construction of that equivalence.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Raw cycle assignments at a Catalan node. -/
abbrev RademacherCatalanNodeRawAssignment
    (ε ι κ : Type) (a b : ℕ) :=
  (Fin (a + b + 1) → ι) ×
    ((Fin (a + b + 1) → κ) ×
      (Fin (a + b + 1) → ε × ε))

/-- Genuine assignments, with the original node compatibility proof. -/
def RademacherCatalanNodeCompatibleAssignment
    (ε ι κ : Type) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :=
  {x : RademacherCatalanNodeRawAssignment ε ι κ a b //
    RademacherCatalanNodeCompatible inside outside x.2.2}

instance instDecidableRademacherCatalanNodeCompatible
    {ε : Type} [DecidableEq ε] {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (choice : Fin (a + b + 1) → ε × ε) :
    Decidable (RademacherCatalanNodeCompatible inside outside choice) := by
  classical
  unfold RademacherCatalanNodeCompatible
  infer_instance

noncomputable instance instFintypeRademacherCatalanNodeCompatibleAssignment
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b} :
    Fintype (RademacherCatalanNodeCompatibleAssignment
      ε ι κ inside outside) := by
  unfold RademacherCatalanNodeCompatibleAssignment
  infer_instance

/-- A closed row occurrence decoration is the typed target of the desired
reindexing. -/
abbrev RademacherCatalanNodeClosedOccurrence
    (ε ι κ : Type) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :=
  Σ i : ι, RademacherRowOccurrenceDecoration ε ι κ
    (.node inside outside) i i

/-- Coefficient weight on a genuine compatible cycle assignment. -/
def rademacherCatalanNodeAssignmentWeight
    {ε ι κ : Type} {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (x : RademacherCatalanNodeCompatibleAssignment ε ι κ inside outside) : ℝ :=
  rademacherGramCycleCoefficient A x.1.1 x.1.2.1 x.1.2.2

/-- Coefficient weight on a closed typed occurrence decoration. -/
def rademacherCatalanNodeOccurrenceWeight
    {ε ι κ : Type} {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (d : RademacherCatalanNodeClosedOccurrence ε ι κ inside outside) : ℝ :=
  rademacherRowOccurrenceWeight A d.2

/-- The precise data needed from the last combinatorial construction: an
actual equivalence and pointwise preservation of the genuine coefficient.
Nothing analytic is included in this structure. -/
structure RademacherCatalanAssignmentOccurrenceEquiv
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) where
  toEquiv :
    RademacherCatalanNodeCompatibleAssignment ε ι κ inside outside ≃
      RademacherCatalanNodeClosedOccurrence ε ι κ inside outside
  weight_eq : ∀ x,
    rademacherCatalanNodeAssignmentWeight A x =
      rademacherCatalanNodeOccurrenceWeight A (toEquiv x)

/-- Any constructed assignment/occurrence equivalence transports the full
finite coefficient sum, including all multiplicities. -/
theorem RademacherCatalanAssignmentOccurrenceEquiv.sum_weights
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (E : RademacherCatalanAssignmentOccurrenceEquiv A inside outside) :
    (∑ x : RademacherCatalanNodeCompatibleAssignment ε ι κ inside outside,
      rademacherCatalanNodeAssignmentWeight A x) =
      ∑ d : RademacherCatalanNodeClosedOccurrence ε ι κ inside outside,
        rademacherCatalanNodeOccurrenceWeight A d := by
  exact Fintype.sum_equiv E.toEquiv _ _ E.weight_eq

/-- Converting an `if compatible` sum to the genuine compatible subtype loses
no terms. -/
theorem sum_nodeAssignments_ite_eq_compatibleSubtype
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    (∑ rows : Fin (a + b + 1) → ι,
      ∑ cols : Fin (a + b + 1) → κ,
      ∑ choice : Fin (a + b + 1) → ε × ε,
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) =
      ∑ x : RademacherCatalanNodeCompatibleAssignment ε ι κ inside outside,
        rademacherCatalanNodeAssignmentWeight A x := by
  classical
  let p : RademacherCatalanNodeRawAssignment ε ι κ a b → Prop :=
    fun x => RademacherCatalanNodeCompatible inside outside x.2.2
  let f : RademacherCatalanNodeRawAssignment ε ι κ a b → ℝ :=
    fun x => rademacherGramCycleCoefficient A x.1 x.2.1 x.2.2
  calc
    (∑ rows : Fin (a + b + 1) → ι,
      ∑ cols : Fin (a + b + 1) → κ,
      ∑ choice : Fin (a + b + 1) → ε × ε,
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) =
        ∑ x : RademacherCatalanNodeRawAssignment ε ι κ a b,
          if p x then f x else 0 := by
            simp [p, f, RademacherCatalanNodeRawAssignment,
              Fintype.sum_prod_type]
    _ = ∑ x ∈ Finset.univ.filter p, f x := by
      simpa using (Finset.sum_filter p f).symm
    _ = ∑ x : {x // p x}, f x := by
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := by rfl

/-- The unsplit assignment sum and the root/inside/outside Fubini form used
by `RademacherCatalanNodeAssignmentsToOccurrenceIdentity` are equal. -/
theorem sum_nodeAssignments_eq_root_inside_outside
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    (∑ rows : Fin (a + b + 1) → ι,
      ∑ cols : Fin (a + b + 1) → κ,
      ∑ choice : Fin (a + b + 1) → ε × ε,
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) =
    (∑ rowRoot : ι, ∑ rowInside : Fin a → ι,
      ∑ rowOutside : Fin b → ι,
      ∑ colRoot : κ, ∑ colInside : Fin a → κ,
      ∑ colOutside : Fin b → κ,
      ∑ choiceRoot : ε × ε, ∑ choiceInside : Fin a → ε × ε,
      ∑ choiceOutside : Fin b → ε × ε,
        let rows := (rademacherCatalanNodeRowsEquiv ι a b).symm
          (rowRoot, rowInside, rowOutside)
        let cols := (rademacherCatalanNodeColsEquiv κ a b).symm
          (colRoot, colInside, colOutside)
        let choice := (rademacherCatalanNodeChoicesEquiv ε a b).symm
          (choiceRoot, choiceInside, choiceOutside)
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) := by
  rw [sum_nodeFunctions_eq_sum_root_inside_outside]
  simp_rw [sum_nodeFunctions_eq_sum_root_inside_outside]
  simp only [rademacherCatalanNodeRowsEquiv,
    rademacherCatalanNodeColsEquiv,
    rademacherCatalanNodeChoicesEquiv]
  rfl

theorem sum_nodeRows_eq_sum_root_inside_outside
    {ι : Type} [Fintype ι] {a b : ℕ}
    (F : (Fin (a + b + 1) → ι) → ℝ) :
    (∑ rows, F rows) =
      ∑ root : ι, ∑ inside : Fin a → ι, ∑ outside : Fin b → ι,
        F ((rademacherCatalanNodeRowsEquiv ι a b).symm
          (root, inside, outside)) :=
  sum_nodeFunctions_eq_sum_root_inside_outside F

theorem sum_nodeCols_eq_sum_root_inside_outside
    {κ : Type} [Fintype κ] {a b : ℕ}
    (F : (Fin (a + b + 1) → κ) → ℝ) :
    (∑ cols, F cols) =
      ∑ root : κ, ∑ inside : Fin a → κ, ∑ outside : Fin b → κ,
        F ((rademacherCatalanNodeColsEquiv κ a b).symm
          (root, inside, outside)) :=
  sum_nodeFunctions_eq_sum_root_inside_outside F

theorem sum_nodeChoices_eq_sum_root_inside_outside
    {ε : Type} [Fintype ε] {a b : ℕ}
    (F : (Fin (a + b + 1) → ε × ε) → ℝ) :
    (∑ choice, F choice) =
      ∑ root : ε × ε, ∑ inside : Fin a → ε × ε,
      ∑ outside : Fin b → ε × ε,
        F ((rademacherCatalanNodeChoicesEquiv ε a b).symm
          (root, inside, outside)) :=
  sum_nodeFunctions_eq_sum_root_inside_outside F

/-- A concrete weight-preserving equivalence identifies the genuine unsplit
compatible assignment sum with the closed occurrence sum. -/
theorem sum_nodeAssignments_eq_occurrences_of_equiv
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (E : RademacherCatalanAssignmentOccurrenceEquiv A inside outside) :
    (∑ rows : Fin (a + b + 1) → ι,
      ∑ cols : Fin (a + b + 1) → κ,
      ∑ choice : Fin (a + b + 1) → ε × ε,
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) =
      ∑ i : ι,
        ∑ d : RademacherRowOccurrenceDecoration ε ι κ
            (.node inside outside) i i,
          rademacherRowOccurrenceWeight A d := by
  classical
  calc
    _ = ∑ x : RademacherCatalanNodeCompatibleAssignment
          ε ι κ inside outside,
        rademacherCatalanNodeAssignmentWeight A x :=
      sum_nodeAssignments_ite_eq_compatibleSubtype A inside outside
    _ = ∑ d : RademacherCatalanNodeClosedOccurrence
          ε ι κ inside outside,
        rademacherCatalanNodeOccurrenceWeight A d := E.sum_weights
    _ = _ := fintypeSum_sigma_explicit _ _

/-- Once the explicit equivalence is constructed, the genuine node
contribution (with the original `pairList` compatibility predicate) equals
the trace, without passing through the legacy scalar residual. -/
theorem rademacherCatalanContributionTraceBridge_of_assignmentEquiv
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (E : RademacherCatalanAssignmentOccurrenceEquiv A inside outside) :
    RademacherCatalanContributionTraceBridge A (.node inside outside) := by
  classical
  unfold RademacherCatalanContributionTraceBridge
  unfold rademacherNoncrossingMatchingContribution
  have hcompat :
      (∑ rows : Fin (a + b + 1) → ι,
        ∑ cols : Fin (a + b + 1) → κ,
        ∑ choice : Fin (a + b + 1) → ε × ε,
          if RademacherNoncrossingCompatible (.node inside outside) choice then
            rademacherGramCycleCoefficient A rows cols choice else 0) =
      (∑ rows : Fin (a + b + 1) → ι,
        ∑ cols : Fin (a + b + 1) → κ,
        ∑ choice : Fin (a + b + 1) → ε × ε,
          if RademacherCatalanNodeCompatible inside outside choice then
            rademacherGramCycleCoefficient A rows cols choice else 0) := by
    apply Finset.sum_congr rfl
    intro rows _
    apply Finset.sum_congr rfl
    intro cols _
    apply Finset.sum_congr rfl
    intro choice _
    by_cases h : RademacherNoncrossingCompatible
        (.node inside outside) choice
    · have hn := (rademacherNoncrossingCompatible_node_iff
        inside outside choice).mp h
      simp [h, hn]
    · have hn : ¬RademacherCatalanNodeCompatible inside outside choice := by
        intro hc
        exact h ((rademacherNoncrossingCompatible_node_iff
          inside outside choice).mpr hc)
      simp [h, hn]
  rw [hcompat]
  rw [sum_nodeAssignments_eq_occurrences_of_equiv A inside outside E]
  exact (trace_rademacherRowOpenWord_eq_occurrenceDecorationSum
    A (.node inside outside)).symm

/-- The sharp already-proved analytic estimate is therefore available for a
node as soon as its purely finite assignment equivalence is supplied. -/
theorem abs_rademacherNoncrossingMatchingContribution_le_of_assignmentEquiv
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (E : RademacherCatalanAssignmentOccurrenceEquiv A inside outside) :
    |rademacherNoncrossingMatchingContribution A (.node inside outside)| ≤
      (Fintype.card ι : ℝ) *
        rademacherVarianceNormMax A ^ (a + b + 1) :=
  abs_rademacherNoncrossingMatchingContribution_le_of_traceBridge
    A (.node inside outside)
      (rademacherCatalanContributionTraceBridge_of_assignmentEquiv
        A inside outside E)


end GraphMatrixReplica
