import R6.PaperRademacherCatalanContributionBound

/-! # The finite reindexing behind the Catalan trace bridge

The compatibility predicate for a Catalan node is split exactly into its
root, inside, and outside pair constraints.  Positive-order trees are then
reduced to one concrete node-level finite-sum reindexing statement.  This
file does not silently assume that reindexing statement.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The three literal compatibility clauses obtained from a Catalan node's
recursive pair list.  They are deliberately expressed in the ambient word,
so no coordinate transport is hidden in the definition. -/
def RademacherCatalanNodeCompatible
    {ε : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (choice : Fin (a + b + 1) → ε × ε) : Prop :=
  (rademacherNatEdgeLabel choice 0 (by omega) =
      rademacherNatEdgeLabel choice (2 * a + 1) (by omega)) ∧
  (∀ i j, ∀ h : (i, j) ∈ inside.pairList,
    rademacherNatEdgeLabel choice (i + 1) (by
        have hi := (inside.pairList_endpoints_lt h).1
        omega) =
      rademacherNatEdgeLabel choice (j + 1) (by
        have hj := (inside.pairList_endpoints_lt h).2
        omega)) ∧
  (∀ i j, ∀ h : (i, j) ∈ outside.pairList,
    rademacherNatEdgeLabel choice (i + (2 * a + 2)) (by
        have hi := (outside.pairList_endpoints_lt h).1
        omega) =
      rademacherNatEdgeLabel choice (j + (2 * a + 2)) (by
        have hj := (outside.pairList_endpoints_lt h).2
        omega))

/-- `pairList` compatibility of a node is exactly the conjunction of its
root, shifted-inside, and shifted-outside clauses. -/
theorem rademacherNoncrossingCompatible_node_iff
    {ε : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (choice : Fin (a + b + 1) → ε × ε) :
    RademacherNoncrossingCompatible (.node inside outside) choice ↔
      RademacherCatalanNodeCompatible inside outside choice := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply h 0 (2 * a + 1)
      simp [RademacherNoncrossingMatching.pairList]
    · intro i j hp
      apply h (i + 1) (j + 1)
      simp [RademacherNoncrossingMatching.pairList, hp]
    · intro i j hp
      apply h (i + (2 * a + 2)) (j + (2 * a + 2))
      simp [RademacherNoncrossingMatching.pairList, hp]
  · rintro ⟨hroot, hin, hout⟩ i j hp
    rw [RademacherNoncrossingMatching.pairList] at hp
    rcases List.mem_cons.mp hp with hroot' | hrest
    · injection hroot' with hi hj
      subst i
      subst j
      exact hroot
    · rcases List.mem_append.mp hrest with hinside | houtside
      · obtain ⟨⟨i', j'⟩, hp', hij⟩ := List.mem_map.mp hinside
        injection hij with hi hj
        subst i
        subst j
        exact hin i' j' hp'
      · obtain ⟨⟨i', j'⟩, hp', hij⟩ := List.mem_map.mp houtside
        injection hij with hi hj
        subst i
        subst j
        exact hout i' j' hp'

/-- Every positive-order Catalan tree is a node, with its index equality
recorded explicitly. -/
theorem exists_node_of_positive_rademacherNoncrossingMatching
    {n : ℕ} (M : RademacherNoncrossingMatching n) (hn : 0 < n) :
    ∃ a b, ∃ inside : RademacherNoncrossingMatching a,
      ∃ outside : RademacherNoncrossingMatching b,
        n = a + b + 1 ∧
          HEq M (RademacherNoncrossingMatching.node inside outside) := by
  cases M with
  | empty => omega
  | @node a b inside outside =>
      exact ⟨a, b, inside, outside, rfl, HEq.rfl⟩

/-- The sole remaining finite Fubini/reindexing statement.  Its left side is
the genuine alternating coefficient-cycle sum, and its right side is the
literal node expansion of the typed open word.  Unlike an abstract bridge,
this exposes the exact node and all original model quantifiers. -/
def RademacherCatalanNodeFinsetReindex
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) : Prop := by
  classical
  exact
    (∑ rows : Fin (a + b + 1) → ι,
      ∑ cols : Fin (a + b + 1) → κ,
      ∑ choice : Fin (a + b + 1) → ε × ε,
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) =
      Matrix.trace
        (rademacherRowSandwich A (rademacherColumnOpenWord A inside) *
          rademacherRowOpenWord A outside)

/-- The concrete node reindexing is equivalent to the trace bridge for that
node; the proof uses the exact compatibility decomposition above. -/
theorem rademacherCatalanNodeFinsetReindex_iff_traceBridge
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanNodeFinsetReindex A inside outside ↔
      RademacherCatalanContributionTraceBridge A (.node inside outside) := by
  classical
  unfold RademacherCatalanNodeFinsetReindex
  unfold RademacherCatalanContributionTraceBridge
  unfold rademacherNoncrossingMatchingContribution
  simp only [rademacherRowOpenWord]
  have hsum :
      (∑ rows : Fin (a + b + 1) → ι,
        ∑ cols : Fin (a + b + 1) → κ,
        ∑ choice : Fin (a + b + 1) → ε × ε,
          if RademacherCatalanNodeCompatible inside outside choice then
            rademacherGramCycleCoefficient A rows cols choice else 0) =
      (∑ rows : Fin (a + b + 1) → ι,
        ∑ cols : Fin (a + b + 1) → κ,
        ∑ choice : Fin (a + b + 1) → ε × ε,
          if RademacherNoncrossingCompatible (.node inside outside) choice then
            rademacherGramCycleCoefficient A rows cols choice else 0) := by
    apply Finset.sum_congr rfl
    intro rows hrows
    apply Finset.sum_congr rfl
    intro cols hcols
    apply Finset.sum_congr rfl
    intro choice hchoice
    by_cases hc : RademacherNoncrossingCompatible (.node inside outside) choice
    · simp [hc, (rademacherNoncrossingCompatible_node_iff
        inside outside choice).mp hc]
    · have hn : ¬RademacherCatalanNodeCompatible inside outside choice := by
        intro h
        exact hc ((rademacherNoncrossingCompatible_node_iff
          inside outside choice).mpr h)
      simp [hc, hn]
  rw [hsum]

/-- If the single concrete node-level reindexing is supplied for every pair
of subtrees, then every positive-order Catalan trace bridge follows.  The
empty tree is intentionally excluded because its genuine empty cycle sum is
`1`, whereas `trace (1)` is the row dimension. -/
theorem rademacherCatalanContributionTraceBridge_of_nodeFinsetReindex
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ)
    (hnode : ∀ {a b : ℕ}
      (inside : RademacherNoncrossingMatching a)
      (outside : RademacherNoncrossingMatching b),
        RademacherCatalanNodeFinsetReindex A inside outside)
    {n : ℕ} (M : RademacherNoncrossingMatching n) (hn : 0 < n) :
    RademacherCatalanContributionTraceBridge A M := by
  cases M with
  | empty => omega
  | node inside outside =>
      exact (rademacherCatalanNodeFinsetReindex_iff_traceBridge
        A inside outside).mp (hnode inside outside)

/-- Consequently the already-proved sharp analytic estimate applies to all
positive Catalan contributions once, and only once, the concrete reindexing
lemma is discharged. -/
theorem abs_rademacherNoncrossingMatchingContribution_le_of_nodeFinsetReindex
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ)
    (hnode : ∀ {a b : ℕ}
      (inside : RademacherNoncrossingMatching a)
      (outside : RademacherNoncrossingMatching b),
        RademacherCatalanNodeFinsetReindex A inside outside)
    {n : ℕ} (M : RademacherNoncrossingMatching n) (hn : 0 < n) :
    |rademacherNoncrossingMatchingContribution A M| ≤
      (Fintype.card ι : ℝ) * rademacherVarianceNormMax A ^ n :=
  abs_rademacherNoncrossingMatchingContribution_le_of_traceBridge A M
    (rademacherCatalanContributionTraceBridge_of_nodeFinsetReindex
      A hnode M hn)

#print axioms rademacherNoncrossingCompatible_node_iff
#print axioms exists_node_of_positive_rademacherNoncrossingMatching
#print axioms rademacherCatalanNodeFinsetReindex_iff_traceBridge
#print axioms
  rademacherCatalanContributionTraceBridge_of_nodeFinsetReindex
#print axioms
  abs_rademacherNoncrossingMatchingContribution_le_of_nodeFinsetReindex

end GraphMatrixReplica
