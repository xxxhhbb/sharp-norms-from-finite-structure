import GraphMatrix.RademacherConcreteAdjacentContraction

/-! # Recursive noncrossing matchings on the original coefficient word

The Catalan matching relation uses natural positions.  Here it is transported
to the original alternating `Fin r × Bool` edge-occurrence word through the
canonical linear-position equivalence.  Thus the contribution below uses the
same row/column cycle coefficient as the dyadic trace expansion, rather than
a surrogate matrix model.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica
namespace RademacherNoncrossingMatching

/-- Every pair listed by the recursive encoding is certified by `Matched`. -/
theorem matched_of_mem_pairList
    {n i j : ℕ} {M : RademacherNoncrossingMatching n}
    (h : (i, j) ∈ M.pairList) : M.Matched i j := by
  induction M generalizing i j with
  | empty => simp [pairList] at h
  | @node a b inside outside ihInside ihOutside =>
      rw [pairList] at h
      rcases List.mem_cons.mp h with hroot | hrest
      · injection hroot with hi hj
        subst i
        subst j
        exact Matched.outer inside outside
      · rcases List.mem_append.mp hrest with hinside | houtside
        · obtain ⟨⟨i', j'⟩, hz, hij⟩ := List.mem_map.mp hinside
          injection hij with hi hj
          subst i
          subst j
          exact Matched.inside (ihInside hz)
        · obtain ⟨⟨i', j'⟩, hz, hij⟩ := List.mem_map.mp houtside
          injection hij with hi hj
          subst i
          subst j
          exact Matched.outside (ihOutside hz)

/-- Consequently, all listed endpoints lie in the original `2n`-word. -/
theorem pairList_endpoints_lt
    {n i j : ℕ} {M : RademacherNoncrossingMatching n}
    (h : (i, j) ∈ M.pairList) : i < 2 * n ∧ j < 2 * n := by
  have hm := matched_of_mem_pairList h
  exact ⟨(hm.lt_and_right_lt.1).trans hm.lt_and_right_lt.2,
    hm.lt_and_right_lt.2⟩

/-- The adjacent pair selected by a deletion certificate occurs in the
concrete recursive pair list. -/
theorem mem_pairList_of_deletesAdjacent
    {n m i : ℕ} {M : RademacherNoncrossingMatching n}
    {M' : RademacherNoncrossingMatching m}
    (h : M.DeletesAdjacent i M') : (i, i + 1) ∈ M.pairList := by
  induction h with
  | root outside => simp [pairList]
  | descend h ih =>
      rw [pairList]
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      convert List.mem_map_of_mem ih using 1

@[simp] theorem pairList_cast
    {n m : ℕ} (h : n = m) (M : RademacherNoncrossingMatching n) :
    (h ▸ M).pairList = M.pairList := by
  subst m
  rfl

end RademacherNoncrossingMatching

/-- The original alternating occurrence at a bounded natural word position. -/
def rademacherOccurrenceOfNat {r : ℕ} (i : ℕ) (hi : i < 2 * r) : Replica r :=
  (rademacherCanonicalMatching r).symm ⟨i, by omega⟩

/-- The edge label of the original alternating word at a natural position. -/
def rademacherNatEdgeLabel
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε)
    (i : ℕ) (hi : i < 2 * r) : ε :=
  rademacherDirectEdgeLabel choice (rademacherOccurrenceOfNat i hi)

@[simp] theorem rademacherNatEdgeLabel_even
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) (t : Fin r) :
    rademacherNatEdgeLabel choice (t.1 * 2) (by omega) = (choice t).1 := by
  unfold rademacherNatEdgeLabel rademacherOccurrenceOfNat
  have heq : (⟨t.1 * 2, by omega⟩ : Fin (r * 2)) =
      rademacherCanonicalMatching r (t, false) := by
    symm
    exact rademacherCanonicalMatching_false t
  rw [heq, Equiv.symm_apply_apply]
  rfl

@[simp] theorem rademacherNatEdgeLabel_odd
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) (t : Fin r) :
    rademacherNatEdgeLabel choice (t.1 * 2 + 1) (by omega) =
      (choice t).2 := by
  unfold rademacherNatEdgeLabel rademacherOccurrenceOfNat
  have heq : (⟨t.1 * 2 + 1, by omega⟩ : Fin (r * 2)) =
      rademacherCanonicalMatching r (t, true) := by
    symm
    exact rademacherCanonicalMatching_true t
  rw [heq, Equiv.symm_apply_apply]
  rfl

/-- Compatibility of a Catalan matching with the actual alternating edge
word, expressed using its concrete recursive list of pairs. -/
def RademacherNoncrossingCompatible
    {ε : Type} {r : ℕ} (M : RademacherNoncrossingMatching r)
    (choice : Fin r → ε × ε) : Prop :=
  ∀ i j, ∀ h : (i, j) ∈ M.pairList,
    rademacherNatEdgeLabel choice i
        (M.pairList_endpoints_lt h).1 =
      rademacherNatEdgeLabel choice j
        (M.pairList_endpoints_lt h).2

instance instDecidableRademacherNoncrossingCompatible
    {ε : Type} [DecidableEq ε] {r : ℕ}
    (M : RademacherNoncrossingMatching r)
    (choice : Fin r → ε × ε) :
    Decidable (RademacherNoncrossingCompatible M choice) := by
  classical
  unfold RademacherNoncrossingCompatible
  infer_instance

/-- The genuine original coefficient-cycle contribution selected by a
recursive noncrossing matching. -/
def rademacherNoncrossingMatchingContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) (M : RademacherNoncrossingMatching r) : ℝ :=
  ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
    ∑ choice : Fin r → ε × ε,
      if RademacherNoncrossingCompatible M choice then
        rademacherGramCycleCoefficient A rows cols choice else 0

/-- Exact row-parity deletion inside arbitrary scalar left/right contexts.
After all other finite indices are fixed, those contexts are constants for
the adjacent edge and column sums. -/
theorem sum_adjacentRowPair_with_context
    {ε ι κ : Type} [Fintype ε] [Fintype κ]
    (A : ε → Matrix ι κ ℝ) (i j : ι) (left right : ℝ) :
    (∑ col : κ, ∑ e : ε,
      left * (A e i col * A e j col) * right) =
      left * rademacherRowVariance A i j * right := by
  have h := congrArg (fun z : ℝ => left * z)
    (sum_adjacentRowPair_mul_const A i j right)
  simpa only [Finset.mul_sum, mul_assoc] using h

/-- Exact column-parity deletion inside arbitrary scalar contexts. -/
theorem sum_adjacentColumnPair_with_context
    {ε ι κ : Type} [Fintype ε] [Fintype ι]
    (A : ε → Matrix ι κ ℝ) (i j : κ) (left right : ℝ) :
    (∑ row : ι, ∑ e : ε,
      left * (A e row i * A e row j) * right) =
      left * rademacherColumnVariance A i j * right := by
  have h := congrArg (fun z : ℝ => left * z)
    (sum_adjacentColumnPair_mul_const A i j right)
  simpa only [Finset.mul_sum, mul_assoc] using h

/-- A listed adjacent pair really forces equality of the corresponding two
labels in the original coefficient word. -/
theorem natEdgeLabel_eq_of_noncrossingCompatible
    {ε : Type} {r m i : ℕ} {M : RademacherNoncrossingMatching r}
    {choice : Fin r → ε × ε}
    (hcompat : RademacherNoncrossingCompatible M choice)
    {M' : RademacherNoncrossingMatching m}
    (hdelete : M.DeletesAdjacent i M') :
    rademacherNatEdgeLabel choice i
        (hdelete.matched.lt_and_right_lt.1.trans
          hdelete.matched.lt_and_right_lt.2) =
      rademacherNatEdgeLabel choice (i + 1)
        hdelete.matched.lt_and_right_lt.2 := by
  apply hcompat i (i + 1)
  exact RademacherNoncrossingMatching.mem_pairList_of_deletesAdjacent hdelete


end GraphMatrixReplica
