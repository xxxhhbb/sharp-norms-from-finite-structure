import GraphMatrix.RademacherDihedralMatching

/-! # Recursive noncrossing perfect matchings

We use the standard Catalan first-pair decomposition. A node with `a` pairs
inside and `b` pairs outside matches position `0` to position `2a+1`, places
the inside matching on positions `1,...,2a`, and shifts the outside matching
past the first `2a+2` positions. Noncrossing is therefore a construction
invariant rather than an unproved predicate.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Catalan encoding of a noncrossing perfect matching with `n` pairs on
`2n` linearly ordered occurrence positions. -/
inductive RademacherNoncrossingMatching : ℕ → Type
  | empty : RademacherNoncrossingMatching 0
  | node {a b : ℕ}
      (inside : RademacherNoncrossingMatching a)
      (outside : RademacherNoncrossingMatching b) :
      RademacherNoncrossingMatching (a + b + 1)

namespace RademacherNoncrossingMatching

/-- The matched-pair relation on natural-number positions. -/
inductive Matched : {n : ℕ} →
    RademacherNoncrossingMatching n → ℕ → ℕ → Prop
  | outer {a b : ℕ}
      (inside : RademacherNoncrossingMatching a)
      (outside : RademacherNoncrossingMatching b) :
      Matched (.node inside outside) 0 (2 * a + 1)
  | inside {a b i j : ℕ}
      {inside : RademacherNoncrossingMatching a}
      {outside : RademacherNoncrossingMatching b}
      (h : Matched inside i j) :
      Matched (.node inside outside) (i + 1) (j + 1)
  | outside {a b i j : ℕ}
      {inside : RademacherNoncrossingMatching a}
      {outside : RademacherNoncrossingMatching b}
      (h : Matched outside i j) :
      Matched (.node inside outside) (i + (2 * a + 2))
        (j + (2 * a + 2))

/-- Every encoded pair is ordered and lies among the `2n` positions. -/
theorem Matched.lt_and_right_lt
    {n i j : ℕ} {M : RademacherNoncrossingMatching n}
    (h : Matched M i j) : i < j ∧ j < 2 * n := by
  induction h with
  | outer inside outside => omega
  | inside h ih => omega
  | outside h ih => omega

/-- Removing one adjacent pair while preserving the recursive noncrossing
encoding. -/
inductive DeletesAdjacent : {n m : ℕ} →
    RademacherNoncrossingMatching n → ℕ →
      RademacherNoncrossingMatching m → Prop
  | root {b : ℕ} (outside : RademacherNoncrossingMatching b) :
      DeletesAdjacent (.node .empty outside) 0 outside
  | descend {a b m i : ℕ}
      {inside : RademacherNoncrossingMatching a}
      {reduced : RademacherNoncrossingMatching m}
      {outside : RademacherNoncrossingMatching b}
      (h : DeletesAdjacent inside i reduced) :
      DeletesAdjacent (.node inside outside) (i + 1)
        (.node reduced outside)

/-- The pair selected by the deletion relation is genuinely adjacent and
matched in the source encoding. -/
theorem DeletesAdjacent.matched
    {n m i : ℕ} {M : RademacherNoncrossingMatching n}
    {M' : RademacherNoncrossingMatching m}
    (h : DeletesAdjacent M i M') : Matched M i (i + 1) := by
  induction h with
  | root outside =>
      simpa using Matched.outer (.empty) outside
  | descend h ih =>
      simpa [Nat.add_assoc] using Matched.inside ih

/-- Deleting an adjacent pair lowers the number of pairs by exactly one. -/
theorem DeletesAdjacent.pairCount
    {n m i : ℕ} {M : RademacherNoncrossingMatching n}
    {M' : RademacherNoncrossingMatching m}
    (h : DeletesAdjacent M i M') : n = m + 1 := by
  induction h with
  | root outside => simp
  | descend h ih => omega

/-- Every nonempty recursive noncrossing matching admits an adjacent-pair
deletion. -/
theorem exists_deletesAdjacent_of_pos
    {n : ℕ} (M : RademacherNoncrossingMatching n) (hn : 0 < n) :
    ∃ m i, ∃ M' : RademacherNoncrossingMatching m,
      DeletesAdjacent M i M' := by
  induction M with
  | empty => omega
  | @node a b inside outside ihInside ihOutside =>
      cases inside with
      | empty =>
          exact ⟨b, 0, outside, DeletesAdjacent.root outside⟩
      | @node c d inner outer =>
          have hpos : 0 < c + d + 1 := by omega
          obtain ⟨m, i, reduced, hdelete⟩ := ihInside hpos
          exact ⟨m + b + 1, i + 1, .node reduced outside,
            DeletesAdjacent.descend hdelete⟩

/-- A concrete list of recursively encoded pairs. -/
def pairList : {n : ℕ} →
    RademacherNoncrossingMatching n → List (ℕ × ℕ)
  | 0, .empty => []
  | _, @node a b inside outside =>
      (0, 2 * a + 1) ::
        ((pairList inside).map fun z => (z.1 + 1, z.2 + 1)) ++
        ((pairList outside).map fun z =>
          (z.1 + (2 * a + 2), z.2 + (2 * a + 2)))

/-- There is exactly one listed pair per pair index. -/
@[simp] theorem pairList_length
    {n : ℕ} (M : RademacherNoncrossingMatching n) :
    (pairList M).length = n := by
  induction M with
  | empty => rfl
  | @node a b inside outside ihInside ihOutside =>
      simp [pairList, ihInside, ihOutside]

/-- At order `r+1`, an actual adjacent matched pair can be removed, leaving
a noncrossing matching of order `r`. -/
theorem exists_adjacentMatchedPair_and_delete
    {r : ℕ} (M : RademacherNoncrossingMatching (r + 1)) :
    ∃ i : ℕ, ∃ M' : RademacherNoncrossingMatching r,
      DeletesAdjacent M i M' ∧ Matched M i (i + 1) ∧
        i + 1 < 2 * (r + 1) := by
  obtain ⟨m, i, M', hdelete⟩ :=
    exists_deletesAdjacent_of_pos M (by omega)
  have hm : m = r := by
    have hc := hdelete.pairCount
    omega
  subst m
  refine ⟨i, M', hdelete, hdelete.matched, ?_⟩
  exact hdelete.matched.lt_and_right_lt.2


end RademacherNoncrossingMatching
end GraphMatrixReplica
