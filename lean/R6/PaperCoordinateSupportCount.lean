import R6.PaperSchurTest

/-! # Counting completions of visible finite coordinates

A full assignment extending fixed values on a visible coordinate set is
determined by its restriction to the complementary coordinates.  Adding an
arbitrary predicate can only reduce the number of completions.  The predicate
is intentionally unrestricted, so it can encode global injectivity,
orientation, edge compatibility, or any conjunction of these constraints.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Full assignments extending a genuinely partial assignment on `visible`
and satisfying an arbitrary additional predicate. -/
def CoordinateCompletion
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (visible : Finset α)
    (boundaryData : {x : α // x ∈ visible} → Fin n)
    (P : (α → Fin n) → Prop) :=
  {f : α → Fin n //
    (∀ (x : α) (hx : x ∈ visible), f x = boundaryData ⟨x, hx⟩) ∧ P f}

/-- The hidden-coordinate restriction of a compatible completion. -/
def coordinateCompletionHiddenRestriction
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {visible : Finset α}
    {boundaryData : {x : α // x ∈ visible} → Fin n}
    {P : (α → Fin n) → Prop}
    (f : CoordinateCompletion n visible boundaryData P) :
    {x : α // x ∈ Finset.univ \ visible} → Fin n :=
  fun x => f.1 x.1

/-- Visible values are fixed, so equality on hidden coordinates determines
the entire completion, independently of the additional predicate. -/
theorem coordinateCompletionHiddenRestriction_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {visible : Finset α}
    {boundaryData : {x : α // x ∈ visible} → Fin n}
    {P : (α → Fin n) → Prop} :
    Function.Injective
      (coordinateCompletionHiddenRestriction
        (n := n) (visible := visible) (boundaryData := boundaryData) (P := P)) := by
  classical
  intro f g hRestriction
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ visible
  · exact (f.2.1 x hx).trans (g.2.1 x hx).symm
  · exact congrFun hRestriction
      ⟨x, Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩⟩

/-- Universal finite completion count: at most `n` choices for each hidden
coordinate. -/
theorem coordinateCompletion_card_le_pow_complement
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (visible : Finset α)
    (boundaryData : {x : α // x ∈ visible} → Fin n)
    (P : (α → Fin n) → Prop) :
    Nat.card (CoordinateCompletion n visible boundaryData P) ≤
      n ^ (Finset.univ \ visible).card := by
  classical
  calc
    Nat.card (CoordinateCompletion n visible boundaryData P) ≤
        Nat.card
          ({x : α // x ∈ Finset.univ \ visible} → Fin n) :=
      Nat.card_le_card_of_injective
        (coordinateCompletionHiddenRestriction
          (n := n) (visible := visible) (boundaryData := boundaryData) (P := P))
        coordinateCompletionHiddenRestriction_injective
    _ = n ^ (Finset.univ \ visible).card := by
      rw [Nat.card_fun, Nat.card_fin]
      congr
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe _

/-- A finite support injected into constrained completions inherits the same
coordinate-power bound. -/
theorem finset_card_le_pow_complement_of_injective_to_completion
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (support : Finset β)
    (n : ℕ) (visible : Finset α)
    (boundaryData : {x : α // x ∈ visible} → Fin n)
    (P : (α → Fin n) → Prop)
    (encode : {b : β // b ∈ support} →
      CoordinateCompletion n visible boundaryData P)
    (hEncode : Function.Injective encode) :
    support.card ≤ n ^ (Finset.univ \ visible).card := by
  classical
  haveI : Finite (CoordinateCompletion n visible boundaryData P) :=
    Finite.of_injective
      (coordinateCompletionHiddenRestriction
        (n := n) (visible := visible) (boundaryData := boundaryData) (P := P))
      coordinateCompletionHiddenRestriction_injective
  calc
    support.card = Nat.card {b : β // b ∈ support} := by simp
    _ ≤ Nat.card (CoordinateCompletion n visible boundaryData P) :=
      Nat.card_le_card_of_injective encode hEncode
    _ ≤ n ^ (Finset.univ \ visible).card :=
      coordinateCompletion_card_le_pow_complement n visible boundaryData P

/-- Reusable row-support endpoint.  It remains only to provide, for each
row, an injective encoding of its nonzero columns as compatible coordinate
completions. -/
theorem matrixRowSupport_card_le_pow_complement_of_completionEncoding
    {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq α] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ)
    (n : ℕ) (visible : Finset α)
    (boundaryData : {x : α // x ∈ visible} → Fin n)
    (P : (α → Fin n) → Prop)
    (encode : ∀ i : ι, {j : κ // j ∈ matrixRowSupport A i} →
      CoordinateCompletion n visible boundaryData P)
    (hEncode : ∀ i, Function.Injective (encode i)) :
    ∀ i, (matrixRowSupport A i).card ≤
      n ^ (Finset.univ \ visible).card := by
  intro i
  exact finset_card_le_pow_complement_of_injective_to_completion
    (matrixRowSupport A i) n visible boundaryData P (encode i) (hEncode i)

/-- Reusable column-support endpoint, dual to the preceding row statement. -/
theorem matrixColSupport_card_le_pow_complement_of_completionEncoding
    {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq α] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ)
    (n : ℕ) (visible : Finset α)
    (boundaryData : {x : α // x ∈ visible} → Fin n)
    (P : (α → Fin n) → Prop)
    (encode : ∀ j : κ, {i : ι // i ∈ matrixColSupport A j} →
      CoordinateCompletion n visible boundaryData P)
    (hEncode : ∀ j, Function.Injective (encode j)) :
    ∀ j, (matrixColSupport A j).card ≤
      n ^ (Finset.univ \ visible).card := by
  intro j
  exact finset_card_le_pow_complement_of_injective_to_completion
    (matrixColSupport A j) n visible boundaryData P (encode j) (hEncode j)

#print axioms coordinateCompletionHiddenRestriction_injective
#print axioms coordinateCompletion_card_le_pow_complement
#print axioms finset_card_le_pow_complement_of_injective_to_completion
#print axioms
  matrixRowSupport_card_le_pow_complement_of_completionEncoding
#print axioms
  matrixColSupport_card_le_pow_complement_of_completionEncoding

end GraphMatrixReplica
