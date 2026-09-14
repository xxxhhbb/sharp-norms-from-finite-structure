import GraphMatrix.RademacherCatalanNodeReindexProof

/-! # Scalar algebra for the Catalan node reindexing

The total Gram-cycle product is split into its root, inside, and outside
blocks using the explicit node-coordinate equivalence.  Separately, the
trace of a row sandwich followed by a row word is expanded into the matching
five boundary sums.  These are the two algebraic sides of the remaining
scalar identity.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Reverse three finite summation binders. -/
theorem sum_three_reverse
    {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    (∑ x : α, ∑ y : β, ∑ z : γ, F x y z) =
      ∑ z : γ, ∑ y : β, ∑ x : α, F x y z := by
  calc
    (∑ x : α, ∑ y : β, ∑ z : γ, F x y z) =
        ∑ y : β, ∑ x : α, ∑ z : γ, F x y z := Finset.sum_comm
    _ = ∑ y : β, ∑ z : γ, ∑ x : α, F x y z := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ z : γ, ∑ y : β, ∑ x : α, F x y z := Finset.sum_comm

/-- A commutative product over a node index splits into root, inside, and
outside products. -/
theorem prod_fin_node_eq_root_inside_outside
    {a b : ℕ} (F : Fin (a + b + 1) → ℝ) :
    (∏ t, F t) =
      F ⟨0, by omega⟩ *
        (∏ i : Fin a, F ⟨i.1 + 1, by omega⟩) *
        (∏ j : Fin b, F ⟨j.1 + (a + 1), by omega⟩) := by
  let E := rademacherCatalanNodeIndexEquiv a b
  calc
    (∏ t, F t) = ∏ z : Fin 1 ⊕ (Fin a ⊕ Fin b), F (E z) := by
      exact (E.prod_comp F).symm
    _ = (∏ z : Fin 1, F (E (Sum.inl z))) *
          ∏ z : Fin a ⊕ Fin b, F (E (Sum.inr z)) := by
      rw [Fintype.prod_sum_type]
    _ = F ⟨0, by omega⟩ *
          ((∏ i : Fin a, F (E (Sum.inr (Sum.inl i)))) *
            ∏ j : Fin b, F (E (Sum.inr (Sum.inr j)))) := by
      rw [Fintype.prod_sum_type]
      simp [E]
    _ = _ := by
      simp only [E, rademacherCatalanNodeIndexEquiv_inside,
        rademacherCatalanNodeIndexEquiv_outside]
      ring

/-- The scalar factor contributed by one Gram-cycle location. -/
def rademacherGramCycleTerm
    {ε ι κ : Type} {n : ℕ}
    (A : ε → Matrix ι κ ℝ) (rows : Fin n → ι)
    (cols : Fin n → κ) (choice : Fin n → ε × ε)
    (t : Fin n) : ℝ :=
  A (choice t).1 (rows t) (cols t) *
    A (choice t).2 (rows (finRotate n t)) (cols t)

/-- The original coefficient is the product of its scalar cycle terms. -/
theorem rademacherGramCycleCoefficient_eq_prod_terms
    {ε ι κ : Type} {n : ℕ}
    (A : ε → Matrix ι κ ℝ) (rows : Fin n → ι)
    (cols : Fin n → κ) (choice : Fin n → ε × ε) :
    rademacherGramCycleCoefficient A rows cols choice =
      ∏ t, rademacherGramCycleTerm A rows cols choice t := rfl

/-- Under node coordinates, the genuine Gram coefficient factors into its
root term, inside segment, and outside segment. -/
theorem rademacherGramCycleCoefficient_node_factorization
    {ε ι κ : Type} {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (rows : Fin (a + b + 1) → ι)
    (cols : Fin (a + b + 1) → κ)
    (choice : Fin (a + b + 1) → ε × ε) :
    rademacherGramCycleCoefficient A rows cols choice =
      rademacherGramCycleTerm A rows cols choice ⟨0, by omega⟩ *
        (∏ i : Fin a, rademacherGramCycleTerm A rows cols choice
          ⟨i.1 + 1, by omega⟩) *
        (∏ j : Fin b, rademacherGramCycleTerm A rows cols choice
          ⟨j.1 + (a + 1), by omega⟩) := by
  rw [rademacherGramCycleCoefficient_eq_prod_terms]
  exact prod_fin_node_eq_root_inside_outside _

/-- Full coordinate expansion of the trace of a row sandwich followed by a
row-side context. -/
theorem trace_rowSandwich_mul_eq_boundary_sum
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix κ κ ℝ)
    (Y : Matrix ι ι ℝ) :
    Matrix.trace (rademacherRowSandwich A X * Y) =
      ∑ rowStart : ι, ∑ rowEnd : ι,
      ∑ colStart : κ, ∑ colEnd : κ, ∑ e : ε,
        A e rowStart colStart * X colStart colEnd *
          A e rowEnd colEnd * Y rowEnd rowStart := by
  classical
  change Matrix.trace
    (nativeMatrixMul (rademacherRowSandwich A X) Y) = _
  simp only [Matrix.trace, Matrix.diag_apply, nativeMatrixMul,
    Matrix.mul_apply, rademacherRowSandwich, Matrix.sum_apply,
    Matrix.transpose_apply]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rowStart hrowStart
  apply Finset.sum_congr rfl
  intro rowEnd hrowEnd
  rw [sum_three_reverse]

/-- The right side of the node scalar identity is therefore the boundary
sum of one root edge, the inside column word, and the outside row word. -/
theorem trace_catalanNodeOpenWord_eq_boundary_sum
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    Matrix.trace
        (rademacherRowSandwich A (rademacherColumnOpenWord A inside) *
          rademacherRowOpenWord A outside) =
      ∑ rowStart : ι, ∑ rowEnd : ι,
      ∑ colStart : κ, ∑ colEnd : κ, ∑ e : ε,
        A e rowStart colStart *
          rademacherColumnOpenWord A inside colStart colEnd *
          A e rowEnd colEnd *
          rademacherRowOpenWord A outside rowEnd rowStart :=
  trace_rowSandwich_mul_eq_boundary_sum A _ _

/-- Final purely scalar residual: after the already-proved three assignment
equivalences, the compatible cycle sum must factor into the two child open
word entries and the common root edge. -/
def RademacherCatalanNodeBoundaryScalarIdentity
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) : Prop := by
  classical
  exact
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
          rademacherGramCycleCoefficient A rows cols choice else 0) =
      ∑ rowStart : ι, ∑ rowEnd : ι,
      ∑ colStart : κ, ∑ colEnd : κ, ∑ e : ε,
        A e rowStart colStart *
          rademacherColumnOpenWord A inside colStart colEnd *
          A e rowEnd colEnd *
          rademacherRowOpenWord A outside rowEnd rowStart

/-- The previous residual scalar identity is equivalent to the explicit
boundary-factorization form. -/
theorem rademacherCatalanNodeScalarProductIdentity_iff_boundary
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanNodeScalarProductIdentity A inside outside ↔
      RademacherCatalanNodeBoundaryScalarIdentity A inside outside := by
  classical
  unfold RademacherCatalanNodeScalarProductIdentity
  unfold RademacherCatalanNodeBoundaryScalarIdentity
  rw [trace_catalanNodeOpenWord_eq_boundary_sum]


end GraphMatrixReplica
