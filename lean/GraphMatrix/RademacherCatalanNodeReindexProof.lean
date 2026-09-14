import GraphMatrix.RademacherCatalanTraceBridge

/-! # Explicit coordinate equivalences for a Catalan node

This file supplies the function-space/Fubini part of the node reindexing.
A length `a+b+1` assignment is split bijectively into its root coordinate,
`a` inside coordinates, and `b` outside coordinates.  The same equivalence
is used for rows, columns, and coefficient-pair choices.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The ordered node-coordinate index: root, then inside, then outside. -/
def rademacherCatalanNodeIndexEquiv (a b : ℕ) :
    Fin 1 ⊕ (Fin a ⊕ Fin b) ≃ Fin (a + b + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp]
theorem rademacherCatalanNodeIndexEquiv_root
    (a b : ℕ) (z : Fin 1) :
    rademacherCatalanNodeIndexEquiv a b (Sum.inl z) =
      ⟨0, by omega⟩ := by
  apply Fin.ext
  simp [rademacherCatalanNodeIndexEquiv, finSumFinEquiv]

@[simp]
theorem rademacherCatalanNodeIndexEquiv_inside
    (a b : ℕ) (i : Fin a) :
    rademacherCatalanNodeIndexEquiv a b (Sum.inr (Sum.inl i)) =
      ⟨i.1 + 1, by omega⟩ := by
  apply Fin.ext
  simp [rademacherCatalanNodeIndexEquiv, finSumFinEquiv]

@[simp]
theorem rademacherCatalanNodeIndexEquiv_outside
    (a b : ℕ) (j : Fin b) :
    rademacherCatalanNodeIndexEquiv a b (Sum.inr (Sum.inr j)) =
      ⟨j.1 + (a + 1), by omega⟩ := by
  apply Fin.ext
  simp [rademacherCatalanNodeIndexEquiv, finSumFinEquiv]
  omega

/-- Evaluation identifies functions on `Fin 1` with their unique value. -/
def rademacherFinOneArrowEquiv (α : Type*) : (Fin 1 → α) ≃ α where
  toFun f := f 0
  invFun x := fun _ => x
  left_inv f := by funext i; exact Fin.eq_zero i ▸ rfl
  right_inv _ := rfl

/-- Split an arbitrary node assignment into root/inside/outside data. -/
def rademacherCatalanNodeFunctionEquiv (α : Type*) (a b : ℕ) :
    (Fin (a + b + 1) → α) ≃
      α × (Fin a → α) × (Fin b → α) :=
  ((rademacherCatalanNodeIndexEquiv a b).arrowCongr
      (Equiv.refl α)).symm |>.trans
    ((Equiv.sumPiEquivProdPi (fun _ : Fin 1 ⊕ (Fin a ⊕ Fin b) => α)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 1 → α))
        (Equiv.sumPiEquivProdPi
          (fun _ : Fin a ⊕ Fin b => α))).trans
        (Equiv.prodCongr (rademacherFinOneArrowEquiv α)
          (Equiv.refl ((Fin a → α) × (Fin b → α))))))

/-- Base application formula for the inverse assembly map. -/
@[simp]
theorem rademacherCatalanNodeFunctionEquiv_symm_root
    {α : Type*} {a b : ℕ}
    (x : α × (Fin a → α) × (Fin b → α)) :
    (rademacherCatalanNodeFunctionEquiv α a b).symm x
        (rademacherCatalanNodeIndexEquiv a b (Sum.inl 0)) = x.1 := by
  rfl

/-- Inside application formula for the inverse assembly map. -/
@[simp]
theorem rademacherCatalanNodeFunctionEquiv_symm_inside
    {α : Type*} {a b : ℕ}
    (x : α × (Fin a → α) × (Fin b → α)) (i : Fin a) :
    (rademacherCatalanNodeFunctionEquiv α a b).symm x
        (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inl i))) = x.2.1 i := by
  change Sum.elim (fun _ : Fin 1 => x.1)
      (Sum.elim x.2.1 x.2.2)
      ((rademacherCatalanNodeIndexEquiv a b).symm
        (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inl i)))) = x.2.1 i
  rw [Equiv.symm_apply_apply]
  rfl

/-- Outside application formula for the inverse assembly map. -/
@[simp]
theorem rademacherCatalanNodeFunctionEquiv_symm_outside
    {α : Type*} {a b : ℕ}
    (x : α × (Fin a → α) × (Fin b → α)) (j : Fin b) :
    (rademacherCatalanNodeFunctionEquiv α a b).symm x
        (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inr j))) = x.2.2 j := by
  change Sum.elim (fun _ : Fin 1 => x.1)
      (Sum.elim x.2.1 x.2.2)
      ((rademacherCatalanNodeIndexEquiv a b).symm
        (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inr j)))) = x.2.2 j
  rw [Equiv.symm_apply_apply]
  rfl

/-- The forward split extracts the original root coordinate. -/
@[simp]
theorem rademacherCatalanNodeFunctionEquiv_root
    {α : Type*} {a b : ℕ} (f : Fin (a + b + 1) → α) :
    (rademacherCatalanNodeFunctionEquiv α a b f).1 = f ⟨0, by omega⟩ := by
  let E := rademacherCatalanNodeFunctionEquiv α a b
  calc
    (E f).1 = E.symm (E f)
        (rademacherCatalanNodeIndexEquiv a b (Sum.inl 0)) := by
      symm
      exact rademacherCatalanNodeFunctionEquiv_symm_root (E f)
    _ = f (rademacherCatalanNodeIndexEquiv a b (Sum.inl 0)) := by
      rw [E.symm_apply_apply]
    _ = f ⟨0, by omega⟩ := by rw [rademacherCatalanNodeIndexEquiv_root]

/-- The forward split extracts positions `1,...,a` as the inside block. -/
@[simp]
theorem rademacherCatalanNodeFunctionEquiv_inside
    {α : Type*} {a b : ℕ} (f : Fin (a + b + 1) → α) (i : Fin a) :
    (rademacherCatalanNodeFunctionEquiv α a b f).2.1 i =
      f ⟨i.1 + 1, by omega⟩ := by
  let E := rademacherCatalanNodeFunctionEquiv α a b
  calc
    (E f).2.1 i = E.symm (E f)
        (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inl i))) := by
      symm
      exact rademacherCatalanNodeFunctionEquiv_symm_inside (E f) i
    _ = f (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inl i))) := by
      rw [E.symm_apply_apply]
    _ = f ⟨i.1 + 1, by omega⟩ := by
      rw [rademacherCatalanNodeIndexEquiv_inside]

/-- The forward split extracts the final `b` coordinates as the outside
block. -/
@[simp]
theorem rademacherCatalanNodeFunctionEquiv_outside
    {α : Type*} {a b : ℕ} (f : Fin (a + b + 1) → α) (j : Fin b) :
    (rademacherCatalanNodeFunctionEquiv α a b f).2.2 j =
      f ⟨j.1 + (a + 1), by omega⟩ := by
  let E := rademacherCatalanNodeFunctionEquiv α a b
  calc
    (E f).2.2 j = E.symm (E f)
        (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inr j))) := by
      symm
      exact rademacherCatalanNodeFunctionEquiv_symm_outside (E f) j
    _ = f (rademacherCatalanNodeIndexEquiv a b
          (Sum.inr (Sum.inr j))) := by
      rw [E.symm_apply_apply]
    _ = f ⟨j.1 + (a + 1), by omega⟩ := by
      rw [rademacherCatalanNodeIndexEquiv_outside]

/-- Every finite sum over node assignments admits the root/inside/outside
Fubini expansion induced by the explicit equivalence. -/
theorem sum_nodeFunctions_eq_sum_root_inside_outside
    {α : Type*} [Fintype α] {a b : ℕ}
    (F : (Fin (a + b + 1) → α) → ℝ) :
    (∑ f, F f) =
      ∑ root : α, ∑ inside : Fin a → α, ∑ outside : Fin b → α,
        F ((rademacherCatalanNodeFunctionEquiv α a b).symm
          (root, inside, outside)) := by
  calc
    (∑ f, F f) =
        ∑ x : α × (Fin a → α) × (Fin b → α),
          F ((rademacherCatalanNodeFunctionEquiv α a b).symm x) := by
      apply Fintype.sum_equiv (rademacherCatalanNodeFunctionEquiv α a b)
      intro f
      simp
    _ = _ := by
      simp_rw [Fintype.sum_prod_type]

/-- Row-coordinate specialization of the node assignment equivalence. -/
def rademacherCatalanNodeRowsEquiv
    (ι : Type*) (a b : ℕ) :
    (Fin (a + b + 1) → ι) ≃
      ι × (Fin a → ι) × (Fin b → ι) :=
  rademacherCatalanNodeFunctionEquiv ι a b

/-- Column-coordinate specialization of the node assignment equivalence. -/
def rademacherCatalanNodeColsEquiv
    (κ : Type*) (a b : ℕ) :
    (Fin (a + b + 1) → κ) ≃
      κ × (Fin a → κ) × (Fin b → κ) :=
  rademacherCatalanNodeFunctionEquiv κ a b

/-- Coefficient-pair specialization of the node assignment equivalence. -/
def rademacherCatalanNodeChoicesEquiv
    (ε : Type*) (a b : ℕ) :
    (Fin (a + b + 1) → ε × ε) ≃
      (ε × ε) × (Fin a → ε × ε) × (Fin b → ε × ε) :=
  rademacherCatalanNodeFunctionEquiv (ε × ε) a b

/-- After the three explicit function-space bijections, the remaining node
proof is a scalar identity over root/inside/outside data.  This formulation
contains no further function-space reindexing. -/
def RademacherCatalanNodeScalarProductIdentity
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
        let choice :=
          (rademacherCatalanNodeChoicesEquiv ε a b).symm
            (choiceRoot, choiceInside, choiceOutside)
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) =
      Matrix.trace
        (rademacherRowSandwich A (rademacherColumnOpenWord A inside) *
          rademacherRowOpenWord A outside)

/-- The original node reindexing is equivalent to the residual scalar
product identity; all three function-space transports are discharged here. -/
theorem rademacherCatalanNodeFinsetReindex_iff_scalarProductIdentity
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanNodeFinsetReindex A inside outside ↔
      RademacherCatalanNodeScalarProductIdentity A inside outside := by
  classical
  unfold RademacherCatalanNodeFinsetReindex
  unfold RademacherCatalanNodeScalarProductIdentity
  rw [sum_nodeFunctions_eq_sum_root_inside_outside]
  simp_rw [sum_nodeFunctions_eq_sum_root_inside_outside]
  simp only [rademacherCatalanNodeRowsEquiv,
    rademacherCatalanNodeColsEquiv,
    rademacherCatalanNodeChoicesEquiv]
  constructor <;> intro h <;> exact h


end GraphMatrixReplica
