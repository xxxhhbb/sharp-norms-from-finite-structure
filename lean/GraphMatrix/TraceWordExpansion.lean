import GraphMatrix.GraphMatrixEntryMoments

/-! # Trace-word gluing for the original graph-matrix model

This file formalizes the two finite sides of the algebraic gluing step.  An
arbitrary positive Gram trace is represented by an exact recursive walk, and
the closed cyclic word has an exact entry-moment/parity expansion.  The direct
equality between those two descriptions is proved here at the first positive
moment; its all-order reindexing theorem remains a separate obligation.

Every replica realization remains a single global injection of all shape
roles into the common ambient label set.  The only identifications between
different replicas are the cyclic left boundary and adjacent right boundary
identifications forced by the trace.

No role-partite independence or product-of-role label count is introduced.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Recursive coordinate kernel for powers of `M Mᵀ`.  This definition is
useful independently of the closed cyclic indexing because its recursion is
exactly matrix multiplication. -/
def paperGramWalk {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (M : Matrix ι κ ℝ) : ℕ → ι → ι → ℝ
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j =>
      ∑ mid : ι, (∑ col : κ, M i col * M mid col) *
        paperGramWalk M k mid j

/-- The recursive coordinate kernel is the actual Gram-matrix power. -/
theorem paperGramWalk_eq_pow {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι]
    (M : Matrix ι κ ℝ) (k : ℕ) (i j : ι) :
    paperGramWalk M k i j = ((M * M.transpose) ^ k) i j := by
  classical
  induction k generalizing i j with
  | zero => simp [paperGramWalk, Matrix.one_apply]
  | succ k ih =>
      rw [pow_succ']
      simp only [paperGramWalk, Matrix.mul_apply, Matrix.transpose_apply]
      simp_rw [ih]

/-- Arbitrary positive Gram trace moments have an exact finite recursive
coordinate expansion. -/
theorem paperGramTracePow_eq_walkSum {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι]
    (M : Matrix ι κ ℝ) (p : ℕ) :
    Matrix.trace ((M * M.transpose) ^ (p + 1)) =
      ∑ row : ι, paperGramWalk M (p + 1) row row := by
  simp [Matrix.trace, paperGramWalk_eq_pow]

/-- Specialization of the arbitrary-order trace expansion to the original
globally-injective paper graph matrix. -/
theorem paperGraphMatrixGramTracePow_eq_walkSum (G : PaperShape) (n p : ℕ)
    (w : PaperNoise n) :
    Matrix.trace ((paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) ^ (p + 1)) =
      ∑ row : PaperRow G n,
        paperGramWalk (paperGraphMatrix G n w) (p + 1) row row := by
  classical
  exact paperGramTracePow_eq_walkSum (paperGraphMatrix G n w) p

/-- Evaluation at the sole index identifies one-tuples with their entry. -/
def finOneArrowEquiv (α : Type*) : (Fin 1 → α) ≃ α where
  toFun f := f 0
  invFun a := fun _ => a
  left_inv f := by
    funext i
    rw [Fin.eq_zero i]
  right_inv _ := rfl

theorem sum_finOne_arrow {α R : Type*} [Fintype α] [AddCommMonoid R]
    (f : (Fin 1 → α) → R) :
    (∑ x : Fin 1 → α, f x) = ∑ a : α, f (fun _ => a) := by
  apply Fintype.sum_equiv (finOneArrowEquiv α)
  intro x
  congr 1
  funext i
  rw [Fin.eq_zero i]
  rfl

/-- Row tuple seen by the two replicas over the `i`-th Gram factor.  The
`false` replica starts at row `i`; the `true` replica ends at the cyclic next
row. -/
def paperTraceReplicaRow (G : PaperShape) (n p : ℕ)
    (rows : Fin (p + 1) → PaperRow G n) :
    Replica (p + 1) → PaperRow G n :=
  fun x => if x.2 then rows (finRotate (p + 1) x.1) else rows x.1

/-- Both replicas over the `i`-th Gram factor use the same column tuple. -/
def paperTraceReplicaCol (G : PaperShape) (n p : ℕ)
    (cols : Fin (p + 1) → PaperCol G n) :
    Replica (p + 1) → PaperCol G n :=
  fun x => cols x.1

/-- The two-entry product at every location of the cyclic Gram trace. -/
def paperTraceEntryProduct (G : PaperShape) (n p : ℕ)
    (w : PaperNoise n) (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) : ℝ :=
  ∏ x : Replica (p + 1),
    paperGraphMatrix G n w (paperTraceReplicaRow G n p rows x)
      (paperTraceReplicaCol G n p cols x)

/-- The replica product is exactly the usual product of the two matrix
entries contributed by each Gram factor. -/
theorem paperTraceEntryProduct_eq_pairProduct (G : PaperShape) (n p : ℕ)
    (w : PaperNoise n) (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) :
    paperTraceEntryProduct G n p w rows cols =
      ∏ i : Fin (p + 1),
        paperGraphMatrix G n w (rows i) (cols i) *
          paperGraphMatrix G n w (rows (finRotate (p + 1) i)) (cols i) := by
  classical
  rw [paperTraceEntryProduct, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp [paperTraceReplicaRow, paperTraceReplicaCol, mul_comm]

/-- The explicit closed cyclic coordinate word before taking expectation.
At arbitrary order its equality with the recursive actual trace expansion is
the remaining purely finite reindexing lemma. -/
def paperGramTraceWordSum (G : PaperShape) (n p : ℕ)
    (w : PaperNoise n) : ℝ :=
  ∑ rows : Fin (p + 1) → PaperRow G n,
    ∑ cols : Fin (p + 1) → PaperCol G n,
      paperTraceEntryProduct G n p w rows cols

/-- At the first positive moment, the closed trace word is definitionally the
actual Gram trace.  This also checks the orientation of the cyclic gluing. -/
theorem paperGramTraceWordSum_zero_eq_trace (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) :
    paperGramTraceWordSum G n 0 w =
      Matrix.trace (paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) := by
  classical
  unfold paperGramTraceWordSum
  calc
    (∑ rows : Fin 1 → PaperRow G n,
        ∑ cols : Fin 1 → PaperCol G n,
          paperTraceEntryProduct G n 0 w rows cols) =
        ∑ row : PaperRow G n, ∑ col : PaperCol G n,
          paperTraceEntryProduct G n 0 w (fun _ => row)
            (fun _ => col) := by
      rw [sum_finOne_arrow]
      apply Finset.sum_congr rfl
      intro row _
      rw [sum_finOne_arrow]
    _ = Matrix.trace (paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) := by
      simp [paperTraceEntryProduct_eq_pairProduct, Matrix.trace,
        Matrix.mul_apply, Matrix.transpose_apply]

/-- A fixed enumeration of the `2(p+1)` replicas, used only because the
entry-moment theorem is indexed by `Fin q`. -/
def paperTraceIndexEquiv (p : ℕ) :
    Replica (p + 1) ≃ Fin (Fintype.card (Replica (p + 1))) :=
  Fintype.equivFin (Replica (p + 1))

def paperTraceIndexedRows (G : PaperShape) (n p : ℕ)
    (rows : Fin (p + 1) → PaperRow G n) :
    Fin (Fintype.card (Replica (p + 1))) → PaperRow G n :=
  fun i => paperTraceReplicaRow G n p rows ((paperTraceIndexEquiv p).symm i)

def paperTraceIndexedCols (G : PaperShape) (n p : ℕ)
    (cols : Fin (p + 1) → PaperCol G n) :
    Fin (Fintype.card (Replica (p + 1))) → PaperCol G n :=
  fun i => paperTraceReplicaCol G n p cols ((paperTraceIndexEquiv p).symm i)

/-- Reindexing the replica product does not alter it. -/
theorem paperTraceEntryProduct_eq_indexedProduct (G : PaperShape) (n p : ℕ)
    (w : PaperNoise n) (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) :
    paperTraceEntryProduct G n p w rows cols =
      ∏ i : Fin (Fintype.card (Replica (p + 1))),
        paperGraphMatrix G n w (paperTraceIndexedRows G n p rows i)
          (paperTraceIndexedCols G n p cols i) := by
  classical
  unfold paperTraceEntryProduct
  apply Fintype.prod_equiv (paperTraceIndexEquiv p)
  intro x
  simp [paperTraceIndexedRows, paperTraceIndexedCols]

/-- Boundary compatibility in semantic trace form.  Each `phis x` is still
globally injective on *all* roles of the shape. -/
def paperTraceCompatible (G : PaperShape) (n p : ℕ)
    (phis : Replica (p + 1) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) : Prop :=
  ∀ x, paperEntryCompatible G (phis x)
    (paperTraceReplicaRow G n p rows x)
    (paperTraceReplicaCol G n p cols x)

/-- The abstract compatibility predicate exposes exactly the adjacent-right
and cyclic-left trace gluing. -/
theorem paperTraceCompatible_iff (G : PaperShape) (n p : ℕ)
    (phis : Replica (p + 1) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) :
    paperTraceCompatible G n p phis rows cols ↔
      (∀ i, paperEntryCompatible G (phis (i, false)) (rows i) (cols i)) ∧
      (∀ i, paperEntryCompatible G (phis (i, true))
        (rows (finRotate (p + 1) i)) (cols i)) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [paperTraceCompatible, paperTraceReplicaRow,
        paperTraceReplicaCol] using h (i, false)
    · intro i
      simpa [paperTraceCompatible, paperTraceReplicaRow,
        paperTraceReplicaCol] using h (i, true)
  · rintro ⟨hFalse, hTrue⟩ ⟨i, b⟩
    cases b
    · simpa [paperTraceCompatible, paperTraceReplicaRow,
        paperTraceReplicaCol] using hFalse i
    · simpa [paperTraceCompatible, paperTraceReplicaRow,
        paperTraceReplicaCol] using hTrue i

/-- The indexed compatibility appearing in the entry theorem is precisely
the semantic trace compatibility after undoing the fixed enumeration. -/
theorem paperTraceIndexedCompatible_iff (G : PaperShape) (n p : ℕ)
    (phis : Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) :
    (∀ i, paperEntryCompatible G (phis i)
      (paperTraceIndexedRows G n p rows i)
      (paperTraceIndexedCols G n p cols i)) ↔
    paperTraceCompatible G n p
      (fun x => phis (paperTraceIndexEquiv p x)) rows cols := by
  constructor
  · intro h x
    simpa [paperTraceIndexedRows, paperTraceIndexedCols] using
      h (paperTraceIndexEquiv p x)
  · intro h i
    simpa [paperTraceIndexedRows, paperTraceIndexedCols] using
      h ((paperTraceIndexEquiv p).symm i)

/-- Exact finite Rademacher expectation of one fixed cyclic trace word. -/
theorem paperTraceEntryProductMean (G : PaperShape) (n p : ℕ)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) :
    paperMean (fun w : PaperNoise n =>
      paperTraceEntryProduct G n p w rows cols) =
      ∑ phis : Fin (Fintype.card (Replica (p + 1))) →
          PaperRealization G n,
        if ∀ i, paperEntryCompatible G (phis i)
            (paperTraceIndexedRows G n p rows i)
            (paperTraceIndexedCols G n p cols i) then
          if ∀ e, Even ((paperUnorderedEdgeWord
              (paperJointEdgeWord G phis)).count e) then
            (1 : ℝ) else 0
        else 0 := by
  classical
  simp_rw [paperTraceEntryProduct_eq_indexedProduct]
  exact paperOriginalEntryJointMoment G n
    (Fintype.card (Replica (p + 1)))
    (paperTraceIndexedRows G n p rows)
    (paperTraceIndexedCols G n p cols)

/-- Exact expectation of the full cyclic coordinate trace-word sum.  This is
the paper-model trace/parity interface: the surviving terms are precisely
families of globally injective realizations whose shared unordered ambient
edge word has even multiplicity. -/
theorem paperGramTraceWordMean (G : PaperShape) (n p : ℕ) :
    paperMean (fun w : PaperNoise n => paperGramTraceWordSum G n p w) =
      ∑ rows : Fin (p + 1) → PaperRow G n,
        ∑ cols : Fin (p + 1) → PaperCol G n,
          ∑ phis : Fin (Fintype.card (Replica (p + 1))) →
              PaperRealization G n,
            if ∀ i, paperEntryCompatible G (phis i)
                (paperTraceIndexedRows G n p rows i)
                (paperTraceIndexedCols G n p cols i) then
              if ∀ e, Even ((paperUnorderedEdgeWord
                  (paperJointEdgeWord G phis)).count e) then
                (1 : ℝ) else 0
            else 0 := by
  classical
  unfold paperGramTraceWordSum
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro rows _
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro cols _
  exact paperTraceEntryProductMean G n p rows cols


end GraphMatrixReplica
