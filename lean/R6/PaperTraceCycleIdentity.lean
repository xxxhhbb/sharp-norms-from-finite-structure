import R6.PaperTraceWordExpansion

/-! # Closed trace words are matrix-power traces

This module closes the purely finite reindexing gap in
`PaperTraceWordExpansion`.  The generic lemma first expands a positive matrix
power between two fixed endpoints as a sum over its intermediate vertices.
The identity `Fin.snoc_eq_cons_rotate` then closes the endpoints and turns the
result into the cyclic coordinate word used by the paper model.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Product of the `q + 1` matrix entries along a path from `a` to `b` with
`q` explicitly indexed intermediate vertices. -/
def paperOpenMatrixPathProduct {ι R : Type*} [Fintype ι]
    [CommSemiring R] (K : Matrix ι ι R) {q : ℕ}
    (a b : ι) (middle : Fin q → ι) : R :=
  ∏ i : Fin (q + 1),
    K (@Fin.cons q (fun _ : Fin (q + 1) => ι) a middle i)
      (@Fin.snoc q (fun _ : Fin (q + 1) => ι) middle b i)

/-- Splitting off the first intermediate vertex splits off the first matrix
entry of an open path product. -/
theorem paperOpenMatrixPathProduct_cons {ι R : Type*} [Fintype ι]
    [CommSemiring R] (K : Matrix ι ι R) {q : ℕ}
    (a b mid : ι) (middle : Fin q → ι) :
    paperOpenMatrixPathProduct K a b (Fin.cons mid middle) =
      K a mid * paperOpenMatrixPathProduct K mid b middle := by
  classical
  unfold paperOpenMatrixPathProduct
  rw [Fin.prod_univ_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.cons_succ, ← Fin.cons_snoc_eq_snoc_cons]

/-- A positive matrix power is the exact finite sum over all intermediate
vertex functions. -/
theorem matrix_pow_succ_apply_eq_sum_openPaths
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (K : Matrix ι ι R) (q : ℕ) (a b : ι) :
    (K ^ (q + 1)) a b =
      ∑ middle : Fin q → ι, paperOpenMatrixPathProduct K a b middle := by
  classical
  induction q generalizing a with
  | zero =>
      simp [paperOpenMatrixPathProduct, Fin.snoc_zero]
  | succ q ih =>
      rw [show q + 1 + 1 = (q + 1) + 1 by omega, pow_succ',
        Matrix.mul_apply]
      simp_rw [ih]
      simp_rw [Finset.mul_sum]
      calc
        (∑ mid : ι, ∑ middle : Fin q → ι,
            K a mid * paperOpenMatrixPathProduct K mid b middle) =
            ∑ z : ι × (Fin q → ι),
              K a z.1 * paperOpenMatrixPathProduct K z.1 b z.2 := by
                rw [Fintype.sum_prod_type]
        _ = ∑ middle : Fin (q + 1) → ι,
              paperOpenMatrixPathProduct K a b middle := by
                apply Fintype.sum_equiv
                  (Fin.consEquiv (fun _ : Fin (q + 1) => ι))
                intro z
                exact (paperOpenMatrixPathProduct_cons
                  K a b z.1 z.2).symm

/-- Closing an open path at its initial vertex is the cyclic product indexed
by `finRotate`. -/
theorem paperOpenMatrixPathProduct_self_eq_cycleProduct
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (K : Matrix ι ι R) {q : ℕ} (rows : Fin (q + 1) → ι) :
    paperOpenMatrixPathProduct K (rows 0) (rows 0) (Fin.tail rows) =
      ∏ i : Fin (q + 1), K (rows i) (rows (finRotate (q + 1) i)) := by
  classical
  have hrows : Fin.cons (rows 0) (Fin.tail rows) = rows :=
    Fin.cons_self_tail rows
  unfold paperOpenMatrixPathProduct
  rw [Fin.snoc_eq_cons_rotate]
  simp only [hrows]

/-- Generic closed-walk expansion of the trace of a positive matrix power. -/
theorem matrix_trace_pow_succ_eq_sum_cycleProducts
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (K : Matrix ι ι R) (q : ℕ) :
    Matrix.trace (K ^ (q + 1)) =
      ∑ rows : Fin (q + 1) → ι,
        ∏ i : Fin (q + 1), K (rows i) (rows (finRotate (q + 1) i)) := by
  classical
  calc
    Matrix.trace (K ^ (q + 1)) =
        ∑ a : ι, (K ^ (q + 1)) a a := rfl
    _ = ∑ a : ι, ∑ middle : Fin q → ι,
        paperOpenMatrixPathProduct K a a middle := by
          apply Finset.sum_congr rfl
          intro a _
          exact matrix_pow_succ_apply_eq_sum_openPaths K q a a
    _ = ∑ z : ι × (Fin q → ι),
          paperOpenMatrixPathProduct K z.1 z.1 z.2 := by
            rw [Fintype.sum_prod_type]
    _ = ∑ rows : Fin (q + 1) → ι,
          paperOpenMatrixPathProduct K (rows 0) (rows 0) (Fin.tail rows) := by
            apply Fintype.sum_equiv
              (Fin.consEquiv (fun _ : Fin (q + 1) => ι))
            intro z
            have htail :
                Fin.tail ((Fin.consEquiv
                  (fun _ : Fin (q + 1) => ι)) z) = z.2 := by
              funext i
              rfl
            have hhead :
                (Fin.consEquiv (fun _ : Fin (q + 1) => ι)) z 0 = z.1 := by
              rfl
            simp only [htail, hhead]
    _ = ∑ rows : Fin (q + 1) → ι,
          ∏ i : Fin (q + 1),
            K (rows i) (rows (finRotate (q + 1) i)) := by
            apply Finset.sum_congr rfl
            intro rows _
            exact paperOpenMatrixPathProduct_self_eq_cycleProduct K rows

/-- The paper's explicit cyclic coordinate word is exactly the trace of the
corresponding positive Gram-matrix power, at every positive moment order. -/
theorem paperGramTraceWordSum_eq_trace (G : PaperShape) (n p : ℕ)
    (w : PaperNoise n) :
    paperGramTraceWordSum G n p w =
      Matrix.trace ((paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) ^ (p + 1)) := by
  classical
  let M := paperGraphMatrix G n w
  let K := M * M.transpose
  calc
    paperGramTraceWordSum G n p w =
        ∑ rows : Fin (p + 1) → PaperRow G n,
          ∑ cols : Fin (p + 1) → PaperCol G n,
            ∏ i : Fin (p + 1),
              M (rows i) (cols i) *
                M (rows (finRotate (p + 1) i)) (cols i) := by
                  simp only [paperGramTraceWordSum,
                    paperTraceEntryProduct_eq_pairProduct, M]
    _ = ∑ rows : Fin (p + 1) → PaperRow G n,
          ∏ i : Fin (p + 1),
            ∑ col : PaperCol G n,
              M (rows i) col *
                M (rows (finRotate (p + 1) i)) col := by
                  apply Finset.sum_congr rfl
                  intro rows _
                  rw [Fintype.prod_sum]
    _ = ∑ rows : Fin (p + 1) → PaperRow G n,
          ∏ i : Fin (p + 1),
            K (rows i) (rows (finRotate (p + 1) i)) := by
                  apply Finset.sum_congr rfl
                  intro rows _
                  apply Finset.prod_congr rfl
                  intro i _
                  simp [K, Matrix.mul_apply, Matrix.transpose_apply]
    _ = Matrix.trace (K ^ (p + 1)) :=
      (matrix_trace_pow_succ_eq_sum_cycleProducts K p).symm
    _ = Matrix.trace ((paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) ^ (p + 1)) := by
          rfl

#print axioms matrix_pow_succ_apply_eq_sum_openPaths
#print axioms matrix_trace_pow_succ_eq_sum_cycleProducts
#print axioms paperGramTraceWordSum_eq_trace

end GraphMatrixReplica
