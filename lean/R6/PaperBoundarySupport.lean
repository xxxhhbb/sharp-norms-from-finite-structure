import R6.PaperGraphMatrixEntryMoments

/-! # Boundary support of the paper graph matrix

The ambient Lean matrix is indexed by all functions on each ordered boundary.
Definition 4.5 only receives contributions from ordered tuples with distinct
labels.  The extra indices are exact zero padding: compatibility with a global
injective realization forces both boundary tuples to be injective.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A compatible row is injective because both the realization and the
ordered left-boundary embedding are injective. -/
theorem paperEntryCompatible_row_injective
    {G : PaperShape} {n : ℕ} {phi : PaperRealization G n}
    {row : PaperRow G n} {col : PaperCol G n}
    (h : paperEntryCompatible G phi row col) :
    Function.Injective row := by
  intro i j hij
  apply G.left.injective
  apply phi.injective
  rw [h.1 i, h.1 j]
  exact hij

/-- A compatible column is injective for the same reason. -/
theorem paperEntryCompatible_col_injective
    {G : PaperShape} {n : ℕ} {phi : PaperRealization G n}
    {row : PaperRow G n} {col : PaperCol G n}
    (h : paperEntryCompatible G phi row col) :
    Function.Injective col := by
  intro i j hij
  apply G.right.injective
  apply phi.injective
  rw [h.2 i, h.2 j]
  exact hij

/-- Every entry on a repeated-label row is identically zero. -/
theorem paperGraphMatrix_zero_of_row_not_injective
    (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (row : PaperRow G n) (col : PaperCol G n)
    (hRow : ¬ Function.Injective row) :
    paperGraphMatrix G n w row col = 0 := by
  classical
  unfold paperGraphMatrix
  apply Finset.sum_eq_zero
  intro phi _
  by_cases hCompatible : paperEntryCompatible G phi row col
  · exact False.elim (hRow (paperEntryCompatible_row_injective hCompatible))
  · simp [hCompatible]

/-- Every entry on a repeated-label column is identically zero. -/
theorem paperGraphMatrix_zero_of_col_not_injective
    (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (row : PaperRow G n) (col : PaperCol G n)
    (hCol : ¬ Function.Injective col) :
    paperGraphMatrix G n w row col = 0 := by
  classical
  unfold paperGraphMatrix
  apply Finset.sum_eq_zero
  intro phi _
  by_cases hCompatible : paperEntryCompatible G phi row col
  · exact False.elim (hCol (paperEntryCompatible_col_injective hCompatible))
  · simp [hCompatible]

/-- The support of the paper matrix consists exactly of injective boundary
tuples (possibly with further zero entries caused by incompatible overlap). -/
theorem paperGraphMatrix_eq_zero_unless_boundary_injective
    (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (row : PaperRow G n) (col : PaperCol G n) :
    ¬ Function.Injective row ∨ ¬ Function.Injective col →
      paperGraphMatrix G n w row col = 0 := by
  rintro (hRow | hCol)
  · exact paperGraphMatrix_zero_of_row_not_injective G n w row col hRow
  · exact paperGraphMatrix_zero_of_col_not_injective G n w row col hCol

#print axioms paperEntryCompatible_row_injective
#print axioms paperEntryCompatible_col_injective
#print axioms paperGraphMatrix_zero_of_row_not_injective
#print axioms paperGraphMatrix_zero_of_col_not_injective

end GraphMatrixReplica
