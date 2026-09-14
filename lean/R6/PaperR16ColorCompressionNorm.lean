import R6.PaperRoleColoredPartiteBridge
import R6.PaperPartialNCKFinalCompression

/-! # R16 fixed-color coordinate compression

This is the deterministic norm step used after selecting disjoint role-color
classes.  The actual ambient colored summand is zero outside the selected
boundary rows and columns; its compressed block is the typed matrix.  The
random-color averaging identity is a separate step and is not assumed here.
-/

noncomputable section
open Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Distinct typed boundary rows have distinct ambient colored rows. -/
theorem PaperRoleColoring.paperRow_injective
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) :
    Function.Injective C.paperRow := by
  intro row₁ row₂ h
  funext ⟨v, hv⟩
  obtain ⟨i, hi⟩ := (G.mem_leftBoundaryFinset_iff v).1 hv
  subst v
  apply (C.embedding (G.left i)).injective
  exact congrFun h i

/-- Distinct typed boundary columns have distinct ambient colored columns. -/
theorem PaperRoleColoring.paperCol_injective
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) :
    Function.Injective C.paperCol := by
  intro col₁ col₂ h
  funext ⟨v, hv⟩
  obtain ⟨i, hi⟩ := (G.mem_rightBoundaryFinset_iff v).1 hv
  subst v
  apply (C.embedding (G.right i)).injective
  exact congrFun h i

def PaperRoleColoring.paperRowEmbedding
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) :
    PartiteBoundaryRow (G := G.toPartiteShape) dimension ↪ PaperRow G n :=
  ⟨C.paperRow, C.paperRow_injective⟩

def PaperRoleColoring.paperColEmbedding
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) :
    PartiteBoundaryCol (G := G.toPartiteShape) dimension ↪ PaperCol G n :=
  ⟨C.paperCol, C.paperCol_injective⟩

/-- Extend a typed boundary matrix by zero to all ambient paper coordinates.
This is a deterministic construction, independent of the signs. -/
def PaperRoleColoring.zeroPaddedBoundaryMatrix
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (A : Matrix (PartiteBoundaryRow (G := G.toPartiteShape) dimension)
      (PartiteBoundaryCol (G := G.toPartiteShape) dimension) ℝ) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ := by
  classical
  exact fun row col =>
    if hr : ∃ r, C.paperRow r = row then
      if hc : ∃ c, C.paperCol c = col then
        A (Classical.choose hr) (Classical.choose hc)
      else 0
    else 0

/-- The selected block of the zero-padded matrix is exactly the input. -/
theorem PaperRoleColoring.zeroPaddedBoundaryMatrix_apply_selected
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (A : Matrix (PartiteBoundaryRow (G := G.toPartiteShape) dimension)
      (PartiteBoundaryCol (G := G.toPartiteShape) dimension) ℝ)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension) :
    C.zeroPaddedBoundaryMatrix A (C.paperRow row) (C.paperCol col) =
      A row col := by
  classical
  unfold zeroPaddedBoundaryMatrix
  split_ifs with hr hc
  · have hRow : Classical.choose hr = row :=
      C.paperRow_injective (Classical.choose_spec hr)
    have hCol : Classical.choose hc = col :=
      C.paperCol_injective (Classical.choose_spec hc)
    simp [hRow, hCol]
  · exact False.elim (hc ⟨col, rfl⟩)
  · exact False.elim (hr ⟨row, rfl⟩)

/-- Zero padding along the fixed disjoint-color boundary embeddings cannot
increase the Euclidean operator norm. -/
theorem PaperRoleColoring.zeroPaddedBoundaryMatrix_norm_le
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (A : Matrix (PartiteBoundaryRow (G := G.toPartiteShape) dimension)
      (PartiteBoundaryCol (G := G.toPartiteShape) dimension) ℝ) :
    ‖C.zeroPaddedBoundaryMatrix A‖ ≤ ‖A‖ := by
  classical
  apply paper_l2_opNorm_le_of_embedded_support
    C.paperRowEmbedding C.paperColEmbedding A
    (C.zeroPaddedBoundaryMatrix A)
  · intro row col
    exact C.zeroPaddedBoundaryMatrix_apply_selected A row col
  · intro row hrow col
    have hNoRow : ¬ ∃ r, C.paperRow r = row := by
      rintro ⟨r, hr⟩
      exact hrow ⟨r, hr⟩
    simp [zeroPaddedBoundaryMatrix, hNoRow]
  · intro col hcol row
    have hNoCol : ¬ ∃ c, C.paperCol c = col := by
      rintro ⟨c, hc⟩
      exact hcol ⟨c, hc⟩
    by_cases hRow : ∃ r, C.paperRow r = row
    · simp [zeroPaddedBoundaryMatrix, hRow, hNoCol]
    · simp [zeroPaddedBoundaryMatrix, hRow]

/-- The pointwise fixed-color comparison for the actual colored paper matrix.
The left matrix has the full ambient paper row/column types; it is supported
only on the selected color block. -/
theorem paperRoleColoredBoundaryMatrix_zeroPadded_norm_le
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n) (w : PaperNoise n) :
    ‖C.zeroPaddedBoundaryMatrix
        (paperRoleColoredBoundaryMatrix G dimension n C w)‖ ≤
      ‖paperRoleColoredBoundaryMatrix G dimension n C w‖ :=
  C.zeroPaddedBoundaryMatrix_norm_le _

#print axioms PaperRoleColoring.paperRow_injective
#print axioms PaperRoleColoring.paperCol_injective
#print axioms PaperRoleColoring.zeroPaddedBoundaryMatrix_apply_selected
#print axioms PaperRoleColoring.zeroPaddedBoundaryMatrix_norm_le
#print axioms paperRoleColoredBoundaryMatrix_zeroPadded_norm_le

end GraphMatrixReplica
