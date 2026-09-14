import GraphMatrix.Model.ColorUpperTransfer
import GraphMatrix.Model.ColorCompressionNorm

/-! # colored summand as a zero-padded typed matrix

For a fixed ambient coloring, assume a `PaperRoleColoring` whose embedding
images are exactly the color classes.  This file identifies the actual R16
colored summand with the zero padding of the corresponding typed block.  The
construction of such a coloring, including empty classes, is separate.
-/

noncomputable section
open scoped BigOperators
open Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Exact image-completeness condition for a role-color embedding. -/
def PaperRoleColoring.ExactColorClasses
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (color : Fin n → Fin G.roles) : Prop :=
  ∀ (v : Fin G.roles) (i : Fin n),
    color i = v ↔ ∃ a : Fin (dimension v), C.embedding v a = i

/-- Assignments into the disjoint color classes are exactly the retained
globally injective realizations. -/
def PaperRoleColoring.retainedRealizationEquiv
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (color : Fin n → Fin G.roles)
    (hExact : C.ExactColorClasses color) :
    PaperRoleColorAssignment G dimension ≃
      {phi : PaperRealization G n // paperR16ColorRespects G color phi} := by
  classical
  apply Equiv.ofBijective (fun assignment =>
    (⟨C.globalRealization assignment, by
      intro v
      exact (hExact v (C.embedding v (assignment v))).2
        ⟨assignment v, rfl⟩⟩ :
      {phi : PaperRealization G n // paperR16ColorRespects G color phi}))
  constructor
  · intro a b hab
    funext v
    apply (C.embedding v).injective
    exact congrArg (fun x => x.1 v) hab
  · rintro ⟨phi, hPhi⟩
    let assignment : PaperRoleColorAssignment G dimension :=
      fun v => Classical.choose ((hExact v (phi v)).1 (hPhi v))
    refine ⟨assignment, ?_⟩
    apply Subtype.ext
    apply Function.Embedding.ext
    intro v
    change C.embedding v (assignment v) = phi v
    exact Classical.choose_spec ((hExact v (phi v)).1 (hPhi v))

/-- Reindex a sum of color-retained global realizations by rolewise typed
assignments, without assuming positive class sizes. -/
theorem PaperRoleColoring.sum_respecting_eq_sum_assignment
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (color : Fin n → Fin G.roles)
    (hExact : C.ExactColorClasses color)
    (term : PaperRealization G n → ℝ) :
    (∑ phi : PaperRealization G n,
      if paperR16ColorRespects G color phi then term phi else 0) =
      ∑ assignment : PaperRoleColorAssignment G dimension,
        term (C.globalRealization assignment) := by
  classical
  calc
    (∑ phi : PaperRealization G n,
      if paperR16ColorRespects G color phi then term phi else 0) =
        ∑ phi ∈ Finset.univ.filter (paperR16ColorRespects G color),
          term phi := by simp [Finset.sum_filter]
    _ = ∑ phi : {phi : PaperRealization G n //
        paperR16ColorRespects G color phi}, term phi.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ assignment : PaperRoleColorAssignment G dimension,
          term (C.globalRealization assignment) := by
      symm
      exact Fintype.sum_equiv (C.retainedRealizationEquiv color hExact)
        (fun assignment => term (C.globalRealization assignment))
        (fun phi => term phi.1) (fun _ => rfl)

/-- On selected boundary coordinates, the actual colored summand is
exactly the fixed-color typed block. -/
theorem paperR16ColoredGraphMatrix_apply_selected
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n)
    (color : Fin n → Fin G.roles)
    (hExact : C.ExactColorClasses color) (w : PaperNoise n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension) :
    paperR16ColoredGraphMatrix G n w color (C.paperRow row) (C.paperCol col) =
      paperRoleColoredBoundaryMatrix G dimension n C w row col := by
  classical
  unfold paperR16ColoredGraphMatrix paperRoleColoredBoundaryMatrix
  exact C.sum_respecting_eq_sum_assignment color hExact
    (fun phi =>
      if paperEntryCompatible G phi (C.paperRow row) (C.paperCol col) then
        ∏ e : Fin G.edges, paperEdgeSign w
          (phi (G.source e)) (phi (G.target e))
      else 0)

/-- A retained summand has no entry outside the selected row block. -/
theorem paperR16ColoredGraphMatrix_zero_outside_rows
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n)
    (color : Fin n → Fin G.roles)
    (hExact : C.ExactColorClasses color) (w : PaperNoise n)
    (row : PaperRow G n) (col : PaperCol G n)
    (hOutside : row ∉ Set.range C.paperRow) :
    paperR16ColoredGraphMatrix G n w color row col = 0 := by
  classical
  unfold paperR16ColoredGraphMatrix
  rw [C.sum_respecting_eq_sum_assignment color hExact]
  apply Finset.sum_eq_zero
  intro assignment _
  by_cases hCompatible :
      paperEntryCompatible G (C.globalRealization assignment) row col
  · exfalso
    apply hOutside
    let typedRow : PartiteBoundaryRow (G := G.toPartiteShape) dimension :=
      fun v => assignment v.1
    refine ⟨typedRow, ?_⟩
    funext i
    change C.embedding (G.left i) (assignment (G.left i)) = row i
    have hi := hCompatible.1 i
    change C.embedding (G.left i) (assignment (G.left i)) = row i at hi
    exact hi
  · simp [hCompatible]

/-- A retained summand has no entry outside the selected column block. -/
theorem paperR16ColoredGraphMatrix_zero_outside_cols
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n)
    (color : Fin n → Fin G.roles)
    (hExact : C.ExactColorClasses color) (w : PaperNoise n)
    (row : PaperRow G n) (col : PaperCol G n)
    (hOutside : col ∉ Set.range C.paperCol) :
    paperR16ColoredGraphMatrix G n w color row col = 0 := by
  classical
  unfold paperR16ColoredGraphMatrix
  rw [C.sum_respecting_eq_sum_assignment color hExact]
  apply Finset.sum_eq_zero
  intro assignment _
  by_cases hCompatible :
      paperEntryCompatible G (C.globalRealization assignment) row col
  · exfalso
    apply hOutside
    let typedCol : PartiteBoundaryCol (G := G.toPartiteShape) dimension :=
      fun v => assignment v.1
    refine ⟨typedCol, ?_⟩
    funext i
    change C.embedding (G.right i) (assignment (G.right i)) = col i
    have hi := hCompatible.2 i
    change C.embedding (G.right i) (assignment (G.right i)) = col i at hi
    exact hi
  · simp [hCompatible]

/-- The actual colored matrix is precisely the zero padding of its
typed fixed-color block, provided the embeddings cover the color classes. -/
theorem paperR16ColoredGraphMatrix_eq_zeroPadded
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n)
    (color : Fin n → Fin G.roles)
    (hExact : C.ExactColorClasses color) (w : PaperNoise n) :
    paperR16ColoredGraphMatrix G n w color =
      C.zeroPaddedBoundaryMatrix
        (paperRoleColoredBoundaryMatrix G dimension n C w) := by
  classical
  funext row col
  by_cases hRow : row ∈ Set.range C.paperRow
  · obtain ⟨typedRow, rfl⟩ := hRow
    by_cases hCol : col ∈ Set.range C.paperCol
    · obtain ⟨typedCol, rfl⟩ := hCol
      rw [paperR16ColoredGraphMatrix_apply_selected G dimension n C
        color hExact w typedRow typedCol]
      exact (C.zeroPaddedBoundaryMatrix_apply_selected _ typedRow typedCol).symm
    · rw [paperR16ColoredGraphMatrix_zero_outside_cols G dimension n C
        color hExact w (C.paperRow typedRow) col hCol]
      have hNoCol : ¬ ∃ c, C.paperCol c = col := by
        rintro ⟨c, hc⟩
        exact hCol ⟨c, hc⟩
      simp [PaperRoleColoring.zeroPaddedBoundaryMatrix, hNoCol]
  · rw [paperR16ColoredGraphMatrix_zero_outside_rows G dimension n C
      color hExact w row col hRow]
    have hNoRow : ¬ ∃ r, C.paperRow r = row := by
      rintro ⟨r, hr⟩
      exact hRow ⟨r, hr⟩
    simp [PaperRoleColoring.zeroPaddedBoundaryMatrix, hNoRow]


end GraphMatrixReplica
