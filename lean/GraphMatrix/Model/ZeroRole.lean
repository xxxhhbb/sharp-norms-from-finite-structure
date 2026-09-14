import GraphMatrix.GraphMatrixEntryMoments

/-! # zero-role scalar convention

The independent random-color identity is used only for positive role count.
When a paper shape has no roles, it has no edges or boundary positions and
there is exactly one globally injective realization. Its sole matrix entry is
the empty product, namely `1`, for every ambient size and sign sample.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

theorem paperR16_zeroRole_edges (G : PaperShape) (hroles : G.roles = 0) :
    G.edges = 0 := by
  letI : IsEmpty (Fin G.roles) := by
    rw [hroles]
    infer_instance
  by_contra he
  exact isEmptyElim (G.source ⟨0, Nat.pos_of_ne_zero he⟩)

/-- The original globally injective graph matrix is the scalar `1` when
there are no shape roles, with no assumption on ambient size or noise. -/
theorem paperR16_zeroRole_graphMatrix_eq_one
    (G : PaperShape) (hroles : G.roles = 0) (n : ℕ)
    (w : PaperNoise n) (row : PaperRow G n) (col : PaperCol G n) :
    paperGraphMatrix G n w row col = 1 := by
  letI : IsEmpty (Fin G.roles) := by
    rw [hroles]
    infer_instance
  letI : Unique (PaperRealization G n) := inferInstance
  have hedges : G.edges = 0 := paperR16_zeroRole_edges G hroles
  letI : IsEmpty (Fin G.edges) := by
    rw [hedges]
    infer_instance
  have hcompat (phi : PaperRealization G n) :
      paperEntryCompatible G phi row col := by
    constructor
    · intro i
      exact isEmptyElim (G.left i)
    · intro j
      exact isEmptyElim (G.right j)
  unfold paperGraphMatrix
  simp [hcompat]


end GraphMatrixReplica
