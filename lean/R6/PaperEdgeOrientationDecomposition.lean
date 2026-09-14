import R6.PaperGraphMatrixEntryMoments

/-! # Edge-orientation decomposition of the paper graph matrix

BLNvH v2 splits a graph matrix into `2 ^ |E|` pieces according to whether
each realized edge is increasing or decreasing in the ambient order.  Each
piece is a chaos of nearly combinatorial type.  This file proves the exact
finite decomposition before any norm inequality is applied.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The ambient orientation pattern of one globally injective realization. -/
def paperEmbeddingOrientation (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) : Fin G.edges → Bool :=
  fun e => decide (phi (G.source e) < phi (G.target e))

/-- A realization belongs to the piece selected by `orientation`. -/
def paperOrientationCompatible (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool)
    (phi : PaperRealization G n) : Prop :=
  orientation = paperEmbeddingOrientation G phi

/-- The orientation-restricted summand in the paper's decomposition. -/
def paperOrientedGraphMatrix (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ := by
  classical
  exact fun row col =>
    ∑ phi : PaperRealization G n,
      if paperEntryCompatible G phi row col ∧
          paperOrientationCompatible G orientation phi then
        ∏ e : Fin G.edges, paperEdgeSign w
          (phi (G.source e)) (phi (G.target e))
      else 0

/-- Every realization selects exactly one orientation piece. -/
theorem paperOrientationCompatible_unique (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) :
    ∃! orientation : Fin G.edges → Bool,
      paperOrientationCompatible G orientation phi := by
  refine ⟨paperEmbeddingOrientation G phi, rfl, ?_⟩
  intro orientation h
  exact h

/-- Summing all orientation-restricted pieces recovers the original graph
matrix entrywise.  Thus subsequent triangle-inequality loss is isolated from
the exact combinatorial decomposition. -/
theorem paperSum_orientedGraphMatrix_eq (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) :
    (∑ orientation : Fin G.edges → Bool,
        paperOrientedGraphMatrix G n orientation w) =
      paperGraphMatrix G n w := by
  classical
  ext row col
  simp only [paperOrientedGraphMatrix, paperGraphMatrix, Matrix.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro phi _
  by_cases hEntry : paperEntryCompatible G phi row col
  · simp [hEntry, paperOrientationCompatible]
  · simp [hEntry]

/-- Distinct orientation pieces have disjoint realization support. -/
theorem paperOrientationCompatible_eq_of_both
    (G : PaperShape) {n : ℕ}
    {a b : Fin G.edges → Bool} {phi : PaperRealization G n}
    (ha : paperOrientationCompatible G a phi)
    (hb : paperOrientationCompatible G b phi) :
    a = b := by
  rw [ha, hb]

#print axioms paperOrientationCompatible_unique
#print axioms paperSum_orientedGraphMatrix_eq
#print axioms paperOrientationCompatible_eq_of_both

end GraphMatrixReplica
