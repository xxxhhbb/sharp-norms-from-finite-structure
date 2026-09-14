import GraphMatrix.BoundarySupport
import GraphMatrix.PartialNCKFinalCompression
import GraphMatrix.Model.ColorLowerCompressionContractive

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica

abbrev InjectiveRowIndex (G : PaperShape) (n : ℕ) := Fin G.leftSize ↪ Fin n
abbrev InjectiveColumnIndex (G : PaperShape) (n : ℕ) := Fin G.rightSize ↪ Fin n

def mainPaperRowEmbedding (G : PaperShape) (n : ℕ) :
    InjectiveRowIndex G n ↪ PaperRow G n where
  toFun row := row
  inj' := by intro row col h; exact DFunLike.coe_injective h

def mainPaperColEmbedding (G : PaperShape) (n : ℕ) :
    InjectiveColumnIndex G n ↪ PaperCol G n where
  toFun col := col
  inj' := by intro row col h; exact DFunLike.coe_injective h

/-- The literal manuscript matrix: rows and columns are injective labels of
the ordered boundaries, with the original globally injective realization sum. -/
def injectiveGraphMatrix (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    Matrix (InjectiveRowIndex G n) (InjectiveColumnIndex G n) ℝ :=
  (paperGraphMatrix G n w).submatrix (mainPaperRowEmbedding G n) (mainPaperColEmbedding G n)

theorem main_paperInjectiveGraphMatrix_entry (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (row : InjectiveRowIndex G n) (col : InjectiveColumnIndex G n) :
    injectiveGraphMatrix G n w row col =
      ∑ phi : PaperRealization G n,
        if (∀ i, phi (G.left i) = row i) ∧ (∀ j, phi (G.right j) = col j) then
          ∏ e : Fin G.edges, paperEdgeSign w (phi (G.source e)) (phi (G.target e))
        else 0 := by
  classical
  rfl

/-- Zero rows and columns from noninjective boundary labels do not change the
operator norm. This includes empty index types, empty boundaries and overlap. -/
theorem main_paperInjectiveGraphMatrix_norm_eq (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    ‖injectiveGraphMatrix G n w‖ = ‖paperGraphMatrix G n w‖ := by
  classical
  apply le_antisymm
  · exact paper_l2_opNorm_submatrix_le (mainPaperRowEmbedding G n)
      (mainPaperColEmbedding G n) (paperGraphMatrix G n w)
  · apply paper_l2_opNorm_le_of_embedded_support (mainPaperRowEmbedding G n)
      (mainPaperColEmbedding G n) (injectiveGraphMatrix G n w) (paperGraphMatrix G n w)
    · intro row col
      rfl
    · intro row hrow col
      apply paperGraphMatrix_zero_of_row_not_injective G n w row col
      intro hInj
      exact hrow ⟨⟨row, hInj⟩, rfl⟩
    · intro col hcol row
      apply paperGraphMatrix_zero_of_col_not_injective G n w row col
      intro hInj
      exact hcol ⟨⟨col, hInj⟩, rfl⟩

/-- The expected norm in the literal manuscript indexing is exactly the same
quantity proved by the original PaperShape upper and lower endpoints. -/
theorem main_paperInjectiveGraphMatrix_mean_norm_eq (G : PaperShape) (n : ℕ) :
    paperMean (fun w : PaperNoise n => ‖injectiveGraphMatrix G n w‖) =
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  simp only [main_paperInjectiveGraphMatrix_norm_eq]

end GraphMatrixReplica
