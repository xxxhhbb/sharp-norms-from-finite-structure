import R6.PaperBoundarySupport
import R6.PaperPartialNCKFinalCompression
import R6.PaperR16ColorLowerCompressionContractive

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica

abbrev RootPaperInjectiveRow (G : PaperShape) (n : ℕ) := Fin G.leftSize ↪ Fin n
abbrev RootPaperInjectiveCol (G : PaperShape) (n : ℕ) := Fin G.rightSize ↪ Fin n

def rootPaperRowEmbedding (G : PaperShape) (n : ℕ) :
    RootPaperInjectiveRow G n ↪ PaperRow G n where
  toFun row := row
  inj' := by intro row col h; exact DFunLike.coe_injective h

def rootPaperColEmbedding (G : PaperShape) (n : ℕ) :
    RootPaperInjectiveCol G n ↪ PaperCol G n where
  toFun col := col
  inj' := by intro row col h; exact DFunLike.coe_injective h

/-- The literal manuscript matrix: rows and columns are injective labels of
the ordered boundaries, with the original globally injective realization sum. -/
def rootPaperInjectiveGraphMatrix (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    Matrix (RootPaperInjectiveRow G n) (RootPaperInjectiveCol G n) ℝ :=
  (paperGraphMatrix G n w).submatrix (rootPaperRowEmbedding G n) (rootPaperColEmbedding G n)

theorem root_paperInjectiveGraphMatrix_entry (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (row : RootPaperInjectiveRow G n) (col : RootPaperInjectiveCol G n) :
    rootPaperInjectiveGraphMatrix G n w row col =
      ∑ phi : PaperRealization G n,
        if (∀ i, phi (G.left i) = row i) ∧ (∀ j, phi (G.right j) = col j) then
          ∏ e : Fin G.edges, paperEdgeSign w (phi (G.source e)) (phi (G.target e))
        else 0 := by
  classical
  rfl

/-- Zero rows and columns from noninjective boundary labels do not change the
operator norm. This includes empty index types, empty boundaries and overlap. -/
theorem root_paperInjectiveGraphMatrix_norm_eq (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    ‖rootPaperInjectiveGraphMatrix G n w‖ = ‖paperGraphMatrix G n w‖ := by
  classical
  apply le_antisymm
  · exact paper_l2_opNorm_submatrix_le (rootPaperRowEmbedding G n)
      (rootPaperColEmbedding G n) (paperGraphMatrix G n w)
  · apply paper_l2_opNorm_le_of_embedded_support (rootPaperRowEmbedding G n)
      (rootPaperColEmbedding G n) (rootPaperInjectiveGraphMatrix G n w) (paperGraphMatrix G n w)
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
theorem root_paperInjectiveGraphMatrix_mean_norm_eq (G : PaperShape) (n : ℕ) :
    paperMean (fun w : PaperNoise n => ‖rootPaperInjectiveGraphMatrix G n w‖) =
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) := by
  simp only [root_paperInjectiveGraphMatrix_norm_eq]

#print axioms root_paperInjectiveGraphMatrix_entry
#print axioms root_paperInjectiveGraphMatrix_norm_eq
#print axioms root_paperInjectiveGraphMatrix_mean_norm_eq
end GraphMatrixReplica
