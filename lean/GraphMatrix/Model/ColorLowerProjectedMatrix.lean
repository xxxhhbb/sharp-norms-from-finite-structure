import GraphMatrix.Model.ColorLowerProjectedEntry
import GraphMatrix.Model.ColorCompressionNorm

/-! # Matrix-valued full Walsh projection of the original graph matrix

The scalar survivor-sum formula and the generic finite-uniform `L^q`
contraction are here attached to the *same* original paper matrix-valued
projection. The colored boundary compression and typed identification
remain separate obligations.
-/

noncomputable section
open Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The matrix-valued Fourier coefficient of the original globally
injective graph matrix under a fixed target edge-pair tag. -/
def paperR16ProjectedGraphMatrix
    (G : PaperShape) (n : ℕ)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (w : PaperNoise n) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ :=
  paperR16FullWalshProject tag (paperGraphMatrix G n) w

/-- The matrix projection and the exact scalar survivor-sum calculation
refer to identical entries, not two unrelated projections. -/
theorem paperR16ProjectedGraphMatrix_apply
    (G : PaperShape) (n : ℕ)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (w : PaperNoise n) (row : PaperRow G n) (col : PaperCol G n) :
    paperR16ProjectedGraphMatrix G n tag w row col =
      paperR16ProjectedGraphEntry G n tag w row col := by
  classical
  unfold paperR16ProjectedGraphMatrix paperR16ProjectedGraphEntry
    paperR16FullWalshProject paperMean
  simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

/-- The actual original graph-matrix Walsh projection is an `L^q`
contraction for every real `q ≥ 1`, before color compression. -/
theorem paperR16ProjectedGraphMatrix_lq_le
    (G : PaperShape) (n : ℕ)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq (paperR16ProjectedGraphMatrix G n tag) q ≤
      paperFiniteUniformLq (paperGraphMatrix G n) q := by
  exact paperR16FullWalshProject_lq_le tag (paperGraphMatrix G n) q hq


end GraphMatrixReplica
