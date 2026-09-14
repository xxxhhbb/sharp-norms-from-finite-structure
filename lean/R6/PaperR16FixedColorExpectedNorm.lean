import R6.PaperR16TypedEdgeNoiseLaw
import R6.C027NormTransferInterface

/-! # Fixed-color expected norm equals the independent-edge typed norm

For one disjoint role-color embedding, the selected ambient edge coordinates
have exactly the typed joint sign law, and the compressed matrix is pointwise
the real-cast typed matrix under the extracted sample.  Thus every real test
statistic of that compressed matrix has the same finite-uniform expectation
as in the typed model.  This still does not compare the full global paper
matrix with the compressed block; random-color averaging and zero-padding
are separate steps.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Exact equality of the fixed-color compressed expected operator norm and
the independent-edge typed expected operator norm. -/
theorem PaperRoleColoring.paperMean_coloredBoundaryNorm_eq_partite
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    [DecidableEq (PaperColoredEdgeCoordinate G dimension)]
    (C : PaperRoleColoring G dimension n) :
    paperMean (fun w : PaperNoise n =>
      ‖paperRoleColoredBoundaryMatrix G dimension n C w‖) =
        c027PartiteExpectedOperatorNorm G dimension := by
  classical
  calc
    paperMean (fun w : PaperNoise n =>
        ‖paperRoleColoredBoundaryMatrix G dimension n C w‖) =
        paperMean (fun w : PaperNoise n =>
          ‖c027PartiteBoundaryMatrixReal G dimension
            (C.readJointEdgeSignSample w)‖) := by
      congr 1
      funext w
      rw [C.coloredBoundaryMatrix_eq_readTyped w]
      rfl
    _ = c027PartiteExpectedOperatorNorm G dimension := by
      exact C.paperMean_readJointEdgeSignSample
        (fun epsilon => ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖)

#print axioms PaperRoleColoring.paperMean_coloredBoundaryNorm_eq_partite

end GraphMatrixReplica
