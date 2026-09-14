import GraphMatrix.Model.ColorLowerPointwiseIdentity
import GraphMatrix.Model.ColorLowerTypedLaw

/-! Final composition for the global color lower transfer. -/

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- After isolated middle roles have been removed, the original global
graph matrix dominates the independent typed fixed-color matrix in every
real Lq, with the positive boundary-fixing automorphism count. Role class
sizes are arbitrary and may differ. -/
theorem PaperRoleColoring.independentTypedColorLower
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (q : ℝ) (hq : 1 ≤ q) :
    (Fintype.card G.R16BoundaryFixingAutomorphism : ℝ) *
      paperFiniteUniformLq
        (c027PartiteBoundaryMatrixReal G dimension) q ≤
      paperFiniteUniformLq (paperGraphMatrix G n) q := by
  apply C.independentTypedLower_of_projection_identity
    C.targetEdgeTag ?_ q hq
  intro w
  simpa only [Nat.cast_smul_eq_nsmul] using
    C.projectedCompressed_eq_aut_smul_typed hNoIsolated w

/-- The shape-dependent coefficient in the lower transfer is positive. -/
theorem PaperShape.colorLowerCoefficient_pos (G : PaperShape) :
    0 < (Fintype.card G.R16BoundaryFixingAutomorphism : ℝ) := by
  exact_mod_cast PaperShape.R16BoundaryFixingAutomorphism.card_pos G


end GraphMatrixReplica
