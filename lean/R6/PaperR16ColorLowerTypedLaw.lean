import R6.PaperR16ColorLowerCompressionContractive
import R6.PaperR16TypedEdgeNoiseLaw
import R6.PaperR16UniformTypedInputBridge
import R6.PaperR16ColorLowerAutomorphism

/-! The fixed disjoint role-color readout has the complete independent typed
joint law, for arbitrary role-dependent class sizes. -/

noncomputable section
set_option maxHeartbeats 1000000
open scoped Matrix.Norms.L2Operator

namespace GraphMatrixReplica

theorem PaperRoleColoring.coloredBoundaryLq_eq_independent
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (q : ℝ) (hq : 0 < q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n =>
        paperRoleColoredBoundaryMatrix G dimension n C w) q =
      paperFiniteUniformLq
        (c027PartiteBoundaryMatrixReal G dimension) q := by
  classical
  have hPoint : ∀ w : PaperNoise n,
      paperRoleColoredBoundaryMatrix G dimension n C w =
        c027PartiteBoundaryMatrixReal G dimension
          (C.readJointEdgeSignSample w) := by
    intro w
    exact C.coloredBoundaryMatrix_eq_readTyped w
  have hMoment :
      paperMean (fun w : PaperNoise n =>
        ‖paperRoleColoredBoundaryMatrix G dimension n C w‖ ^ q) =
      paperMean (fun epsilon : JointEdgeSignSample
        (G := G.toPartiteShape) dimension =>
          ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ q) := by
    calc
      paperMean (fun w : PaperNoise n =>
        ‖paperRoleColoredBoundaryMatrix G dimension n C w‖ ^ q) =
          paperMean (fun w : PaperNoise n =>
            ‖c027PartiteBoundaryMatrixReal G dimension
              (C.readJointEdgeSignSample w)‖ ^ q) := by
            congr 1
            funext w
            rw [hPoint w]
      _ = paperMean (fun epsilon : JointEdgeSignSample
          (G := G.toPartiteShape) dimension =>
            ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ q) :=
        C.paperMean_readJointEdgeSignSample
          (fun epsilon : JointEdgeSignSample
            (G := G.toPartiteShape) dimension =>
              ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ q)
  rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ q hq,
    paperFiniteUniformLq_eq_paperMean_norm_rpow _ q hq]
  exact congrArg (fun x : ℝ => x ^ q⁻¹) hMoment

/-- Once the concrete survivor sum has been identified with the automorphism
count times the fixed-color matrix, the complete paper color lower transfer
follows for every real q at once. The pointwise identity is explicitly the
remaining hypothesis here. -/
theorem PaperRoleColoring.independentTypedLower_of_projection_identity
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (hIdentity : ∀ w : PaperNoise n,
      (paperR16ProjectedGraphMatrix G n tag w).submatrix
        C.paperRowEmbedding C.paperColEmbedding =
          (Fintype.card G.R16BoundaryFixingAutomorphism : ℝ) •
            paperRoleColoredBoundaryMatrix G dimension n C w)
    (q : ℝ) (hq : 1 ≤ q) :
    (Fintype.card G.R16BoundaryFixingAutomorphism : ℝ) *
      paperFiniteUniformLq
        (c027PartiteBoundaryMatrixReal G dimension) q ≤
      paperFiniteUniformLq (paperGraphMatrix G n) q := by
  have h := C.projectedCompressed_lower_of_identity tag
    (fun w => paperRoleColoredBoundaryMatrix G dimension n C w)
    (Fintype.card G.R16BoundaryFixingAutomorphism : ℝ)
    (by positivity) hIdentity q hq
  rw [C.coloredBoundaryLq_eq_independent q (lt_of_lt_of_le zero_lt_one hq)] at h
  exact h

#print axioms PaperRoleColoring.coloredBoundaryLq_eq_independent
#print axioms PaperRoleColoring.independentTypedLower_of_projection_identity

end GraphMatrixReplica
