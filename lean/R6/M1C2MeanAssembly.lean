import R6.C2ActualIntegrationAcceptance
import R6.PaperBranchSym2VarianceCompression
import R6.PaperR16UniformTypedInputBridge
import R6.PaperR16FiniteColorNormTransfer

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open PaperR16.C2Actual
attribute [local instance] Classical.propDecidable

theorem root_actualFreshMean_eq_paperMean (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (f : FreshSample (G := P.toPartiteShape) S dimension → ℝ) :
    actualFreshMean P S dimension f = paperMean f := by
  unfold actualFreshMean paperMean
  rw [div_eq_inv_mul]

/-- The existing genuine edge partition gives exact iterated finite means.
No independence or factorized-law premise is needed. -/
theorem root_mean_frozen_fresh_eq_joint (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (f : JointEdgeSignSample (G := P.toPartiteShape) dimension → ℝ) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualFreshMean P S dimension
        (fun ξ => f (assembleSample (G := P.toPartiteShape) S dimension ω ξ))) =
        paperMean f := by
  simp_rw [root_actualFreshMean_eq_paperMean]
  let g : (FrozenSample (G := P.toPartiteShape) S dimension ×
      FreshSample (G := P.toPartiteShape) S dimension) → ℝ :=
    fun p => f (assembleSample (G := P.toPartiteShape) S dimension p.1 p.2)
  exact (paperMean_prod_eq_iterated g).symm.trans
    (paperMean_equiv (sampleSplitEquiv (G := P.toPartiteShape) S dimension).symm f)

theorem root_mean_C2FreshMean_eq_typedMean (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualC2FreshMean P S dimension ω) =
        paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
          ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  exact root_mean_frozen_fresh_eq_joint P S dimension
    (fun ε => ‖c027PartiteBoundaryMatrixReal P dimension ε‖)

/-- C2 integrated over the complete frozen realization, with its RHS exactly
the actual typed matrix mean. The only premises are the proved geometric scope
of C2 and positive role dimensions. -/
theorem root_integrated_C2_lower (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualC2CoefficientScale P S dimension ω) ≤
        Real.sqrt 3 ^ freshCount P S *
          paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
            ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  have h := paperMean_mono (fun ω => actual_C2_lower_bound P S dimension hNoIso hMin hdim ω)
  rw [paperMean_const_mul_color, root_mean_C2FreshMean_eq_typedMean] at h
  exact h

theorem root_integrated_C2_lower_div (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualC2CoefficientScale P S dimension ω) / (Real.sqrt 3 ^ freshCount P S) ≤
        paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
          ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 3 ^ freshCount P S)).mpr
  simpa only [mul_comm] using root_integrated_C2_lower P S dimension hNoIso hMin hdim

#print axioms root_mean_frozen_fresh_eq_joint
#print axioms root_mean_C2FreshMean_eq_typedMean
#print axioms root_integrated_C2_lower
#print axioms root_integrated_C2_lower_div
end GraphMatrixReplica
