import GraphMatrix.Lower.Flattening.Theorems
import GraphMatrix.BranchSym2VarianceCompression
import GraphMatrix.Model.UniformTypedInputBridge
import GraphMatrix.Model.FiniteColorNormTransfer

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open Model.C2Actual
attribute [local instance] Classical.propDecidable

theorem main_actualFreshMean_eq_paperMean (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (f : FreshSample (G := P.toPartiteShape) S dimension → ℝ) :
    actualFreshMean P S dimension f = paperMean f := by
  unfold actualFreshMean paperMean
  rw [div_eq_inv_mul]

/-- The existing genuine edge partition gives exact iterated finite means.
No independence or factorized-law premise is needed. -/
theorem main_mean_frozen_fresh_eq_joint (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (f : JointEdgeSignSample (G := P.toPartiteShape) dimension → ℝ) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualFreshMean P S dimension
        (fun ξ => f (assembleSample (G := P.toPartiteShape) S dimension ω ξ))) =
        paperMean f := by
  simp_rw [main_actualFreshMean_eq_paperMean]
  let g : (FrozenSample (G := P.toPartiteShape) S dimension ×
      FreshSample (G := P.toPartiteShape) S dimension) → ℝ :=
    fun p => f (assembleSample (G := P.toPartiteShape) S dimension p.1 p.2)
  exact (paperMean_prod_eq_iterated g).symm.trans
    (paperMean_equiv (sampleSplitEquiv (G := P.toPartiteShape) S dimension).symm f)

theorem main_mean_C2FreshMean_eq_typedMean (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualC2FreshMean P S dimension ω) =
        paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
          ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  exact main_mean_frozen_fresh_eq_joint P S dimension
    (fun ε => ‖c027PartiteBoundaryMatrixReal P dimension ε‖)

/-- integrated over the complete frozen realization, with its RHS exactly
the actual typed matrix mean. The only premises are the proved geometric scope
of and positive role dimensions. -/
theorem main_integrated_C2_lower (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualC2CoefficientScale P S dimension ω) ≤
        Real.sqrt 3 ^ freshCount P S *
          paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
            ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  have h := paperMean_mono (fun ω => actual_C2_lower_bound P S dimension hNoIso hMin hdim ω)
  rw [paperMean_const_mul_color, main_mean_C2FreshMean_eq_typedMean] at h
  exact h

theorem main_integrated_C2_lower_div (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v) :
    paperMean (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      actualC2CoefficientScale P S dimension ω) / (Real.sqrt 3 ^ freshCount P S) ≤
        paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
          ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt 3 ^ freshCount P S)).mpr
  simpa only [mul_comm] using main_integrated_C2_lower P S dimension hNoIso hMin hdim

end GraphMatrixReplica
