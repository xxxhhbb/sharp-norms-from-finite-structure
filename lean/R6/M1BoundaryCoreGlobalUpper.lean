import R6.M1TraceScaleBounds
import R6.U3IntegrationAcceptance
import R6.PaperR16UniformTypedInputBridge
import R6.PaperMomentToMean
import R6.FiniteMengerResidualPathProjection

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica

/-- The actual normalized finite first moment is bounded by its L2 norm. -/
theorem root_mean_norm_le_finiteUniformL2
    {Ω E : Type} [Fintype Ω] [NormedAddCommGroup E] (f : Ω → E) :
    paperMean (fun w => ‖f w‖) ≤ paperFiniteUniformLq f 2 := by
  rw [paperFiniteUniformLq_eq_paperMean_norm_rpow f 2 (by norm_num)]
  simp only [Real.rpow_two]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le
    (paperMean_pow_le_mean_pow (fun w => ‖f w‖) 2 (by norm_num) (fun w => norm_nonneg _))

def rootBoundaryCoreUpperConstant (G : PaperShape) : ℝ :=
  (G.roles : ℝ) ^ G.roles *
    (2 * (c079C G.roles : ℝ) *
      Real.exp ((G.toPartiteShape.rightLeftSeparatorNumber : ℝ) / 2) *
      (8 : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2))

theorem rootBoundaryCoreUpperConstant_pos (G : PaperShape) (hr : 0 < G.roles) :
    0 < rootBoundaryCoreUpperConstant G := by
  have hC : 0 < (c079C G.roles : ℝ) := by
    unfold c079C
    positivity
  unfold rootBoundaryCoreUpperConstant
  positivity

set_option backward.isDefEq.respectTransparency false in
/-- Assembly lemma. Its count dependency remains explicit until the separately
verified U3 proof is imported; this is not the unconditional main theorem. -/
theorem root_boundaryCore_globalMean_sharp_of_exactCount
    (hCount : C079U3.U3ExactStratumAcceptance)
    (G : PaperShape) (hr : 0 < G.roles) (hCore : G.toPartiteShape.IsBoundaryCore) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        rootBoundaryCoreUpperConstant G *
          (n : ℝ) ^ (((G.roles : ℝ) -
            (G.toPartiteShape.rightLeftSeparatorNumber : ℝ)) / 2) *
          Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2) := by
  let H := G.toPartiteShape
  let s := H.rightLeftSeparatorNumber
  let a := H.c079ActiveMaximum
  let family : H.VertexDisjointRightToLeftPaths s := by
    dsimp [s]
    rw [← H.rightLeftOptima_eq]
    exact H.maximumRightLeftPathPacking
  have hs : s ≤ H.roles := family.pathCount_le_roles
  obtain ⟨N, hN⟩ := paperR16_typedCore_realLpRoot_le_finiteScale_eventually
    H s a 2 (by norm_num)
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnTwo : 2 ≤ n := (le_max_right _ _).trans hn
  have hWindow : (2 : ℝ) ≤ 2 * Real.log (2 * (n : ℝ)) := by
    have hh := one_le_log_two_mul_nat_of_two_le n hnTwo
    linarith
  let T : ℝ := (2 * (c079C G.roles : ℝ) * Real.exp ((s : ℝ) / 2) *
    (8 : ℝ) ^ ((a : ℝ) / 2)) *
    (n : ℝ) ^ (((G.roles : ℝ) - (s : ℝ)) / 2) * Real.log (n : ℝ) ^ ((a : ℝ) / 2)
  have hT : 0 ≤ T := by
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    dsimp [T]
    positivity
  have hTyped : ∀ dimension : Fin G.roles → ℕ, (∀ v, dimension v ≤ n) →
      paperFiniteUniformLq (fun epsilon : JointEdgeSignSample (G := H) dimension =>
        c027PartiteBoundaryMatrixReal G dimension epsilon) 2 ≤ T := by
    intro dimension hDim
    rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ 2 (by norm_num)]
    simp_rw [paperR16_c027PartiteReal_eq_c079PartiteReal]
    have hc := hCount H (paperR16ReplicaParameter n 2)
      (paperR16ReplicaParameter_pos n 2) hr hCore H.rightLeftMengerCertificate
    have ht := hN n hnN 2 (by norm_num) hWindow dimension hDim
      (H.roleCovered_of_isBoundaryCore hCore) family hc
    have hScale : paperR16TypedCoreFiniteLpScale H (paperR16ReplicaParameter n 2) s a n ≤ T := by
      simpa only [T, H, s, a, G.toPartiteShape_roles,
        show (2 : ℝ) * (2 + 2) = 8 by norm_num] using
        root_paper_finiteScale_le_original_log_scale
          H s a n 2 2 hs hnTwo (by norm_num) (by norm_num) hWindow
    exact le_trans ht hScale
  have hg := paperR16_globalLq_le_of_uniformTypedBound G n hr 2 (by norm_num) T hT hTyped
  calc
    _ ≤ paperFiniteUniformLq (fun w : PaperNoise n => paperGraphMatrix G n w) 2 :=
      root_mean_norm_le_finiteUniformL2 _
    _ ≤ (G.roles : ℝ) ^ G.roles * T := hg
    _ = _ := by dsimp [T, rootBoundaryCoreUpperConstant, s, a, H]; ring

/-- Unconditional boundary-core upper bound for the actual globally-injective
paper matrix.  The U3 exact count is now supplied by its proved acceptance
theorem rather than by a conclusion-shaped argument. -/
theorem m1_boundaryCore_globalMean_sharp
    (G : PaperShape) (hr : 0 < G.roles)
    (hCore : G.toPartiteShape.IsBoundaryCore) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        rootBoundaryCoreUpperConstant G *
          (n : ℝ) ^ (((G.roles : ℝ) -
            (G.toPartiteShape.rightLeftSeparatorNumber : ℝ)) / 2) *
          Real.log (n : ℝ) ^
            ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2) :=
  root_boundaryCore_globalMean_sharp_of_exactCount
    C079U3.u3ExactStratumAcceptance G hr hCore

#print axioms root_mean_norm_le_finiteUniformL2
#print axioms rootBoundaryCoreUpperConstant_pos
#print axioms root_boundaryCore_globalMean_sharp_of_exactCount
#print axioms m1_boundaryCore_globalMean_sharp
end GraphMatrixReplica
