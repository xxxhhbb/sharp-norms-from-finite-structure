import GraphMatrix.Probability.Factorization.RawProductBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ENNReal
open MeasureTheory
namespace GraphMatrixReplica.Model.RawFactorShape
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

def rawNormPrimitive (x : S.RawPrimitiveCoord → ℝ) : ℝ :=
  ‖S.rawOperatorMatrix (S.unflattenRawSample x)‖

theorem rawNormPrimitive_eq_blocks (x : S.RawPrimitiveCoord → ℝ) :
    S.rawNormPrimitive x =
      S.canonicalPreprocessedShape.unusedScalar *
        (∏ j, |S.detachedScalarFromBlock j (S.rawFlatToBlocksMeasurableEquiv x (Sum.inr j))|) *
        ‖S.coreMatrixFromBlock (S.rawFlatToBlocksMeasurableEquiv x (Sum.inl ()))‖ := by
  have h := S.rawOperatorNorm_ofBlocks_eq_nonneg (S.rawFlatToBlocksMeasurableEquiv x)
  simpa only [rawSampleOfBlocks, MeasurableEquiv.symm_apply_apply, rawNormPrimitive] using h

theorem measurable_rawNormPrimitive : Measurable S.rawNormPrimitive := by
  classical
  have hc := S.measurable_coreNormFromBlock.comp
    ((measurable_pi_apply (Sum.inl ())).comp S.rawFlatToBlocksMeasurableEquiv.measurable)
  have hd (j : S.DetachedComponent) := (S.measurable_abs_detachedScalarFromBlock j).comp
    ((measurable_pi_apply (Sum.inr j)).comp S.rawFlatToBlocksMeasurableEquiv.measurable)
  simp_rw [show S.rawNormPrimitive = fun x =>
      S.canonicalPreprocessedShape.unusedScalar *
        (∏ j, |S.detachedScalarFromBlock j (S.rawFlatToBlocksMeasurableEquiv x (Sum.inr j))|) *
        ‖S.coreMatrixFromBlock (S.rawFlatToBlocksMeasurableEquiv x (Sum.inl ()))‖ from
      funext S.rawNormPrimitive_eq_blocks]
  exact (measurable_const.mul (Finset.measurable_prod _ fun j _ => hd j)).mul hc

theorem rawNormPrimitive_rpow_eq_blocks (q : ℝ) (x : S.RawPrimitiveCoord → ℝ) :
    S.rawNormPrimitive x ^ q =
      S.canonicalPreprocessedShape.unusedScalar ^ q *
        (‖S.coreMatrixFromBlock (S.rawFlatToBlocksMeasurableEquiv x (Sum.inl ()))‖ ^ q *
          ∏ j, |S.detachedScalarFromBlock j (S.rawFlatToBlocksMeasurableEquiv x (Sum.inr j))| ^ q) := by
  rw [S.rawNormPrimitive_eq_blocks]
  rw [Real.mul_rpow (mul_nonneg S.unusedScalar_nonneg (Finset.prod_nonneg (fun _ _ => abs_nonneg _))) (norm_nonneg _)]
  rw [Real.mul_rpow S.unusedScalar_nonneg (Finset.prod_nonneg (fun _ _ => abs_nonneg _))]
  rw [← Real.finsetProd_rpow _ _ (fun _ _ => abs_nonneg _) q]
  ring

/-- Exact real-q moment identity on the actual primitive law. This identity
uses totalized Bochner integrals; finite Lq membership is proved separately. -/
theorem integral_rawNormPrimitive_rpow (ν : E → Measure ℝ)
    [∀ e, IsProbabilityMeasure (ν e)] (q : ℝ) :
    (∫ x, S.rawNormPrimitive x ^ q ∂S.rawPrimitiveLaw ν) =
      S.canonicalPreprocessedShape.unusedScalar ^ q *
        ((∫ x, ‖S.coreMatrixFromBlock x‖ ^ q ∂S.oneBlockLaw ν (Sum.inl ())) *
          ∏ j, ∫ x, |S.detachedScalarFromBlock j x| ^ q ∂S.oneBlockLaw ν (Sum.inr j)) := by
  classical
  simp_rw [S.rawNormPrimitive_rpow_eq_blocks q]
  rw [integral_const_mul]
  congr 1
  exact (S.integral_raw_reindex ν (fun blocks =>
      ‖S.coreMatrixFromBlock (blocks (Sum.inl ()))‖ ^ q *
        ∏ j, |S.detachedScalarFromBlock j (blocks (Sum.inr j))| ^ q)).trans
    (S.integral_actual_core_detached_tests ν (fun M => ‖M‖ ^ q) (fun _ z => |z| ^ q))

/-- Exact Lq norm factorization for every finite real q >= 1. The hypotheses
are finiteness of the individual factor Lq norms, not the sought product law. -/
theorem raw_lpNorm_factorization (ν : E → Measure ℝ)
    [∀ e, IsProbabilityMeasure (ν e)] (q : ℝ) (hq : 1 ≤ q)
    (hc : MemLp (fun x => ‖S.coreMatrixFromBlock x‖) (ENNReal.ofReal q)
      (S.oneBlockLaw ν (Sum.inl ())))
    (hd : ∀ j, MemLp (S.detachedScalarFromBlock j) (ENNReal.ofReal q)
      (S.oneBlockLaw ν (Sum.inr j))) :
    lpNorm S.rawNormPrimitive (ENNReal.ofReal q) (S.rawPrimitiveLaw ν) =
      S.canonicalPreprocessedShape.unusedScalar *
        (∏ j, lpNorm (S.detachedScalarFromBlock j) (ENNReal.ofReal q)
          (S.oneBlockLaw ν (Sum.inr j))) *
        lpNorm (fun x => ‖S.coreMatrixFromBlock x‖) (ENNReal.ofReal q)
          (S.oneBlockLaw ν (Sum.inl ())) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp0 : ENNReal.ofReal q ≠ 0 := by positivity
  have hpt : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpt S.measurable_rawNormPrimitive.aestronglyMeasurable]
  rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpt hc.aestronglyMeasurable]
  simp_rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hpt (hd _).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hq0.le, norm_norm]
  have hr (x : S.RawPrimitiveCoord → ℝ) : ‖S.rawNormPrimitive x‖ = S.rawNormPrimitive x :=
    Real.norm_of_nonneg (norm_nonneg _)
  simp_rw [hr, Real.norm_eq_abs]
  rw [S.integral_rawNormPrimitive_rpow ν q]
  have hc0 : 0 ≤ ∫ x, ‖S.coreMatrixFromBlock x‖ ^ q ∂S.oneBlockLaw ν (Sum.inl ()) :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hd0 (j : S.DetachedComponent) :
      0 ≤ ∫ x, |S.detachedScalarFromBlock j x| ^ q ∂S.oneBlockLaw ν (Sum.inr j) :=
    integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  rw [Real.mul_rpow (Real.rpow_nonneg S.unusedScalar_nonneg q)
    (mul_nonneg hc0 (Finset.prod_nonneg (fun j _ => hd0 j)))]
  rw [← Real.rpow_mul S.unusedScalar_nonneg, mul_inv_cancel₀ hq0.ne', Real.rpow_one]
  rw [Real.mul_rpow hc0 (Finset.prod_nonneg (fun j _ => hd0 j))]
  rw [← Real.finsetProd_rpow _ _ (fun j _ => hd0 j) q⁻¹]
  dsimp only [BlockCoord]
  ring

/-- Finite factor Lq norms imply finite Lq norm of the actual raw matrix norm.
Thus the real-valued norm equality above is a genuine finite-Lq statement. -/
theorem rawNormPrimitive_memLp (ν : E → Measure ℝ)
    [∀ e, IsProbabilityMeasure (ν e)] (q : ℝ) (hq : 1 ≤ q)
    (hc : MemLp (fun x => ‖S.coreMatrixFromBlock x‖) (ENNReal.ofReal q)
      (S.oneBlockLaw ν (Sum.inl ())))
    (hd : ∀ j, MemLp (S.detachedScalarFromBlock j) (ENNReal.ofReal q)
      (S.oneBlockLaw ν (Sum.inr j))) :
    MemLp S.rawNormPrimitive (ENNReal.ofReal q) (S.rawPrimitiveLaw ν) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp0 : ENNReal.ofReal q ≠ 0 := by positivity
  have hpt : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  let f := S.blockTest (fun x => ‖S.coreMatrixFromBlock x‖ ^ q)
    (fun j x => |S.detachedScalarFromBlock j x| ^ q)
  have hf (b : S.ProbabilityBlock) : Integrable (f b) (S.oneBlockLaw ν b) := by
    cases b with
    | inl u =>
      cases u
      simpa only [f, blockTest, ENNReal.toReal_ofReal hq0.le, norm_norm] using
        hc.integrable_norm_rpow hp0 hpt
    | inr j =>
      simpa only [f, blockTest, ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs] using
        (hd j).integrable_norm_rpow hp0 hpt
  let H : (∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) → ℝ :=
    fun blocks => S.canonicalPreprocessedShape.unusedScalar ^ q *
      ∏ b : S.ProbabilityBlock, f b (blocks b)
  have hH : Integrable H (S.groupedPrimitiveLaw ν) := by
    rw [S.groupedPrimitiveLaw_eq_pi ν]
    exact (Integrable.fintype_prod_dep hf).const_mul _
  have hi : Integrable (H ∘ S.rawFlatToBlocksMeasurableEquiv) (S.rawPrimitiveLaw ν) := by
    apply (integrable_map_equiv S.rawFlatToBlocksMeasurableEquiv H).mp
    rw [S.map_rawPrimitiveLaw_eq_groupedPrimitiveLaw ν]
    exact hH
  apply (integrable_norm_rpow_iff S.measurable_rawNormPrimitive.aestronglyMeasurable hp0 hpt).mp
  apply hi.congr
  filter_upwards [] with x
  simp only [Function.comp_def, H, f, Fintype.prod_sum_type,
    Fintype.prod_unique, blockTest, ENNReal.toReal_ofReal hq0.le]
  rw [Real.norm_of_nonneg (show 0 ≤ S.rawNormPrimitive x from norm_nonneg _)]
  exact (S.rawNormPrimitive_rpow_eq_blocks q x).symm

end GraphMatrixReplica.Model.RawFactorShape
