import GraphMatrix.Main.TypedScaleAssembly
import GraphMatrix.Main.CoreProbabilityIdentification
import GraphMatrix.Main.DetachedSecondMoment
import GraphMatrix.Main.BoundaryCoreGlobalUpper

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

theorem main_finiteUniformL2_nonneg {Ω E : Type} [Fintype Ω] [NormedAddCommGroup E]
    (f : Ω → E) : 0 ≤ paperFiniteUniformLq f 2 := by
  rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ 2 (by norm_num)]
  exact Real.rpow_nonneg (by unfold paperMean; positivity) _

/-- Full-shape typed second moment: detached components and empty cores are
included. Only the independently proved U3 count remains an integration input. -/
theorem main_full_typedSecondMoment_sharp_of_exactCount
    (hCount : ReplicaCounting.ExactStratumBound) (G : PaperShape) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ dimension : Fin G.roles → ℕ, (∀ v, dimension v ≤ n) →
      paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
        ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ 2) ≤
          (mainTypedCoreConstant (mainBoundaryCoreShape G) * mainFullTypedGraphScale G n) ^ 2 := by
  obtain ⟨N, hN⟩ := main_boundaryCore_typedL2_sharp_of_exactCount hCount
    (mainBoundaryCoreShape G) (main_boundaryCoreShape_isBoundaryCore G)
  refine ⟨max N 2, ?_⟩
  intro n hn dimension hDim
  let S := mainGraphRawFactorShape G dimension
  let K := mainBoundaryCoreShape G
  let B := mainTypedCoreConstant K * mainTypedGraphScale K n
  have hnTwo : 2 ≤ n := (le_max_right _ _).trans hn
  have hB : 0 ≤ B := mul_nonneg (mainTypedCoreConstant_pos K).le
    (main_typedGraphScale_nonneg K n (by omega))
  have hU := main_unusedScalar_le_pow G dimension n hDim
  have hUsq : S.canonicalPreprocessedShape.unusedScalar ^ 2 ≤
      ((n : ℝ) ^ G.isolatedMiddleRoles.card) ^ 2 :=
    (sq_le_sq₀ S.unusedScalar_nonneg (by positivity)).mpr hU
  have hCore := hN n ((le_max_left _ _).trans hn) (mainCoreDimension G dimension)
    (fun v => hDim (mainCoreInclude G v))
  have hCoreSq : (∫ x, ‖S.coreMatrixFromBlock x‖ ^ 2
      ∂S.oneBlockLaw (fun _ => mainScalarSignLaw) (Sum.inl ())) ≤ B ^ 2 := by
    rw [main_core_secondIntegral_eq_typedSecondMoment,
      ← main_finiteUniformL2_sq_eq_mean_sq]
    exact (sq_le_sq₀ (main_finiteUniformL2_nonneg _) hB).mpr hCore
  have hDetached := S.prod_integral_abs_detachedScalar_sq_le_pow_sum n hDim
  have hCoreNonneg : 0 ≤ (∫ x, ‖S.coreMatrixFromBlock x‖ ^ 2
      ∂S.oneBlockLaw (fun _ => mainScalarSignLaw) (Sum.inl ())) :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hDetachedNonneg : 0 ≤ (∏ j : S.DetachedComponent,
      ∫ x, |S.detachedScalarFromBlock j x| ^ 2
        ∂S.oneBlockLaw (fun _ => mainScalarSignLaw) (Sum.inr j)) :=
    Finset.prod_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  rw [main_typed_secondMoment_factorization]
  calc
    _ ≤ ((n : ℝ) ^ G.isolatedMiddleRoles.card) ^ 2 *
        (B ^ 2 * (n : ℝ) ^ (∑ j : S.DetachedComponent, Fintype.card (S.CanonicalDetached j))) :=
      mul_le_mul hUsq (mul_le_mul hCoreSq hDetached hDetachedNonneg (sq_nonneg _))
        (mul_nonneg hCoreNonneg hDetachedNonneg) (by positivity)
    _ = _ := main_typed_squared_scale_assembly G dimension n (by omega) _

theorem main_full_typedL2_sharp_of_exactCount
    (hCount : ReplicaCounting.ExactStratumBound) (G : PaperShape) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ dimension : Fin G.roles → ℕ, (∀ v, dimension v ≤ n) →
      paperFiniteUniformLq (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
        c027PartiteBoundaryMatrixReal G dimension epsilon) 2 ≤
          mainTypedCoreConstant (mainBoundaryCoreShape G) * mainFullTypedGraphScale G n := by
  obtain ⟨N, hN⟩ := main_full_typedSecondMoment_sharp_of_exactCount hCount G
  refine ⟨max N 2, ?_⟩
  intro n hn dimension hDim
  have hb := hN n ((le_max_left _ _).trans hn) dimension hDim
  rw [← main_finiteUniformL2_sq_eq_mean_sq] at hb
  have hScale := main_fullTypedGraphScale_nonneg G n
    (show 1 ≤ n from Nat.le_trans (by norm_num) ((le_max_right N 2).trans hn))
  exact (sq_le_sq₀ (main_finiteUniformL2_nonneg _)
    (mul_nonneg (mainTypedCoreConstant_pos _).le hScale)).mp hb

def mainFullGraphUpperConstant (G : PaperShape) : ℝ :=
  max 1 ((G.roles : ℝ) ^ G.roles * mainTypedCoreConstant (mainBoundaryCoreShape G))

theorem mainFullGraphUpperConstant_pos (G : PaperShape) : 0 < mainFullGraphUpperConstant G :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Actual globally injective graph matrix, including empty/overlapping
boundaries, isolated roles and detached components. Formal integration supplies
the already proved U3 theorem; no shape-reduction or norm-bound hypotheses. -/
theorem main_full_globalMean_sharp_of_exactCount
    (hCount : ReplicaCounting.ExactStratumBound) (G : PaperShape) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        mainFullGraphUpperConstant G * mainFullTypedGraphScale G n := by
  by_cases hzero : G.roles = 0
  · refine ⟨2, ?_⟩
    intro n hn
    have hh : G.isolatedMiddleRoles.card = 0 := by
      have h := Finset.card_le_univ G.isolatedMiddleRoles
      simpa [hzero] using h
    have hs : G.toPartiteShape.rightLeftSeparatorNumber = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [PartiteShape.rightLeftSeparatorNumber, G.toPartiteShape_roles, hzero] using
        Finset.card_le_univ G.toPartiteShape.minimumRightLeftSeparator
    have ha : G.toPartiteShape.activeComponentMaximum = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [G.toPartiteShape_roles, hzero] using G.toPartiteShape.c079ActiveMaximum_le_roles
    simp only [paperR16_zeroRole_graphMatrix_norm_eq_one G hzero, paperMean_const_function]
    have he : mainFullTypedGraphScale G n = 1 := by simp [mainFullTypedGraphScale, hzero, hh, hs, ha]
    rw [he, mul_one]
    exact le_max_left _ _
  · have hr : 0 < G.roles := Nat.pos_of_ne_zero hzero
    obtain ⟨N, hN⟩ := main_full_typedL2_sharp_of_exactCount hCount G
    refine ⟨max N 2, ?_⟩
    intro n hn
    have hScale := main_fullTypedGraphScale_nonneg G n
      (show 1 ≤ n from Nat.le_trans (by norm_num) ((le_max_right N 2).trans hn))
    have hB := mul_nonneg (mainTypedCoreConstant_pos (mainBoundaryCoreShape G)).le hScale
    have hg := paperR16_globalLq_le_of_uniformTypedBound G n hr 2 (by norm_num)
      (mainTypedCoreConstant (mainBoundaryCoreShape G) * mainFullTypedGraphScale G n) hB
      (hN n ((le_max_left _ _).trans hn))
    calc
      _ ≤ paperFiniteUniformLq (fun w : PaperNoise n => paperGraphMatrix G n w) 2 :=
        main_mean_norm_le_finiteUniformL2 _
      _ ≤ (G.roles : ℝ) ^ G.roles *
          (mainTypedCoreConstant (mainBoundaryCoreShape G) * mainFullTypedGraphScale G n) := hg
      _ ≤ mainFullGraphUpperConstant G * mainFullTypedGraphScale G n := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hScale

/-- Unconditional upper half of the original graph-matrix theorem, with only
the actual PaperShape as input and graph-dependent constants before n. -/
theorem main_full_globalMean_sharp (G : PaperShape) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
        C * (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
          G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
            Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2) := by
  obtain ⟨N, hN⟩ := main_full_globalMean_sharp_of_exactCount
    ReplicaCounting.exactStratumBound G
  refine ⟨mainFullGraphUpperConstant G, mainFullGraphUpperConstant_pos G, N, ?_⟩
  intro n hn
  simpa only [mainFullTypedGraphScale, mul_assoc] using hN n hn

end GraphMatrixReplica
