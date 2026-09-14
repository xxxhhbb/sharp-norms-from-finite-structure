import R6.M1GraphRawFactorBridge
import R6.F1aRealLpFactorization
import Mathlib.Probability.Distributions.Uniform

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ENNReal
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica

def rootFiniteUniformLaw (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] : Measure A :=
  (PMF.uniformOfFintype A).toMeasure

instance rootFiniteUniformLaw_probability (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] :
    IsProbabilityMeasure (rootFiniteUniformLaw A) := by
  unfold rootFiniteUniformLaw
  infer_instance

@[simp] theorem rootFiniteUniformLaw_singleton {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (a : A) :
    rootFiniteUniformLaw A {a} = (Fintype.card A : ℝ≥0∞)⁻¹ := by
  unfold rootFiniteUniformLaw
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a), PMF.uniformOfFintype_apply]

theorem root_map_finiteUniformLaw_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] (e : A ≃ B) :
    Measure.map e (rootFiniteUniformLaw A) = rootFiniteUniformLaw B := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton b)]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext a
    exact e.eq_symm_apply.symm
  rw [he]
  simp only [rootFiniteUniformLaw_singleton, Fintype.card_congr e]

theorem root_uniform_bool_function_law (K : Type*) [Fintype K] [DecidableEq K] :
    rootFiniteUniformLaw (K → Bool) =
      Measure.infinitePi (fun _ : K => rootFiniteUniformLaw Bool) := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.infinitePi_eq_pi, Measure.pi_singleton]
  simp [ENNReal.inv_pow]

def rootRawCellEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) (e : Fin G.edges) :
    (rootGraphRawFactorShape G dimension).RawCell e ≃
      EdgeSignCoordinate (G := G.toPartiteShape) dimension e where
  toFun x := (x ⟨G.source e, by simp [rootGraphRawFactorShape]⟩,
    x ⟨G.target e, by simp [rootGraphRawFactorShape]⟩)
  invFun p w := if h : w.1 = G.source e then h.symm ▸ p.1 else
    have ht : w.1 = G.target e := by
      have hm := w.2
      simp only [rootGraphRawFactorShape, Finset.mem_insert, Finset.mem_singleton] at hm
      exact hm.resolve_left h
    ht.symm ▸ p.2
  left_inv x := by
    funext w
    rcases w with ⟨v, hv⟩
    dsimp only
    split_ifs with hs
    · cases hs; rfl
    · have ht : v = G.target e := by
        have hm := hv
        simp only [rootGraphRawFactorShape, Finset.mem_insert, Finset.mem_singleton] at hm
        exact hm.resolve_left hs
      cases ht
      rfl
  right_inv p := by
    have hne : G.target e ≠ G.source e := (G.edge_order e).ne'
    simp [hne]

/-- Each typed sign array cell is exactly one occurrence-tagged raw primitive. -/
def rootRawBoolEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    JointEdgeSignSample (G := G.toPartiteShape) dimension ≃
      ((rootGraphRawFactorShape G dimension).RawPrimitiveCoord → Bool) where
  toFun epsilon c := epsilon c.1 (rootRawCellEquiv G dimension c.1 c.2)
  invFun omega e p := omega ⟨e, (rootRawCellEquiv G dimension e).symm p⟩
  left_inv epsilon := by
    funext e p
    simp
  right_inv omega := by
    funext c
    rcases c with ⟨e, p⟩
    simp

def rootScalarSignLaw : Measure ℝ :=
  Measure.map (fun b : Bool => (rademacherSign b : ℝ)) (rootFiniteUniformLaw Bool)

instance rootScalarSignLaw_probability : IsProbabilityMeasure rootScalarSignLaw := by
  unfold rootScalarSignLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def rootTypedToRawPrimitive (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    (rootGraphRawFactorShape G dimension).RawPrimitiveCoord → ℝ :=
  (rootGraphRawFactorShape G dimension).flattenRawSample (rootGraphRawSignSample G dimension epsilon)

theorem root_typed_map_eq_rawPrimitiveLaw (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Measure.map (rootTypedToRawPrimitive G dimension)
      (rootFiniteUniformLaw (JointEdgeSignSample (G := G.toPartiteShape) dimension)) =
      (rootGraphRawFactorShape G dimension).rawPrimitiveLaw (fun _ => rootScalarSignLaw) := by
  classical
  let S := rootGraphRawFactorShape G dimension
  let sign : (S.RawPrimitiveCoord → Bool) → S.RawPrimitiveCoord → ℝ :=
    fun omega c => (rademacherSign (omega c) : ℝ)
  have hmap : rootTypedToRawPrimitive G dimension = sign ∘ rootRawBoolEquiv G dimension := rfl
  rw [hmap, ← Measure.map_map (measurable_of_finite sign) (measurable_of_finite _),
    root_map_finiteUniformLaw_equiv, root_uniform_bool_function_law]
  exact Measure.infinitePi_map_pi (fun _ : S.RawPrimitiveCoord => rootFiniteUniformLaw Bool)
    (fun _ => measurable_of_finite (fun b : Bool => (rademacherSign b : ℝ)))

theorem root_integral_finiteUniformLaw_eq_paperMean {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ x, f x ∂rootFiniteUniformLaw A) = paperMean f := by
  classical
  unfold rootFiniteUniformLaw paperMean
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, smul_eq_mul, Finset.sum_mul, mul_comm]

theorem root_typed_mean_norm_eq_raw_integral (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
      ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖) =
      ∫ x, (rootGraphRawFactorShape G dimension).rawNormPrimitive x
        ∂(rootGraphRawFactorShape G dimension).rawPrimitiveLaw (fun _ => rootScalarSignLaw) := by
  rw [← root_typed_map_eq_rawPrimitiveLaw]
  rw [integral_map (measurable_of_finite _).aemeasurable
    (rootGraphRawFactorShape G dimension).measurable_rawNormPrimitive.aestronglyMeasurable]
  rw [root_integral_finiteUniformLaw_eq_paperMean]
  congr 1
  funext epsilon
  simp only [PaperR16.RawFactorShape.rawNormPrimitive, rootTypedToRawPrimitive,
    PaperR16.RawFactorShape.unflatten_flattenRawSample, root_typed_norm_eq_rawOperatorNorm]

theorem root_typed_secondMoment_eq_raw_integral (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
      ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ 2) =
      ∫ x, (rootGraphRawFactorShape G dimension).rawNormPrimitive x ^ 2
        ∂(rootGraphRawFactorShape G dimension).rawPrimitiveLaw (fun _ => rootScalarSignLaw) := by
  rw [← root_typed_map_eq_rawPrimitiveLaw]
  rw [integral_map (measurable_of_finite _).aemeasurable
    ((rootGraphRawFactorShape G dimension).measurable_rawNormPrimitive.pow_const 2).aestronglyMeasurable]
  rw [root_integral_finiteUniformLaw_eq_paperMean]
  congr 1
  funext epsilon
  simp only [PaperR16.RawFactorShape.rawNormPrimitive, rootTypedToRawPrimitive,
    PaperR16.RawFactorShape.unflatten_flattenRawSample, root_typed_norm_eq_rawOperatorNorm]

/-- Exact second-moment factorization for the existing typed graph matrix,
under its original finite uniform joint edge-sign sample. -/
theorem root_typed_secondMoment_factorization (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    let S := rootGraphRawFactorShape G dimension
    paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
      ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ 2) =
      S.canonicalPreprocessedShape.unusedScalar ^ 2 *
        ((∫ x, ‖S.coreMatrixFromBlock x‖ ^ 2 ∂S.oneBlockLaw (fun _ => rootScalarSignLaw) (Sum.inl ())) *
          ∏ j : S.DetachedComponent,
            ∫ x, |S.detachedScalarFromBlock j x| ^ 2 ∂S.oneBlockLaw (fun _ => rootScalarSignLaw) (Sum.inr j)) := by
  dsimp only
  rw [root_typed_secondMoment_eq_raw_integral]
  simpa only [Real.rpow_natCast] using
    (rootGraphRawFactorShape G dimension).integral_rawNormPrimitive_rpow (fun _ => rootScalarSignLaw) (2 : ℕ)

#print axioms rootRawCellEquiv
#print axioms rootRawBoolEquiv
#print axioms root_typed_map_eq_rawPrimitiveLaw
#print axioms root_typed_mean_norm_eq_raw_integral
#print axioms root_typed_secondMoment_eq_raw_integral
#print axioms root_typed_secondMoment_factorization
end GraphMatrixReplica
