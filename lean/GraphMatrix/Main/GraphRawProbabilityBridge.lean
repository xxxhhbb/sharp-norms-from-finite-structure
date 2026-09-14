import GraphMatrix.Main.GraphRawFactorBridge
import GraphMatrix.Probability.Factorization.RealLpFactorization
import Mathlib.Probability.Distributions.Uniform

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ENNReal
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica

def mainFiniteUniformLaw (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] : Measure A :=
  (PMF.uniformOfFintype A).toMeasure

instance mainFiniteUniformLaw_probability (A : Type*) [Fintype A] [Nonempty A] [MeasurableSpace A] :
    IsProbabilityMeasure (mainFiniteUniformLaw A) := by
  unfold mainFiniteUniformLaw
  infer_instance

@[simp] theorem mainFiniteUniformLaw_singleton {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (a : A) :
    mainFiniteUniformLaw A {a} = (Fintype.card A : ℝ≥0∞)⁻¹ := by
  unfold mainFiniteUniformLaw
  rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a), PMF.uniformOfFintype_apply]

theorem main_map_finiteUniformLaw_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] (e : A ≃ B) :
    Measure.map e (mainFiniteUniformLaw A) = mainFiniteUniformLaw B := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton b)]
  have he : e ⁻¹' {b} = {e.symm b} := by
    ext a
    exact e.eq_symm_apply.symm
  rw [he]
  simp only [mainFiniteUniformLaw_singleton, Fintype.card_congr e]

theorem main_uniform_bool_function_law (K : Type*) [Fintype K] [DecidableEq K] :
    mainFiniteUniformLaw (K → Bool) =
      Measure.infinitePi (fun _ : K => mainFiniteUniformLaw Bool) := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.infinitePi_eq_pi, Measure.pi_singleton]
  simp [ENNReal.inv_pow]

def mainRawCellEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) (e : Fin G.edges) :
    (mainGraphRawFactorShape G dimension).RawCell e ≃
      EdgeSignCoordinate (G := G.toPartiteShape) dimension e where
  toFun x := (x ⟨G.source e, by simp [mainGraphRawFactorShape]⟩,
    x ⟨G.target e, by simp [mainGraphRawFactorShape]⟩)
  invFun p w := if h : w.1 = G.source e then h.symm ▸ p.1 else
    have ht : w.1 = G.target e := by
      have hm := w.2
      simp only [mainGraphRawFactorShape, Finset.mem_insert, Finset.mem_singleton] at hm
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
        simp only [mainGraphRawFactorShape, Finset.mem_insert, Finset.mem_singleton] at hm
        exact hm.resolve_left hs
      cases ht
      rfl
  right_inv p := by
    have hne : G.target e ≠ G.source e := (G.edge_order e).ne'
    simp [hne]

/-- Each typed sign array cell is exactly one occurrence-tagged raw primitive. -/
def mainRawBoolEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    JointEdgeSignSample (G := G.toPartiteShape) dimension ≃
      ((mainGraphRawFactorShape G dimension).RawPrimitiveCoord → Bool) where
  toFun epsilon c := epsilon c.1 (mainRawCellEquiv G dimension c.1 c.2)
  invFun omega e p := omega ⟨e, (mainRawCellEquiv G dimension e).symm p⟩
  left_inv epsilon := by
    funext e p
    simp
  right_inv omega := by
    funext c
    rcases c with ⟨e, p⟩
    simp

def mainScalarSignLaw : Measure ℝ :=
  Measure.map (fun b : Bool => (rademacherSign b : ℝ)) (mainFiniteUniformLaw Bool)

instance mainScalarSignLaw_probability : IsProbabilityMeasure mainScalarSignLaw := by
  unfold mainScalarSignLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def mainTypedToRawPrimitive (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    (mainGraphRawFactorShape G dimension).RawPrimitiveCoord → ℝ :=
  (mainGraphRawFactorShape G dimension).flattenRawSample (mainGraphRawSignSample G dimension epsilon)

theorem main_typed_map_eq_rawPrimitiveLaw (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Measure.map (mainTypedToRawPrimitive G dimension)
      (mainFiniteUniformLaw (JointEdgeSignSample (G := G.toPartiteShape) dimension)) =
      (mainGraphRawFactorShape G dimension).rawPrimitiveLaw (fun _ => mainScalarSignLaw) := by
  classical
  let S := mainGraphRawFactorShape G dimension
  let sign : (S.RawPrimitiveCoord → Bool) → S.RawPrimitiveCoord → ℝ :=
    fun omega c => (rademacherSign (omega c) : ℝ)
  have hmap : mainTypedToRawPrimitive G dimension = sign ∘ mainRawBoolEquiv G dimension := rfl
  rw [hmap, ← Measure.map_map (measurable_of_finite sign) (measurable_of_finite _),
    main_map_finiteUniformLaw_equiv, main_uniform_bool_function_law]
  exact Measure.infinitePi_map_pi (fun _ : S.RawPrimitiveCoord => mainFiniteUniformLaw Bool)
    (fun _ => measurable_of_finite (fun b : Bool => (rademacherSign b : ℝ)))

theorem main_integral_finiteUniformLaw_eq_paperMean {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ x, f x ∂mainFiniteUniformLaw A) = paperMean f := by
  classical
  unfold mainFiniteUniformLaw paperMean
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, smul_eq_mul, Finset.sum_mul, mul_comm]

theorem main_typed_mean_norm_eq_raw_integral (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
      ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖) =
      ∫ x, (mainGraphRawFactorShape G dimension).rawNormPrimitive x
        ∂(mainGraphRawFactorShape G dimension).rawPrimitiveLaw (fun _ => mainScalarSignLaw) := by
  rw [← main_typed_map_eq_rawPrimitiveLaw]
  rw [integral_map (measurable_of_finite _).aemeasurable
    (mainGraphRawFactorShape G dimension).measurable_rawNormPrimitive.aestronglyMeasurable]
  rw [main_integral_finiteUniformLaw_eq_paperMean]
  congr 1
  funext epsilon
  simp only [Model.RawFactorShape.rawNormPrimitive, mainTypedToRawPrimitive,
    Model.RawFactorShape.unflatten_flattenRawSample, main_typed_norm_eq_rawOperatorNorm]

theorem main_typed_secondMoment_eq_raw_integral (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
      ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ 2) =
      ∫ x, (mainGraphRawFactorShape G dimension).rawNormPrimitive x ^ 2
        ∂(mainGraphRawFactorShape G dimension).rawPrimitiveLaw (fun _ => mainScalarSignLaw) := by
  rw [← main_typed_map_eq_rawPrimitiveLaw]
  rw [integral_map (measurable_of_finite _).aemeasurable
    ((mainGraphRawFactorShape G dimension).measurable_rawNormPrimitive.pow_const 2).aestronglyMeasurable]
  rw [main_integral_finiteUniformLaw_eq_paperMean]
  congr 1
  funext epsilon
  simp only [Model.RawFactorShape.rawNormPrimitive, mainTypedToRawPrimitive,
    Model.RawFactorShape.unflatten_flattenRawSample, main_typed_norm_eq_rawOperatorNorm]

/-- Exact second-moment factorization for the existing typed graph matrix,
under its original finite uniform joint edge-sign sample. -/
theorem main_typed_secondMoment_factorization (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    let S := mainGraphRawFactorShape G dimension
    paperMean (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
      ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ 2) =
      S.canonicalPreprocessedShape.unusedScalar ^ 2 *
        ((∫ x, ‖S.coreMatrixFromBlock x‖ ^ 2 ∂S.oneBlockLaw (fun _ => mainScalarSignLaw) (Sum.inl ())) *
          ∏ j : S.DetachedComponent,
            ∫ x, |S.detachedScalarFromBlock j x| ^ 2 ∂S.oneBlockLaw (fun _ => mainScalarSignLaw) (Sum.inr j)) := by
  dsimp only
  rw [main_typed_secondMoment_eq_raw_integral]
  simpa only [Real.rpow_natCast] using
    (mainGraphRawFactorShape G dimension).integral_rawNormPrimitive_rpow (fun _ => mainScalarSignLaw) (2 : ℕ)

end GraphMatrixReplica
