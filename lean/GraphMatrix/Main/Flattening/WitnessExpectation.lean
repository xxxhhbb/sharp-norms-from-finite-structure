import GraphMatrix.Main.Flattening.MeanAssembly
import GraphMatrix.Main.Flattening.CoefficientScale
import GraphMatrix.HighMomentTailMarkov

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica
open Model Model.C2Actual
attribute [local instance] Classical.propDecidable

theorem main_event_threshold_mul_le_mean {Ω : Type} [Fintype Ω]
    (E : Ω → Prop) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hE : ∀ ω, E ω → c ≤ f ω) :
    c * finiteUniformProbability E ≤ paperMean f := by
  unfold finiteUniformProbability
  rw [← paperMean_const_mul_color]
  apply paperMean_mono
  intro ω
  by_cases h : E ω
  · simpa only [h, if_true, mul_one] using hE ω h
  · simpa only [h, if_false, mul_zero] using hf ω

/-- A single simultaneous separator witness yields the actual typed matrix
mean lower bound with its actual event probability. No independent-maxima
assumption, probability-law assumption or matrix identification is an input. -/
theorem main_C2_witnessProbability_mean_lower (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v) (t : ℝ) :
    (mainC2DimensionFactor P S dimension * t *
        finiteUniformProbability (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
          ∃ s : CutAssignment (G := P.toPartiteShape) S dimension,
            t ≤ |actualWeight (G := P.toPartiteShape) S dimension ω s|)) /
          (Real.sqrt 3 ^ freshCount P S) ≤
      paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
        ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  have h := main_event_threshold_mul_le_mean
    (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
      ∃ s : CutAssignment (G := P.toPartiteShape) S dimension,
        t ≤ |actualWeight (G := P.toPartiteShape) S dimension ω s|)
    (actualC2CoefficientScale P S dimension) (mainC2DimensionFactor P S dimension * t)
    (fun _ => norm_nonneg _)
    (fun ω hω => main_C2_coefficientScale_ge_of_witness P S dimension hNoIso hMin hdim ω t hω)
  convert (div_le_div_of_nonneg_right h (by positivity)).trans
    (main_integrated_C2_lower_div P S dimension hNoIso hMin hdim) using 1 <;> congr!

/-- A concrete probability estimate from is the only probability premise of
this final deterministic expectation adapter. -/
theorem main_C2_mean_lower_of_witnessProbability (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v) (t p : ℝ) (ht : 0 ≤ t)
    (hp : p ≤ finiteUniformProbability
      (fun ω : FrozenSample (G := P.toPartiteShape) S dimension =>
        ∃ s : CutAssignment (G := P.toPartiteShape) S dimension,
          t ≤ |actualWeight (G := P.toPartiteShape) S dimension ω s|)) :
    (mainC2DimensionFactor P S dimension * t * p) / (Real.sqrt 3 ^ freshCount P S) ≤
      paperMean (fun ε : JointEdgeSignSample (G := P.toPartiteShape) dimension =>
        ‖c027PartiteBoundaryMatrixReal P dimension ε‖) := by
  have h := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (main_C2_dimensionFactor_nonneg P S dimension) ht)
  exact (div_le_div_of_nonneg_right h (by positivity)).trans
    (main_C2_witnessProbability_mean_lower P S dimension hNoIso hMin hdim t)

end GraphMatrixReplica
