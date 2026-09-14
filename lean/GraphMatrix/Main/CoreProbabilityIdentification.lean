import GraphMatrix.Main.CoreMatrixIdentification
import GraphMatrix.Main.GraphRawProbabilityBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory
namespace GraphMatrixReplica

def mainCoreTaggedPrimitiveEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (Σ e : (mainGraphRawFactorShape G dimension).CanonicalCoreOccurrence,
      (mainGraphRawFactorShape G dimension).RawCell e.1) ≃
      (mainGraphRawFactorShape G dimension).CorePrimitiveCoord where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv p := by rcases p with ⟨⟨e, he⟩, a⟩; rfl
  right_inv p := by rcases p with ⟨⟨e, a⟩, he⟩; rfl

/-- Genuine new-core graph primitive addresses biject with the old canonical core block. -/
def mainCorePrimitiveEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).RawPrimitiveCoord ≃
      (mainGraphRawFactorShape G dimension).CorePrimitiveCoord :=
  (Equiv.sigmaCongr
    (β₂ := fun e : (mainGraphRawFactorShape G dimension).CanonicalCoreOccurrence =>
      (mainGraphRawFactorShape G dimension).RawCell e.1)
    (mainCoreOccurrenceEquiv G dimension) (mainCoreCellEquiv G dimension)).trans
      (mainCoreTaggedPrimitiveEquiv G dimension)

def mainCoreBlockToPrimitive (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    ((mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) ≃ᵐ
      ((mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).RawPrimitiveCoord → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (mainCorePrimitiveEquiv G dimension).symm

@[simp] theorem main_coreBlockToPrimitive_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ)
    (p : (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).RawPrimitiveCoord) :
    mainCoreBlockToPrimitive G dimension x p = x (mainCorePrimitiveEquiv G dimension p) := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (mainCorePrimitiveEquiv G dimension).symm x) p = _
  simpa only [Equiv.symm_apply_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ)
      (mainCorePrimitiveEquiv G dimension).symm x (mainCorePrimitiveEquiv G dimension p))

theorem main_core_unflatten_reindexed (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).unflattenRawSample
      (mainCoreBlockToPrimitive G dimension x) = mainCoreRawSampleFromBlock G dimension x := by
  unfold Model.RawFactorShape.unflattenRawSample mainCoreRawSampleFromBlock
  congr 1
  funext e a
  change mainCoreBlockToPrimitive G dimension x ⟨e, a⟩ = _
  rw [main_coreBlockToPrimitive_apply]
  rfl

/-- The core block law becomes the actual new graph primitive law under its
constructed coordinate bijection, with no independence input. -/
theorem main_core_map_blockLaw (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Measure.map (mainCoreBlockToPrimitive G dimension)
      ((mainGraphRawFactorShape G dimension).oneBlockLaw (fun _ => mainScalarSignLaw) (Sum.inl ())) =
      (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).rawPrimitiveLaw
        (fun _ => mainScalarSignLaw) := by
  change Measure.map (mainCoreBlockToPrimitive G dimension)
    (Measure.infinitePi (fun _ : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord => mainScalarSignLaw)) =
    Measure.infinitePi (fun _ :
      (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).RawPrimitiveCoord =>
        mainScalarSignLaw)
  exact Measure.infinitePi_map_piCongrLeft (fun _ => mainScalarSignLaw)
    (mainCorePrimitiveEquiv G dimension).symm

theorem main_core_rawNormPrimitive_reindex (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (mainGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (mainGraphRawFactorShape (mainBoundaryCoreShape G) (mainCoreDimension G dimension)).rawNormPrimitive
      (mainCoreBlockToPrimitive G dimension x) =
      ‖(mainGraphRawFactorShape G dimension).coreMatrixFromBlock x‖ := by
  unfold Model.RawFactorShape.rawNormPrimitive
  rw [main_core_unflatten_reindexed, main_core_rawOperatorNorm_eq_native]

/-- Exact identification of the remaining core factor in the original typed
second moment with the actual finite-sign matrix of the concrete boundary core. -/
theorem main_core_secondIntegral_eq_typedSecondMoment (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (∫ x, ‖(mainGraphRawFactorShape G dimension).coreMatrixFromBlock x‖ ^ 2
      ∂(mainGraphRawFactorShape G dimension).oneBlockLaw (fun _ => mainScalarSignLaw) (Sum.inl ())) =
    paperMean (fun epsilon : JointEdgeSignSample (G := (mainBoundaryCoreShape G).toPartiteShape)
        (mainCoreDimension G dimension) =>
      ‖c027PartiteBoundaryMatrixReal (mainBoundaryCoreShape G) (mainCoreDimension G dimension) epsilon‖ ^ 2) := by
  rw [main_typed_secondMoment_eq_raw_integral]
  rw [← main_core_map_blockLaw]
  rw [integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [main_core_rawNormPrimitive_reindex]

end GraphMatrixReplica
