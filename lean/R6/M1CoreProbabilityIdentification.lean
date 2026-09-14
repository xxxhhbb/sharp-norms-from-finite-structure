import R6.M1CoreMatrixIdentification
import R6.M1GraphRawProbabilityBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory
namespace GraphMatrixReplica

def rootCoreTaggedPrimitiveEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (Σ e : (rootGraphRawFactorShape G dimension).CanonicalCoreOccurrence,
      (rootGraphRawFactorShape G dimension).RawCell e.1) ≃
      (rootGraphRawFactorShape G dimension).CorePrimitiveCoord where
  toFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv p := by rcases p with ⟨⟨e, he⟩, a⟩; rfl
  right_inv p := by rcases p with ⟨⟨e, a⟩, he⟩; rfl

/-- Genuine new-core graph primitive addresses biject with the old canonical core block. -/
def rootCorePrimitiveEquiv (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).RawPrimitiveCoord ≃
      (rootGraphRawFactorShape G dimension).CorePrimitiveCoord :=
  (Equiv.sigmaCongr
    (β₂ := fun e : (rootGraphRawFactorShape G dimension).CanonicalCoreOccurrence =>
      (rootGraphRawFactorShape G dimension).RawCell e.1)
    (rootCoreOccurrenceEquiv G dimension) (rootCoreCellEquiv G dimension)).trans
      (rootCoreTaggedPrimitiveEquiv G dimension)

def rootCoreBlockToPrimitive (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    ((rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) ≃ᵐ
      ((rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).RawPrimitiveCoord → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) (rootCorePrimitiveEquiv G dimension).symm

@[simp] theorem root_coreBlockToPrimitive_apply (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ)
    (p : (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).RawPrimitiveCoord) :
    rootCoreBlockToPrimitive G dimension x p = x (rootCorePrimitiveEquiv G dimension p) := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (rootCorePrimitiveEquiv G dimension).symm x) p = _
  simpa only [Equiv.symm_apply_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ)
      (rootCorePrimitiveEquiv G dimension).symm x (rootCorePrimitiveEquiv G dimension p))

theorem root_core_unflatten_reindexed (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).unflattenRawSample
      (rootCoreBlockToPrimitive G dimension x) = rootCoreRawSampleFromBlock G dimension x := by
  unfold PaperR16.RawFactorShape.unflattenRawSample rootCoreRawSampleFromBlock
  congr 1
  funext e a
  change rootCoreBlockToPrimitive G dimension x ⟨e, a⟩ = _
  rw [root_coreBlockToPrimitive_apply]
  rfl

/-- The core block law becomes the actual new graph primitive law under its
constructed coordinate bijection, with no independence input. -/
theorem root_core_map_blockLaw (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Measure.map (rootCoreBlockToPrimitive G dimension)
      ((rootGraphRawFactorShape G dimension).oneBlockLaw (fun _ => rootScalarSignLaw) (Sum.inl ())) =
      (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).rawPrimitiveLaw
        (fun _ => rootScalarSignLaw) := by
  change Measure.map (rootCoreBlockToPrimitive G dimension)
    (Measure.infinitePi (fun _ : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord => rootScalarSignLaw)) =
    Measure.infinitePi (fun _ :
      (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).RawPrimitiveCoord =>
        rootScalarSignLaw)
  exact Measure.infinitePi_map_piCongrLeft (fun _ => rootScalarSignLaw)
    (rootCorePrimitiveEquiv G dimension).symm

theorem root_core_rawNormPrimitive_reindex (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (x : (rootGraphRawFactorShape G dimension).CorePrimitiveCoord → ℝ) :
    (rootGraphRawFactorShape (rootBoundaryCoreShape G) (rootCoreDimension G dimension)).rawNormPrimitive
      (rootCoreBlockToPrimitive G dimension x) =
      ‖(rootGraphRawFactorShape G dimension).coreMatrixFromBlock x‖ := by
  unfold PaperR16.RawFactorShape.rawNormPrimitive
  rw [root_core_unflatten_reindexed, root_core_rawOperatorNorm_eq_native]

/-- Exact identification of the remaining core factor in the original typed
second moment with the actual finite-sign matrix of the concrete boundary core. -/
theorem root_core_secondIntegral_eq_typedSecondMoment (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (∫ x, ‖(rootGraphRawFactorShape G dimension).coreMatrixFromBlock x‖ ^ 2
      ∂(rootGraphRawFactorShape G dimension).oneBlockLaw (fun _ => rootScalarSignLaw) (Sum.inl ())) =
    paperMean (fun epsilon : JointEdgeSignSample (G := (rootBoundaryCoreShape G).toPartiteShape)
        (rootCoreDimension G dimension) =>
      ‖c027PartiteBoundaryMatrixReal (rootBoundaryCoreShape G) (rootCoreDimension G dimension) epsilon‖ ^ 2) := by
  rw [root_typed_secondMoment_eq_raw_integral]
  rw [← root_core_map_blockLaw]
  rw [integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [root_core_rawNormPrimitive_reindex]

#print axioms rootCorePrimitiveEquiv
#print axioms root_core_unflatten_reindexed
#print axioms root_core_map_blockLaw
#print axioms root_core_secondIntegral_eq_typedSecondMoment
end GraphMatrixReplica
