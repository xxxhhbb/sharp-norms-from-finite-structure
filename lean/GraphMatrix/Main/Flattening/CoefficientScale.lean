import GraphMatrix.Lower.Flattening.Theorems

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica
open Model Model.C2Actual
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency true in
/-- The two proved norm identifications give the explicit scale for the
actual retained-address coefficient, with its native operator-norm instance. -/
theorem main_C2_coefficientScale_eq_explicit (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    actualC2CoefficientScale P S dimension ω = actualC2ExplicitScale P S dimension hdim ω := by
  letI : ∀ v : Fin P.roles, Nonempty (Fin (dimension v)) :=
    fun v => ⟨⟨0, hdim v⟩⟩
  unfold actualC2CoefficientScale actualC2ExplicitScale
  rw [C1C2.retainedAddressCoefficient_norm]
  have h := actualCoefficientNormProof P S dimension hNoIso hMin hdim ω
  convert h using 1
  all_goals congr!

def mainC2DimensionFactor (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) : ℝ :=
  Real.sqrt
    ((Fintype.card (C2.RoleAssign (C1C2.retainedLabel P S (X dimension))
        (C1C2.rows P S \ C1C2.separator P S)) : ℝ) *
     (Fintype.card (C2.RoleAssign (C1C2.retainedLabel P S (X dimension))
        (C1C2.cols P S \ C1C2.separator P S)) : ℝ))

theorem main_C2_dimensionFactor_nonneg (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) : 0 ≤ mainC2DimensionFactor P S dimension := Real.sqrt_nonneg _

/-- Every single genuine separator tuple lower-bounds the coefficient norm;
this directly consumes a simultaneous-witness event without products of maxima. -/
theorem main_C2_coefficientScale_ge_weight (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension)
    (s : CutAssignment (G := P.toPartiteShape) S dimension) :
    mainC2DimensionFactor P S dimension * |actualWeight (G := P.toPartiteShape) S dimension ω s| ≤
      actualC2CoefficientScale P S dimension ω := by
  rw [main_C2_coefficientScale_eq_explicit P S dimension hNoIso hMin hdim ω]
  unfold actualC2ExplicitScale mainC2DimensionFactor
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have h := Finset.le_sup' (fun t : C1C2.SeparatorAssignment P S (X dimension) =>
      |actualWeight (G := P.toPartiteShape) S dimension ω (c1c2ToCutAssignment P S dimension t)|)
    (Finset.mem_univ (cutToC1C2Assignment P S dimension s))
  simpa only [c1c2ToCut_cutToC1C2] using h

theorem main_C2_coefficientScale_ge_of_witness (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hNoIso : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (t : ℝ)
    (hWitness : ∃ s : CutAssignment (G := P.toPartiteShape) S dimension,
      t ≤ |actualWeight (G := P.toPartiteShape) S dimension ω s|) :
    mainC2DimensionFactor P S dimension * t ≤ actualC2CoefficientScale P S dimension ω := by
  obtain ⟨s, hs⟩ := hWitness
  exact (mul_le_mul_of_nonneg_left hs (main_C2_dimensionFactor_nonneg P S dimension)).trans
    (main_C2_coefficientScale_ge_weight P S dimension hNoIso hMin hdim ω s)

end GraphMatrixReplica
