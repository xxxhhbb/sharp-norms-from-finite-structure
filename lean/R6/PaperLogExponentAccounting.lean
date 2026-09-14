import R6.PaperRpowHalfExponent
import R6.PaperIntermediateFlattening

/-! # Logarithmic half-exponent accounting

This file transports a real half exponent along the combinatorial edge-order
bound.  Any NCK estimate remains an explicit hypothesis; only monotonicity of
`Real.rpow` and the already-proved ordering count are used here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- If `log n ≥ 1`, its real powers are monotone in the exponent.  Both
exponents are the true real half powers, so this covers odd `k` and `f`. -/
theorem log_rpow_half_mono_of_nat_le
    (n k f : ℕ) (hlog : 1 ≤ Real.log (n : ℝ)) (hkf : k ≤ f) :
    Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2) ≤
      Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) := by
  apply Real.rpow_le_rpow_of_exponent_le hlog
  exact div_le_div_of_nonneg_right (by exact_mod_cast hkf) (by norm_num)

/-- Transport an externally supplied numerical bound from `k/2` to `f/2`.
This is the interface used after a future NCK estimate. -/
theorem le_mul_log_rpow_half_of_le_of_nat_le
    (X K : ℝ) (n k f : ℕ) (hK : 0 ≤ K)
    (hlog : 1 ≤ Real.log (n : ℝ)) (hkf : k ≤ f)
    (hX : X ≤ K * Real.rpow (Real.log (n : ℝ)) ((k : ℝ) / 2)) :
    X ≤ K * Real.rpow (Real.log (n : ℝ)) ((f : ℝ) / 2) := by
  exact hX.trans (mul_le_mul_of_nonneg_left
    (log_rpow_half_mono_of_nat_le n k f hlog hkf) hK)

namespace PartiteShape

/-- The combinatorial budget on `k₁+k₂` supplied by the special edge
ordering for a clean path family. -/
def intermediateOrderingBudget (G : PartiteShape) (s : ℕ) : ℕ :=
  s - (G.leftBoundary ∩ G.rightBoundary).card +
    (G.middleRoles.card - G.isolatedMiddleRoles.card)

/-- The existing `k₁+k₂` count, restated using the named ordering budget. -/
theorem BoundaryCleanRightToLeftPaths.pathEdges_add_extraEdges_le_budget
    {G : PartiteShape} {s : ℕ}
    (family : G.BoundaryCleanRightToLeftPaths s)
    (hSaturates : family.SaturatesCommonBoundary) :
    family.pathEdges.card + family.extraEdges.card ≤
      G.intermediateOrderingBudget s := by
  exact family.pathEdges_add_extraEdges_le hSaturates

/-- BLNvH's `k₁+k₂≤f(α)` transports directly to its final logarithmic half
exponent for every parity of the two cardinalities. -/
theorem BoundaryCleanRightToLeftPaths.log_rpow_pathExtra_half_le_budget_half
    {G : PartiteShape} {s : ℕ}
    (family : G.BoundaryCleanRightToLeftPaths s)
    (hSaturates : family.SaturatesCommonBoundary)
    (n : ℕ) (hlog : 1 ≤ Real.log (n : ℝ)) :
    Real.rpow (Real.log (n : ℝ))
        (((family.pathEdges.card + family.extraEdges.card : ℕ) : ℝ) / 2) ≤
      Real.rpow (Real.log (n : ℝ))
        ((G.intermediateOrderingBudget s : ℝ) / 2) := by
  exact log_rpow_half_mono_of_nat_le n
    (family.pathEdges.card + family.extraEdges.card)
    (G.intermediateOrderingBudget s) hlog
    (family.pathEdges_add_extraEdges_le_budget hSaturates)

/-- Since the two selected edge phases are disjoint, the same transport can
be stated using the actual cardinality of `orderingEdges`. -/
theorem BoundaryCleanRightToLeftPaths.log_rpow_orderingEdges_half_le_budget_half
    {G : PartiteShape} {s : ℕ}
    (family : G.BoundaryCleanRightToLeftPaths s)
    (hSaturates : family.SaturatesCommonBoundary)
    (n : ℕ) (hlog : 1 ≤ Real.log (n : ℝ)) :
    Real.rpow (Real.log (n : ℝ))
        ((family.orderingEdges.card : ℝ) / 2) ≤
      Real.rpow (Real.log (n : ℝ))
        ((G.intermediateOrderingBudget s : ℝ) / 2) := by
  apply log_rpow_half_mono_of_nat_le n family.orderingEdges.card
    (G.intermediateOrderingBudget s) hlog
  exact family.card_orderingEdges_le hSaturates

/-- The clean Menger certificate automatically supplies the saturation
hypothesis, and its separator cardinality is the path count in the budget. -/
theorem BoundaryCleanRightLeftMengerCertificate.log_rpow_orderingEdges_half_le_budget_half
    {G : PartiteShape}
    (certificate : G.BoundaryCleanRightLeftMengerCertificate)
    (n : ℕ) (hlog : 1 ≤ Real.log (n : ℝ)) :
    Real.rpow (Real.log (n : ℝ))
        ((certificate.paths.orderingEdges.card : ℝ) / 2) ≤
      Real.rpow (Real.log (n : ℝ))
        ((G.intermediateOrderingBudget certificate.cut.card : ℝ) / 2) := by
  exact certificate.paths.log_rpow_orderingEdges_half_le_budget_half
    certificate.paths_saturateCommonBoundary n hlog

/-- Final transport interface with a numerical NCK bound kept explicit.
The prefactor `K` may contain all constants and non-logarithmic powers. -/
theorem BoundaryCleanRightLeftMengerCertificate.le_mul_log_rpow_budget_half_of_nck
    {G : PartiteShape}
    (certificate : G.BoundaryCleanRightLeftMengerCertificate)
    (X K : ℝ) (n : ℕ) (hK : 0 ≤ K)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hNCK : X ≤ K * Real.rpow (Real.log (n : ℝ))
      ((certificate.paths.orderingEdges.card : ℝ) / 2)) :
    X ≤ K * Real.rpow (Real.log (n : ℝ))
      ((G.intermediateOrderingBudget certificate.cut.card : ℝ) / 2) := by
  exact hNCK.trans (mul_le_mul_of_nonneg_left
    (certificate.log_rpow_orderingEdges_half_le_budget_half n hlog) hK)

#print axioms log_rpow_half_mono_of_nat_le
#print axioms le_mul_log_rpow_half_of_le_of_nat_le
#print axioms BoundaryCleanRightToLeftPaths.pathEdges_add_extraEdges_le_budget
#print axioms BoundaryCleanRightToLeftPaths.log_rpow_pathExtra_half_le_budget_half
#print axioms BoundaryCleanRightToLeftPaths.log_rpow_orderingEdges_half_le_budget_half
#print axioms BoundaryCleanRightLeftMengerCertificate.log_rpow_orderingEdges_half_le_budget_half
#print axioms BoundaryCleanRightLeftMengerCertificate.le_mul_log_rpow_budget_half_of_nck

end PartiteShape
end GraphMatrixReplica
