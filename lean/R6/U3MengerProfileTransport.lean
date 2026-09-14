import R6.U3ProfileBudgetSum
import R6.C079R16CountingTarget

/-!
U3: the internally chosen maximum family is indexed by the PACKING number.
A supplied, actual Menger certificate identifies that number with the
minimum SEPARATOR number.  No definitional equality is presumed.
This module has not been executed in Lean in the return environment.
-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U3
open C079U2

open Classical in
attribute [local instance] propDecidable

/-- Reindex the coefficient, NOT the actual stored maximum path family. -/
theorem actual_coefficientNat_eq_sum_profiles
    (G : PartiteShape) (p delta : ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (menger : G.RightLeftMengerCertificate) :
    c079DefectCoefficientNat G p G.rightLeftSeparatorNumber delta =
      ∑ d : StratumProfile G p G.rightLeftPathPackingNumber delta,
        Fintype.card (DefectFiber G p d.1) := by
  have hOpt := G.rightLeftOptima_eq_of_mengerCertificate menger
  change Fintype.card (C079DefectStratum G p G.rightLeftSeparatorNumber delta) = _
  rw [← hOpt]
  exact stratum_card_eq_sum_profiles hCovered G.maximumRightLeftPathPacking

/-- The exact finite-indexed hCount coefficient has the same decomposition. -/
theorem actual_coefficient_eq_sum_profiles
    (G : PartiteShape) (p : ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (menger : G.RightLeftMengerCertificate)
    (delta : Fin (c079BlockTarget G p G.rightLeftSeparatorNumber + 1)) :
    c079DefectCoefficient G p G.rightLeftSeparatorNumber delta =
      ∑ d : StratumProfile G p G.rightLeftPathPackingNumber delta.1,
        Fintype.card (DefectFiber G p d.1) := by
  exact actual_coefficientNat_eq_sum_profiles G p delta.1 hCovered menger

/-- Covered roles are a proved consequence of the supplied boundary core. -/
theorem actual_coefficient_eq_sum_profiles_of_boundaryCore
    (G : PartiteShape) (p : ℕ) (hCore : G.IsBoundaryCore)
    (menger : G.RightLeftMengerCertificate)
    (delta : Fin (c079BlockTarget G p G.rightLeftSeparatorNumber + 1)) :
    c079DefectCoefficient G p G.rightLeftSeparatorNumber delta =
      ∑ d : StratumProfile G p G.rightLeftPathPackingNumber delta.1,
        Fintype.card (DefectFiber G p d.1) := by
  exact actual_coefficient_eq_sum_profiles G p
    (G.roleCovered_of_isBoundaryCore hCore) menger delta

#print axioms actual_coefficientNat_eq_sum_profiles
#print axioms actual_coefficient_eq_sum_profiles_of_boundaryCore
end GraphMatrixReplica.C079U3
