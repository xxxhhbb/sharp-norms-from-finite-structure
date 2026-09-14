import R6.U3PathFiberRestriction
import R6.U3SeedEntropyCharge
import R6.U3MengerProfileTransport

/-!
# U3 actual fixed-profile and stratum counts

This module combines the actual path-product injection and actual seed entropy
bound with the existing encoder.  It removes the external `hPath`, `hSeed`,
and `hCount` assumptions from the U3 counting chain.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.C079U3
open C079U2

attribute [local instance] Classical.propDecidable

variable {G : PartiteShape} {p s delta : Nat}

/-- The actual path product, followed by the unconditional canonical path
count and the existing numerical product budget. -/
theorem root_pathFiber_card_le_requested
    (hp : 1 ≤ p) (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (S : DefectFiber G p d) :
    Fintype.card (PathFiber p family d) ≤
      100 ^ (2 * (p + 1) * G.roles) *
        (p + 1) ^ (2 * onDefect p family d) := by
  calc
    Fintype.card (PathFiber p family d) ≤
        ∏ i : Fin s,
          Fintype.card
            (C079PathStateDegreeFiber
              (c079CanonicalPathShape ((family.path i).vertexCount - 1))
              p ((family.path i).vertexCount - 1)
              (pathExcess p family d i)) :=
      actual_pathFiber_card_le_canonicalProduct family d
    _ ≤ ∏ i : Fin s,
          (100 ^ (2 * (p + 1) * (family.path i).vertexCount) *
            (p + 1) ^ (2 * pathExcess p family d i)) := by
      apply Finset.prod_le_prod'
      intro i _
      simpa only [path_vertexCount_sub_one_add_one] using
        c079CanonicalPath_stateFiber_card_le
          ((family.path i).vertexCount - 1) p
          (pathExcess p family d i) hp (pathExcess_le family S i)
    _ ≤ 100 ^ (2 * (p + 1) * G.roles) *
          (p + 1) ^ (2 * onDefect p family d) :=
      product_path_budgets_le family d

/-- Every actual fixed defect profile obeys exactly the ledger budget. -/
theorem root_defectFiber_card_le_fixedProfileBudget
    (hp : 1 ≤ p) (hr : 1 ≤ G.roles) (hCore : G.IsBoundaryCore)
    (menger : G.RightLeftMengerCertificate)
    (d : Fin G.roles → Nat) (S : DefectFiber G p d) :
    Fintype.card (DefectFiber G p d) ≤
      fixedProfileBudget G.roles (p + 1) G.c079ActiveMaximum
        (onDefect p G.maximumRightLeftPathPacking d)
        (offDefect G.maximumRightLeftPathPacking d) := by
  let family := G.maximumRightLeftPathPacking
  let pathBound := 100 ^ (2 * (p + 1) * G.roles) *
    (p + 1) ^ (2 * onDefect p family d)
  let seedBound := 2 ^ (G.roles * (p + 1)) * (p + 1) ^
    (G.c079ActiveMaximum * (p + 1) + G.roles * onDefect p family d +
      3 * G.roles ^ 2 * offDefect family d)
  have hOpt : G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber :=
    G.rightLeftOptima_eq_of_mengerCertificate menger
  have hPath : Fintype.card (PathFiber p family d) ≤ pathBound :=
    root_pathFiber_card_le_requested hp family d S
  have hSeed : ∀ (B : PathFiber p family d)
      (forward : ForwardCode (Fin G.roles) (p + 1)
        (3 * G.roles * offDefect family d)),
      Fintype.card (SeedFiber B forward) ≤ seedBound := by
    intro B forward
    exact root_seedFiber_card_le_requested hCore hOpt B forward
  have h := actual_fiber_card_le G p d
    (G.roleCovered_of_isBoundaryCore hCore) hr pathBound seedBound hPath hSeed
  simpa only [family, pathBound, seedBound, fixedProfileBudget] using h

/-- Empty fixed fibers are zero, so the same budget holds for every profile. -/
theorem root_defectFiber_card_le_fixedProfileBudget_all
    (hp : 1 ≤ p) (hr : 1 ≤ G.roles) (hCore : G.IsBoundaryCore)
    (menger : G.RightLeftMengerCertificate) (d : Fin G.roles → Nat) :
    Fintype.card (DefectFiber G p d) ≤
      fixedProfileBudget G.roles (p + 1) G.c079ActiveMaximum
        (onDefect p G.maximumRightLeftPathPacking d)
        (offDefect G.maximumRightLeftPathPacking d) := by
  classical
  by_cases h : Nonempty (DefectFiber G p d)
  · obtain ⟨S⟩ := h
    exact root_defectFiber_card_le_fixedProfileBudget hp hr hCore menger d S
  · letI : IsEmpty (DefectFiber G p d) := not_nonempty_iff.mp h
    simp

/-- Summing actual fiber cards over all profiles equals summing over the
realizable subtype; the complementary fibers are definitionally empty. -/
theorem root_sum_defectFiber_cards_eq_sum_realizable
    (G : PartiteShape) (p s delta : Nat) :
    (∑ d : StratumProfile G p s delta,
        Fintype.card (DefectFiber G p d.1)) =
      ∑ d : RealizableProfile G p s delta,
        Fintype.card (DefectFiber G p d.1.1) := by
  classical
  let profile := StratumProfile G p s delta
  let good : profile → Prop := fun d => Nonempty (DefectFiber G p d.1)
  let weight : profile → Nat := fun d => Fintype.card (DefectFiber G p d.1)
  have hEmpty : (∑ d : {d : profile // ¬ good d}, weight d.1) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    haveI : IsEmpty (DefectFiber G p d.1.1) := not_nonempty_iff.mp d.2
    simp [weight]
  have hSplit := Fintype.sum_subtype_add_sum_subtype good weight
  have hGood : (∑ d : {d : profile // good d}, weight d.1) =
      ∑ d : profile, weight d := by
    simpa only [hEmpty, add_zero] using hSplit
  exact hGood.symm

/-- Natural-indexed exact U3 coefficient count, with no external count
certificate. -/
theorem root_actual_coefficientNat_le_requested
    (G : PartiteShape) (p : Nat) (hp : 1 ≤ p) (hr : 1 ≤ G.roles)
    (hCore : G.IsBoundaryCore) (menger : G.RightLeftMengerCertificate)
    (delta : Nat) :
    c079DefectCoefficientNat G p G.rightLeftSeparatorNumber delta ≤
      c079C G.roles ^ (2 * (p + 1)) *
        (p + 1) ^
          (G.c079ActiveMaximum * (p + 1) + c079K G.roles * delta) := by
  let family := G.maximumRightLeftPathPacking
  rw [actual_coefficientNat_eq_sum_profiles G p delta
    (G.roleCovered_of_isBoundaryCore hCore) menger]
  rw [root_sum_defectFiber_cards_eq_sum_realizable]
  calc
    (∑ d : RealizableProfile G p G.rightLeftPathPackingNumber delta,
        Fintype.card (DefectFiber G p d.1.1)) ≤
      ∑ d : RealizableProfile G p G.rightLeftPathPackingNumber delta,
        fixedProfileBudget G.roles (p + 1) G.c079ActiveMaximum
          (onDefect p family d.1.1) (offDefect family d.1.1) := by
      apply Finset.sum_le_sum
      intro d _
      exact root_defectFiber_card_le_fixedProfileBudget hp hr hCore menger d.1.1
        (Classical.choice d.2)
    _ ≤ c079C G.roles ^ (2 * (p + 1)) *
        (p + 1) ^
          (G.c079ActiveMaximum * (p + 1) + c079K G.roles * delta) :=
      sum_realizable_profile_budgets_le_requested G p
        G.rightLeftPathPackingNumber delta G.c079ActiveMaximum
        (G.roleCovered_of_isBoundaryCore hCore) family hr

/-- Finite-indexed form used by the existing R16 wrapper. -/
theorem root_actual_coefficient_le_requested
    (G : PartiteShape) (p : Nat) (hp : 1 ≤ p) (hr : 1 ≤ G.roles)
    (hCore : G.IsBoundaryCore) (menger : G.RightLeftMengerCertificate)
    (delta : Fin (c079BlockTarget G p G.rightLeftSeparatorNumber + 1)) :
    c079DefectCoefficient G p G.rightLeftSeparatorNumber delta ≤
      c079C G.roles ^ (2 * (p + 1)) *
        (p + 1) ^
          (G.c079ActiveMaximum * (p + 1) + c079K G.roles * delta.1) :=
  root_actual_coefficientNat_le_requested G p hp hr hCore menger delta.1

#print axioms root_pathFiber_card_le_requested
#print axioms root_defectFiber_card_le_fixedProfileBudget
#print axioms root_sum_defectFiber_cards_eq_sum_realizable
#print axioms root_actual_coefficientNat_le_requested
#print axioms root_actual_coefficient_le_requested

end GraphMatrixReplica.C079U3
