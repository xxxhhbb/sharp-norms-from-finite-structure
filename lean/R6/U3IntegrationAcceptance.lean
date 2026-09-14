import R6.U3ActualCountIntegration

/-!
U3 integration/acceptance entry point.

This file is the proved U3 acceptance entry point.  The actual PathFiber
restriction injection and actual SeedFiber active-component entropy bound are
assembled into the original finite and natural coefficient statements.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.C079U3
open C079U2
attribute [local instance] Classical.propDecidable

/-- Exact finite-indexed target requested by U3, including only the legal
original hypotheses.  This is a target proposition, not a proof. -/
def U3ExactStratumAcceptance : Prop :=
  ∀ (G : PartiteShape) (p : ℕ),
    1 ≤ p →
    1 ≤ G.roles →
    G.IsBoundaryCore →
    G.RightLeftMengerCertificate →
    ∀ delta : Fin (c079BlockTarget G p G.rightLeftSeparatorNumber + 1),
      c079DefectCoefficient G p G.rightLeftSeparatorNumber delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (G.c079ActiveMaximum * (p + 1) + c079K G.roles * delta.1)

/-- Natural-defect version after the existing finite-to-natural closure. -/
def U3NaturalAcceptance : Prop :=
  ∀ (G : PartiteShape) (p : ℕ),
    1 ≤ p →
    1 ≤ G.roles →
    G.IsBoundaryCore →
    G.RightLeftMengerCertificate →
    ∀ delta : ℕ,
      c079DefectCoefficientNat G p G.rightLeftSeparatorNumber delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (G.c079ActiveMaximum * (p + 1) + c079K G.roles * delta)

/-- First missing Lean gate.  It has no boundary-core, Menger, or positivity
hypothesis; those are not needed for the restriction map itself. -/
def U3PathFiberCanonicalProductGate : Prop :=
  ∀ (G : PartiteShape) (p s : ℕ)
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ),
    Fintype.card (PathFiber p family d) ≤
      ∏ i : Fin s,
        Fintype.card
          (C079PathStateDegreeFiber
            (c079CanonicalPathShape ((family.path i).vertexCount - 1))
            p ((family.path i).vertexCount - 1)
            (pathExcess p family d i))

/-! ## Proved acceptance theorems -/

/-- The geometric PathFiber product gate is now an actual theorem. -/
theorem u3PathFiberCanonicalProductGate : U3PathFiberCanonicalProductGate := by
  intro G p s family d
  exact actual_pathFiber_card_le_canonicalProduct family d

/-- Exact finite-indexed U3 coefficient theorem with only the legal original
hypotheses. -/
theorem u3ExactStratumAcceptance : U3ExactStratumAcceptance := by
  intro G p hp hr hCore menger delta
  exact root_actual_coefficient_le_requested G p hp hr hCore menger delta

/-- Natural-defect U3 coefficient theorem. -/
theorem u3NaturalAcceptance : U3NaturalAcceptance := by
  intro G p hp hr hCore menger delta
  exact root_actual_coefficientNat_le_requested G p hp hr hCore menger delta

/-! ## Core supplied declarations -/

#check GraphMatrixReplica.C079U3.stratumProfileEquiv
#print GraphMatrixReplica.C079U3.stratumProfileEquiv
#print axioms GraphMatrixReplica.C079U3.stratumProfileEquiv

#check GraphMatrixReplica.C079U3.coefficient_eq_sum_profiles
#print GraphMatrixReplica.C079U3.coefficient_eq_sum_profiles
#print axioms GraphMatrixReplica.C079U3.coefficient_eq_sum_profiles

#check GraphMatrixReplica.C079U3.pathExcess_le
#print GraphMatrixReplica.C079U3.pathExcess_le
#print axioms GraphMatrixReplica.C079U3.pathExcess_le

#check GraphMatrixReplica.C079U3.product_path_budgets_le
#print GraphMatrixReplica.C079U3.product_path_budgets_le
#print axioms GraphMatrixReplica.C079U3.product_path_budgets_le

#check GraphMatrixReplica.C079U3.seedFiber_predicate_iff
#print GraphMatrixReplica.C079U3.seedFiber_predicate_iff
#print axioms GraphMatrixReplica.C079U3.seedFiber_predicate_iff

#check GraphMatrixReplica.C079U3.freeSeedRestriction_injective
#print GraphMatrixReplica.C079U3.freeSeedRestriction_injective
#print axioms GraphMatrixReplica.C079U3.freeSeedRestriction_injective

#check GraphMatrixReplica.C079U3.forwardLoss_le
#print GraphMatrixReplica.C079U3.forwardLoss_le
#print axioms GraphMatrixReplica.C079U3.forwardLoss_le

#check GraphMatrixReplica.C079U3.profileBudget_le_requested_at_lean_order
#print GraphMatrixReplica.C079U3.profileBudget_le_requested_at_lean_order
#print axioms GraphMatrixReplica.C079U3.profileBudget_le_requested_at_lean_order

#check GraphMatrixReplica.C079U3.sum_realizable_profile_budgets_le_requested
#print GraphMatrixReplica.C079U3.sum_realizable_profile_budgets_le_requested
#print axioms GraphMatrixReplica.C079U3.sum_realizable_profile_budgets_le_requested

#check GraphMatrixReplica.C079U3.actual_coefficient_eq_sum_profiles_of_boundaryCore
#print GraphMatrixReplica.C079U3.actual_coefficient_eq_sum_profiles_of_boundaryCore
#print axioms GraphMatrixReplica.C079U3.actual_coefficient_eq_sum_profiles_of_boundaryCore

/-! ## Exact target declarations and existing downstream wrapper -/

#check GraphMatrixReplica.C079U3.U3ExactStratumAcceptance
#print GraphMatrixReplica.C079U3.U3ExactStratumAcceptance

#check GraphMatrixReplica.C079U3.U3NaturalAcceptance
#print GraphMatrixReplica.C079U3.U3NaturalAcceptance

#check GraphMatrixReplica.C079U3.U3PathFiberCanonicalProductGate
#print GraphMatrixReplica.C079U3.U3PathFiberCanonicalProductGate

#check GraphMatrixReplica.C079U3.u3PathFiberCanonicalProductGate
#print axioms GraphMatrixReplica.C079U3.u3PathFiberCanonicalProductGate

#check GraphMatrixReplica.C079U3.u3ExactStratumAcceptance
#print axioms GraphMatrixReplica.C079U3.u3ExactStratumAcceptance

#check GraphMatrixReplica.C079U3.u3NaturalAcceptance
#print axioms GraphMatrixReplica.C079U3.u3NaturalAcceptance

#check GraphMatrixReplica.c079_r16_count_of_exactStratumCertificate
#print GraphMatrixReplica.c079_r16_count_of_exactStratumCertificate
#print axioms GraphMatrixReplica.c079_r16_count_of_exactStratumCertificate

/-! ## Acceptance examples for the portions that are actually formalized -/

/-- C: actual coefficient/profile decomposition, using only legal U3 inputs. -/
theorem accept_profile_decomposition (G : PartiteShape) (p : ℕ)
    (hCore : G.IsBoundaryCore)
    (menger : G.RightLeftMengerCertificate)
    (delta : Fin (c079BlockTarget G p G.rightLeftSeparatorNumber + 1)) :
    c079DefectCoefficient G p G.rightLeftSeparatorNumber delta =
      ∑ d : StratumProfile G p G.rightLeftPathPackingNumber delta.1,
        Fintype.card (DefectFiber G p d.1) := by
  exact actual_coefficient_eq_sum_profiles_of_boundaryCore G p hCore menger delta

/-- A numerical sub-result: actual-path canonical budgets fit the global
path constant/excess budget.  This is intentionally not a PathFiber-cardinality
claim. -/
theorem accept_path_budget (G : PartiteShape) (p s : ℕ)
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) :
    (∏ i : Fin s,
      (100 ^ (2 * (p + 1) * (family.path i).vertexCount) *
        (p + 1) ^ (2 * pathExcess p family d i))) ≤
      100 ^ (2 * (p + 1) * G.roles) *
        (p + 1) ^ (2 * onDefect p family d) := by
  exact product_path_budgets_le family d

/-- B numerical sub-result: every type-correct forward word obeys the actual
block-loss budget; no encoder-image assumption is supplied. -/
theorem accept_forward_loss (G : PartiteShape) (p s : ℕ)
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ)
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1)
      (3 * G.roles * offDefect family d)) :
    forwardLoss B forward ≤ 3 * G.roles * offDefect family d := by
  exact forwardLoss_le B forward

/-- D arithmetic/profile-sum acceptance, using boundary-core only to derive
covered roles and the positive-role hypothesis explicitly. -/
theorem accept_profile_budget_sum (G : PartiteShape) (p : ℕ)
    (hCore : G.IsBoundaryCore) (hr : 1 ≤ G.roles) :
    (∑ d : RealizableProfile G p G.rightLeftPathPackingNumber 0,
      fixedProfileBudget G.roles (p + 1) G.c079ActiveMaximum
        (onDefect p G.maximumRightLeftPathPacking d.1.1)
        (offDefect G.maximumRightLeftPathPacking d.1.1)) ≤
      c079C G.roles ^ (2 * (p + 1)) *
        (p + 1) ^
          (G.c079ActiveMaximum * (p + 1) + c079K G.roles * 0) := by
  exact sum_realizable_profile_budgets_le_requested
    G p G.rightLeftPathPackingNumber 0 G.c079ActiveMaximum
    (G.roleCovered_of_isBoundaryCore hCore)
    G.maximumRightLeftPathPacking hr

end GraphMatrixReplica.C079U3
