import GraphMatrix.Counting.Bounds.CoefficientAssembly

/-!
U3 coefficient bound theorems.

This file is the coefficient bound module.  The actual PathFiber
restriction injection and actual SeedFiber active-component entropy bound are
assembled into the original finite and natural coefficient statements.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.ReplicaCounting
open ReplicaEncoding
attribute [local instance] Classical.propDecidable

/-- Exact finite-indexed target requested by U3, including only the legal
original hypotheses.  This is a target proposition, not a proof. -/
def ExactStratumBound : Prop :=
  ∀ (G : PartiteShape) (p : ℕ),
    1 ≤ p →
    1 ≤ G.roles →
    G.IsBoundaryCore →
    G.RightLeftMengerCertificate →
    ∀ delta : Fin (c079BlockTarget G p G.rightLeftSeparatorNumber + 1),
      c079DefectCoefficient G p G.rightLeftSeparatorNumber delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (G.activeComponentMaximum * (p + 1) + c079K G.roles * delta.1)

/-- Natural-defect version after the existing finite-to-natural closure. -/
def NaturalCoefficientBound : Prop :=
  ∀ (G : PartiteShape) (p : ℕ),
    1 ≤ p →
    1 ≤ G.roles →
    G.IsBoundaryCore →
    G.RightLeftMengerCertificate →
    ∀ delta : ℕ,
      c079DefectCoefficientNat G p G.rightLeftSeparatorNumber delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (G.activeComponentMaximum * (p + 1) + c079K G.roles * delta)

/-- Path-fiber product bound. No boundary-core, Menger, or positivity
hypothesis; those are not needed for the restriction map itself. -/
def PathFiberProductBound : Prop :=
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

/-! ## Coefficient bounds -/

/-- The canonical restriction map yields the path-fiber product bound. -/
theorem pathFiberProductBound : PathFiberProductBound := by
  intro G p s family d
  exact actual_pathFiber_card_le_canonicalProduct family d

/-- Exact finite-indexed U3 coefficient theorem with only the legal original
hypotheses. -/
theorem exactStratumBound : ExactStratumBound := by
  intro G p hp hr hCore menger delta
  exact main_actual_coefficient_le_requested G p hp hr hCore menger delta

/-- Natural-defect U3 coefficient theorem. -/
theorem naturalCoefficientBound : NaturalCoefficientBound := by
  intro G p hp hr hCore menger delta
  exact main_actual_coefficientNat_le_requested G p hp hr hCore menger delta

/-! ## Profile decomposition and budgets -/

/-- C: actual coefficient/profile decomposition, using only legal U3 inputs. -/
theorem coefficient_profile_decomposition (G : PartiteShape) (p : ℕ)
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
theorem path_product_budget_bound (G : PartiteShape) (p s : ℕ)
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
theorem forward_loss_bound (G : PartiteShape) (p s : ℕ)
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ)
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1)
      (3 * G.roles * offDefect family d)) :
    forwardLoss B forward ≤ 3 * G.roles * offDefect family d := by
  exact forwardLoss_le B forward

/-- Arithmetic profile-sum bound, using boundary-core only to derive
covered roles and the positive-role hypothesis explicitly. -/
theorem profile_budget_sum_bound (G : PartiteShape) (p : ℕ)
    (hCore : G.IsBoundaryCore) (hr : 1 ≤ G.roles) :
    (∑ d : RealizableProfile G p G.rightLeftPathPackingNumber 0,
      fixedProfileBudget G.roles (p + 1) G.activeComponentMaximum
        (onDefect p G.maximumRightLeftPathPacking d.1.1)
        (offDefect G.maximumRightLeftPathPacking d.1.1)) ≤
      c079C G.roles ^ (2 * (p + 1)) *
        (p + 1) ^
          (G.activeComponentMaximum * (p + 1) + c079K G.roles * 0) := by
  exact sum_realizable_profile_budgets_le_requested
    G p G.rightLeftPathPackingNumber 0 G.activeComponentMaximum
    (G.roleCovered_of_isBoundaryCore hCore)
    G.maximumRightLeftPathPacking hr

end GraphMatrixReplica.ReplicaCounting
