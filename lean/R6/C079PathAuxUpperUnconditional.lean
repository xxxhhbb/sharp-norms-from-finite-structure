import R6.C079IidMomentFromTail
import R6.C079PathProductMomentFromFactor

/-! Unconditional canonical path auxiliary upper-weight sum. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

theorem c079CanonicalPath_auxiliaryUpper_unconditional
    (ell p t : ℕ) :
    (∑ T : C079PathStateDegreeFiber (c079CanonicalPathShape ell) p ell t,
      c079PathAuxiliaryWeight T) ≤
      12 ^ (2 * (p + 1) * ell) *
        (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1) := by
  exact c079CanonicalPath_auxiliaryUpper_of_iidEvenWalkCount ell p t
    (c079_iid_evenWalkCount_bound (p + 1) (by omega))

private theorem c079CanonicalPath_roleCovered (ell : ℕ) :
    ∀ v : Fin (c079CanonicalPathShape ell).roles,
      (c079CanonicalPathShape ell).RoleCovered v := by
  intro v
  change Fin (ell + 1) at v
  induction v using Fin.cases with
  | zero =>
      unfold PartiteShape.RoleCovered
      exact Or.inr (Or.inl (by
        change (0 : Fin (ell + 1)) ∈ ({0} : Finset (Fin (ell + 1)))
        exact Finset.mem_singleton_self _))
  | succ i =>
      unfold PartiteShape.RoleCovered
      exact Or.inl ⟨i, Or.inr (by simp [c079CanonicalPathShape])⟩

theorem c079CanonicalPath_stateFiber_card_le
    (ell p t : ℕ) (hp : 1 ≤ p) (ht : t ≤ ell * p) :
    Fintype.card
      (C079PathStateDegreeFiber (c079CanonicalPathShape ell) p ell t) ≤
      100 ^ (2 * (p + 1) * (ell + 1)) * (p + 1) ^ (2 * t) := by
  exact c079_pathStateDegreeFiber_card_le_of_auxiliary_upper
    (c079CanonicalPathShape ell) p ell t rfl
    (c079CanonicalPath_roleCovered ell) hp ht
    (c079CanonicalPath_auxiliaryUpper_unconditional ell p t)

#print axioms c079CanonicalPath_auxiliaryUpper_unconditional
#print axioms c079CanonicalPath_stateFiber_card_le

end GraphMatrixReplica
end
