import GraphMatrix.Counting.Bounds.ExponentLedger

/-!

-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.ReplicaCounting
open ReplicaEncoding

open Classical in
attribute [local instance] propDecidable

/-- The common cap is independent of a profile's off-backbone defect D. -/
def uniformProfileBudget (r m a delta : ℕ) : ℕ :=
  (100 ^ (2 * m * r) * 2 ^ (r * m) *
    (2 * r) ^ (4 * r ^ 2 * m) * 4 ^ (2 * r ^ 2 * m)) *
      m ^ (a * m + c079K r * delta)

theorem fixedProfileBudget_le_uniform
    (r m a delta deltaOn D : ℕ) (hr : 1 ≤ r) (hm : 0 < m)
    (hD : D ≤ r * m) (hSplit : delta = deltaOn + D) :
    fixedProfileBudget r m a deltaOn D ≤ uniformProfileBudget r m a delta := by
  rw [fixedProfileBudget_eq]
  have h1 : 3 * r * D ≤ 4 * r ^ 2 * m := by
    have h := Nat.mul_le_mul_left (3 * r) hD
    nlinarith
  have h2 : 2 * r * D ≤ 2 * r ^ 2 * m := by
    have h := Nat.mul_le_mul_left (2 * r) hD
    nlinarith
  have hk : c079K r = 3 * r ^ 2 + 10 * r + 2 := by
    simp [c079K, show r ≠ 0 by omega]
  have hExp : a * m + (r + 2) * deltaOn +
      (3 * r ^ 2 + 10 * r + 2) * D ≤ a * m + c079K r * delta := by
    rw [← hk]
    exact c079_complete_exponent_bookkeeping_of_split r m a delta deltaOn D hr hSplit
  unfold uniformProfileBudget
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul
      (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (show 0 < 2 * r by omega) h1))
      (Nat.pow_le_pow_right (by norm_num : 0 < (4 : ℕ)) h2)
  · exact Nat.pow_le_pow_right hm hExp

theorem profileCount_mul_uniformBudget (r m a delta : ℕ) :
    2 ^ (r * m) * uniformProfileBudget r m a delta =
      c079C r ^ (2 * m) * m ^ (a * m + c079K r * delta) := by
  calc
    _ = (2 ^ (2 * r * m) * 100 ^ (2 * m * r) *
        (2 * r) ^ (4 * r ^ 2 * m) * 4 ^ (2 * r ^ 2 * m)) *
          m ^ (a * m + c079K r * delta) := by
      unfold uniformProfileBudget
      rw [show 2 * r * m = r * m + r * m by ring, pow_add]
      ring
    _ = _ := by rw [baseBudget_at_cap_eq]

/-- Empty fixed-profile fibers do not contribute to the actual coefficient. -/
abbrev RealizableProfile (G : PartiteShape) (p s delta : ℕ) :=
  {d : StratumProfile G p s delta // Nonempty (DefectFiber G p d.1)}

/-- Fully summed numerical budget on the exact, shifted, realizable profile
index.  The unproved PathFiber/SeedFiber cardinality interfaces are not inputs. -/
theorem sum_realizable_profile_budgets_le_requested
    (G : PartiteShape) (p s delta a : ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s) (hr : 1 ≤ G.roles) :
    (∑ d : RealizableProfile G p s delta,
      fixedProfileBudget G.roles (p + 1) a
        (onDefect p family d.1.1) (offDefect family d.1.1)) ≤
      c079C G.roles ^ (2 * (p + 1)) *
        (p + 1) ^ (a * (p + 1) + c079K G.roles * delta) := by
  classical
  by_cases hNonempty : Nonempty (C079DefectStratum G p s delta)
  · have hCard : Fintype.card (RealizableProfile G p s delta) ≤
        2 ^ (G.roles * (p + 1)) := by
      calc
        _ ≤ Fintype.card (StratumProfile G p s delta) :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        _ ≤ _ := profile_card_le_of_nonempty_stratum hCovered family hNonempty
    have hEach (d : RealizableProfile G p s delta) :
        fixedProfileBudget G.roles (p + 1) a
          (onDefect p family d.1.1) (offDefect family d.1.1) ≤
            uniformProfileBudget G.roles (p + 1) a delta := by
      obtain ⟨S⟩ := d.2
      exact fixedProfileBudget_le_uniform G.roles (p + 1) a delta
        (onDefect p family d.1.1) (offDefect family d.1.1)
        hr (Nat.succ_pos _)
        ((offDefect_le_role_mul family S).trans
          (Nat.mul_le_mul_left G.roles (Nat.le_succ p)))
        (defectFiber_excess_split hCovered family d.1.2 S)
    calc
      _ ≤ ∑ _d : RealizableProfile G p s delta,
          uniformProfileBudget G.roles (p + 1) a delta :=
        Finset.sum_le_sum (fun d _ => hEach d)
      _ = Fintype.card (RealizableProfile G p s delta) *
          uniformProfileBudget G.roles (p + 1) a delta := by simp
      _ ≤ 2 ^ (G.roles * (p + 1)) *
          uniformProfileBudget G.roles (p + 1) a delta :=
        Nat.mul_le_mul_right _ hCard
      _ = _ := profileCount_mul_uniformBudget G.roles (p + 1) a delta
  · letI : IsEmpty (RealizableProfile G p s delta) := ⟨fun d => by
      obtain ⟨S⟩ := d.2
      exact hNonempty ⟨⟨asAdmissible S.1,
        profile_gives_stratum hCovered family d.1 S⟩⟩⟩
    simp

end GraphMatrixReplica.ReplicaCounting
