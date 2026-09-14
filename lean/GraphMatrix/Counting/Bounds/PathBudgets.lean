import GraphMatrix.Counting.Bounds.RolewiseProfiles
import GraphMatrix.Counting.PathAuxUpperUnconditional

/-!

-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.ReplicaCounting
open ReplicaEncoding

open Classical in
attribute [local instance] propDecidable

variable {G : PartiteShape} {p s : ℕ}

theorem path_vertexCount_pos {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : 0 < path.vertexCount := by
  cases path <;> simp [PartiteShape.EdgePathToLeft.vertexCount]

theorem path_vertexCount_sub_one_add_one {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : path.vertexCount - 1 + 1 = path.vertexCount := by
  have h := path_vertexCount_pos path
  omega

/-- Every actual path occurrence belongs to the actual backbone image. -/
theorem family_vertexAt_mem_backbone
    (family : G.VertexDisjointRightToLeftPaths s)
    (i : Fin s) (o : Fin (family.path i).vertexCount) :
    (family.path i).vertexAt o ∈ family.backboneRoles := by
  exact Finset.mem_image.mpr ⟨⟨i, o⟩, Finset.mem_univ _, rfl⟩

/-- This counts occurrences, not only path names.  No repeated role is lost. -/
theorem family_sum_vertexCount_le_roles
    (family : G.VertexDisjointRightToLeftPaths s) :
    (∑ i : Fin s, (family.path i).vertexCount) ≤ G.roles := by
  have h := Fintype.card_le_of_injective
    family.backboneRoleAt family.vertexAt_injective
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

theorem path_profile_sum_eq_defect
    {d : Fin G.roles → ℕ} (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) (i : Fin s) :
    (∑ o : Fin (family.path i).vertexCount,
      d ((family.path i).vertexAt o)) = (family.path i).vertexDefectSum S.1 := by
  rw [(family.path i).vertexDefectSum_eq_sum_occurrences]
  exact Finset.sum_congr rfl
    (fun o _ => (S.2 ((family.path i).vertexAt o)).symm)

/-- The p baseline on each actual boundary-to-boundary path is derived. -/
theorem path_profile_baseline
    {d : Fin G.roles → ℕ} (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) (i : Fin s) :
    p ≤ ∑ o : Fin (family.path i).vertexCount,
      d ((family.path i).vertexAt o) := by
  rw [path_profile_sum_eq_defect family S i]
  exact S.1.rightToLeftPath_defect_lower_bound
    (family.start i) (family.startRight i) (family.path i)

theorem path_profile_sum_le
    {d : Fin G.roles → ℕ} (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) (i : Fin s) :
    (∑ o : Fin (family.path i).vertexCount,
      d ((family.path i).vertexAt o)) ≤ (family.path i).vertexCount * p := by
  calc
    _ ≤ ∑ _o : Fin (family.path i).vertexCount, p := by
      apply Finset.sum_le_sum
      intro o _
      rw [← S.2 ((family.path i).vertexAt o)]
      exact roleProfile_le S.1 ((family.path i).vertexAt o)
    _ = _ := by simp

/-- The canonical-path range condition t_i ≤ ell_i*p is not an input. -/
theorem pathExcess_le
    {d : Fin G.roles → ℕ} (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) (i : Fin s) :
    pathExcess p family d i ≤ ((family.path i).vertexCount - 1) * p := by
  have hLower := path_profile_baseline family S i
  have hUpper := path_profile_sum_le family S i
  have hLength := path_vertexCount_sub_one_add_one (family.path i)
  have hMul : (family.path i).vertexCount * p =
      ((family.path i).vertexCount - 1) * p + p := by
    calc
      (family.path i).vertexCount * p =
          ((family.path i).vertexCount - 1 + 1) * p :=
        congrArg (fun n : ℕ => n * p) hLength.symm
      _ = ((family.path i).vertexCount - 1) * p + p := by ring
  rw [hMul] at hUpper
  unfold pathExcess
  omega

/-- Exact degree bookkeeping, before replacing occurrence count by ell+1. -/
theorem pathExcess_add_baseline
    {d : Fin G.roles → ℕ} (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) (i : Fin s) :
    pathExcess p family d i + p =
      ∑ o : Fin (family.path i).vertexCount,
        d ((family.path i).vertexAt o) := by
  exact Nat.sub_add_cancel (path_profile_baseline family S i)

/-- Product of the canonical numerical budgets on the actual paths.
The remaining geometric injection cannot be replaced by this arithmetic. -/
theorem product_path_budgets_le
    (family : G.VertexDisjointRightToLeftPaths s) (d : Fin G.roles → ℕ) :
    (∏ i : Fin s,
      (100 ^ (2 * (p + 1) * (family.path i).vertexCount) *
        (p + 1) ^ (2 * pathExcess p family d i))) ≤
      100 ^ (2 * (p + 1) * G.roles) *
        (p + 1) ^ (2 * onDefect p family d) := by
  rw [Finset.prod_mul_distrib]
  have h100 :
      (∏ i : Fin s, (100 : ℕ) ^ (2 * (p + 1) * (family.path i).vertexCount)) =
        100 ^ (2 * (p + 1) * ∑ i : Fin s, (family.path i).vertexCount) := by
    rw [Finset.prod_pow_eq_pow_sum]
    rw [Finset.mul_sum]
  have hpowers :
      (∏ i : Fin s, (p + 1) ^ (2 * pathExcess p family d i)) =
        (p + 1) ^ (2 * onDefect p family d) := by
    rw [Finset.prod_pow_eq_pow_sum]
    simp only [onDefect, Finset.mul_sum]
  rw [h100, hpowers]
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (by norm_num : 0 < (100 : ℕ))
    (Nat.mul_le_mul_left (2 * (p + 1)) (family_sum_vertexCount_le_roles family))

end GraphMatrixReplica.ReplicaCounting
