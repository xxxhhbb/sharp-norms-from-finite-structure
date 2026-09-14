import GraphMatrix.Counting.Encoding.ActualEncoder
import GraphMatrix.Counting.ForwardNormalization

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.ReplicaEncoding

variable {G : PartiteShape} {s : ℕ}

theorem componentDefect_le (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) (c : G.C079CutComponent family.backboneRoles) :
    componentDefect family d c ≤ offDefect family d := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro y hy
  have h := ((G.mem_c079ComponentRoles_iff family.backboneRoles c y).mp hy).1
  simpa [PartiteShape.VertexDisjointRightToLeftPaths.offBackboneRoles] using h

theorem sum_off_defect (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) :
    (∑ y : OffBackbone family, d y.1) = offDefect family d := by
  classical
  symm
  exact Finset.sum_subtype family.offBackboneRoles
    (fun x => by simp [PartiteShape.VertexDisjointRightToLeftPaths.offBackboneRoles]) d

abbrev ReconstructionFamily (m : ℕ) (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) :=
  (y : OffBackbone family) → ReconstructionCode m
    (2 * componentDefect family d (G.c079OffBackboneComponent family y.1 y.2)) (d y.1)

/-- Exact local radii are retained; the global bound charges each role at
    most twice the total off-backbone defect. -/
theorem card_reconstruction_family_le (m : ℕ) (hm : 0 < m)
    (family : G.VertexDisjointRightToLeftPaths s) (d : Fin G.roles → ℕ) :
    Fintype.card (ReconstructionFamily m family d) ≤
      (4 * m ^ 2) ^ (2 * G.roles * offDefect family d) * m ^ (2 * offDefect family d) := by
  classical
  have hcard : Fintype.card (OffBackbone family) ≤ G.roles := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)
  have hsum : (∑ y : OffBackbone family,
      2 * componentDefect family d (G.c079OffBackboneComponent family y.1 y.2)) ≤
      2 * G.roles * offDefect family d := by
    calc
      _ ≤ ∑ _y : OffBackbone family, 2 * offDefect family d :=
        Finset.sum_le_sum (fun y _ => Nat.mul_le_mul_left 2 (componentDefect_le family d _))
      _ = Fintype.card (OffBackbone family) * (2 * offDefect family d) := by simp
      _ ≤ G.roles * (2 * offDefect family d) := Nat.mul_le_mul_right _ hcard
      _ = _ := by ring
  rw [Fintype.card_pi]
  simp_rw [card_reconstruction_code]
  have hsumd : (∑ y : OffBackbone family, 2 * d y.1) = 2 * offDefect family d := by
    rw [← Finset.mul_sum, sum_off_defect]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hsumd]
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_right
  · have hpos := pow_pos hm 2
    omega
  · exact hsum

/-- The original fixed-base factors and the exponent (10r+2)D are explicit. -/
theorem card_forward_times_reconstruction_le {r m : ℕ}
    (hr : G.roles = r) (hrpos : 0 < r) (hm : 0 < m)
    (family : G.VertexDisjointRightToLeftPaths s) (d : Fin G.roles → ℕ) :
    Fintype.card (ForwardCode (Fin G.roles) m (3 * G.roles * offDefect family d)) *
      Fintype.card (ReconstructionFamily m family d) ≤
      (2 * r) ^ (3 * r * offDefect family d) *
        4 ^ (2 * r * offDefect family d) *
          m ^ ((10 * r + 2) * offDefect family d) := by
  subst r
  have hf := card_forward_code_le (b := 3 * G.roles * offDefect family d)
    (show 0 < G.roles by omega) hm
  have hc := card_reconstruction_family_le m hm family d
  have h := Nat.mul_le_mul hf hc
  rw [c079_forward_and_reconstruction_power_eq] at h
  exact h

end GraphMatrixReplica.ReplicaEncoding
