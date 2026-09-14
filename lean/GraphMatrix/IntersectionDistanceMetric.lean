import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Intersection-codimension distance on fixed-rank subspaces

This is the linear-algebra engine cited in C078 for the matching-distance
triangle inequality.  It is independent of the later realization of a perfect
matching as the subspace of vectors constant on its pairs.
-/

noncomputable section

namespace GraphMatrixReplica

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Two intersections through a common middle subspace satisfy the rank
inequality needed for the triangle inequality. -/
theorem finrank_inf_add_finrank_inf_le
    (A B C : Submodule K V) :
    Module.finrank K ↑(A ⊓ B) + Module.finrank K ↑(B ⊓ C) ≤
      Module.finrank K B + Module.finrank K ↑(A ⊓ C) := by
  let X : Submodule K V := A ⊓ B
  let Y : Submodule K V := B ⊓ C
  have hsup : X ⊔ Y ≤ B := by
    apply sup_le
    · exact inf_le_right
    · exact inf_le_left
  have hinf : X ⊓ Y ≤ A ⊓ C := by
    apply le_inf
    · exact le_trans inf_le_left inf_le_left
    · exact le_trans inf_le_right inf_le_right
  calc
    Module.finrank K ↑(A ⊓ B) + Module.finrank K ↑(B ⊓ C) =
        Module.finrank K ↑(X ⊔ Y) + Module.finrank K ↑(X ⊓ Y) := by
      simpa [X, Y] using
        (Submodule.finrank_sup_add_finrank_inf_eq X Y).symm
    _ ≤ Module.finrank K B + Module.finrank K ↑(A ⊓ C) :=
      Nat.add_le_add (Submodule.finrank_mono hsup)
        (Submodule.finrank_mono hinf)

/-- Submodules whose dimension is a prescribed natural number. -/
def FixedRankSubmodule (K V : Type*) [DivisionRing K] [AddCommGroup V]
    [Module K V] (p : ℕ) :=
  {A : Submodule K V // Module.finrank K A = p}

/-- Codimension of the intersection inside either fixed-rank subspace. -/
def fixedRankIntersectionDistance (p : ℕ)
    (A B : FixedRankSubmodule K V p) : ℕ :=
  p - Module.finrank K ↑(A.1 ⊓ B.1)

theorem fixedRankIntersectionDistance_self (p : ℕ)
    (A : FixedRankSubmodule K V p) :
    fixedRankIntersectionDistance p A A = 0 := by
  unfold fixedRankIntersectionDistance
  have h : Module.finrank K ↑(A.1 ⊓ A.1) = p := by
    rw [show (A.1 ⊓ A.1 : Submodule K V) = A.1 by exact inf_idem A.1]
    exact A.2
  omega

theorem fixedRankIntersectionDistance_comm (p : ℕ)
    (A B : FixedRankSubmodule K V p) :
    fixedRankIntersectionDistance p A B =
      fixedRankIntersectionDistance p B A := by
  unfold fixedRankIntersectionDistance
  rw [inf_comm A.1 B.1]

theorem fixedRankIntersectionDistance_eq_zero_iff (p : ℕ)
    (A B : FixedRankSubmodule K V p) :
    fixedRankIntersectionDistance p A B = 0 ↔ A = B := by
  constructor
  · intro hzero
    have hleA : Module.finrank K ↑(A.1 ⊓ B.1) ≤ p := by
      calc
        Module.finrank K ↑(A.1 ⊓ B.1) ≤ Module.finrank K A.1 :=
          Submodule.finrank_mono inf_le_left
        _ = p := A.2
    have hfinrank : Module.finrank K ↑(A.1 ⊓ B.1) = p := by
      unfold fixedRankIntersectionDistance at hzero
      omega
    have hA : A.1 ⊓ B.1 = A.1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (hfinrank.trans A.2.symm)
    have hB : A.1 ⊓ B.1 = B.1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (hfinrank.trans B.2.symm)
    exact Subtype.ext (hA.symm.trans hB)
  · rintro rfl
    exact fixedRankIntersectionDistance_self p A

/-- Triangle inequality for the intersection-codimension distance. -/
theorem fixedRankIntersectionDistance_triangle (p : ℕ)
    (A B C : FixedRankSubmodule K V p) :
    fixedRankIntersectionDistance p A C ≤
      fixedRankIntersectionDistance p A B +
        fixedRankIntersectionDistance p B C := by
  have hAB : Module.finrank K ↑(A.1 ⊓ B.1) ≤ p := by
    calc
      Module.finrank K ↑(A.1 ⊓ B.1) ≤ Module.finrank K A.1 :=
        Submodule.finrank_mono inf_le_left
      _ = p := A.2
  have hBC : Module.finrank K ↑(B.1 ⊓ C.1) ≤ p := by
    calc
      Module.finrank K ↑(B.1 ⊓ C.1) ≤ Module.finrank K B.1 :=
        Submodule.finrank_mono inf_le_left
      _ = p := B.2
  have hAC : Module.finrank K ↑(A.1 ⊓ C.1) ≤ p := by
    calc
      Module.finrank K ↑(A.1 ⊓ C.1) ≤ Module.finrank K A.1 :=
        Submodule.finrank_mono inf_le_left
      _ = p := A.2
  have hcross :
      Module.finrank K ↑(A.1 ⊓ B.1) + Module.finrank K ↑(B.1 ⊓ C.1) ≤
        p + Module.finrank K ↑(A.1 ⊓ C.1) := by
    simpa only [B.2] using
      (finrank_inf_add_finrank_inf_le A.1 B.1 C.1)
  unfold fixedRankIntersectionDistance
  omega


end GraphMatrixReplica
