import R6.PaperRademacherColorProjectionContraction
import Mathlib.Data.Fintype.Perm

/-! # Slot symmetrization for finite Rademacher chaos

Slot permutations do not change a coupled chaos: all slots read the same
noise field.  For a fully decoupled chaos the same permutation merely
relabels the independent noise copies, so its expected norm is unchanged.
These two facts justify coefficient symmetrization without any hidden
symmetry assumption.

The permutation-sum estimate below costs exactly the number of permutations.
In degree two this gives the honest factor `2`.  It is a symmetrization
estimate, not by itself the missing projection/polarization theorem comparing
the diagonal coupled field with independent copies.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

section GenericChaos

variable {q : ℕ} {ι τ E : Type} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Permute the ordered coordinate slots of every chaos term. -/
def paperSlotPermutedChaosData
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (σ : Equiv.Perm (Fin q)) :
    PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q where
  coordinate t k := D.coordinate t (σ k)
  coefficient := D.coefficient
  squareFree := by
    intro t ht
    exact (D.squareFree t ht).comp σ.injective

/-- A slot permutation is invisible when every slot reads the same noise
field. -/
theorem paperCoupledRademacherChaos_slotPermuted
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (σ : Equiv.Perm (Fin q)) (epsilon : ι → Bool) :
    paperCoupledRademacherChaos (paperSlotPermutedChaosData D σ) epsilon =
      paperCoupledRademacherChaos D epsilon := by
  classical
  unfold paperCoupledRademacherChaos paperCoupledSignMonomial
    paperSlotPermutedChaosData
  apply Finset.sum_congr rfl
  intro t _ht
  congr 1
  exact Equiv.prod_comp σ
    (fun k : Fin q => paperSign (epsilon (D.coordinate t k)))

/-- Relabel independent noise copies by a slot permutation. -/
def paperPermuteDecoupledCopiesEquiv (σ : Equiv.Perm (Fin q)) :
    (Fin q → ι → Bool) ≃ (Fin q → ι → Bool) where
  toFun eta k := eta (σ.symm k)
  invFun eta k := eta (σ k)
  left_inv eta := by
    funext k i
    simp
  right_inv eta := by
    funext k i
    simp

/-- Permuting slots is pointwise equal to inversely relabeling the independent
noise copies. -/
theorem paperFullyDecoupledRademacherChaos_slotPermuted
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (σ : Equiv.Perm (Fin q)) (eta : Fin q → ι → Bool) :
    paperFullyDecoupledRademacherChaos
        (paperSlotPermutedChaosData D σ) eta =
      paperFullyDecoupledRademacherChaos D
        (paperPermuteDecoupledCopiesEquiv (ι := ι) σ eta) := by
  classical
  unfold paperFullyDecoupledRademacherChaos paperSlotPermutedChaosData
  apply Finset.sum_congr rfl
  intro t _ht
  congr 1
  let g : Fin q → ℝ := fun k =>
    paperSign (eta (σ.symm k) (D.coordinate t k))
  have hprod := Equiv.prod_comp σ g
  simpa [g, paperPermuteDecoupledCopiesEquiv] using hprod

/-- Fully decoupled expected norm is invariant under slot permutations. -/
theorem paperMean_norm_fullyDecoupled_slotPermuted
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (σ : Equiv.Perm (Fin q)) :
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos
          (paperSlotPermutedChaosData D σ) eta‖) =
      paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  calc
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos
          (paperSlotPermutedChaosData D σ) eta‖) =
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D
            (paperPermuteDecoupledCopiesEquiv (ι := ι) σ eta)‖) := by
      congr 1
      funext eta
      rw [paperFullyDecoupledRademacherChaos_slotPermuted]
    _ = paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) :=
      paperMean_equiv (paperPermuteDecoupledCopiesEquiv (ι := ι) σ)
        (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖)

/-- The unnormalized sum of all slot-permuted fully decoupled chaoses. -/
def paperPermutationSumDecoupledChaos
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (eta : Fin q → ι → Bool) : E :=
  ∑ σ : Equiv.Perm (Fin q),
    paperFullyDecoupledRademacherChaos
      (paperSlotPermutedChaosData D σ) eta

/-- On the diagonal, permutation symmetrization is exactly multiplication by
`q!`. -/
theorem paperPermutationSumDecoupledChaos_diagonal
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (epsilon : ι → Bool) :
    paperPermutationSumDecoupledChaos D (fun _ => epsilon) =
      (Nat.factorial q) • paperCoupledRademacherChaos D epsilon := by
  classical
  simp [paperPermutationSumDecoupledChaos,
    paperFullyDecoupledChaos_diagonal,
    paperCoupledRademacherChaos_slotPermuted, Fintype.card_perm]

/-- The expected norm of the permutation sum costs at most `q!` times one
fully decoupled expected norm. -/
theorem paperMean_norm_permutationSumDecoupled_le_factorial_mul
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q) :
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperPermutationSumDecoupledChaos D eta‖) ≤
      (Nat.factorial q : ℝ) *
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  calc
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperPermutationSumDecoupledChaos D eta‖) ≤
        paperMean (fun eta : Fin q → ι → Bool =>
          ∑ σ : Equiv.Perm (Fin q),
            ‖paperFullyDecoupledRademacherChaos
              (paperSlotPermutedChaosData D σ) eta‖) := by
      apply paperMean_mono
      intro eta
      exact norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin q),
          paperMean (fun eta : Fin q → ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos
              (paperSlotPermutedChaosData D σ) eta‖) :=
      paperMean_sum _
    _ = ∑ _σ : Equiv.Perm (Fin q),
          paperMean (fun eta : Fin q → ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos D eta‖) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      exact paperMean_norm_fullyDecoupled_slotPermuted D σ
    _ = (Nat.factorial q : ℝ) *
          paperMean (fun eta : Fin q → ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos D eta‖) := by
      simp [Fintype.card_perm]

/-- The degree-two instance of permutation symmetrization has the exact
constant `2`. -/
theorem paperMean_norm_permutationSumDecoupled_degreeTwo_le_two_mul
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 2) :
    paperMean (fun eta : Fin 2 → ι → Bool =>
        ‖paperPermutationSumDecoupledChaos D eta‖) ≤
      2 * paperMean (fun eta : Fin 2 → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  simpa using paperMean_norm_permutationSumDecoupled_le_factorial_mul D

/-- On diagonal noise, the same degree-two symmetrization is exactly twice
the original coupled chaos. -/
theorem paperPermutationSumDecoupled_degreeTwo_diagonal
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 2)
    (epsilon : ι → Bool) :
    paperPermutationSumDecoupledChaos D (fun _ => epsilon) =
      2 • paperCoupledRademacherChaos D epsilon := by
  simpa using paperPermutationSumDecoupledChaos_diagonal D epsilon

end GenericChaos

/-! ## Fixed-orientation paper endpoint -/

/-- Slot permutation leaves the fixed-orientation paper coupled chaos, hence
the existing oriented matrix, pointwise unchanged. -/
theorem paperOrientedCoupledChaos_slotPermuted_eq_matrix
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (σ : Equiv.Perm (Fin G.edges))
    (epsilon : Sym2 (Fin n) → Bool) :
    paperCoupledRademacherChaos
        (paperSlotPermutedChaosData
          (paperOrientedSquareFreeChaosData G n orientation) σ) epsilon =
      paperOrientedGraphMatrix G n orientation
        (paperSym2NoiseToPaper epsilon) := by
  rw [paperCoupledRademacherChaos_slotPermuted]
  exact paperCoupledOrientedChaos_eq_paperOrientedGraphMatrix
    G n orientation epsilon

/-- The slot-symmetrized fully-decoupled fixed-orientation paper chaos has
the general factorial expected-norm bound. -/
theorem paperMean_norm_orientedPermutationSumDecoupled_le_factorial_mul
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperMean (fun eta : Fin G.edges → Sym2 (Fin n) → Bool =>
        ‖paperPermutationSumDecoupledChaos
          (paperOrientedSquareFreeChaosData G n orientation) eta‖) ≤
      (Nat.factorial G.edges : ℝ) *
        paperMean (fun eta : Fin G.edges → Sym2 (Fin n) → Bool =>
          ‖paperFullyDecoupledRademacherChaos
            (paperOrientedSquareFreeChaosData G n orientation) eta‖) :=
  paperMean_norm_permutationSumDecoupled_le_factorial_mul _

#print axioms paperCoupledRademacherChaos_slotPermuted
#print axioms paperFullyDecoupledRademacherChaos_slotPermuted
#print axioms paperMean_norm_fullyDecoupled_slotPermuted
#print axioms paperPermutationSumDecoupledChaos_diagonal
#print axioms paperMean_norm_permutationSumDecoupled_le_factorial_mul
#print axioms paperMean_norm_permutationSumDecoupled_degreeTwo_le_two_mul
#print axioms paperPermutationSumDecoupled_degreeTwo_diagonal
#print axioms paperOrientedCoupledChaos_slotPermuted_eq_matrix
#print axioms paperMean_norm_orientedPermutationSumDecoupled_le_factorial_mul

end GraphMatrixReplica
