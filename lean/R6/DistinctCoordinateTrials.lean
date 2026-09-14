import Mathlib

/-!
The finite diagonal packing used before conditional separator trials.
The hypothesis `N ≤ size z` is the precise quantitative input from balanced
role classes; it does not assert independence of the associated random arrays.
-/

namespace PaperR16LowerSync

variable {S : Type*} (size : S → ℕ) (N : ℕ)

def diagonalTrial (hN : ∀ z : S, N ≤ size z) (i : Fin N) (z : S) : Fin (size z) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (hN z)⟩

theorem diagonalTrial_coordinate_injective (hN : ∀ z : S, N ≤ size z) (z : S) :
    Function.Injective (fun i : Fin N => diagonalTrial size N hN i z) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Fin (size z) => x.val) hij

theorem diagonalTrial_coordinate_disjoint (hN : ∀ z : S, N ≤ size z)
    (z : S) {i j : Fin N} (hij : i ≠ j) :
    diagonalTrial size N hN i z ≠ diagonalTrial size N hN j z := by
  intro hcoord
  exact hij (diagonalTrial_coordinate_injective size N hN z hcoord)

theorem diagonalTrial_injective [Nonempty S] (hN : ∀ z : S, N ≤ size z) :
    Function.Injective (diagonalTrial size N hN) := by
  intro i j hij
  exact diagonalTrial_coordinate_injective size N hN (Classical.choice inferInstance)
    (congrFun hij (Classical.choice inferInstance))

#print axioms PaperR16LowerSync.diagonalTrial_coordinate_injective
#print axioms PaperR16LowerSync.diagonalTrial_coordinate_disjoint
#print axioms PaperR16LowerSync.diagonalTrial_injective

end PaperR16LowerSync
