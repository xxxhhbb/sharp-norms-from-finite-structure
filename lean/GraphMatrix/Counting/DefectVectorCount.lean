import GraphMatrix.Counting.BackboneDefectSplit
import Mathlib.Combinatorics.Enumerative.Composition

/-! # C079 exact-defect vector count

The path excesses and individual off-backbone widths form a nonnegative
vector whose entries add to the total defect.  Adding one to every entry
turns that vector into a composition.  This proves the paper's uniform
`2^(delta+r)` count without finite enumeration.  The vector length below
is an arbitrary `k`; the application has `k <= r`.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Nonnegative vectors of fixed length and fixed total defect. -/
abbrev C079DefectVector (k delta : Nat) :=
  {d : Fin k → Nat // (∑ i : Fin k, d i) = delta}

/-- The stars-and-bars record as a composition of `delta+k`. -/
def c079DefectVectorComposition {k delta : Nat}
    (d : C079DefectVector k delta) : Composition (delta + k) where
  blocks := List.ofFn (fun i : Fin k => d.1 i + 1)
  blocks_pos := by
    intro n hn
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
    omega
  blocks_sum := by
    rw [List.sum_ofFn]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, mul_one, d.2]
    simp

/-- The composition retains every coordinate, so its encoding is injective. -/
theorem c079DefectVectorComposition_injective {k delta : Nat} :
    Function.Injective (c079DefectVectorComposition (k := k) (delta := delta)) := by
  intro d e he
  apply Subtype.ext
  funext i
  have hList :
      List.ofFn (fun j : Fin k => d.1 j + 1) =
        List.ofFn (fun j : Fin k => e.1 j + 1) :=
    congrArg Composition.blocks he
  have hFn := List.ofFn_injective hList
  have hCoord := congrFun hFn i
  omega

noncomputable instance c079DefectVectorFintype (k delta : Nat) :
    Fintype (C079DefectVector k delta) := by
  classical
  exact Fintype.ofInjective c079DefectVectorComposition
    c079DefectVectorComposition_injective

/-- The number of vectors with `k` coordinates and total `delta` is at most
`2^(delta+k)`.  This holds also for the empty vector at `k=delta=0`. -/
theorem c079DefectVector_card_le_pow (k delta : Nat) :
    Fintype.card (C079DefectVector k delta) ≤ 2 ^ (delta + k) := by
  calc
    Fintype.card (C079DefectVector k delta) ≤
        Fintype.card (Composition (delta + k)) :=
      Fintype.card_le_of_injective c079DefectVectorComposition
        c079DefectVectorComposition_injective
    _ = 2 ^ ((delta + k) - 1) := composition_card _
    _ ≤ 2 ^ (delta + k) :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat))
        (by omega : (delta + k) - 1 ≤ delta + k)

/-- Paper form when the number of defect coordinates is bounded by the
number of graph roles. -/
theorem c079DefectVector_card_le_role_pow
    (k delta r : Nat) (hk : k ≤ r) :
    Fintype.card (C079DefectVector k delta) ≤ 2 ^ (delta + r) := by
  exact (c079DefectVector_card_le_pow k delta).trans
    (Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat))
      (by omega : delta + k ≤ delta + r))


end GraphMatrixReplica
