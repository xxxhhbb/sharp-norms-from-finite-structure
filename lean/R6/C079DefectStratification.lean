import R6.AdmissibleStatePolynomial
import R6.DisjointPathDegreeBound
import R6.C079UniformCoefficientBound

/-! # Exact C079 defect stratification

For Lean's moment parameter `p`, the actual trace order is `p + 1`.  Given a
separator size `s`, C079's sharp block target is therefore

`(p + 1) * (roles - s) + s`.

This module partitions the finite admissible state space by the exact loss
from that target.  It is purely an indexing theorem: the sharp block cap must
be supplied by the already separate path/Menger chain, while the cardinality
bound for each fiber is the still-open combinatorial content of C079.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- C079's maximal block degree at trace order `p + 1`. -/
def c079BlockTarget (G : PartiteShape) (p s : ℕ) : ℕ :=
  (p + 1) * (G.roles - s) + s

/-- Exact defect of an admissible state relative to the C079 target. -/
def c079StateDefect (G : PartiteShape) (p s : ℕ)
    (T : AdmissiblePartitionState G p) : ℕ :=
  c079BlockTarget G p s - T.toReplicaState.totalBlockCount

/-- The finite fiber of admissible states at one exact C079 defect. -/
abbrev C079DefectStratum (G : PartiteShape) (p s delta : ℕ) :=
  {T : AdmissiblePartitionState G p //
    T.toReplicaState.totalBlockCount + delta = c079BlockTarget G p s}

/-- Under the sharp block cap, every admissible state has an exact defect in
`Fin (target + 1)`, and this gives a lossless stratification equivalence. -/
def c079DefectStratificationEquiv
    (G : PartiteShape) (p s : ℕ)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s) :
    AdmissiblePartitionState G p ≃
      Σ delta : Fin (c079BlockTarget G p s + 1),
        C079DefectStratum G p s delta.1 where
  toFun T :=
    ⟨⟨c079StateDefect G p s T, by
        exact Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩,
      ⟨T, by
        exact Nat.add_sub_of_le (hBlocks T)⟩⟩
  invFun z := z.2.1
  left_inv T := rfl
  right_inv := by
    rintro ⟨delta, ⟨T, hdelta⟩⟩
    have hfin :
        (⟨c079StateDefect G p s T,
            Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩ :
          Fin (c079BlockTarget G p s + 1)) = delta := by
      apply Fin.ext
      unfold c079StateDefect
      have hle :
          T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s := by
        omega
      exact (Nat.sub_eq_iff_eq_add hle).2 (by
        simpa [Nat.add_comm] using hdelta.symm)
    cases hfin
    rfl

/-- Exact all-defect cardinality decomposition.  No coefficient estimate is
hidden here: bounding the individual stratum cardinalities remains precisely
the C079 counting obligation. -/
theorem c079_admissibleState_card_eq_sum_defectStrata
    (G : PartiteShape) (p s : ℕ)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s) :
    Fintype.card (AdmissiblePartitionState G p) =
      ∑ delta : Fin (c079BlockTarget G p s + 1),
        Fintype.card (C079DefectStratum G p s delta.1) := by
  calc
    Fintype.card (AdmissiblePartitionState G p) =
        Fintype.card
          (Σ delta : Fin (c079BlockTarget G p s + 1),
            C079DefectStratum G p s delta.1) :=
      Fintype.card_congr (c079DefectStratificationEquiv G p s hBlocks)
    _ = ∑ delta : Fin (c079BlockTarget G p s + 1),
          Fintype.card (C079DefectStratum G p s delta.1) :=
      Fintype.card_sigma

/-- The explicit coefficient function appearing in the C079 all-defect
generating sum. -/
def c079DefectCoefficient (G : PartiteShape) (p s : ℕ)
    (delta : Fin (c079BlockTarget G p s + 1)) : ℕ :=
  Fintype.card (C079DefectStratum G p s delta.1)

theorem c079_admissibleState_card_eq_sum_defectCoefficient
    (G : PartiteShape) (p s : ℕ)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s) :
    Fintype.card (AdmissiblePartitionState G p) =
      ∑ delta : Fin (c079BlockTarget G p s + 1),
        c079DefectCoefficient G p s delta := by
  exact c079_admissibleState_card_eq_sum_defectStrata G p s hBlocks

#print axioms c079DefectStratificationEquiv
#print axioms c079_admissibleState_card_eq_sum_defectStrata
#print axioms c079_admissibleState_card_eq_sum_defectCoefficient

end GraphMatrixReplica
