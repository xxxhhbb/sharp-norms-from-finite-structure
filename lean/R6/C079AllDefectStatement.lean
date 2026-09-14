import R6.C079BoundaryCoreScope
import R6.C079ExplicitConstants
import R6.FiniteMengerCertificate

/-! # The R16 C079 statement at every natural-number defect

The earlier coefficient interface uses `Fin (target + 1)` because those are
exactly the potentially nonempty fibers.  R16 states its theorem for every
`delta >= 0`.  This file bridges the two domains without treating a finite
range check as the counting proof.  The exact-fiber estimate remains a visible
input, as does the boundary-core scope of R16.
-/

noncomputable section

namespace GraphMatrixReplica

/-- C079's exact fiber cardinality, now defined for every natural-number
defect rather than only the possible range. -/
def c079DefectCoefficientNat (G : PartiteShape) (p s delta : ℕ) : ℕ :=
  Fintype.card (C079DefectStratum G p s delta)

/-- A defect larger than the sharp block target cannot occur, regardless of
the graph's path structure. -/
theorem c079DefectCoefficientNat_eq_zero_of_target_lt
    (G : PartiteShape) (p s delta : ℕ)
    (h : c079BlockTarget G p s < delta) :
    c079DefectCoefficientNat G p s delta = 0 := by
  classical
  letI : IsEmpty (C079DefectStratum G p s delta) :=
    ⟨fun T => by
      have hT := T.2
      omega⟩
  simp [c079DefectCoefficientNat]

/-- Inside the possible range, the natural-indexed coefficient is precisely
the already-used finite-indexed exact defect coefficient. -/
theorem c079DefectCoefficientNat_eq_coefficient
    (G : PartiteShape) (p s delta : ℕ)
    (h : delta ≤ c079BlockTarget G p s) :
    c079DefectCoefficientNat G p s delta =
      c079DefectCoefficient G p s
        ⟨delta, Nat.lt_succ_of_le h⟩ := by
  rfl

/-- All-natural-defect form of the conditional C079 count.  The hypothesis
is exactly the unproved finite exact-fiber inequality; the extra natural
defects are empty by the preceding theorem. -/
theorem c079_allDefect_bound_of_exactFiberCount
    (G : PartiteShape) (p s a K C : ℕ)
    (hCount : ∀ d : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s d ≤
        C ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1) + K * d.1)) :
    ∀ delta : ℕ,
      c079DefectCoefficientNat G p s delta ≤
        C ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1) + K * delta) := by
  intro delta
  by_cases h : delta ≤ c079BlockTarget G p s
  · rw [c079DefectCoefficientNat_eq_coefficient G p s delta h]
    exact hCount ⟨delta, Nat.lt_succ_of_le h⟩
  · rw [c079DefectCoefficientNat_eq_zero_of_target_lt G p s delta (by omega)]
    exact Nat.zero_le _

/-- R16-shaped specialization: `p` is Lean's moment index, so the paper's
trace order is `p + 1 >= 2`; `s` is witnessed to be a minimum separator.
`hCore` states the no-detached-component scope, but cannot itself supply the
still-open exact count.  The numerical `a` will be instantiated by the
active-minimum-cut statistic once its component definition is formalized. -/
theorem c079_r16_uniform_allDefect_of_countCertificate
    (G : PartiteShape) (p a : ℕ) (_hp : 1 ≤ p)
    (_hCore : G.IsBoundaryCore)
    (menger : G.RightLeftMengerCertificate)
    (hCount : ∀ d : Fin
        (c079BlockTarget G p menger.cut.card + 1),
      c079DefectCoefficient G p menger.cut.card d ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * d.1)) :
    ∀ delta : ℕ,
      c079DefectCoefficientNat G p menger.cut.card delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta) := by
  exact c079_allDefect_bound_of_exactFiberCount
    G p menger.cut.card a (c079K G.roles) (c079C G.roles) hCount

/-- The R16 degenerate role-zero case has exactly one admissible state. -/
theorem c079_emptyShape_admissibleState_card_eq_one
    (G : PartiteShape) (p : ℕ) (hRoles : G.roles = 0) :
    Fintype.card (AdmissiblePartitionState G p) = 1 := by
  classical
  let P : PartitionAssignment G p :=
    fun v => Fin.elim0 (Fin.cast hRoles v)
  let T : AdmissiblePartitionState G p := ⟨P, by
    refine ⟨?_, ?_, ?_⟩
    · intro e
      exact Fin.elim0 (Fin.cast hRoles (G.source e))
    · intro v
      exact Fin.elim0 (Fin.cast hRoles v)
    · intro v
      exact Fin.elim0 (Fin.cast hRoles v)⟩
  have hUnique : ∀ U : AdmissiblePartitionState G p, U = T := by
    intro U
    apply Subtype.ext
    funext v
    exact Fin.elim0 (Fin.cast hRoles v)
  let e : AdmissiblePartitionState G p ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => T
      left_inv := by intro U; exact (hUnique U).symm
      right_inv := by intro x; fin_cases x; rfl }
  simpa using Fintype.card_congr e

/-- In the empty shape, the target degree is zero and every existing state
has zero blocks. -/
theorem c079_emptyShape_target_and_blocks_zero
    (G : PartiteShape) (p : ℕ) (hRoles : G.roles = 0) :
    c079BlockTarget G p 0 = 0 ∧
      ∀ T : AdmissiblePartitionState G p,
        T.toReplicaState.totalBlockCount = 0 := by
  constructor
  · simp [c079BlockTarget, hRoles]
  · intro T
    change (∑ v : Fin G.roles,
      partitionBlockCount (T.toReplicaState.partition v)) = 0
    letI : IsEmpty (Fin G.roles) :=
      ⟨fun v => Fin.elim0 (Fin.cast hRoles v)⟩
    simp

/-- R16's separate `r = 0` coefficient statement, for every defect. -/
theorem c079_emptyShape_coefficient_eq_ite
    (G : PartiteShape) (p delta : ℕ) (hRoles : G.roles = 0) :
    c079DefectCoefficientNat G p 0 delta = if delta = 0 then 1 else 0 := by
  classical
  obtain ⟨hTarget, hBlocks⟩ :=
    c079_emptyShape_target_and_blocks_zero G p hRoles
  by_cases hDelta : delta = 0
  · subst delta
    simp only [ite_true]
    let e : C079DefectStratum G p 0 0 ≃ AdmissiblePartitionState G p :=
      { toFun := fun T => T.1
        invFun := fun T => ⟨T, by rw [hBlocks T, hTarget]⟩
        left_inv := by intro T; cases T; rfl
        right_inv := by intro T; rfl }
    unfold c079DefectCoefficientNat
    rw [Fintype.card_congr e]
    exact c079_emptyShape_admissibleState_card_eq_one G p hRoles
  · simp only [if_neg hDelta]
    exact c079DefectCoefficientNat_eq_zero_of_target_lt
      G p 0 delta (by omega)

#print axioms c079DefectCoefficientNat_eq_zero_of_target_lt
#print axioms c079_allDefect_bound_of_exactFiberCount
#print axioms c079_r16_uniform_allDefect_of_countCertificate
#print axioms c079_emptyShape_coefficient_eq_ite

end GraphMatrixReplica
