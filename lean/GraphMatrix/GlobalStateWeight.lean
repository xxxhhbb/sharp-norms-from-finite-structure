import GraphMatrix.GlobalEqualityState
import Mathlib.Data.Fintype.CardEmbedding

/-! # One global falling-factorial weight for a paper equality state

The original paper model labels every `(role, replica)` occurrence in one
common ambient set.  Consequently a fixed global equality state is counted
by one embedding of its quotient blocks into `Fin n`, hence by one descending
factorial.  There is no product over roles in this module.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A labeling of an arbitrary type has exactly the classes prescribed by a
setoid.  This is the type-generic version of `HasEqualityPattern`. -/
def HasSetoidEqualityPattern {β α : Type*}
    (S : Setoid β) (label : β → α) : Prop :=
  ∀ a b, label a = label b ↔ S.r a b

/-- Label the elements of a setoid through an injection on its quotient
classes. -/
def setoidLabelingOfEmbedding {β α : Type*}
    (S : Setoid β) (e : Quotient S ↪ α) : β → α :=
  fun a => e (Quotient.mk'' a)

theorem setoidLabelingOfEmbedding_hasPattern {β α : Type*}
    (S : Setoid β) (e : Quotient S ↪ α) :
    HasSetoidEqualityPattern S (setoidLabelingOfEmbedding S e) := by
  intro a b
  constructor
  · intro h
    exact Quotient.exact (e.injective h)
  · intro h
    exact congrArg e (Quotient.sound h)

/-- A labeling with exactly the prescribed pattern descends to an embedding
of the quotient classes. -/
def setoidQuotientEmbeddingOfPattern {β α : Type*}
    (S : Setoid β)
    (label : {f : β → α // HasSetoidEqualityPattern S f}) :
    Quotient S ↪ α where
  toFun := Quotient.lift label.1
    (fun _ _ h => (label.2 _ _).2 h)
  inj' := by
    intro q r h
    refine Quotient.inductionOn₂ q r ?_ h
    intro a b hab
    exact Quotient.sound ((label.2 a b).1 hab)

/-- Exact equivalence between labelings with a fixed arbitrary setoid pattern
and injections on its quotient blocks. -/
def setoidPatternLabelingEquivEmbedding {β α : Type*}
    (S : Setoid β) :
    {f : β → α // HasSetoidEqualityPattern S f} ≃
      (Quotient S ↪ α) where
  toFun := setoidQuotientEmbeddingOfPattern S
  invFun := fun e => ⟨setoidLabelingOfEmbedding S e,
    setoidLabelingOfEmbedding_hasPattern S e⟩
  left_inv := by
    intro label
    apply Subtype.ext
    funext a
    rfl
  right_inv := by
    intro e
    apply Function.Embedding.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    rfl

/-- Number of quotient blocks of an arbitrary finite setoid. -/
def finiteSetoidBlockCount {β : Type*} [Fintype β] (S : Setoid β) : ℕ := by
  classical
  exact Fintype.card (Quotient S)

/-- A finite setoid with `b` quotient blocks has exactly `(n)_b` labelings
whose induced equality relation is that setoid. -/
theorem setoidPatternLabelingCount_eq_descFactorial
    {β : Type*} [Fintype β] (S : Setoid β) (n : ℕ) :
    Nat.card {f : β → Fin n // HasSetoidEqualityPattern S f} =
      n.descFactorial (finiteSetoidBlockCount S) := by
  classical
  let _ : Fintype (Quotient S) := Quotient.fintype S
  calc
    Nat.card {f : β → Fin n // HasSetoidEqualityPattern S f} =
        Nat.card (Quotient S ↪ Fin n) :=
      Nat.card_congr (setoidPatternLabelingEquivEmbedding S)
    _ = Fintype.card (Quotient S ↪ Fin n) :=
      Nat.card_eq_fintype_card
    _ = n.descFactorial (finiteSetoidBlockCount S) := by
      simpa only [finiteSetoidBlockCount, Fintype.card_fin] using
        (Fintype.card_embedding_eq (α := Quotient S) (β := Fin n))

/-- Same-replica rigidity for a labeling of all paper occurrences. -/
def PaperSameReplicaRigidLabeling (G : PaperShape) (n p : ℕ)
    (label : PaperOccurrence G p → Fin n) : Prop :=
  ∀ (x : Replica (p + 1)) (v w : Fin G.roles),
    label (v, x) = label (w, x) → v = w

/-- A family of globally injective paper realizations is exactly one global
occurrence labeling satisfying same-replica rigidity. -/
def paperRealizationFamilyEquivRigidLabeling
    (G : PaperShape) (n p : ℕ) :
    (Replica (p + 1) → PaperRealization G n) ≃
      {label : PaperOccurrence G p → Fin n //
        PaperSameReplicaRigidLabeling G n p label} where
  toFun := fun phis =>
    ⟨paperFamilyLabel G phis, fun x v w h => (phis x).injective h⟩
  invFun := fun label x =>
    { toFun := fun v => label.1 (v, x)
      inj' := fun _ _ h => label.2 x _ _ h }
  left_inv := by
    intro phis
    funext x
    apply Function.Embedding.ext
    intro v
    rfl
  right_inv := by
    intro label
    apply Subtype.ext
    funext z
    rfl

/-- Labeling fiber of one global paper equality state. -/
abbrev PaperGlobalStateLabelingFiber
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) (n : ℕ) :=
  {label : PaperOccurrence G p → Fin n //
    HasSetoidEqualityPattern S.partition label}

/-- Realization-family fiber inducing exactly one fixed global equality
state. -/
abbrev PaperGlobalStateRealizationFamilyFiber
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) (n : ℕ) :=
  {phis : Replica (p + 1) → PaperRealization G n //
    paperFamilyEqualityPartition G phis = S.partition}

/-- A fixed-state global labeling automatically has the same-replica
rigidity needed to reconstruct a family of injective realizations. -/
theorem PaperTraceGlobalEqualityState.labelingFiber_sameReplicaRigid
    {G : PaperShape} {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (label : PaperGlobalStateLabelingFiber S n) :
    PaperSameReplicaRigidLabeling G n p label.1 := by
  intro x v w h
  exact S.withinReplicaInjective x v w ((label.2 (v, x) (w, x)).1 h)

/-- Realization families inducing `S` and arbitrary ambient labelings with
exact equality pattern `S.partition` are equivalent. -/
def paperGlobalStateRealizationFamilyEquivLabelingFiber
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) (n : ℕ) :
    PaperGlobalStateRealizationFamilyFiber S n ≃
      PaperGlobalStateLabelingFiber S n where
  toFun := fun phis =>
    ⟨paperFamilyLabel G phis.1, by
      intro a b
      change (paperFamilyEqualityPartition G phis.1).r a b ↔
        S.partition.r a b
      rw [phis.2]⟩
  invFun := fun label =>
    ⟨(paperRealizationFamilyEquivRigidLabeling G n p).symm
        ⟨label.1, S.labelingFiber_sameReplicaRigid label⟩, by
      have hlabel :
          paperFamilyLabel G
              ((paperRealizationFamilyEquivRigidLabeling G n p).symm
                ⟨label.1, S.labelingFiber_sameReplicaRigid label⟩) =
            label.1 := by
        have hrigid :=
          (paperRealizationFamilyEquivRigidLabeling G n p).apply_symm_apply
            ⟨label.1, S.labelingFiber_sameReplicaRigid label⟩
        exact congrArg
          (fun rigid : {f : PaperOccurrence G p → Fin n //
              PaperSameReplicaRigidLabeling G n p f} => rigid.1)
          hrigid
      apply Setoid.ext
      intro a b
      change
        paperFamilyLabel G
            ((paperRealizationFamilyEquivRigidLabeling G n p).symm
              ⟨label.1, S.labelingFiber_sameReplicaRigid label⟩) a =
          paperFamilyLabel G
            ((paperRealizationFamilyEquivRigidLabeling G n p).symm
              ⟨label.1, S.labelingFiber_sameReplicaRigid label⟩) b ↔
          S.partition.r a b
      rw [hlabel]
      exact label.2 a b⟩
  left_inv := by
    intro phis
    apply Subtype.ext
    funext x
    apply Function.Embedding.ext
    intro v
    rfl
  right_inv := by
    intro label
    apply Subtype.ext
    funext z
    rfl

/-- The paper-model weight of a global equality state: one descending
factorial, not a product of per-role factors. -/
def PaperTraceGlobalEqualityState.globalLabelingWeight
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) (n : ℕ) : ℕ :=
  n.descFactorial S.blockCount

/-- Exact cardinality of ambient labelings realizing one global state. -/
theorem PaperTraceGlobalEqualityState.labelingFiber_card_eq_globalWeight
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) (n : ℕ) :
    Nat.card (PaperGlobalStateLabelingFiber S n) =
      S.globalLabelingWeight n := by
  simpa [PaperTraceGlobalEqualityState.globalLabelingWeight,
    PaperTraceGlobalEqualityState.blockCount, finiteSetoidBlockCount] using
    setoidPatternLabelingCount_eq_descFactorial S.partition n

/-- Exact cardinality of realization families inducing one global state.
The same-replica rigidity stored in `S` is exactly what turns the global
labeling back into globally injective realizations. -/
theorem PaperTraceGlobalEqualityState.realizationFamilyFiber_card_eq_globalWeight
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) (n : ℕ) :
    Nat.card (PaperGlobalStateRealizationFamilyFiber S n) =
      S.globalLabelingWeight n := by
  calc
    Nat.card (PaperGlobalStateRealizationFamilyFiber S n) =
        Nat.card (PaperGlobalStateLabelingFiber S n) :=
      Nat.card_congr
        (paperGlobalStateRealizationFamilyEquivLabelingFiber S n)
    _ = S.globalLabelingWeight n :=
      S.labelingFiber_card_eq_globalWeight n


end GraphMatrixReplica
