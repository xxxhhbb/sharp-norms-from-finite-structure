import GraphMatrix.ReplicaPartitionState
import Mathlib.Data.Fintype.CardEmbedding

/-! # Exact number of labelings realizing an equality partition

The labelings with a fixed equality pattern are identified with embeddings
from the quotient set of blocks into the label type. For a label set of size
`n`, their number is the descending factorial `(n)_b`, where `b` is the number
of blocks.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A labeling has exactly the equivalence classes prescribed by `pi`. -/
def HasEqualityPattern {p : ℕ} {alpha : Type*}
    (pi : ReplicaPartition p) (x : Replica p → alpha) : Prop :=
  ∀ a b, x a = x b ↔ pi.r a b

/-- An injection on the quotient blocks gives a labeling of the replicas. -/
def labelingOfEmbedding {p : ℕ} {alpha : Type*}
    (pi : ReplicaPartition p) (e : Quotient pi ↪ alpha) : Replica p → alpha :=
  fun a => e (Quotient.mk'' a)

theorem labelingOfEmbedding_hasEqualityPattern
    {p : ℕ} {alpha : Type*} (pi : ReplicaPartition p)
    (e : Quotient pi ↪ alpha) :
    HasEqualityPattern pi (labelingOfEmbedding pi e) := by
  intro a b
  constructor
  · intro h
    exact Quotient.exact (e.injective h)
  · intro h
    exact congrArg e (Quotient.sound h)

/-- A labeling with exactly pattern `pi` descends to an injection on blocks. -/
def quotientEmbeddingOfPattern
    {p : ℕ} {alpha : Type*} (pi : ReplicaPartition p)
    (x : {x : Replica p → alpha // HasEqualityPattern pi x}) :
    Quotient pi ↪ alpha where
  toFun := Quotient.lift x.1 (fun _ _ h => (x.2 _ _).2 h)
  inj' := by
    intro q r h
    refine Quotient.inductionOn₂ q r ?_ h
    intro a b hab
    exact Quotient.sound ((x.2 a b).1 hab)

/-- Exact equivalence between realizations of a partition and injective block
labels. -/
def equalityPatternLabelingEquivEmbedding
    {p : ℕ} {alpha : Type*} (pi : ReplicaPartition p) :
    {x : Replica p → alpha // HasEqualityPattern pi x} ≃ (Quotient pi ↪ alpha) where
  toFun := quotientEmbeddingOfPattern pi
  invFun := fun e => ⟨labelingOfEmbedding pi e,
    labelingOfEmbedding_hasEqualityPattern pi e⟩
  left_inv := by
    intro x
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

/-- A `b`-block equality pattern has exactly `(n)_b` realizations by labels in
`Fin n`. -/
theorem equalityPatternLabelingCount_eq_descFactorial
    {p : ℕ} (pi : ReplicaPartition p) (n : ℕ) :
    Nat.card {x : Replica p → Fin n // HasEqualityPattern pi x} =
      n.descFactorial (partitionBlockCount pi) := by
  classical
  calc
    Nat.card {x : Replica p → Fin n // HasEqualityPattern pi x} =
        Nat.card (Quotient pi ↪ Fin n) :=
      Nat.card_congr (equalityPatternLabelingEquivEmbedding pi)
    _ = Fintype.card (Quotient pi ↪ Fin n) := Nat.card_eq_fintype_card
    _ = n.descFactorial (partitionBlockCount pi) := by
      simpa [partitionBlockCount] using
        (Fintype.card_embedding_eq (alpha := Quotient pi) (beta := Fin n))


end GraphMatrixReplica
