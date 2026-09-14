import GraphMatrix.EqualityPatternLabelCount

/-! # Product falling-factorial weight of a typed replica state

Role labelings are independent once their equality partitions are fixed.
This file packages the rolewise quotient-embedding equivalences into one exact
product formula.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A simultaneous choice of concrete labels at every role. -/
abbrev RoleLabeling (G : PartiteShape) (p : ℕ)
    (dimension : Fin G.roles → ℕ) :=
  ∀ v : Fin G.roles, Replica (p + 1) → Fin (dimension v)

/-- The simultaneous labeling realizes every partition of the state. -/
def RealizesReplicaState {G : PartiteShape} {p : ℕ}
    (dimension : Fin G.roles → ℕ) (S : ReplicaState G p)
    (x : RoleLabeling G p dimension) : Prop :=
  ∀ v, HasEqualityPattern (S.partition v) (x v)

/-- Fiber formulation using literal equality with the induced setoid. -/
def HasReplicaStateEqualityPatterns {G : PartiteShape} {p : ℕ}
    (dimension : Fin G.roles → ℕ) (S : ReplicaState G p)
    (x : RoleLabeling G p dimension) : Prop :=
  ∀ v, equalityPartition (x v) = S.partition v

theorem hasReplicaStateEqualityPatterns_iff_realizes
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (S : ReplicaState G p) (x : RoleLabeling G p dimension) :
    HasReplicaStateEqualityPatterns dimension S x ↔
      RealizesReplicaState dimension S x := by
  constructor
  · intro h v a b
    rw [← h v]
    rfl
  · intro h v
    apply Setoid.ext
    intro a b
    exact h v a b

/-- The literal fiber of the equality-pattern map is equivalent to the
relation-level realization subtype. -/
def replicaStatePatternFiberEquivRealizations
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (S : ReplicaState G p) :
    {x : RoleLabeling G p dimension //
      HasReplicaStateEqualityPatterns dimension S x} ≃
    {x : RoleLabeling G p dimension // RealizesReplicaState dimension S x} where
  toFun := fun x =>
    ⟨x.1, (hasReplicaStateEqualityPatterns_iff_realizes dimension S x.1).1 x.2⟩
  invFun := fun x =>
    ⟨x.1, (hasReplicaStateEqualityPatterns_iff_realizes dimension S x.1).2 x.2⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := fun x => Subtype.ext rfl

/-- The exact falling-factorial weight attached to a replica state. -/
def ReplicaState.labelingWeight {G : PartiteShape} {p : ℕ}
    (S : ReplicaState G p) (dimension : Fin G.roles → ℕ) : ℕ :=
  ∏ v : Fin G.roles,
    (dimension v).descFactorial (partitionBlockCount (S.partition v))

/-- Simultaneous state realizations are precisely independent embeddings of
each role's quotient blocks into that role's label set. -/
def replicaStateLabelingEquivEmbeddings
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (S : ReplicaState G p) :
    {x : RoleLabeling G p dimension // RealizesReplicaState dimension S x} ≃
      (∀ v : Fin G.roles, Quotient (S.partition v) ↪ Fin (dimension v)) where
  toFun := fun x v => quotientEmbeddingOfPattern (S.partition v)
    ⟨x.1 v, x.2 v⟩
  invFun := fun e =>
    ⟨fun v => labelingOfEmbedding (S.partition v) (e v),
      fun v => labelingOfEmbedding_hasEqualityPattern (S.partition v) (e v)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext v a
    rfl
  right_inv := by
    intro e
    funext v
    apply Function.Embedding.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro a
    rfl

/-- Exact all-role count: the weight of a state is the product of the
descending factorials of its role block counts. -/
theorem replicaStateLabelingCount_eq_weight
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (S : ReplicaState G p) :
    Nat.card
        {x : RoleLabeling G p dimension // RealizesReplicaState dimension S x} =
      S.labelingWeight dimension := by
  classical
  calc
    Nat.card
        {x : RoleLabeling G p dimension // RealizesReplicaState dimension S x} =
        Nat.card (∀ v : Fin G.roles,
          Quotient (S.partition v) ↪ Fin (dimension v)) :=
      Nat.card_congr (replicaStateLabelingEquivEmbeddings dimension S)
    _ = Fintype.card (∀ v : Fin G.roles,
          Quotient (S.partition v) ↪ Fin (dimension v)) :=
      Nat.card_eq_fintype_card
    _ = S.labelingWeight dimension := by
      simp [ReplicaState.labelingWeight, Fintype.card_pi,
        Fintype.card_embedding_eq, partitionBlockCount]

/-- Fiber-cardinality form used when a concrete labeling sum is grouped by
its induced replica state. -/
theorem replicaStatePatternFiberCount_eq_weight
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (S : ReplicaState G p) :
    Nat.card
        {x : RoleLabeling G p dimension //
          HasReplicaStateEqualityPatterns dimension S x} =
      S.labelingWeight dimension := by
  rw [Nat.card_congr (replicaStatePatternFiberEquivRealizations dimension S)]
  exact replicaStateLabelingCount_eq_weight dimension S


end GraphMatrixReplica
