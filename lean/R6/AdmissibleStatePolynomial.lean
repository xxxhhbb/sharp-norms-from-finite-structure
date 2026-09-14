import R6.ReplicaStateWeight
import Mathlib.SetTheory.Cardinal.Finite

/-! # Exact admissible-state polynomial

This file removes proof fields from the enumerated state data.  A raw tuple of
role partitions is retained precisely when it satisfies all edge-parity and
boundary-gluing constraints.  Concrete admissible labelings then decompose as
a disjoint sigma type over those states, and each fiber has the product
falling-factorial weight proved earlier.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Setoids on a finite replica type form a finite type. -/
noncomputable instance replicaPartitionFintype (p : ℕ) :
    Fintype (ReplicaPartition p) := by
  classical
  apply Fintype.ofInjective
    (fun pi : ReplicaPartition p => fun a b => decide (pi.r a b))
  intro pi sigma h
  apply Setoid.ext
  intro a b
  exact decide_eq_decide.mp (congrFun (congrFun h a) b)

/-- Proof-free data underlying a typed state. -/
abbrev PartitionAssignment (G : PartiteShape) (p : ℕ) :=
  Fin G.roles → ReplicaPartition (p + 1)

/-- All C078 edge and trace constraints imposed on a partition tuple. -/
def IsAdmissiblePartitionAssignment (G : PartiteShape) (p : ℕ)
    (P : PartitionAssignment G p) : Prop :=
  (∀ e : Fin G.edges,
    EdgeParityCompatible (P (G.source e)) (P (G.target e))) ∧
  (∀ v : Fin G.roles, v ∈ G.leftBoundary → LeftTraceCoarsens (P v)) ∧
  (∀ v : Fin G.roles, v ∈ G.rightBoundary → RightTraceCoarsens (P v))

/-- Finite, enumerable presentation of the admissible typed states. -/
abbrev AdmissiblePartitionState (G : PartiteShape) (p : ℕ) :=
  {P : PartitionAssignment G p // IsAdmissiblePartitionAssignment G p P}

noncomputable instance admissiblePartitionStateFintype
    (G : PartiteShape) (p : ℕ) : Fintype (AdmissiblePartitionState G p) :=
  Fintype.ofFinite _

/-- Convert the enumerable tuple presentation to the proof-carrying state. -/
def AdmissiblePartitionState.toReplicaState
    {G : PartiteShape} {p : ℕ} (T : AdmissiblePartitionState G p) :
    ReplicaState G p where
  partition := T.1
  edgeParity := T.2.1
  leftGlue := T.2.2.1
  rightGlue := T.2.2.2

/-- The concrete role labeling survives all Rademacher and trace constraints. -/
def ConcreteLabelingAdmissible
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (x : RoleLabeling G p dimension) : Prop :=
  IsAdmissiblePartitionAssignment G p
    (fun v => equalityPartition (x v))

/-- Literal fiber of the equality-pattern map over an admissible state. -/
def AdmissibleStateFiber
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (T : AdmissiblePartitionState G p) :=
  {x : RoleLabeling G p dimension //
    ∀ v, equalityPartition (x v) = T.1 v}

noncomputable instance admissibleStateFiberFintype
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (T : AdmissiblePartitionState G p) :
    Fintype (AdmissibleStateFiber dimension T) := by
  classical
  let e : AdmissibleStateFiber dimension T ≃
      (∀ v : Fin G.roles,
        Quotient (T.toReplicaState.partition v) ↪ Fin (dimension v)) :=
    (replicaStatePatternFiberEquivRealizations dimension T.toReplicaState).trans
      (replicaStateLabelingEquivEmbeddings dimension T.toReplicaState)
  exact Fintype.ofEquiv
    (∀ v : Fin G.roles,
      Quotient (T.toReplicaState.partition v) ↪ Fin (dimension v)) e.symm

/-- Admissible labelings are a disjoint union of equality-pattern fibers over
the finite admissible state space. -/
def admissibleLabelingEquivSigmaFibers
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    {x : RoleLabeling G p dimension // ConcreteLabelingAdmissible dimension x} ≃
      (Σ T : AdmissiblePartitionState G p, AdmissibleStateFiber dimension T) where
  toFun := fun x =>
    ⟨⟨fun v => equalityPartition (x.1 v), x.2⟩, ⟨x.1, fun _ => rfl⟩⟩
  invFun := fun z => ⟨z.2.1, by
    unfold ConcreteLabelingAdmissible
    rw [show (fun v => equalityPartition (z.2.1 v)) = z.1.1 from
      funext z.2.2]
    exact z.1.2⟩
  left_inv := fun x => Subtype.ext rfl
  right_inv := by
    rintro ⟨⟨P, hP⟩, ⟨x, hx⟩⟩
    dsimp at hx ⊢
    have hPattern : (fun v => equalityPartition (x v)) = P := funext hx
    subst P
    rfl

/-- Every admissible-state fiber has the already-defined product weight. -/
theorem admissibleStateFiber_card_eq_weight
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ)
    (T : AdmissiblePartitionState G p) :
    Nat.card (AdmissibleStateFiber dimension T) =
      T.toReplicaState.labelingWeight dimension := by
  exact replicaStatePatternFiberCount_eq_weight dimension T.toReplicaState

/-- The exact C078 combinatorial polynomial: the number of concrete labelings
surviving all parity and trace constraints is the sum of product
falling-factorial weights over finite admissible typed states. -/
theorem admissibleLabelingCount_eq_statePolynomial
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    Nat.card
        {x : RoleLabeling G p dimension // ConcreteLabelingAdmissible dimension x} =
      ∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension := by
  classical
  calc
    Nat.card
        {x : RoleLabeling G p dimension // ConcreteLabelingAdmissible dimension x} =
        Nat.card (Σ T : AdmissiblePartitionState G p,
          AdmissibleStateFiber dimension T) :=
      Nat.card_congr (admissibleLabelingEquivSigmaFibers dimension)
    _ = ∑ T : AdmissiblePartitionState G p,
          Nat.card (AdmissibleStateFiber dimension T) := Nat.card_sigma
    _ = ∑ T : AdmissiblePartitionState G p,
          T.toReplicaState.labelingWeight dimension := by
      apply Finset.sum_congr rfl
      intro T _
      exact admissibleStateFiber_card_eq_weight dimension T

#print axioms admissibleLabelingEquivSigmaFibers
#print axioms admissibleStateFiber_card_eq_weight
#print axioms admissibleLabelingCount_eq_statePolynomial

end GraphMatrixReplica
