import GraphMatrix.Counting.PathStateCountArithmetic
import GraphMatrix.AdmissibleStatePolynomial
import GraphMatrix.DisjointPathDegreeBound

/-! # C079 path-state counting interface

The paper's path lemma uses trace order `q >= 2`.  Existing replica modules
index the same object by `p = q - 1`, because `ReplicaState G p` has `p+1`
trace copies.  This file keeps that shift explicit in every definition.

It packages the exact total-block fiber and specializes the arithmetic kernel
to its falling-factorial weight at the auxiliary dimension
`2 * (p+1)^2`.  No sphere-net or random-matrix moment estimate is asserted.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Exact degree fiber appearing in C079 Lemma 3.  `p` is the Lean moment
index, so the paper's trace order is `p+1`. -/
abbrev C079PathStateDegreeFiber
    (G : PartiteShape) (p ell t : Nat) :=
  {T : AdmissiblePartitionState G p //
    T.toReplicaState.totalBlockCount = (p + 1) * ell + 1 - t}

/-- Falling-factorial weight at the auxiliary dimension used solely for the
path count. -/
def c079PathAuxiliaryWeight
    {G : PartiteShape} {p ell t : Nat}
    (T : C079PathStateDegreeFiber G p ell t) : Nat :=
  T.1.toReplicaState.labelingWeight
    (fun _v : Fin G.roles => 2 * (p + 1) ^ 2)

/-- Replica-indexed form of the conditional Lemma 3 kernel.  The two visible
hypotheses are exactly the remaining analytic obligations:

* the falling-factorial lower bound for every state in this fiber;
* the auxiliary sign-matrix-product moment upper bound.

The role-count equation records that the intended shape is a path with
`ell+1` roles.  Structural path admissibility is not inferred from it; it must
be used upstream when proving the two analytic hypotheses. -/
theorem c079_pathStateDegreeFiber_card_le_of_auxiliary_bounds
    (G : PartiteShape) (p ell t : Nat)
    (_hRoles : G.roles = ell + 1)
    (hp : 1 <= p) (ht : t <= ell * p)
    (hLower : forall T : C079PathStateDegreeFiber G p ell t,
      (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1 - t) <=
        3 ^ (ell + 1) * c079PathAuxiliaryWeight T)
    (hUpper :
      (∑ T : C079PathStateDegreeFiber G p ell t,
          c079PathAuxiliaryWeight T) <=
        12 ^ (2 * (p + 1) * ell) *
          (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1)) :
    Fintype.card (C079PathStateDegreeFiber G p ell t) <=
      100 ^ (2 * (p + 1) * (ell + 1)) * (p + 1) ^ (2 * t) := by
  apply c079_pathState_card_le_of_auxiliary_weight_bounds
    c079PathAuxiliaryWeight ell (p + 1) t (by omega)
  · simpa using ht
  · exact hLower
  · exact hUpper

/-- If every role is simultaneously on the left and right boundary, there is
at most one admissible partition state.  This proves the finite-count part of
the singleton-path clause without an analytic hypothesis. -/
theorem c079_admissiblePartitionState_card_le_one_of_all_commonBoundary
    (G : PartiteShape) (p : Nat)
    (hLeft : forall v : Fin G.roles, v ∈ G.leftBoundary)
    (hRight : forall v : Fin G.roles, v ∈ G.rightBoundary) :
    Fintype.card (AdmissiblePartitionState G p) <= 1 := by
  have hSubsingleton : Subsingleton (AdmissiblePartitionState G p) := by
    refine ⟨?_⟩
    intro T U
    apply Subtype.ext
    funext v
    apply Setoid.ext
    intro a b
    constructor
    · intro _hab
      exact U.toReplicaState.commonBoundary_universal
        v (hLeft v) (hRight v) a b
    · intro _hab
      exact T.toReplicaState.commonBoundary_universal
        v (hLeft v) (hRight v) a b
  let f : AdmissiblePartitionState G p -> Fin 1 := fun _ => 0
  have hf : Function.Injective f := by
    intro T U _h
    exact hSubsingleton.elim T U
  simpa using Fintype.card_le_of_injective f hf

/-- Every exact degree fiber of an all-common-boundary shape also has at most
one state.  In particular this covers the singleton right-to-left path's
finite counting assertion. -/
theorem c079_pathStateDegreeFiber_card_le_one_of_all_commonBoundary
    (G : PartiteShape) (p ell t : Nat)
    (hLeft : forall v : Fin G.roles, v ∈ G.leftBoundary)
    (hRight : forall v : Fin G.roles, v ∈ G.rightBoundary) :
    Fintype.card (C079PathStateDegreeFiber G p ell t) <= 1 := by
  let forget : C079PathStateDegreeFiber G p ell t ->
      AdmissiblePartitionState G p := fun T => T.1
  have hInjective : Function.Injective forget := by
    intro T U h
    exact Subtype.ext h
  calc
    Fintype.card (C079PathStateDegreeFiber G p ell t) <=
        Fintype.card (AdmissiblePartitionState G p) :=
      Fintype.card_le_of_injective forget hInjective
    _ <= 1 :=
      c079_admissiblePartitionState_card_le_one_of_all_commonBoundary
        G p hLeft hRight


end GraphMatrixReplica
