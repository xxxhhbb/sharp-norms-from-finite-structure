import R6.C079PathFallingFactorialLower
import R6.PartiteBoundaryMatrixTrace

/-! # The canonical fully-partite path for C079 Lemma 3

The paper's path entropy estimate concerns a single oriented, simple path.
This module fixes its typed role/edge indexing and gives a restriction map
from any embedded backbone path.  No moment bound is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- `ell` oriented edges `i -> i+1`, with its two endpoint boundaries. -/
def c079CanonicalPathShape (ell : Nat) : PartiteShape where
  roles := ell + 1
  edges := ell
  source := fun i => i.castSucc
  target := fun i => i.succ
  leftBoundary := {0}
  rightBoundary := {Fin.last ell}

/-- Uniform auxiliary dimension on the canonical path. -/
def c079CanonicalPathDimension (ell m : Nat) :
    Fin (c079CanonicalPathShape ell).roles -> Nat := fun _ => m

/-- The typed edge-sign sample is exactly a family of `ell` independent
square sign arrays.  The claim is an equivalence of sample *spaces*, not a
probabilistic norm estimate. -/
def c079PathSampleEquiv (ell m : Nat) :
    JointEdgeSignSample (c079CanonicalPathDimension ell m) ≃
      (Fin ell -> Fin m × Fin m -> Bool) where
  toFun := fun epsilon e ab => epsilon e ab
  invFun := fun epsilon e ab => epsilon e ab
  left_inv := by intro epsilon; rfl
  right_inv := by intro epsilon; rfl

/-- One edge array as an `m × m` rational sign matrix. -/
def c079PathEdgeMatrix (ell m : Nat)
    (epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m))
    (e : Fin ell) : Matrix (Fin m) (Fin m) Rat :=
  fun a b => (rademacherSign (epsilon e (a, b)) : Rat)

/-- For the canonical path, the one-copy edge monomial is literally the
product of entries of the separately sampled edge matrices. -/
theorem c079Path_edgeMonomial_eq_matrixEntryProduct
    (ell m : Nat)
    (epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m))
    (phi : PartiteRoleAssignment (c079CanonicalPathDimension ell m)) :
    partiteAssignmentEdgeMonomial epsilon phi =
      ∏ e : Fin ell,
        c079PathEdgeMatrix ell m epsilon e
          (phi e.castSucc) (phi e.succ) := by
  rfl

/-- A selected graph-backbone path, including its orientation and endpoint
gluing.  Reversed shape edges are allowed because parity compatibility is
symmetric.  This structure is a local input; it does not assert that a
particular Menger family has already been converted to this indexing. -/
structure C079PathBackboneEmbedding (G : PartiteShape) (ell : Nat) where
  role : Fin (ell + 1) -> Fin G.roles
  edge : Fin ell -> Fin G.edges
  endpointMatch : forall i : Fin ell,
    (G.source (edge i) = role i.castSucc ∧
      G.target (edge i) = role i.succ) ∨
    (G.source (edge i) = role i.succ ∧
      G.target (edge i) = role i.castSucc)
  leftEnd : role 0 ∈ G.leftBoundary
  rightEnd : role (Fin.last ell) ∈ G.rightBoundary

/-- Restrict an admissible fully-partite state to its selected path.  This
forgets non-backbone constraints and therefore can only enlarge a later
count; it does not identify the paper's globally injective model. -/
def C079PathBackboneEmbedding.restrictState
    {G : PartiteShape} {ell p : Nat}
    (B : C079PathBackboneEmbedding G ell)
    (T : AdmissiblePartitionState G p) :
    AdmissiblePartitionState (c079CanonicalPathShape ell) p := by
  refine ⟨fun v => T.1 (B.role v), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases B.endpointMatch i with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simpa [c079CanonicalPathShape, hs, ht] using T.2.1 (B.edge i)
    · have h := edgeParityCompatible_comm
        (T.1 (G.source (B.edge i)))
        (T.1 (G.target (B.edge i)))
      simpa [c079CanonicalPathShape, hs, ht] using
        (h.mp (T.2.1 (B.edge i)))
  · intro v hv
    change v ∈ ({0} : Finset (Fin (ell + 1))) at hv
    have hv0 : v = (0 : Fin (ell + 1)) := Finset.mem_singleton.mp hv
    subst v
    exact T.2.2.1 (B.role 0) B.leftEnd
  · intro v hv
    change v ∈ ({Fin.last ell} : Finset (Fin (ell + 1))) at hv
    have hvLast : v = Fin.last ell := Finset.mem_singleton.mp hv
    subst v
    exact T.2.2.2 (B.role (Fin.last ell)) B.rightEnd

#print axioms c079PathSampleEquiv
#print axioms c079Path_edgeMonomial_eq_matrixEntryProduct
#print axioms C079PathBackboneEmbedding.restrictState

end GraphMatrixReplica
