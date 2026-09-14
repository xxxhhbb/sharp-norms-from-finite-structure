import GraphMatrix.Counting.PathAuxMomentShape

/-! # Non-circular matrix algebra for the C079 path auxiliary moment

This file uses only finite sums and matrix multiplication.  It shows that an
ordered list of square matrices has entries given by the recursive sum over
all internal path indices.  The edge matrices of the canonical path are
independent sign arrays in the precise sense of `c079PathSampleEquiv`.
No operator-norm estimate or probabilistic tail bound is used.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Ordered product, with the empty path represented by the identity matrix. -/
def c079OrderedMatrixProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (xs : List (Matrix ι ι Rat)) : Matrix ι ι Rat :=
  xs.prod

/-- Recursive open-walk sum through an ordered list of edge matrices. -/
def c079OpenWalkSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (xs : List (Matrix ι ι Rat)) (a b : ι) : Rat :=
  match xs with
  | [] => if a = b then 1 else 0
  | X :: ys => ∑ c : ι, X a c * c079OpenWalkSum ys c b

/-- Exact algebraic meaning of the sign-matrix product. -/
theorem c079OrderedMatrixProduct_apply_eq_openWalkSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (xs : List (Matrix ι ι Rat)) (a b : ι) :
    c079OrderedMatrixProduct xs a b = c079OpenWalkSum xs a b := by
  induction xs generalizing a with
  | nil => simp [c079OrderedMatrixProduct, c079OpenWalkSum, Matrix.one_apply]
  | cons X ys ih =>
      simp only [c079OrderedMatrixProduct, List.prod_cons,
        Matrix.mul_apply, c079OpenWalkSum]
      apply Finset.sum_congr rfl
      intro c _
      rw [← ih]
      rfl

/-- The canonical path's ordered product of its `ell` distinct edge arrays. -/
def c079CanonicalPathMatrixProduct (ell m : Nat)
    (epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m)) :
    Matrix (Fin m) (Fin m) Rat :=
  c079OrderedMatrixProduct
    (List.ofFn (fun e : Fin ell => c079PathEdgeMatrix ell m epsilon e))

/-- Its entries are exactly the finite open-walk sum. -/
theorem c079CanonicalPathMatrixProduct_apply
    (ell m : Nat)
    (epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m))
    (a b : Fin m) :
    c079CanonicalPathMatrixProduct ell m epsilon a b =
      c079OpenWalkSum
        (List.ofFn (fun e : Fin ell => c079PathEdgeMatrix ell m epsilon e))
        a b :=
  c079OrderedMatrixProduct_apply_eq_openWalkSum _ a b

/-- A singleton left boundary is precisely one matrix row index. -/
def c079CanonicalPathRowEquiv (ell m : Nat) :
    PartiteBoundaryRow (c079CanonicalPathDimension ell m) ≃ Fin m where
  toFun := fun row => row ⟨(0 : Fin (ell + 1)), by
    change (0 : Fin (ell + 1)) ∈ ({0} : Finset (Fin (ell + 1)))
    simp⟩
  invFun := fun a _v => a
  left_inv := by
    intro row
    funext v
    have hv0 : v.1 = (0 : Fin (ell + 1)) := by
      exact Finset.mem_singleton.mp
        (show v.1 ∈ ({0} : Finset (Fin (ell + 1))) from v.property)
    have heq : v = ⟨(0 : Fin (ell + 1)), by
        change (0 : Fin (ell + 1)) ∈ ({0} : Finset (Fin (ell + 1)))
        simp⟩ := Subtype.ext hv0
    subst v
    rfl
  right_inv := by intro a; rfl

/-- A singleton right boundary is precisely one matrix column index. -/
def c079CanonicalPathColEquiv (ell m : Nat) :
    PartiteBoundaryCol (c079CanonicalPathDimension ell m) ≃ Fin m where
  toFun := fun col => col ⟨Fin.last ell, by
    change Fin.last ell ∈
      ({Fin.last ell} : Finset (Fin (ell + 1)))
    simp⟩
  invFun := fun b _v => b
  left_inv := by
    intro col
    funext v
    have hvLast : v.1 = Fin.last ell := by
      exact Finset.mem_singleton.mp
        (show v.1 ∈
          ({Fin.last ell} : Finset (Fin (ell + 1))) from v.property)
    have heq : v = ⟨Fin.last ell, by
        change Fin.last ell ∈
          ({Fin.last ell} : Finset (Fin (ell + 1)))
        simp⟩ := Subtype.ext hvLast
    subst v
    rfl
  right_inv := by intro b; rfl

/-- The existing boundary-entry predicate becomes equality of the two path
endpoint indices; all internal roles remain freely summed. -/
theorem c079Path_boundaryEntryCompatible_iff_endpoints
    (ell m : Nat)
    (phi : PartiteRoleAssignment (c079CanonicalPathDimension ell m))
    (row : PartiteBoundaryRow (c079CanonicalPathDimension ell m))
    (col : PartiteBoundaryCol (c079CanonicalPathDimension ell m)) :
    partiteBoundaryEntryCompatible phi row col ↔
      phi (0 : Fin (ell + 1)) = c079CanonicalPathRowEquiv ell m row ∧
      phi (Fin.last ell) = c079CanonicalPathColEquiv ell m col := by
  constructor
  · intro h
    exact ⟨h.1 ⟨(0 : Fin (ell + 1)), by
      change (0 : Fin (ell + 1)) ∈ ({0} : Finset (Fin (ell + 1)))
      simp⟩, h.2 ⟨Fin.last ell, by
      change Fin.last ell ∈
        ({Fin.last ell} : Finset (Fin (ell + 1)))
      simp⟩⟩
  · rintro ⟨hLeft, hRight⟩
    constructor
    · intro v
      have hv0 : v.1 = (0 : Fin (ell + 1)) := by
        exact Finset.mem_singleton.mp
          (show v.1 ∈ ({0} : Finset (Fin (ell + 1))) from v.property)
      have heq : v = ⟨(0 : Fin (ell + 1)), by
          change (0 : Fin (ell + 1)) ∈ ({0} : Finset (Fin (ell + 1)))
          simp⟩ := Subtype.ext hv0
      subst v
      exact hLeft
    · intro v
      have hvLast : v.1 = Fin.last ell := by
        exact Finset.mem_singleton.mp
          (show v.1 ∈
            ({Fin.last ell} : Finset (Fin (ell + 1))) from v.property)
      have heq : v = ⟨Fin.last ell, by
          change Fin.last ell ∈
            ({Fin.last ell} : Finset (Fin (ell + 1)))
          simp⟩ := Subtype.ext hvLast
      subst v
      exact hRight

/-- Exact boundary-matrix entry as an open-walk sum.  This is a finite
algebraic identity, not a stochastic estimate. -/
theorem c079Path_boundaryMatrix_entry_eq_assignmentSum
    (ell m : Nat)
    (epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m))
    (row : PartiteBoundaryRow (c079CanonicalPathDimension ell m))
    (col : PartiteBoundaryCol (c079CanonicalPathDimension ell m)) :
    partiteBoundaryMatrix (c079CanonicalPathShape ell)
        (c079CanonicalPathDimension ell m) epsilon row col =
      ∑ phi : Fin (ell + 1) -> Fin m,
        if phi (0 : Fin (ell + 1)) = c079CanonicalPathRowEquiv ell m row ∧
            phi (Fin.last ell) = c079CanonicalPathColEquiv ell m col then
          ∏ e : Fin ell,
            c079PathEdgeMatrix ell m epsilon e
              (phi e.castSucc) (phi e.succ)
        else 0 := by
  classical
  unfold partiteBoundaryMatrix
  apply Finset.sum_congr rfl
  intro phi _
  by_cases h : partiteBoundaryEntryCompatible phi row col
  · have he := (c079Path_boundaryEntryCompatible_iff_endpoints
      ell m phi row col).mp h
    simp only [if_pos h]
    split_ifs with hEnd
    · exact c079Path_edgeMonomial_eq_matrixEntryProduct ell m epsilon phi
    · exact False.elim (hEnd he)
  · have he : ¬ (phi (0 : Fin (ell + 1)) =
        c079CanonicalPathRowEquiv ell m row ∧
        phi (Fin.last ell) = c079CanonicalPathColEquiv ell m col) :=
      fun he => h ((c079Path_boundaryEntryCompatible_iff_endpoints
        ell m phi row col).mpr he)
    simp only [if_neg h]
    split_ifs with hEnd
    · exact False.elim (he hEnd)
    · rfl

/-- The remaining pointwise algebraic bridge can be supplied independently
of every norm estimate.  A witness proves that the existing boundary matrix,
after endpoint reindexing, is this ordered product.  This is *not* asserted
here as an unconditional theorem. -/
def C079PathBoundaryProductBridge (ell m : Nat) : Prop :=
  ∃ rowIndex : PartiteBoundaryRow (c079CanonicalPathDimension ell m) ≃ Fin m,
    ∃ colIndex : PartiteBoundaryCol (c079CanonicalPathDimension ell m) ≃ Fin m,
      ∀ epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m),
        ∀ row col,
          partiteBoundaryMatrix (c079CanonicalPathShape ell)
              (c079CanonicalPathDimension ell m) epsilon row col =
            c079CanonicalPathMatrixProduct ell m epsilon
              (rowIndex row) (colIndex col)


end GraphMatrixReplica
