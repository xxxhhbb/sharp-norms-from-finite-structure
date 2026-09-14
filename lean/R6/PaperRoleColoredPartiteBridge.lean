import R6.PaperGraphMatrixEntryMoments
import R6.PaperToPartiteBridge
import R6.PartiteBoundaryMatrixTrace

/-! # Exact entry bridge for disjoint role colors

This module formalizes the local algebraic core of the C027 fully-partite
reduction.  A `PaperRoleColoring` embeds the label set of every shape role
into one ambient label set, with pairwise disjoint images.  Hence every
rolewise assignment canonically becomes a globally injective paper
realization.  After restricting rows and columns to the corresponding color
classes, and matching the ambient edge signs to the edgewise arrays, the
colored paper entry is exactly the real cast of the concrete fully-partite
boundary-matrix entry.

This is an entry identity for the color-restricted summand.  It does not by
itself formalize the random-balanced-color averaging or the Fourier projection
used for the two-sided expected-operator-norm comparison in C027.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A rolewise label assignment, written against `PaperShape` so that its
finite product instance does not depend on reduction unfolding. -/
abbrev PaperRoleColorAssignment (G : PaperShape)
    (dimension : Fin G.roles → ℕ) :=
  ∀ v : Fin G.roles, Fin (dimension v)

/-- Pairwise disjoint role color classes inside one ambient label set. -/
structure PaperRoleColoring (G : PaperShape)
    (dimension : Fin G.roles → ℕ) (n : ℕ) where
  embedding : ∀ v : Fin G.roles, Fin (dimension v) ↪ Fin n
  disjoint : ∀ {v w : Fin G.roles}, v ≠ w →
    ∀ (a : Fin (dimension v)) (b : Fin (dimension w)),
      embedding v a ≠ embedding w b

/-- A rolewise assignment becomes globally injective because different role
colors have disjoint ambient images. -/
def PaperRoleColoring.globalRealization
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRoleColorAssignment G dimension) :
    PaperRealization G n where
  toFun v := C.embedding v (phi v)
  inj' := by
    intro v w h
    by_contra hvw
    exact C.disjoint hvw (phi v) (phi w) h

/-- Embed a fully-partite left-boundary row into the selected paper row block. -/
def PaperRoleColoring.paperRow
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension) :
    PaperRow G n :=
  fun i => C.embedding (G.left i)
    (row ⟨G.left i, by
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

/-- Embed a fully-partite right-boundary column into the selected paper column
block. -/
def PaperRoleColoring.paperCol
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension) :
    PaperCol G n :=
  fun i => C.embedding (G.right i)
    (col ⟨G.right i, by
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

/-- Boundary compatibility is preserved and reflected by the disjoint-color
embedding. -/
theorem PaperRoleColoring.paperEntryCompatible_globalRealization_iff
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRoleColorAssignment G dimension)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension) :
    paperEntryCompatible G (C.globalRealization phi)
        (C.paperRow row) (C.paperCol col) ↔
      partiteBoundaryEntryCompatible phi row col := by
  constructor
  · rintro ⟨hLeft, hRight⟩
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨i, hi⟩ := (G.mem_leftBoundaryFinset_iff v).1 hv
      subst v
      exact (C.embedding (G.left i)).injective (hLeft i)
    · rintro ⟨v, hv⟩
      obtain ⟨i, hi⟩ := (G.mem_rightBoundaryFinset_iff v).1 hv
      subst v
      exact (C.embedding (G.right i)).injective (hRight i)
  · rintro ⟨hLeft, hRight⟩
    constructor
    · intro i
      apply congrArg (C.embedding (G.left i))
      exact hLeft ⟨G.left i, by
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    · intro i
      apply congrArg (C.embedding (G.right i))
      exact hRight ⟨G.right i, by
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

/-- The paper matrix entry after retaining only realizations whose role labels
lie in the selected disjoint color classes. -/
def paperRoleColoredBoundaryMatrix
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n) (w : PaperNoise n) :
    Matrix (PartiteBoundaryRow (G := G.toPartiteShape) dimension)
      (PartiteBoundaryCol (G := G.toPartiteShape) dimension) ℝ := by
  classical
  exact fun row col =>
    ∑ phi : PaperRoleColorAssignment G dimension,
      if paperEntryCompatible G (C.globalRealization phi)
          (C.paperRow row) (C.paperCol col) then
        ∏ e : Fin G.edges, paperEdgeSign w
          (C.embedding (G.source e) (phi (G.source e)))
          (C.embedding (G.target e) (phi (G.target e)))
      else 0

/-- If the ambient signs on the selected cross-color coordinates agree with
the edgewise sign arrays, then the colored paper matrix is exactly the real
cast of the fully-partite boundary matrix, entry by entry. -/
theorem paperRoleColoredBoundaryMatrix_eq_partiteBoundaryMatrix
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n) (w : PaperNoise n)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension)
    (hSign : ∀ (e : Fin G.edges)
        (a : Fin (dimension (G.source e)))
        (b : Fin (dimension (G.target e))),
      paperEdgeSign w (C.embedding (G.source e) a)
          (C.embedding (G.target e) b) =
        (rademacherSign (epsilon e (a, b)) : ℝ)) :
    paperRoleColoredBoundaryMatrix G dimension n C w =
      fun row col =>
        ((partiteBoundaryMatrix G.toPartiteShape dimension epsilon row col : ℚ) : ℝ) := by
  classical
  funext row col
  unfold paperRoleColoredBoundaryMatrix partiteBoundaryMatrix
  simp_rw [C.paperEntryCompatible_globalRealization_iff]
  push_cast
  apply Finset.sum_congr rfl
  intro phi _
  by_cases hCompatible : partiteBoundaryEntryCompatible phi row col
  · simp only [hCompatible, if_true]
    unfold partiteAssignmentEdgeMonomial
    simp only [Rat.cast_prod, Rat.cast_intCast]
    apply Finset.prod_congr rfl
    intro e _
    exact hSign e (phi (G.source e)) (phi (G.target e))
  · simp [hCompatible]

#print axioms PaperRoleColoring.globalRealization
#print axioms PaperRoleColoring.paperEntryCompatible_globalRealization_iff
#print axioms paperRoleColoredBoundaryMatrix_eq_partiteBoundaryMatrix

end GraphMatrixReplica
