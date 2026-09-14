import R6.SeparatorPathCertificate

/-! # Finite path-packing witnesses toward the Menger certificate

Mathlib currently has no packaged vertex-Menger theorem that directly
matches `PartiteShape.EdgePathToLeft`.  This file therefore makes the finite
optimization problem internal: the maximum cardinality of a vertex-disjoint
right-to-left path family exists, is bounded by every separator, and is
attained.  It also proves strong duality (hence an actual
`RightLeftMengerCertificate`) when either boundary is contained in the other.

The remaining general obligation is precisely equality between the packing
number and the already-defined minimum-separator number.  No graph-matrix or
replica assumption is involved in that purely finite graph statement.
-/

noncomputable section

namespace GraphMatrixReplica

/-- There is a vertex-disjoint right-to-left path family of size `s`. -/
def PartiteShape.HasRightLeftPathPacking (G : PartiteShape) (s : ℕ) : Prop :=
  Nonempty (G.VertexDisjointRightToLeftPaths s)

/-- The empty path family is always available. -/
def PartiteShape.emptyRightLeftPathPacking (G : PartiteShape) :
    G.VertexDisjointRightToLeftPaths 0 where
  start := Fin.elim0
  startRight := fun i => Fin.elim0 i
  path := fun i => Fin.elim0 i
  vertexAt_injective := by
    intro z
    exact Fin.elim0 z.1

theorem PartiteShape.hasRightLeftPathPacking_zero (G : PartiteShape) :
    G.HasRightLeftPathPacking 0 :=
  ⟨G.emptyRightLeftPathPacking⟩

/-- The largest cardinality of a vertex-disjoint right-to-left path family.
Existence is obtained from the explicit empty family and the uniform bound by
the finite role set. -/
def PartiteShape.rightLeftPathPackingNumber (G : PartiteShape) : ℕ :=
  by
    classical
    exact Nat.findGreatest G.HasRightLeftPathPacking G.roles

theorem PartiteShape.rightLeftPathPackingNumber_le_roles (G : PartiteShape) :
    G.rightLeftPathPackingNumber ≤ G.roles :=
  by
    classical
    exact Nat.findGreatest_le G.roles

/-- The path-packing optimum is attained. -/
theorem PartiteShape.hasRightLeftPathPacking_packingNumber (G : PartiteShape) :
    G.HasRightLeftPathPacking G.rightLeftPathPackingNumber := by
  classical
  exact Nat.findGreatest_spec (P := G.HasRightLeftPathPacking)
    (Nat.zero_le G.roles) G.hasRightLeftPathPacking_zero

/-- A chosen maximum-cardinality path packing. -/
def PartiteShape.maximumRightLeftPathPacking (G : PartiteShape) :
    G.VertexDisjointRightToLeftPaths G.rightLeftPathPackingNumber :=
  Classical.choice G.hasRightLeftPathPacking_packingNumber

/-- Every concrete path packing is bounded by the finite optimum. -/
theorem PartiteShape.pathCount_le_rightLeftPathPackingNumber
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s) :
    s ≤ G.rightLeftPathPackingNumber := by
  classical
  exact Nat.le_findGreatest family.pathCount_le_roles
    (show G.HasRightLeftPathPacking s from ⟨family⟩)

/-- A chosen minimum separator, whose existence was proved in the preceding
module. -/
def PartiteShape.minimumRightLeftSeparator (G : PartiteShape) :
    Finset (Fin G.roles) :=
  Classical.choose G.exists_minimumRightLeftSeparator

theorem PartiteShape.minimumRightLeftSeparator_isMinimum (G : PartiteShape) :
    G.IsMinimumRightLeftSeparator G.minimumRightLeftSeparator :=
  Classical.choose_spec G.exists_minimumRightLeftSeparator

/-- Cardinality of a minimum right-left vertex separator. -/
def PartiteShape.rightLeftSeparatorNumber (G : PartiteShape) : ℕ :=
  G.minimumRightLeftSeparator.card

/-- Weak duality for the two internally attained finite optima. -/
theorem PartiteShape.rightLeftPathPackingNumber_le_separatorNumber
    (G : PartiteShape) :
    G.rightLeftPathPackingNumber ≤ G.rightLeftSeparatorNumber := by
  exact G.maximumRightLeftPathPacking.pathCount_le_cutCard
    G.minimumRightLeftSeparator
    G.minimumRightLeftSeparator_isMinimum.1

/-- Equality of the two finite optima constructs the required strong-duality
certificate; no additional choice or existence hypothesis remains. -/
def PartiteShape.rightLeftMengerCertificateOfEquality
    (G : PartiteShape)
    (h : G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber) :
    G.RightLeftMengerCertificate where
  cut := G.minimumRightLeftSeparator
  cut_minimum := G.minimumRightLeftSeparator_isMinimum
  paths := by
    change G.VertexDisjointRightToLeftPaths G.rightLeftSeparatorNumber
    rw [← h]
    exact G.maximumRightLeftPathPacking

/-- Conversely, any Menger certificate forces equality of the two internally
defined finite optima. -/
theorem PartiteShape.rightLeftOptima_eq_of_mengerCertificate
    {G : PartiteShape} (certificate : G.RightLeftMengerCertificate) :
    G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber := by
  apply Nat.le_antisymm G.rightLeftPathPackingNumber_le_separatorNumber
  have hPacking : certificate.cut.card ≤ G.rightLeftPathPackingNumber :=
    G.pathCount_le_rightLeftPathPackingNumber certificate.paths
  have hMinimum : G.rightLeftSeparatorNumber ≤ certificate.cut.card :=
    G.minimumRightLeftSeparator_isMinimum.2 certificate.cut
      certificate.cut_minimum.1
  exact hMinimum.trans hPacking

/-- The exact unresolved graph-theoretic statement is equivalent to
nonemptiness of the certificate type. -/
theorem PartiteShape.nonempty_rightLeftMengerCertificate_iff_optima_eq
    (G : PartiteShape) :
    Nonempty G.RightLeftMengerCertificate ↔
      G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber := by
  constructor
  · rintro ⟨certificate⟩
    exact G.rightLeftOptima_eq_of_mengerCertificate certificate
  · intro h
    exact ⟨G.rightLeftMengerCertificateOfEquality h⟩

/-- The right boundary itself is always a right-left separator because each
path contains its starting vertex. -/
theorem PartiteShape.rightBoundary_isRightLeftSeparator (G : PartiteShape) :
    G.IsRightLeftSeparator G.rightBoundary := by
  intro v hRight path
  exact ⟨path.headOccurrence, by simpa using hRight⟩

/-- Every path contains an occurrence in the left boundary (its recursively
recorded final vertex). -/
theorem PartiteShape.EdgePathToLeft.exists_vertexAt_mem_leftBoundary
    {G : PartiteShape} {v : Fin G.roles} (path : G.EdgePathToLeft v) :
    ∃ o : Fin path.vertexCount, path.vertexAt o ∈ G.leftBoundary := by
  induction path with
  | finish v hLeft =>
      exact ⟨⟨0, by simp [PartiteShape.EdgePathToLeft.vertexCount]⟩, hLeft⟩
  | @step v e w hAtStart hAtEnd tail ih =>
      obtain ⟨o, ho⟩ := ih
      exact ⟨Fin.succ o, ho⟩

/-- The left boundary is also always a separator. -/
theorem PartiteShape.leftBoundary_isRightLeftSeparator (G : PartiteShape) :
    G.IsRightLeftSeparator G.leftBoundary := by
  intro v hRight path
  exact path.exists_vertexAt_mem_leftBoundary

/-- Singleton paths indexed by any finite set of roles lying in both
boundaries form a vertex-disjoint family. -/
def PartiteShape.singletonBoundaryPathPacking
    (G : PartiteShape) (vertices : Finset (Fin G.roles))
    (hRight : vertices ⊆ G.rightBoundary)
    (hLeft : vertices ⊆ G.leftBoundary) :
    G.VertexDisjointRightToLeftPaths vertices.card where
  start := fun i => ((vertices.equivFin).symm i).1
  startRight := fun i => hRight (((vertices.equivFin).symm i).2)
  path := fun i => .finish _ (hLeft (((vertices.equivFin).symm i).2))
  vertexAt_injective := by
    rintro ⟨i, oi⟩ ⟨j, oj⟩ hij
    have hvalue : ((vertices.equivFin).symm i) =
        ((vertices.equivFin).symm j) := by
      apply Subtype.ext
      exact hij
    have hindex : i = j := (vertices.equivFin).symm.injective hvalue
    subst j
    have hoi : oi.val < 1 := by
      simpa [PartiteShape.EdgePathToLeft.vertexCount] using oi.isLt
    have hoj : oj.val < 1 := by
      simpa [PartiteShape.EdgePathToLeft.vertexCount] using oj.isLt
    have hoccurrence : oi = oj := by
      apply Fin.ext
      omega
    subst oj
    rfl

/-- The common boundary supplies that many disjoint singleton paths. -/
def PartiteShape.commonBoundaryPathPacking (G : PartiteShape) :
    G.VertexDisjointRightToLeftPaths
      (G.leftBoundary ∩ G.rightBoundary).card :=
  G.singletonBoundaryPathPacking
    (G.leftBoundary ∩ G.rightBoundary)
    (by intro v hv; exact (Finset.mem_inter.mp hv).2)
    (by intro v hv; exact (Finset.mem_inter.mp hv).1)

theorem PartiteShape.commonBoundary_card_le_pathPackingNumber
    (G : PartiteShape) :
    (G.leftBoundary ∩ G.rightBoundary).card ≤
      G.rightLeftPathPackingNumber :=
  G.pathCount_le_rightLeftPathPackingNumber G.commonBoundaryPathPacking

/-- If every right-boundary role is already left-boundary, the right boundary
is a minimum separator and its singleton paths give a full Menger
certificate. -/
def PartiteShape.rightLeftMengerCertificate_of_rightBoundary_subset_left
    (G : PartiteShape) (h : G.rightBoundary ⊆ G.leftBoundary) :
    G.RightLeftMengerCertificate where
  cut := G.rightBoundary
  cut_minimum := by
    refine ⟨G.rightBoundary_isRightLeftSeparator, ?_⟩
    intro other hOther
    let family := G.singletonBoundaryPathPacking G.rightBoundary
      (fun _ hv => hv) h
    exact family.pathCount_le_cutCard other hOther
  paths := G.singletonBoundaryPathPacking G.rightBoundary
    (fun _ hv => hv) h

/-- Symmetric nested-boundary case, using the left boundary as the minimum
separator and singleton paths. -/
def PartiteShape.rightLeftMengerCertificate_of_leftBoundary_subset_right
    (G : PartiteShape) (h : G.leftBoundary ⊆ G.rightBoundary) :
    G.RightLeftMengerCertificate where
  cut := G.leftBoundary
  cut_minimum := by
    refine ⟨G.leftBoundary_isRightLeftSeparator, ?_⟩
    intro other hOther
    let family := G.singletonBoundaryPathPacking G.leftBoundary h
      (fun _ hv => hv)
    exact family.pathCount_le_cutCard other hOther
  paths := G.singletonBoundaryPathPacking G.leftBoundary h
    (fun _ hv => hv)

#print axioms PartiteShape.hasRightLeftPathPacking_packingNumber
#print axioms PartiteShape.rightLeftPathPackingNumber_le_separatorNumber
#print axioms PartiteShape.nonempty_rightLeftMengerCertificate_iff_optima_eq
#print axioms
  PartiteShape.rightLeftMengerCertificate_of_rightBoundary_subset_left
#print axioms
  PartiteShape.rightLeftMengerCertificate_of_leftBoundary_subset_right

end GraphMatrixReplica
