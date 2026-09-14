import GraphMatrix.DisjointPathDegreeBound

/-! # Separator/path dual certificates

This file gives the exact finite interface between C078's minimum role
separator and the vertex-disjoint path degree bound. Weak duality is proved
internally. Strong duality is isolated as a finite certificate.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A role set meets every right-to-left path. Singleton paths at roles in
both boundaries are included automatically. -/
def PartiteShape.IsRightLeftSeparator (G : PartiteShape)
    (cut : Finset (Fin G.roles)) : Prop :=
  ∀ (v : Fin G.roles), v ∈ G.rightBoundary →
    ∀ path : G.EdgePathToLeft v,
      ∃ o : Fin path.vertexCount, path.vertexAt o ∈ cut

/-- A separator of minimum cardinality. -/
def PartiteShape.IsMinimumRightLeftSeparator (G : PartiteShape)
    (cut : Finset (Fin G.roles)) : Prop :=
  G.IsRightLeftSeparator cut ∧
    ∀ other : Finset (Fin G.roles),
      G.IsRightLeftSeparator other → cut.card ≤ other.card

/-- The full role set is always a separator. -/
theorem PartiteShape.univ_isRightLeftSeparator (G : PartiteShape) :
    G.IsRightLeftSeparator Finset.univ := by
  intro v hRight path
  exact ⟨path.headOccurrence, Finset.mem_univ _⟩

/-- The finite collection of all right-left separators. -/
def PartiteShape.rightLeftSeparators (G : PartiteShape) :
    Finset (Finset (Fin G.roles)) := by
  classical
  exact Finset.univ.filter G.IsRightLeftSeparator

theorem PartiteShape.mem_rightLeftSeparators_iff
    (G : PartiteShape) (cut : Finset (Fin G.roles)) :
    cut ∈ G.rightLeftSeparators ↔ G.IsRightLeftSeparator cut := by
  classical
  simp [PartiteShape.rightLeftSeparators]

/-- A minimum right-left separator exists, including for empty or overlapping
boundaries. -/
theorem PartiteShape.exists_minimumRightLeftSeparator (G : PartiteShape) :
    ∃ cut : Finset (Fin G.roles), G.IsMinimumRightLeftSeparator cut := by
  classical
  have hNonempty : G.rightLeftSeparators.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    exact (G.mem_rightLeftSeparators_iff Finset.univ).2
      G.univ_isRightLeftSeparator
  obtain ⟨cut, hCutMem, hMinimal⟩ :=
    Finset.exists_min_image G.rightLeftSeparators Finset.card hNonempty
  refine ⟨cut, (G.mem_rightLeftSeparators_iff cut).1 hCutMem, ?_⟩
  intro other hOther
  exact hMinimal other
    ((G.mem_rightLeftSeparators_iff other).2 hOther)

/-- A chosen occurrence where a path meets a separator. -/
def PartiteShape.IsRightLeftSeparator.hitOccurrence
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (hCut : G.IsRightLeftSeparator cut)
    (v : Fin G.roles) (hRight : v ∈ G.rightBoundary)
    (path : G.EdgePathToLeft v) : Fin path.vertexCount :=
  Classical.choose (hCut v hRight path)

theorem PartiteShape.IsRightLeftSeparator.hitOccurrence_mem
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (hCut : G.IsRightLeftSeparator cut)
    (v : Fin G.roles) (hRight : v ∈ G.rightBoundary)
    (path : G.EdgePathToLeft v) :
    path.vertexAt (hCut.hitOccurrence v hRight path) ∈ cut :=
  Classical.choose_spec (hCut v hRight path)

/-- Select one cut vertex from every path. -/
def PartiteShape.VertexDisjointRightToLeftPaths.hitVertex
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (cut : Finset (Fin G.roles)) (hCut : G.IsRightLeftSeparator cut) :
    Fin s → cut := fun i =>
  ⟨(family.path i).vertexAt
      (hCut.hitOccurrence (family.start i) (family.startRight i)
        (family.path i)),
    hCut.hitOccurrence_mem (family.start i) (family.startRight i)
      (family.path i)⟩

/-- Distinct vertex-disjoint paths select distinct vertices of every
separator. -/
theorem PartiteShape.VertexDisjointRightToLeftPaths.hitVertex_injective
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (cut : Finset (Fin G.roles)) (hCut : G.IsRightLeftSeparator cut) :
    Function.Injective (family.hitVertex cut hCut) := by
  intro i j hij
  have hVertex :
      (family.path i).vertexAt
          (hCut.hitOccurrence (family.start i) (family.startRight i)
            (family.path i)) =
        (family.path j).vertexAt
          (hCut.hitOccurrence (family.start j) (family.startRight j)
            (family.path j)) :=
    congrArg Subtype.val hij
  have hOccurrence :
      (⟨i, hCut.hitOccurrence (family.start i) (family.startRight i)
          (family.path i)⟩ :
        Σ k : Fin s, Fin (family.path k).vertexCount) =
      ⟨j, hCut.hitOccurrence (family.start j) (family.startRight j)
          (family.path j)⟩ :=
    family.vertexAt_injective hVertex
  exact congrArg Sigma.fst hOccurrence

/-- Weak separator/path duality. -/
theorem PartiteShape.VertexDisjointRightToLeftPaths.pathCount_le_cutCard
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (cut : Finset (Fin G.roles)) (hCut : G.IsRightLeftSeparator cut) :
    s ≤ cut.card := by
  simpa using Fintype.card_le_of_injective
    (family.hitVertex cut hCut) (family.hitVertex_injective cut hCut)

/-- A finite strong-duality certificate: a minimum separator together with
an equally large vertex-disjoint right-to-left path family. -/
structure PartiteShape.RightLeftMengerCertificate (G : PartiteShape) where
  cut : Finset (Fin G.roles)
  cut_minimum : G.IsMinimumRightLeftSeparator cut
  paths : G.VertexDisjointRightToLeftPaths cut.card

/-- The path family in a Menger certificate is maximum among all
vertex-disjoint right-to-left path families. -/
theorem PartiteShape.RightLeftMengerCertificate.pathCount_le
    {G : PartiteShape} (certificate : G.RightLeftMengerCertificate)
    {t : ℕ} (family : G.VertexDisjointRightToLeftPaths t) :
    t ≤ certificate.cut.card :=
  family.pathCount_le_cutCard certificate.cut certificate.cut_minimum.1

/-- A strong-duality certificate supplies the sharp C078 degree bound with
the genuine minimum-separator cardinality. -/
theorem ReplicaState.totalBlockCount_le_minSeparator
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (certificate : G.RightLeftMengerCertificate) :
    S.totalBlockCount ≤
      (p + 1) * (G.roles - certificate.cut.card) + certificate.cut.card :=
  S.totalBlockCount_le_sharp hCovered certificate.paths


end GraphMatrixReplica
