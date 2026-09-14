import GraphMatrix.MengerPathTrimming

/-! # Finite Menger strong-duality augmentation core

This file records the constructive core needed for a fully internal proof of
finite vertex Menger duality for `PartiteShape`.  It audits the exact existing
path representation: arbitrary `EdgePathToLeft` terms may repeat vertices,
while a `VertexDisjointRightToLeftPaths` family cannot repeat a role either
within or between paths.

We prove the delicate family-extension operation without changing the old
types.  Thus a new internally simple path avoiding all roles of a packing
strictly augments it.  Consequently the roles used by a maximum packing meet
every internally simple right-left path.  We also isolate the standard final
augment-or-cut interface and prove that it supplies both the old and the
boundary-clean Menger certificates.
-/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.EdgePathToLeft

variable {G : PartiteShape} {v : Fin G.roles}

/-- Internal simplicity for the old inductive path representation. -/
def IsVertexSimple (path : G.EdgePathToLeft v) : Prop :=
  Function.Injective path.vertexAt

theorem finish_isVertexSimple (hLeft : v ∈ G.leftBoundary) :
    (PartiteShape.EdgePathToLeft.finish v hLeft).IsVertexSimple := by
  intro a b _
  apply Fin.ext
  have ha : a.val < 1 := by
    simpa [PartiteShape.EdgePathToLeft.vertexCount] using a.isLt
  have hb : b.val < 1 := by
    simpa [PartiteShape.EdgePathToLeft.vertexCount] using b.isLt
  omega

end PartiteShape.EdgePathToLeft

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

abbrev Occurrence (family : G.VertexDisjointRightToLeftPaths s) :=
  Σ i : Fin s, Fin ((family.path i).vertexCount)

def occurrenceRole (family : G.VertexDisjointRightToLeftPaths s) :
    family.Occurrence → Fin G.roles :=
  fun z => (family.path z.1).vertexAt z.2

/-- Deduplicated set of all roles used by a path packing. -/
def usedRoles (family : G.VertexDisjointRightToLeftPaths s) :
    Finset (Fin G.roles) := by
  classical
  exact Finset.univ.image family.occurrenceRole

theorem mem_usedRoles_iff (family : G.VertexDisjointRightToLeftPaths s)
    (v : Fin G.roles) :
    v ∈ family.usedRoles ↔
      ∃ i : Fin s, ∃ o : Fin ((family.path i).vertexCount),
        (family.path i).vertexAt o = v := by
  classical
  simp [usedRoles, occurrenceRole]

theorem usedRoles_card
    (family : G.VertexDisjointRightToLeftPaths s) :
    family.usedRoles.card = Fintype.card family.Occurrence := by
  classical
  calc
    family.usedRoles.card =
        (Finset.univ : Finset family.Occurrence).card := by
      exact Finset.card_image_iff.mpr family.vertexAt_injective.injOn
    _ = Fintype.card family.Occurrence := Finset.card_univ

/-- The existing global occurrence injection in a packed family in particular
rules out repeated roles inside each one of its paths. -/
theorem path_isVertexSimple
    (family : G.VertexDisjointRightToLeftPaths s) (i : Fin s) :
    (family.path i).IsVertexSimple := by
  intro oi oj hVertex
  have hOccurrence :
      (⟨i, oi⟩ : family.Occurrence) = ⟨i, oj⟩ :=
    family.vertexAt_injective hVertex
  cases hOccurrence
  rfl

/-- A path avoids a packing when none of its vertex occurrences is an old
used role. -/
def Avoids {v : Fin G.roles} (family : G.VertexDisjointRightToLeftPaths s)
    (path : G.EdgePathToLeft v) : Prop :=
  ∀ o, path.vertexAt o ∉ family.usedRoles

/-- Prepend a genuinely new, internally simple path to an old disjoint
family.  This is the basic strict augmentation operation. -/
def prependDisjointPath
    (family : G.VertexDisjointRightToLeftPaths s)
    {v : Fin G.roles} (hRight : v ∈ G.rightBoundary)
    (newPath : G.EdgePathToLeft v)
    (hSimple : newPath.IsVertexSimple)
    (hAvoids : family.Avoids newPath) :
    G.VertexDisjointRightToLeftPaths (s + 1) where
  start := Fin.cases v family.start
  startRight := Fin.cases hRight family.startRight
  path := Fin.cases newPath family.path
  vertexAt_injective := by
    rintro ⟨i, oi⟩ ⟨j, oj⟩ hVertex
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero =>
            have hOccurrence : oi = oj := hSimple hVertex
            subst oj
            rfl
        | succ j =>
            exfalso
            apply hAvoids oi
            rw [family.mem_usedRoles_iff]
            exact ⟨j, oj, hVertex.symm⟩
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            exfalso
            apply hAvoids oj
            rw [family.mem_usedRoles_iff]
            exact ⟨i, oi, hVertex⟩
        | succ j =>
            have hOld :
                (⟨i, oi⟩ : family.Occurrence) = ⟨j, oj⟩ :=
              family.vertexAt_injective hVertex
            cases hOld
            rfl

/-- The used-role set of a packing meets every internally simple right-left
path exactly when no strict augmentation by an avoiding path is possible. -/
def UsedRolesMeetEverySimplePath
    (family : G.VertexDisjointRightToLeftPaths s) : Prop :=
  ∀ (v : Fin G.roles), v ∈ G.rightBoundary →
    ∀ path : G.EdgePathToLeft v, path.IsVertexSimple →
      ∃ o : Fin path.vertexCount, path.vertexAt o ∈ family.usedRoles

theorem usedRoles_meetEverySimplePath_of_no_augmentation
    (family : G.VertexDisjointRightToLeftPaths s)
    (hMax : ¬ G.HasRightLeftPathPacking (s + 1)) :
    family.UsedRolesMeetEverySimplePath := by
  classical
  intro v hRight path hSimple
  by_contra hNoHit
  have hAvoids : family.Avoids path := by
    intro o ho
    exact hNoHit ⟨o, ho⟩
  apply hMax
  exact ⟨family.prependDisjointPath hRight path hSimple hAvoids⟩

theorem maximum_usedRoles_meetEverySimplePath (G : PartiteShape) :
    G.maximumRightLeftPathPacking.UsedRolesMeetEverySimplePath := by
  apply usedRoles_meetEverySimplePath_of_no_augmentation
  intro hLarger
  obtain ⟨larger⟩ := hLarger
  have hBound := G.pathCount_le_rightLeftPathPackingNumber larger
  omega

end PartiteShape.VertexDisjointRightToLeftPaths

namespace PartiteShape

/-- Every separator contains the common boundary: the singleton path at a
common role has only that occurrence. -/
theorem commonBoundary_subset_everySeparator
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (hCut : G.IsRightLeftSeparator cut) :
    G.leftBoundary ∩ G.rightBoundary ⊆ cut := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hLeft, hRight⟩
  obtain ⟨o, ho⟩ := hCut v hRight
    (PartiteShape.EdgePathToLeft.finish v hLeft)
  simpa [PartiteShape.EdgePathToLeft.vertexAt] using ho

theorem commonBoundary_card_le_everySeparator
    (G : PartiteShape) (cut : Finset (Fin G.roles))
    (hCut : G.IsRightLeftSeparator cut) :
    (G.leftBoundary ∩ G.rightBoundary).card ≤ cut.card :=
  Finset.card_le_card (G.commonBoundary_subset_everySeparator cut hCut)

/-- The exact output of one finite augmenting-path search: either the current
packing can be enlarged, or the search returns a separator no larger than the
current number of paths. -/
def HasMengerAugmentOrCut (G : PartiteShape) : Prop :=
  ∀ {s : ℕ} (_family : G.VertexDisjointRightToLeftPaths s),
    G.HasRightLeftPathPacking (s + 1) ∨
      ∃ cut : Finset (Fin G.roles),
        G.IsRightLeftSeparator cut ∧ cut.card ≤ s

/-- The augment-or-cut output at a maximum packing forces equality of the two
finite optima. -/
theorem rightLeftOptima_eq_of_augmentOrCut
    (G : PartiteShape) (hSearch : G.HasMengerAugmentOrCut) :
    G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber := by
  apply Nat.le_antisymm G.rightLeftPathPackingNumber_le_separatorNumber
  rcases hSearch G.maximumRightLeftPathPacking with hAugment | hCut
  · obtain ⟨larger⟩ := hAugment
    have hBound := G.pathCount_le_rightLeftPathPackingNumber larger
    omega
  · obtain ⟨cut, hSeparator, hCard⟩ := hCut
    exact (G.minimumRightLeftSeparator_isMinimum.2 cut hSeparator).trans hCard

/-- A finite augment-or-cut search constructs the old Menger certificate. -/
def rightLeftMengerCertificateOfAugmentOrCut
    (G : PartiteShape) (hSearch : G.HasMengerAugmentOrCut) :
    G.RightLeftMengerCertificate :=
  G.rightLeftMengerCertificateOfEquality
    (G.rightLeftOptima_eq_of_augmentOrCut hSearch)

/-- Together with the now-proved path trimming theorem, the same search also
constructs the paper-normalized clean certificate. -/
def boundaryCleanRightLeftMengerCertificateOfAugmentOrCut
    (G : PartiteShape) (hSearch : G.HasMengerAugmentOrCut) :
    G.BoundaryCleanRightLeftMengerCertificate :=
  Classical.choice
    (G.rightLeftMengerCertificateOfAugmentOrCut hSearch).nonemptyBoundaryClean

/-- It suffices to construct the small separator only for the chosen maximum
packing; this is the residual-reachability cut obligation in the usual
augmenting-path proof. -/
def HasMaximumPackingCut (G : PartiteShape) : Prop :=
  ∃ cut : Finset (Fin G.roles),
    G.IsRightLeftSeparator cut ∧
      cut.card ≤ G.rightLeftPathPackingNumber

theorem rightLeftOptima_eq_of_maximumPackingCut
    (G : PartiteShape) (hCut : G.HasMaximumPackingCut) :
    G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber := by
  apply Nat.le_antisymm G.rightLeftPathPackingNumber_le_separatorNumber
  obtain ⟨cut, hSeparator, hCard⟩ := hCut
  exact (G.minimumRightLeftSeparator_isMinimum.2 cut hSeparator).trans hCard

/-- The residual-cut obligation is not merely sufficient: it is exactly the
remaining strong-duality statement after the finite optima and a maximum
packing have been constructed. -/
theorem hasMaximumPackingCut_iff_optima_eq (G : PartiteShape) :
    G.HasMaximumPackingCut ↔
      G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber := by
  constructor
  · exact G.rightLeftOptima_eq_of_maximumPackingCut
  · intro hEquality
    refine ⟨G.minimumRightLeftSeparator,
      G.minimumRightLeftSeparator_isMinimum.1, ?_⟩
    simpa [rightLeftSeparatorNumber] using hEquality.ge

def rightLeftMengerCertificateOfMaximumPackingCut
    (G : PartiteShape) (hCut : G.HasMaximumPackingCut) :
    G.RightLeftMengerCertificate :=
  G.rightLeftMengerCertificateOfEquality
    (G.rightLeftOptima_eq_of_maximumPackingCut hCut)

def boundaryCleanRightLeftMengerCertificateOfMaximumPackingCut
    (G : PartiteShape) (hCut : G.HasMaximumPackingCut) :
    G.BoundaryCleanRightLeftMengerCertificate :=
  Classical.choice
    (G.rightLeftMengerCertificateOfMaximumPackingCut hCut).nonemptyBoundaryClean


end PartiteShape

end GraphMatrixReplica
