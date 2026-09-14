import R6.PaperMengerPathAlignment

/-! # Occurrence-preserving boundary trimming

This file discharges the finite path-normalization obligation isolated in
`PaperMengerPathAlignment`.  The recursive search stops at the first left
boundary occurrence and, while unwinding, discards everything before the last
right boundary occurrence.  In particular, a vertex in both boundaries is
trimmed to a singleton.
-/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.EdgePathToLeft

variable {G : PartiteShape}

/-- Add a new head occurrence to an occurrence embedding. -/
private def consEmbedding {m n : ℕ} (f : Fin m ↪ Fin n) :
    Fin (m + 1) ↪ Fin (n + 1) where
  toFun := Fin.cases 0 (fun o => Fin.succ (f o))
  inj' := by
    intro a b h
    cases a using Fin.cases with
    | zero =>
        cases b using Fin.cases with
        | zero => rfl
        | succ b =>
            have hv := congrArg Fin.val h
            simp at hv
    | succ a =>
        cases b using Fin.cases with
        | zero =>
            have hv := congrArg Fin.val h
            simp at hv
        | succ b =>
            simp only [Fin.cases_succ, Fin.succ_inj] at h
            rw [f.injective h]

/-- Shift an occurrence embedding after deleting the old head. -/
private def succEmbedding {m n : ℕ} (f : Fin m ↪ Fin n) :
    Fin m ↪ Fin (n + 1) where
  toFun := fun o => Fin.succ (f o)
  inj' := fun _ _ h => f.injective (Fin.succ_injective _ h)

/-- The unsuccessful branch of the backward search: an occurrence-preserving
prefix which stops at the first left boundary and contains no right-boundary
vertex.  Its start is definitionally the start of the original path. -/
private structure LeftCleanRightFreePrefix
    {v : Fin G.roles} (original : G.EdgePathToLeft v) where
  path : G.EdgePathToLeft v
  left_clean : ∀ o,
    path.vertexAt o ∈ G.leftBoundary ↔ o = path.lastOccurrence
  right_free : ∀ o, path.vertexAt o ∉ G.rightBoundary
  occurrenceEmbedding : Fin path.vertexCount ↪ Fin original.vertexCount
  vertexAt_occurrenceEmbedding : ∀ o,
    original.vertexAt (occurrenceEmbedding o) = path.vertexAt o

/-- If the current vertex is already in both boundaries, the required trim is
the zero-edge singleton at that occurrence. -/
private def singletonTrimming {v : Fin G.roles}
    (original : G.EdgePathToLeft v)
    (hRight : v ∈ G.rightBoundary) (hLeft : v ∈ G.leftBoundary) :
    BoundaryCleanTrimming original where
  start := v
  startRight := hRight
  path := .finish v hLeft
  boundary_clean := finish_isBoundaryClean hRight hLeft
  occurrenceEmbedding := {
    toFun := fun _ => original.headOccurrence
    inj' := by
      intro a b _
      apply Fin.ext
      have ha : a.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using a.isLt
      have hb : b.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using b.isLt
      omega
  }
  vertexAt_occurrenceEmbedding := by
    intro o
    change original.vertexAt original.headOccurrence = v
    exact original.vertexAt_headOccurrence

/-- A non-right vertex in the left boundary initializes the pending prefix. -/
private def singletonPrefix {v : Fin G.roles}
    (original : G.EdgePathToLeft v)
    (hLeft : v ∈ G.leftBoundary) (hNotRight : v ∉ G.rightBoundary) :
    LeftCleanRightFreePrefix original where
  path := .finish v hLeft
  left_clean := by
    intro o
    constructor
    · intro _
      apply Fin.ext
      change o.val = 0
      have ho : o.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using o.isLt
      omega
    · intro _
      exact hLeft
  right_free := fun _ => hNotRight
  occurrenceEmbedding := {
    toFun := fun _ => original.headOccurrence
    inj' := by
      intro a b _
      apply Fin.ext
      have ha : a.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using a.isLt
      have hb : b.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using b.isLt
      omega
  }
  vertexAt_occurrenceEmbedding := by
    intro o
    change original.vertexAt original.headOccurrence = v
    exact original.vertexAt_headOccurrence

/-- Delete one old head before an already found clean segment. -/
private def BoundaryCleanTrimming.dropOldHead
    {v w : Fin G.roles} {e : Fin G.edges}
    {hAtStart : G.EdgeIncident e v} {hAtEnd : G.EdgeIncident e w}
    {tail : G.EdgePathToLeft w}
    (trim : BoundaryCleanTrimming tail) :
    BoundaryCleanTrimming (.step e w hAtStart hAtEnd tail) where
  start := trim.start
  startRight := trim.startRight
  path := trim.path
  boundary_clean := trim.boundary_clean
  occurrenceEmbedding := succEmbedding trim.occurrenceEmbedding
  vertexAt_occurrenceEmbedding := by
    intro o
    exact trim.vertexAt_occurrenceEmbedding o

/-- Prepend a vertex outside both boundaries to a pending prefix. -/
private def LeftCleanRightFreePrefix.prepend
    {v w : Fin G.roles} {e : Fin G.edges}
    {hAtStart : G.EdgeIncident e v} {hAtEnd : G.EdgeIncident e w}
    {tail : G.EdgePathToLeft w}
    (pending : LeftCleanRightFreePrefix tail)
    (hNotLeft : v ∉ G.leftBoundary) (hNotRight : v ∉ G.rightBoundary) :
    LeftCleanRightFreePrefix (.step e w hAtStart hAtEnd tail) where
  path := .step e w hAtStart hAtEnd pending.path
  left_clean := by
    intro o
    cases o using Fin.cases with
    | zero =>
        constructor
        · exact fun h => (hNotLeft h).elim
        · intro h
          have : (0 : ℕ) = pending.path.lastOccurrence.val + 1 :=
            congrArg Fin.val h
          omega
    | succ o =>
        change pending.path.vertexAt o ∈ G.leftBoundary ↔
          Fin.succ o = Fin.succ pending.path.lastOccurrence
        simpa only [Fin.succ_inj] using pending.left_clean o
  right_free := by
    intro o
    cases o using Fin.cases with
    | zero => exact hNotRight
    | succ o => exact pending.right_free o
  occurrenceEmbedding := consEmbedding pending.occurrenceEmbedding
  vertexAt_occurrenceEmbedding := by
    intro o
    cases o using Fin.cases with
    | zero => rfl
    | succ o => exact pending.vertexAt_occurrenceEmbedding o

/-- When the unwinding search first meets a right-boundary vertex, prepend it
to the pending right-free prefix.  It is then the unique right occurrence. -/
private def LeftCleanRightFreePrefix.closeAtRight
    {v w : Fin G.roles} {e : Fin G.edges}
    {hAtStart : G.EdgeIncident e v} {hAtEnd : G.EdgeIncident e w}
    {tail : G.EdgePathToLeft w}
    (pending : LeftCleanRightFreePrefix tail)
    (hNotLeft : v ∉ G.leftBoundary) (hRight : v ∈ G.rightBoundary) :
    BoundaryCleanTrimming (.step e w hAtStart hAtEnd tail) where
  start := v
  startRight := hRight
  path := .step e w hAtStart hAtEnd pending.path
  boundary_clean := by
    constructor
    · intro o
      cases o using Fin.cases with
      | zero => exact iff_of_true hRight rfl
      | succ o =>
          constructor
          · exact fun h => (pending.right_free o h).elim
          · intro h
            have : o.val + 1 = 0 := congrArg Fin.val h
            omega
    · intro o
      cases o using Fin.cases with
      | zero =>
          constructor
          · exact fun h => (hNotLeft h).elim
          · intro h
            have : (0 : ℕ) = pending.path.lastOccurrence.val + 1 :=
              congrArg Fin.val h
            omega
      | succ o =>
          change pending.path.vertexAt o ∈ G.leftBoundary ↔
            Fin.succ o = Fin.succ pending.path.lastOccurrence
          simpa only [Fin.succ_inj] using pending.left_clean o
  occurrenceEmbedding := consEmbedding pending.occurrenceEmbedding
  vertexAt_occurrenceEmbedding := by
    intro o
    cases o using Fin.cases with
    | zero => rfl
    | succ o => exact pending.vertexAt_occurrenceEmbedding o

/-- Recursive earliest-left/last-right search.  A successful branch is a
clean trimming; the other branch is a right-free prefix which a preceding
right-boundary vertex can close. -/
private def boundaryCleanSearch :
    {v : Fin G.roles} → (path : G.EdgePathToLeft v) →
      BoundaryCleanTrimming path ⊕ LeftCleanRightFreePrefix path
  | v, path =>
      if hLeft : v ∈ G.leftBoundary then
        if hRight : v ∈ G.rightBoundary then
          Sum.inl (singletonTrimming path hRight hLeft)
        else
          Sum.inr (singletonPrefix path hLeft hRight)
      else
        match path with
        | .finish v hFinish => (hLeft hFinish).elim
        | .step e w hAtStart hAtEnd tail =>
            match boundaryCleanSearch tail with
            | Sum.inl trim => Sum.inl trim.dropOldHead
            | Sum.inr pending =>
                if hRight : v ∈ G.rightBoundary then
                  Sum.inl (pending.closeAtRight hLeft hRight)
                else
                  Sum.inr (pending.prepend hLeft hRight)
termination_by v path => path.vertexCount
decreasing_by simp [PartiteShape.EdgePathToLeft.vertexCount]

/-- Every right-started finite edge path admits the occurrence-preserving
boundary-clean trimming required by `PaperMengerPathAlignment`. -/
theorem everyRightStartedPathHasBoundaryCleanTrimming (G : PartiteShape) :
    G.EveryRightStartedPathHasBoundaryCleanTrimming := by
  intro v hRight path
  cases boundaryCleanSearch path with
  | inl trim => exact ⟨trim⟩
  | inr pending =>
      exact (pending.right_free pending.path.headOccurrence
        (by simpa using hRight)).elim

end PartiteShape.EdgePathToLeft

/-- Every old vertex-disjoint family has an occurrence-preserving clean
family of exactly the same cardinality. -/
theorem PartiteShape.everyDisjointFamilyHasBoundaryCleanTrimming
    (G : PartiteShape) :
    G.EveryDisjointFamilyHasBoundaryCleanTrimming :=
  G.everyFamilyTrimming_of_everyPathTrimming
    (PartiteShape.EdgePathToLeft.everyRightStartedPathHasBoundaryCleanTrimming G)

theorem PartiteShape.nonemptyBoundaryCleanFamily
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s) :
    Nonempty (G.BoundaryCleanRightToLeftPaths s) :=
  G.exists_boundaryCleanFamily_of_trimming
    (G.everyDisjointFamilyHasBoundaryCleanTrimming) family

/-- Every pre-existing Menger certificate upgrades to a boundary-clean
certificate while retaining its minimum separator and path count. -/
theorem PartiteShape.RightLeftMengerCertificate.nonemptyBoundaryClean
    {G : PartiteShape} (certificate : G.RightLeftMengerCertificate) :
    Nonempty G.BoundaryCleanRightLeftMengerCertificate :=
  G.nonempty_boundaryCleanMengerCertificate_of_trimming
    G.everyDisjointFamilyHasBoundaryCleanTrimming certificate

#print axioms PartiteShape.EdgePathToLeft.everyRightStartedPathHasBoundaryCleanTrimming
#print axioms PartiteShape.everyDisjointFamilyHasBoundaryCleanTrimming
#print axioms PartiteShape.nonemptyBoundaryCleanFamily
#print axioms PartiteShape.RightLeftMengerCertificate.nonemptyBoundaryClean

end GraphMatrixReplica
