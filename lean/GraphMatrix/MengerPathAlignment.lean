import GraphMatrix.FiniteMengerCertificate

/-! # Boundary-clean Menger paths for the paper model

The path family used by the existing replica bound only asks each path to
start in the right boundary and eventually finish in the left boundary.
BLNvH v2, Theorem A.11, uses the stronger normalization that every path
contains exactly one vertex of each boundary.  This file records that stronger
condition without changing the existing path type.

When the two boundaries overlap, a common-boundary vertex is represented by a
zero-edge singleton path.  For general paths, the remaining purely finite
graph operation is isolated as occurrence-preserving trimming data.  Such data
is already sufficient to transfer vertex-disjointness and all existing replica
degree bounds.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The final occurrence of an inductively represented path. -/
def PartiteShape.EdgePathToLeft.lastOccurrence
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : Fin path.vertexCount :=
  match path with
  | .finish _ _ => ⟨0, by simp [PartiteShape.EdgePathToLeft.vertexCount]⟩
  | .step _ _ _ _ tail => Fin.succ tail.lastOccurrence

@[simp] theorem PartiteShape.EdgePathToLeft.vertexAt_lastOccurrence_mem_left
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.vertexAt path.lastOccurrence ∈ G.leftBoundary := by
  induction path with
  | finish v hLeft => exact hLeft
  | step e w hAtStart hAtEnd tail ih => exact ih

theorem PartiteShape.EdgePathToLeft.lastOccurrence_val_add_one
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.lastOccurrence.val + 1 = path.vertexCount := by
  induction path with
  | finish => rfl
  | step e w hAtStart hAtEnd tail ih =>
      simp only [lastOccurrence, Fin.val_succ,
        PartiteShape.EdgePathToLeft.vertexCount]
      omega

/-- A path from a right-boundary start is boundary-clean when its head is its
unique right-boundary occurrence and its terminal occurrence is its unique
left-boundary occurrence.  Thus it contains exactly one point of each
boundary, as required in the paper. -/
def PartiteShape.EdgePathToLeft.IsBoundaryClean
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : Prop :=
  (∀ o, path.vertexAt o ∈ G.rightBoundary ↔ o = path.headOccurrence) ∧
  (∀ o, path.vertexAt o ∈ G.leftBoundary ↔ o = path.lastOccurrence)

def PartiteShape.EdgePathToLeft.rightBoundaryOccurrences
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : Finset (Fin path.vertexCount) :=
  Finset.univ.filter fun o => path.vertexAt o ∈ G.rightBoundary

def PartiteShape.EdgePathToLeft.leftBoundaryOccurrences
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) : Finset (Fin path.vertexCount) :=
  Finset.univ.filter fun o => path.vertexAt o ∈ G.leftBoundary

theorem PartiteShape.EdgePathToLeft.clean_rightBoundaryOccurrences
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean) :
    path.rightBoundaryOccurrences = {path.headOccurrence} := by
  classical
  ext o
  simp [PartiteShape.EdgePathToLeft.rightBoundaryOccurrences, hClean.1 o]

theorem PartiteShape.EdgePathToLeft.clean_leftBoundaryOccurrences
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean) :
    path.leftBoundaryOccurrences = {path.lastOccurrence} := by
  classical
  ext o
  simp [PartiteShape.EdgePathToLeft.leftBoundaryOccurrences, hClean.2 o]

/-- Literal cardinal formulation of “exactly one point in each boundary”. -/
theorem PartiteShape.EdgePathToLeft.clean_boundaryOccurrenceCards
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean) :
    path.rightBoundaryOccurrences.card = 1 ∧
      path.leftBoundaryOccurrences.card = 1 := by
  rw [path.clean_rightBoundaryOccurrences hClean,
    path.clean_leftBoundaryOccurrences hClean]
  simp

theorem PartiteShape.EdgePathToLeft.isBoundaryClean_head_mem_right
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean) :
    v ∈ G.rightBoundary := by
  simpa using (hClean.1 path.headOccurrence).2 rfl

theorem PartiteShape.EdgePathToLeft.isBoundaryClean_last_mem_left
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean) :
    path.vertexAt path.lastOccurrence ∈ G.leftBoundary :=
  (hClean.2 path.lastOccurrence).2 rfl

/-- A singleton at a common-boundary vertex is boundary-clean. -/
theorem PartiteShape.EdgePathToLeft.finish_isBoundaryClean
    {G : PartiteShape} {v : Fin G.roles}
    (hRight : v ∈ G.rightBoundary) (hLeft : v ∈ G.leftBoundary) :
    (PartiteShape.EdgePathToLeft.finish v hLeft).IsBoundaryClean := by
  constructor <;> intro o
  · constructor
    · intro _
      apply Fin.ext
      have ho : o.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using o.isLt
      simp [PartiteShape.EdgePathToLeft.headOccurrence]
      omega
    · intro _
      exact hRight
  · constructor
    · intro _
      apply Fin.ext
      have ho : o.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using o.isLt
      simp [PartiteShape.EdgePathToLeft.lastOccurrence]
      omega
    · intro _
      exact hLeft

/-- In a boundary-clean path, a common-boundary start forces the first and
last occurrences to coincide. -/
theorem PartiteShape.EdgePathToLeft.headOccurrence_eq_lastOccurrence_of_mem_left
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean)
    (hLeft : v ∈ G.leftBoundary) :
    path.headOccurrence = path.lastOccurrence := by
  exact (hClean.2 path.headOccurrence).1 (by simpa using hLeft)

/-- Consequently a boundary-clean path beginning in `U ∩ V` has one vertex
occurrence and hence no edge step. -/
theorem PartiteShape.EdgePathToLeft.vertexCount_eq_one_of_clean_start_mem_left
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean)
    (hLeft : v ∈ G.leftBoundary) :
    path.vertexCount = 1 := by
  have hEq := path.headOccurrence_eq_lastOccurrence_of_mem_left hClean hLeft
  have hVal : path.lastOccurrence.val = 0 := by
    simpa [PartiteShape.EdgePathToLeft.headOccurrence] using
      congrArg Fin.val hEq.symm
  have hLast := path.lastOccurrence_val_add_one
  omega

/-- Every non-endpoint occurrence of a boundary-clean path lies outside both
boundaries.  This is the form consumed by edge-ordering arguments such as the
`k₁+k₂` count in Theorem A.11. -/
theorem PartiteShape.EdgePathToLeft.clean_interior_not_mem_boundaries
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (hClean : path.IsBoundaryClean)
    (o : Fin path.vertexCount) (hHead : o ≠ path.headOccurrence)
    (hLast : o ≠ path.lastOccurrence) :
    path.vertexAt o ∉ G.rightBoundary ∧
      path.vertexAt o ∉ G.leftBoundary := by
  constructor
  · intro hRight
    exact hHead ((hClean.1 o).1 hRight)
  · intro hLeft
    exact hLast ((hClean.2 o).1 hLeft)

/-- Local occurrence-preserving trimming of one path. -/
structure PartiteShape.EdgePathToLeft.BoundaryCleanTrimming
    {G : PartiteShape} {v : Fin G.roles}
    (original : G.EdgePathToLeft v) where
  start : Fin G.roles
  startRight : start ∈ G.rightBoundary
  path : G.EdgePathToLeft start
  boundary_clean : path.IsBoundaryClean
  occurrenceEmbedding :
    Fin path.vertexCount ↪ Fin original.vertexCount
  vertexAt_occurrenceEmbedding : ∀ o,
    original.vertexAt (occurrenceEmbedding o) = path.vertexAt o

/-- The sharp, purely path-theoretic remaining lemma: a path whose head is in
the right boundary can be trimmed, without introducing vertices, until its
only right-boundary point is its new head and its only left-boundary point is
its terminal point. -/
def PartiteShape.EveryRightStartedPathHasBoundaryCleanTrimming
    (G : PartiteShape) : Prop :=
  ∀ {v : Fin G.roles} (_hRight : v ∈ G.rightBoundary)
    (path : G.EdgePathToLeft v),
    Nonempty (PartiteShape.EdgePathToLeft.BoundaryCleanTrimming path)

/-- A vertex-disjoint family satisfying the paper's boundary normalization. -/
structure PartiteShape.BoundaryCleanRightToLeftPaths
    (G : PartiteShape) (s : ℕ) where
  paths : G.VertexDisjointRightToLeftPaths s
  boundary_clean : ∀ i : Fin s, (paths.path i).IsBoundaryClean

namespace PartiteShape.BoundaryCleanRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

/-- Forgetting cleanliness gives exactly the pre-existing family type. -/
def forget (family : G.BoundaryCleanRightToLeftPaths s) :
    G.VertexDisjointRightToLeftPaths s :=
  family.paths

theorem pathCount_le_roles (family : G.BoundaryCleanRightToLeftPaths s) :
    s ≤ G.roles :=
  family.paths.pathCount_le_roles

theorem pathCount_le_cutCard (family : G.BoundaryCleanRightToLeftPaths s)
    (cut : Finset (Fin G.roles)) (hCut : G.IsRightLeftSeparator cut) :
    s ≤ cut.card :=
  family.paths.pathCount_le_cutCard cut hCut

end PartiteShape.BoundaryCleanRightToLeftPaths

/-- An occurrence-preserving refinement of an existing disjoint family.
The occurrence embeddings make the preservation of vertex-disjointness
checkable rather than implicit. -/
structure PartiteShape.BoundaryCleanTrimmingData
    {G : PartiteShape} {s : ℕ}
    (family : G.VertexDisjointRightToLeftPaths s) where
  start : Fin s → Fin G.roles
  startRight : ∀ i, start i ∈ G.rightBoundary
  path : ∀ i, G.EdgePathToLeft (start i)
  boundary_clean : ∀ i, (path i).IsBoundaryClean
  occurrenceEmbedding : ∀ i,
    Fin ((path i).vertexCount) ↪ Fin ((family.path i).vertexCount)
  vertexAt_occurrenceEmbedding : ∀ i o,
    (family.path i).vertexAt (occurrenceEmbedding i o) =
      (path i).vertexAt o

/-- The local trimming lemma supplies occurrence-preserving trimming data for
every member of an existing disjoint family. -/
def PartiteShape.boundaryCleanTrimmingDataOfPathTrimming
    {G : PartiteShape}
    (hTrim : G.EveryRightStartedPathHasBoundaryCleanTrimming)
    {s : ℕ} (family : G.VertexDisjointRightToLeftPaths s) :
    G.BoundaryCleanTrimmingData family := by
  classical
  let trim : ∀ i : Fin s,
      PartiteShape.EdgePathToLeft.BoundaryCleanTrimming (family.path i) :=
    fun i => Classical.choice (hTrim (family.startRight i) (family.path i))
  exact {
    start := fun i => (trim i).start
    startRight := fun i => (trim i).startRight
    path := fun i => (trim i).path
    boundary_clean := fun i => (trim i).boundary_clean
    occurrenceEmbedding := fun i => (trim i).occurrenceEmbedding
    vertexAt_occurrenceEmbedding := fun i o =>
      (trim i).vertexAt_occurrenceEmbedding o
  }

/-- Occurrence-preserving trimming data constructs a clean family of the same
cardinality. -/
def PartiteShape.BoundaryCleanTrimmingData.toBoundaryCleanFamily
    {G : PartiteShape} {s : ℕ}
    {family : G.VertexDisjointRightToLeftPaths s}
    (data : G.BoundaryCleanTrimmingData family) :
    G.BoundaryCleanRightToLeftPaths s where
  paths := {
    start := data.start
    startRight := data.startRight
    path := data.path
    vertexAt_injective := by
      rintro ⟨i, o₁⟩ ⟨j, o₂⟩ hVertex
      let old₁ : Σ i : Fin s, Fin ((family.path i).vertexCount) :=
        ⟨i, data.occurrenceEmbedding i o₁⟩
      let old₂ : Σ i : Fin s, Fin ((family.path i).vertexCount) :=
        ⟨j, data.occurrenceEmbedding j o₂⟩
      have hOldVertex :
          (family.path old₁.1).vertexAt old₁.2 =
            (family.path old₂.1).vertexAt old₂.2 := by
        rw [data.vertexAt_occurrenceEmbedding,
          data.vertexAt_occurrenceEmbedding]
        exact hVertex
      have hOld : old₁ = old₂ := family.vertexAt_injective hOldVertex
      have hIndex : i = j := by
        have h := congrArg (fun z => z.1) hOld
        simpa [old₁, old₂] using h
      subst j
      have hEmbedding : data.occurrenceEmbedding i o₁ =
          data.occurrenceEmbedding i o₂ := by
        change (⟨i, data.occurrenceEmbedding i o₁⟩ :
            Σ k : Fin s, Fin ((family.path k).vertexCount)) =
          ⟨i, data.occurrenceEmbedding i o₂⟩ at hOld
        exact eq_of_heq (Sigma.mk.inj_iff.mp hOld).2
      have hOccurrence : o₁ = o₂ :=
        (data.occurrenceEmbedding i).injective hEmbedding
      subst o₂
      rfl
  }
  boundary_clean := data.boundary_clean

/-- The exact remaining finite trimming obligation.  It is purely a theorem
about finite paths and boundary membership; no replica or probability object
occurs in it. -/
def PartiteShape.EveryDisjointFamilyHasBoundaryCleanTrimming
    (G : PartiteShape) : Prop :=
  ∀ {s : ℕ} (family : G.VertexDisjointRightToLeftPaths s),
    Nonempty (G.BoundaryCleanTrimmingData family)

theorem PartiteShape.everyFamilyTrimming_of_everyPathTrimming
    {G : PartiteShape}
    (hTrim : G.EveryRightStartedPathHasBoundaryCleanTrimming) :
    G.EveryDisjointFamilyHasBoundaryCleanTrimming := by
  intro s family
  exact ⟨G.boundaryCleanTrimmingDataOfPathTrimming hTrim family⟩

/-- Once the finite trimming obligation is supplied, every old-style family
has a paper-normalized family of the same size. -/
theorem PartiteShape.exists_boundaryCleanFamily_of_trimming
    {G : PartiteShape}
    (hTrim : G.EveryDisjointFamilyHasBoundaryCleanTrimming)
    {s : ℕ} (family : G.VertexDisjointRightToLeftPaths s) :
    Nonempty (G.BoundaryCleanRightToLeftPaths s) := by
  obtain ⟨data⟩ := hTrim family
  exact ⟨data.toBoundaryCleanFamily⟩

/-- A Menger certificate whose path side satisfies the paper normalization. -/
structure PartiteShape.BoundaryCleanRightLeftMengerCertificate
    (G : PartiteShape) where
  cut : Finset (Fin G.roles)
  cut_minimum : G.IsMinimumRightLeftSeparator cut
  paths : G.BoundaryCleanRightToLeftPaths cut.card

/-- Forgetting the normalization recovers the existing certificate. -/
def PartiteShape.BoundaryCleanRightLeftMengerCertificate.forget
    {G : PartiteShape}
    (certificate : G.BoundaryCleanRightLeftMengerCertificate) :
    G.RightLeftMengerCertificate where
  cut := certificate.cut
  cut_minimum := certificate.cut_minimum
  paths := certificate.paths.forget

/-- Trimming data for the path family in an existing certificate upgrades it
to the paper-normalized certificate with the same minimum separator. -/
def PartiteShape.RightLeftMengerCertificate.toBoundaryClean
    {G : PartiteShape} (certificate : G.RightLeftMengerCertificate)
    (data : G.BoundaryCleanTrimmingData certificate.paths) :
    G.BoundaryCleanRightLeftMengerCertificate where
  cut := certificate.cut
  cut_minimum := certificate.cut_minimum
  paths := data.toBoundaryCleanFamily

/-- Under the isolated finite trimming obligation, every existing Menger
certificate has a boundary-clean refinement. -/
theorem PartiteShape.nonempty_boundaryCleanMengerCertificate_of_trimming
    {G : PartiteShape}
    (hTrim : G.EveryDisjointFamilyHasBoundaryCleanTrimming)
    (certificate : G.RightLeftMengerCertificate) :
    Nonempty G.BoundaryCleanRightLeftMengerCertificate := by
  obtain ⟨data⟩ := hTrim certificate.paths
  exact ⟨certificate.toBoundaryClean data⟩

/-- The already-proved sharp replica degree bound applies after forgetting
the additional paper normalization. -/
theorem ReplicaState.totalBlockCount_le_of_boundaryCleanPaths
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.BoundaryCleanRightToLeftPaths s) :
    S.totalBlockCount ≤ (p + 1) * (G.roles - s) + s :=
  S.totalBlockCount_le_sharp hCovered family.forget

/-- Common-boundary vertices give the required singleton clean paths. -/
def PartiteShape.commonBoundaryCleanPathPacking (G : PartiteShape) :
    G.BoundaryCleanRightToLeftPaths
      (G.leftBoundary ∩ G.rightBoundary).card where
  paths := G.commonBoundaryPathPacking
  boundary_clean := by
    intro i
    apply PartiteShape.EdgePathToLeft.finish_isBoundaryClean
    · exact (Finset.mem_inter.mp
        (((G.leftBoundary ∩ G.rightBoundary).equivFin).symm i).2).2


end GraphMatrixReplica
