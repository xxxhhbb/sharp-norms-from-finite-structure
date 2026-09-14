import R6.U3PathBudgets
import R6.C079PathAuxMomentShape
import R6.PaperIntermediateEdgeOrdering
import R6.PaperMengerPathAlignment

/-!
# Actual U3 path restriction

This scratch module constructs the canonical left-to-right embedding of each
actual right-to-left path in a vertex-disjoint family.  It is the geometric
part of the missing `PathFiber` product injection.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

variable {G : PartiteShape} {p s : Nat}

namespace PartiteShape.EdgePathToLeft

/-- The vertex occurrence at the initial endpoint of a path-edge occurrence. -/
def edgeStartOccurrence {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (o : Fin path.edgeCount) : Fin path.vertexCount :=
  ⟨o.val, by
    have hCount := path.edgeCount_add_one_eq_vertexCount
    omega⟩

@[simp] theorem edgeStartOccurrence_val {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (o : Fin path.edgeCount) :
    (path.edgeStartOccurrence o).val = o.val := rfl

/-- The selected edge is incident to the occurrence immediately before its
`edgeEndOccurrence`. -/
theorem edgeAt_incident_edgeStart {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (o : Fin path.edgeCount) :
    G.EdgeIncident (path.edgeAt o)
      (path.vertexAt (path.edgeStartOccurrence o)) := by
  induction path with
  | finish v hLeft => exact Fin.elim0 o
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o using Fin.cases with
      | zero =>
          change G.EdgeIncident e v
          exact hAtStart
      | succ o =>
          change G.EdgeIncident (tail.edgeAt o)
            (tail.vertexAt (tail.edgeStartOccurrence o))
          exact ih o

/-- Two distinct incident endpoints determine one of the two allowed edge
orientations. -/
theorem edgeAt_endpointMatch_of_ne {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (o : Fin path.edgeCount)
    (hne : path.vertexAt (path.edgeStartOccurrence o) ≠
      path.vertexAt (path.edgeEndOccurrence o)) :
    (G.source (path.edgeAt o) =
        path.vertexAt (path.edgeStartOccurrence o) ∧
      G.target (path.edgeAt o) =
        path.vertexAt (path.edgeEndOccurrence o)) ∨
    (G.source (path.edgeAt o) =
        path.vertexAt (path.edgeEndOccurrence o) ∧
      G.target (path.edgeAt o) =
        path.vertexAt (path.edgeStartOccurrence o)) := by
  have hs := path.edgeAt_incident_edgeStart o
  have ht := path.edgeAt_incident_edgeEnd o
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact False.elim (hne (hs.symm.trans ht))
  · exact Or.inl ⟨hs, ht⟩
  · exact Or.inr ⟨ht, hs⟩
  · exact False.elim (hne (hs.symm.trans ht))

/-- Reverse a vertex occurrence so the canonical path runs left-to-right. -/
def reverseVertexOccurrence {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (j : Fin (path.edgeCount + 1)) : Fin path.vertexCount :=
  Fin.cast path.edgeCount_add_one_eq_vertexCount j.rev

/-- Reverse an edge occurrence in parallel with `reverseVertexOccurrence`. -/
def reverseEdgeOccurrence {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (i : Fin path.edgeCount) : Fin path.edgeCount :=
  i.rev

theorem reverseVertex_castSucc_eq_edgeEnd {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (i : Fin path.edgeCount) :
    path.reverseVertexOccurrence i.castSucc =
      path.edgeEndOccurrence (path.reverseEdgeOccurrence i) := by
  apply Fin.ext
  simp only [reverseVertexOccurrence, reverseEdgeOccurrence, Fin.val_cast,
    Fin.val_rev, Fin.val_castSucc, edgeEndOccurrence]
  omega

theorem reverseVertex_succ_eq_edgeStart {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (i : Fin path.edgeCount) :
    path.reverseVertexOccurrence i.succ =
      path.edgeStartOccurrence (path.reverseEdgeOccurrence i) := by
  apply Fin.ext
  simp only [reverseVertexOccurrence, reverseEdgeOccurrence, Fin.val_cast,
    Fin.val_rev, Fin.val_succ, edgeStartOccurrence_val]
  omega

theorem reverseVertex_zero_eq_lastOccurrence {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.reverseVertexOccurrence 0 = path.lastOccurrence := by
  apply Fin.ext
  simp only [reverseVertexOccurrence, Fin.val_cast, Fin.val_rev, Fin.val_zero]
  have hEdges := path.edgeCount_add_one_eq_vertexCount
  have hLast := path.lastOccurrence_val_add_one
  omega

theorem reverseVertex_last_eq_headOccurrence {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.reverseVertexOccurrence (Fin.last path.edgeCount) =
      path.headOccurrence := by
  apply Fin.ext
  simp [reverseVertexOccurrence, headOccurrence]

theorem edgeCount_eq_vertexCount_sub_one {v : Fin G.roles}
    (path : G.EdgePathToLeft v) :
    path.edgeCount = path.vertexCount - 1 := by
  have h := path.edgeCount_add_one_eq_vertexCount
  omega

/-- Every vertex occurrence of an actual boundary path is retained: the head
of a nontrivial path is incident to its first edge, and a terminal singleton
is in the left boundary. -/
theorem vertexAt_roleCovered {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (o : Fin path.vertexCount) :
    G.RoleCovered (path.vertexAt o) := by
  induction path with
  | finish v hLeft =>
      exact Or.inr (Or.inl hLeft)
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o using Fin.cases with
      | zero =>
          exact Or.inl ⟨e, hAtStart⟩
      | succ o =>
          exact ih o

end PartiteShape.EdgePathToLeft

namespace C079U3
open C079U2

open Classical in
attribute [local instance] propDecidable

/-- Every actual path in the Menger family gives the embedding required by
the canonical C079 path state. -/
def actualPathEmbedding
    (family : G.VertexDisjointRightToLeftPaths s) (i : Fin s) :
    C079PathBackboneEmbedding G (family.path i).edgeCount where
  role := fun j => (family.path i).vertexAt
    ((family.path i).reverseVertexOccurrence j)
  edge := fun j => (family.path i).edgeAt
    ((family.path i).reverseEdgeOccurrence j)
  endpointMatch := by
    intro j
    let path := family.path i
    let k := path.reverseEdgeOccurrence j
    have hDistinct :
        path.vertexAt (path.edgeStartOccurrence k) ≠
          path.vertexAt (path.edgeEndOccurrence k) := by
      intro hRole
      have hOccurrence :
          (⟨i, path.edgeStartOccurrence k⟩ :
              Σ q : Fin s, Fin ((family.path q).vertexCount)) =
            ⟨i, path.edgeEndOccurrence k⟩ :=
        family.vertexAt_injective hRole
      have hTail : path.edgeStartOccurrence k =
          path.edgeEndOccurrence k :=
        eq_of_heq (Sigma.mk.inj_iff.mp hOccurrence).2
      have hVal := congrArg Fin.val hTail
      simp only [PartiteShape.EdgePathToLeft.edgeStartOccurrence_val,
        PartiteShape.EdgePathToLeft.edgeEndOccurrence] at hVal
      omega
    have hEdge := path.edgeAt_endpointMatch_of_ne k hDistinct
    rw [path.reverseVertex_castSucc_eq_edgeEnd,
      path.reverseVertex_succ_eq_edgeStart]
    rcases hEdge with hEdge | hEdge
    · exact Or.inr hEdge
    · exact Or.inl hEdge
  leftEnd := by
    rw [(family.path i).reverseVertex_zero_eq_lastOccurrence]
    exact (family.path i).vertexAt_lastOccurrence_mem_left
  rightEnd := by
    rw [(family.path i).reverseVertex_last_eq_headOccurrence]
    simpa using family.startRight i

/-- The target uses `vertexCount - 1`; this is definitionally the same path
after transporting along `edgeCount + 1 = vertexCount`. -/
def actualPathEmbeddingForTarget
    (family : G.VertexDisjointRightToLeftPaths s) (i : Fin s) :
    C079PathBackboneEmbedding G ((family.path i).vertexCount - 1) := by
  rw [← (family.path i).edgeCount_eq_vertexCount_sub_one]
  exact actualPathEmbedding family i

/-- Restriction of an actual defect-fiber state to one path, before the
harmless `edgeCount = vertexCount - 1` transport. -/
def actualPathStateRaw
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (S : DefectFiber G p d) (i : Fin s) :
    AdmissiblePartitionState
      (c079CanonicalPathShape (family.path i).edgeCount) p :=
  (actualPathEmbedding family i).restrictState
    ((admissibleDefectFiberEquiv G p d).symm S)

/-- Reversing the occurrence order does not change a finite sum. -/
theorem sum_reverseVertexOccurrence
    {v : Fin G.roles} (path : G.EdgePathToLeft v) (weight : Fin G.roles → Nat) :
    (∑ j : Fin (path.edgeCount + 1),
        weight (path.vertexAt (path.reverseVertexOccurrence j))) =
      ∑ o : Fin path.vertexCount, weight (path.vertexAt o) := by
  let e : Fin (path.edgeCount + 1) ≃ Fin path.vertexCount :=
    Fin.revPerm.trans (finCongr path.edgeCount_add_one_eq_vertexCount)
  simpa [e, PartiteShape.EdgePathToLeft.reverseVertexOccurrence,
    Fin.revPerm_apply, finCongr_apply] using
    (Equiv.sum_comp e (fun o : Fin path.vertexCount => weight (path.vertexAt o)))

/-- Exact canonical degree of the restriction of an actual defect-fiber
state.  This is the bookkeeping needed to land in the C079 degree fiber. -/
theorem actualPathStateRaw_totalBlockCount
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (S : DefectFiber G p d) (i : Fin s) :
    (actualPathStateRaw family d S i).toReplicaState.totalBlockCount =
      (p + 1) * (family.path i).edgeCount + 1 -
        pathExcess p family d i := by
  let path := family.path i
  let T : AdmissiblePartitionState G p :=
    (admissibleDefectFiberEquiv G p d).symm S
  have hBlock (o : Fin path.vertexCount) :
      partitionBlockCount (T.1 (path.vertexAt o)) =
        (p + 1) - d (path.vertexAt o) := by
    have hDefect := S.2 (path.vertexAt o)
    have hBound := S.1.coveredRole_blockCount_le (path.vertexAt o)
      (path.vertexAt_roleCovered o)
    change (p + 1) - partitionBlockCount (T.1 (path.vertexAt o)) =
      d (path.vertexAt o) at hDefect
    change partitionBlockCount (T.1 (path.vertexAt o)) ≤ p + 1 at hBound
    omega
  have hD (o : Fin path.vertexCount) : d (path.vertexAt o) ≤ p + 1 := by
    calc
      d (path.vertexAt o) =
          (p + 1) - partitionBlockCount (S.1.partition (path.vertexAt o)) :=
        (S.2 (path.vertexAt o)).symm
      _ ≤ p + 1 := Nat.sub_le _ _
  change
    (∑ j : Fin (path.edgeCount + 1),
      partitionBlockCount (T.1 (path.vertexAt
        (path.reverseVertexOccurrence j)))) =
      (p + 1) * path.edgeCount + 1 - pathExcess p family d i
  rw [sum_reverseVertexOccurrence path
    (fun x => partitionBlockCount (T.1 x))]
  calc
    (∑ o : Fin path.vertexCount,
        partitionBlockCount (T.1 (path.vertexAt o))) =
        ∑ o : Fin path.vertexCount, ((p + 1) - d (path.vertexAt o)) := by
      apply Finset.sum_congr rfl
      intro o _
      exact hBlock o
    _ = (∑ _o : Fin path.vertexCount, (p + 1)) -
          ∑ o : Fin path.vertexCount, d (path.vertexAt o) := by
      exact Finset.sum_tsub_distrib Finset.univ
        (fun o _ => hD o)
    _ = path.vertexCount * (p + 1) -
          ∑ o : Fin path.vertexCount, d (path.vertexAt o) := by simp
    _ = (p + 1) * path.edgeCount + 1 - pathExcess p family d i := by
      let D : Nat := ∑ o : Fin path.vertexCount, d (path.vertexAt o)
      have hCount := path.edgeCount_add_one_eq_vertexCount
      have hExcess := pathExcess_add_baseline family S i
      change pathExcess p family d i + p = D at hExcess
      change path.vertexCount * (p + 1) - D =
        (p + 1) * path.edgeCount + 1 - pathExcess p family d i
      rw [← hExcess, ← hCount]
      have hExpand :
          (path.edgeCount + 1) * (p + 1) =
            ((p + 1) * path.edgeCount + 1) + p := by
        ring
      rw [hExpand]
      exact Nat.add_sub_add_right
        ((p + 1) * path.edgeCount + 1) p (pathExcess p family d i)

/-- The actual restriction, packaged in the exact degree fiber used by the
C079 path count. -/
def actualPathDegreeFiberRaw
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (S : DefectFiber G p d) (i : Fin s) :
    C079PathStateDegreeFiber
      (c079CanonicalPathShape (family.path i).edgeCount)
      p (family.path i).edgeCount (pathExcess p family d i) :=
  ⟨actualPathStateRaw family d S i,
    actualPathStateRaw_totalBlockCount family d S i⟩

/-- Same restriction with the exact `vertexCount - 1` index appearing in U3. -/
def actualPathDegreeFiber
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (S : DefectFiber G p d) (i : Fin s) :
    C079PathStateDegreeFiber
      (c079CanonicalPathShape ((family.path i).vertexCount - 1))
      p ((family.path i).vertexCount - 1) (pathExcess p family d i) := by
  rw [← (family.path i).edgeCount_eq_vertexCount_sub_one]
  exact actualPathDegreeFiberRaw family d S i

/-- A canonical coordinate corresponding to an original path occurrence. -/
def canonicalIndexOfOccurrence {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (o : Fin path.vertexCount) :
    Fin (path.edgeCount + 1) :=
  (Fin.cast path.edgeCount_add_one_eq_vertexCount.symm o).rev

theorem reverseVertex_canonicalIndex {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (o : Fin path.vertexCount) :
    path.reverseVertexOccurrence (canonicalIndexOfOccurrence path o) = o := by
  apply Fin.ext
  simp [canonicalIndexOfOccurrence,
    PartiteShape.EdgePathToLeft.reverseVertexOccurrence]

/-- The backbone subtype represented by a concrete family occurrence. -/
def backboneOfOccurrence
    (family : G.VertexDisjointRightToLeftPaths s)
    (i : Fin s) (o : Fin (family.path i).vertexCount) : Backbone family :=
  ⟨(family.path i).vertexAt o, family_vertexAt_mem_backbone family i o⟩

/-- Choose the actual defect-fiber witness carried by a `PathFiber` element. -/
def pathFiberWitness
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (B : PathFiber p family d) : DefectFiber G p d :=
  Classical.choose B.2

theorem pathFiberWitness_partition
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (B : PathFiber p family d)
    (x : Backbone family) :
    (pathFiberWitness family d B).1.partition x.1 = B.1 x :=
  Classical.choose_spec B.2 x

/-- Restrict a `PathFiber` point to all actual canonical paths.  The selected
global witness is used only for proof fields; its partitions on the backbone
are exactly `B`. -/
def pathFiberRestrictionRaw
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (B : PathFiber p family d) :
    ∀ i : Fin s,
      C079PathStateDegreeFiber
        (c079CanonicalPathShape (family.path i).edgeCount)
        p (family.path i).edgeCount (pathExcess p family d i) :=
  fun i => actualPathDegreeFiberRaw family d (pathFiberWitness family d B) i

/-- Evaluation of the restricted state recovers the original backbone
partition at every actual occurrence. -/
theorem pathFiberRestrictionRaw_partition
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) (B : PathFiber p family d)
    (i : Fin s) (o : Fin (family.path i).vertexCount) :
    (pathFiberRestrictionRaw family d B i).1.1
        (canonicalIndexOfOccurrence (family.path i) o) =
      B.1 (backboneOfOccurrence family i o) := by
  change
    (pathFiberWitness family d B).1.partition
        ((family.path i).vertexAt
          ((family.path i).reverseVertexOccurrence
            (canonicalIndexOfOccurrence (family.path i) o))) =
      B.1 (backboneOfOccurrence family i o)
  rw [reverseVertex_canonicalIndex]
  exact pathFiberWitness_partition family d B (backboneOfOccurrence family i o)

/-- Vertex-disjointness makes the product of path restrictions injective on
the actual `PathFiber`. -/
theorem pathFiberRestrictionRaw_injective
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) :
    Function.Injective (pathFiberRestrictionRaw (p := p) family d) := by
  classical
  intro B C hRestriction
  apply Subtype.ext
  funext x
  rcases x with ⟨x, hx⟩
  unfold PartiteShape.VertexDisjointRightToLeftPaths.backboneRoles at hx
  rcases Finset.mem_image.mp hx with ⟨⟨i, o⟩, _hmem, hxRole⟩
  have hAtPath := congrFun hRestriction i
  have hAtCoordinate := congrArg
    (fun T => T.1.1 (canonicalIndexOfOccurrence (family.path i) o)) hAtPath
  rw [pathFiberRestrictionRaw_partition,
    pathFiberRestrictionRaw_partition] at hAtCoordinate
  have hxSubtype :
      (⟨x, hx⟩ : Backbone family) = backboneOfOccurrence family i o := by
    apply Subtype.ext
    exact hxRole.symm
  simpa [hxSubtype] using hAtCoordinate

/-- Actual `PathFiber` cardinality is bounded by the product of the exact
canonical degree fibers, first in the natural `edgeCount` indexing. -/
theorem pathFiber_card_le_canonicalProduct_raw
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) :
    Fintype.card (PathFiber p family d) ≤
      ∏ i : Fin s,
        Fintype.card
          (C079PathStateDegreeFiber
            (c079CanonicalPathShape (family.path i).edgeCount)
            p (family.path i).edgeCount (pathExcess p family d i)) := by
  have hCard := Fintype.card_le_of_injective
    (pathFiberRestrictionRaw (p := p) family d)
    (pathFiberRestrictionRaw_injective (p := p) family d)
  simpa only [Fintype.card_pi] using hCard

/-- The exact missing U3 path-product gate, with the requested
`vertexCount - 1` path length and no supplied counting hypothesis. -/
theorem actual_pathFiber_card_le_canonicalProduct
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → Nat) :
    Fintype.card (PathFiber p family d) ≤
      ∏ i : Fin s,
        Fintype.card
          (C079PathStateDegreeFiber
            (c079CanonicalPathShape ((family.path i).vertexCount - 1))
            p ((family.path i).vertexCount - 1)
            (pathExcess p family d i)) := by
  calc
    Fintype.card (PathFiber p family d) ≤
        ∏ i : Fin s,
          Fintype.card
            (C079PathStateDegreeFiber
              (c079CanonicalPathShape (family.path i).edgeCount)
              p (family.path i).edgeCount (pathExcess p family d i)) :=
      pathFiber_card_le_canonicalProduct_raw family d
    _ = ∏ i : Fin s,
          Fintype.card
            (C079PathStateDegreeFiber
              (c079CanonicalPathShape ((family.path i).vertexCount - 1))
              p ((family.path i).vertexCount - 1)
              (pathExcess p family d i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← (family.path i).edgeCount_eq_vertexCount_sub_one]

#print axioms PartiteShape.EdgePathToLeft.edgeAt_incident_edgeStart
#print axioms PartiteShape.EdgePathToLeft.edgeAt_endpointMatch_of_ne
#print axioms actualPathEmbeddingForTarget
#print axioms PartiteShape.EdgePathToLeft.vertexAt_roleCovered
#print axioms actualPathStateRaw_totalBlockCount
#print axioms actualPathDegreeFiber
#print axioms pathFiberRestrictionRaw_injective
#print axioms actual_pathFiber_card_le_canonicalProduct

end C079U3
end GraphMatrixReplica
