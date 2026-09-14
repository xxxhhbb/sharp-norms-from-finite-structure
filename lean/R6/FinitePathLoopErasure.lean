import R6.FiniteMengerStrongDuality

/-! # Loop erasure for the finite right-to-left path representation

`EdgePathToLeft` is intentionally a walk-like inductive type: its constructors
do not prohibit repeated roles.  This file erases loops while retaining a
typed occurrence witness showing that every role of the reduced path already
occurred in the original path.

As a consequence, meeting all vertex-simple paths is equivalent to being a
genuine separator for arbitrary old paths.  Applied to a maximum packing,
this proves that its full used-role set is a separator.  Its cardinality is
the total number of path occurrences, however, so the sharp Menger cut still
requires the usual alternating residual-reachability selection of at most one
role from each packed path.
-/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.EdgePathToLeft

variable {G : PartiteShape} {v : Fin G.roles}

/-- The suffix beginning at a chosen occurrence. -/
def suffixAt {G : PartiteShape} :
    {v : Fin G.roles} → (path : G.EdgePathToLeft v) →
      (o : Fin path.vertexCount) → G.EdgePathToLeft (path.vertexAt o)
  | _, .finish v hLeft => fun _ => .finish v hLeft
  | _, .step e w hAtStart hAtEnd tail => fun o =>
      Fin.cases (.step e w hAtStart hAtEnd tail)
        (fun j => suffixAt tail j) o

/-- Every role in a suffix occurs in the original path. -/
theorem suffixAt_vertex_mem
    (path : G.EdgePathToLeft v) (o : Fin path.vertexCount)
    (u : Fin (path.suffixAt o).vertexCount) :
    ∃ old : Fin path.vertexCount,
      (path.suffixAt o).vertexAt u = path.vertexAt old := by
  induction path with
  | finish v hLeft =>
      exact ⟨u, rfl⟩
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o using Fin.cases with
      | zero => exact ⟨u, rfl⟩
      | succ o =>
          obtain ⟨old, hOld⟩ := ih o u
          exact ⟨Fin.succ old, hOld⟩

/-- A suffix of a vertex-simple path is vertex-simple. -/
theorem suffixAt_isVertexSimple
    (path : G.EdgePathToLeft v) (hSimple : path.IsVertexSimple)
    (o : Fin path.vertexCount) :
    (path.suffixAt o).IsVertexSimple := by
  induction path with
  | finish v hLeft =>
      exact finish_isVertexSimple hLeft
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o using Fin.cases with
      | zero => exact hSimple
      | succ o =>
          apply ih
          intro a b hVertex
          have hShifted :
              (PartiteShape.EdgePathToLeft.step e w hAtStart hAtEnd tail).vertexAt
                  (Fin.succ a) =
                (PartiteShape.EdgePathToLeft.step e w hAtStart hAtEnd tail).vertexAt
                  (Fin.succ b) := hVertex
          exact Fin.succ_injective _ (hSimple hShifted)

/-- A vertex-simple replacement of an old path, together with the exact
vertex-set inclusion needed to transfer separator hits back to the old path.
The dependent path index ensures that the initial role is unchanged. -/
structure SimpleReduction (original : G.EdgePathToLeft v) where
  reduced : G.EdgePathToLeft v
  isVertexSimple : reduced.IsVertexSimple
  vertex_mem_original :
    ∀ o : Fin reduced.vertexCount,
      ∃ old : Fin original.vertexCount,
        reduced.vertexAt o = original.vertexAt old

/-- Change the dependent start index of a candidate reduction along an
equality of roles.  Isolating this transport keeps the loop-erasure recursion
free of dependent `subst` steps. -/
def SimpleReduction.ofStartEq
    {w : Fin G.roles} (original : G.EdgePathToLeft v)
    (candidate : G.EdgePathToLeft w) (hStart : w = v)
    (hSimple : candidate.IsVertexSimple)
    (hMem : ∀ o : Fin candidate.vertexCount,
      ∃ old : Fin original.vertexCount,
        candidate.vertexAt o = original.vertexAt old) :
    SimpleReduction original := by
  subst v
  exact
    { reduced := candidate
      isVertexSimple := hSimple
      vertex_mem_original := hMem }

/-- Constructive loop erasure.  First erase the tail.  If the old head occurs
in that reduced tail, discard everything before that occurrence; otherwise
retain the head step. -/
def loopErase (path : G.EdgePathToLeft v) : SimpleReduction path := by
  classical
  induction path with
  | finish v hLeft =>
      exact
        { reduced := .finish v hLeft
          isVertexSimple := finish_isVertexSimple hLeft
          vertex_mem_original := fun o => ⟨o, rfl⟩ }
  | @step v e w hAtStart hAtEnd tail tailReduction =>
      let originalPath : G.EdgePathToLeft v :=
        .step e w hAtStart hAtEnd tail
      by_cases hHeadOccurs :
          ∃ o : Fin tailReduction.reduced.vertexCount,
            tailReduction.reduced.vertexAt o = v
      · have hWitness : Nonempty
            {o : Fin tailReduction.reduced.vertexCount //
              tailReduction.reduced.vertexAt o = v} := by
          rcases hHeadOccurs with ⟨o, hRole⟩
          exact ⟨⟨o, hRole⟩⟩
        let witness := Classical.choice hWitness
        let o : Fin tailReduction.reduced.vertexCount := witness.1
        have hRole : tailReduction.reduced.vertexAt o = v := witness.2
        let candidate := tailReduction.reduced.suffixAt o
        have hCandidateSimple : candidate.IsVertexSimple :=
          tailReduction.reduced.suffixAt_isVertexSimple
            tailReduction.isVertexSimple o
        have hCandidateMem :
            ∀ u : Fin candidate.vertexCount,
              ∃ old : Fin originalPath.vertexCount,
                candidate.vertexAt u = originalPath.vertexAt old := by
          intro u
          obtain ⟨middle, hMiddle⟩ :=
            tailReduction.reduced.suffixAt_vertex_mem o u
          obtain ⟨old, hOld⟩ :=
            tailReduction.vertex_mem_original middle
          exact ⟨Fin.succ old, hMiddle.trans hOld⟩
        simpa [originalPath] using
          SimpleReduction.ofStartEq originalPath candidate hRole
            hCandidateSimple hCandidateMem
      · refine
          { reduced := .step e w hAtStart hAtEnd tailReduction.reduced
            isVertexSimple := ?_
            vertex_mem_original := ?_ }
        · intro a b hVertex
          cases a using Fin.cases with
          | zero =>
              cases b using Fin.cases with
              | zero => rfl
              | succ b =>
                  exfalso
                  apply hHeadOccurs
                  exact ⟨b, hVertex.symm⟩
          | succ a =>
              cases b using Fin.cases with
              | zero =>
                  exfalso
                  apply hHeadOccurs
                  exact ⟨a, hVertex⟩
              | succ b =>
                  have hTail : a = b :=
                    tailReduction.isVertexSimple hVertex
                  subst b
                  rfl
        · intro u
          cases u using Fin.cases with
          | zero =>
              exact
                ⟨PartiteShape.EdgePathToLeft.headOccurrence
                    (PartiteShape.EdgePathToLeft.step
                      e w hAtStart hAtEnd tail), rfl⟩
          | succ u =>
              obtain ⟨old, hOld⟩ :=
                tailReduction.vertex_mem_original u
              exact ⟨Fin.succ old, hOld⟩

theorem exists_simpleReduction (path : G.EdgePathToLeft v) :
    Nonempty (SimpleReduction path) :=
  ⟨path.loopErase⟩

end PartiteShape.EdgePathToLeft

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

/-- Once loop erasure is available, hitting all simple paths is exactly enough
to hit every old walk-like `EdgePathToLeft`. -/
theorem usedRoles_isRightLeftSeparator_of_meetEverySimplePath
    (family : G.VertexDisjointRightToLeftPaths s)
    (hMeet : family.UsedRolesMeetEverySimplePath) :
    G.IsRightLeftSeparator family.usedRoles := by
  intro v hRight original
  let reduction := original.loopErase
  obtain ⟨o, hUsed⟩ :=
    hMeet v hRight reduction.reduced reduction.isVertexSimple
  obtain ⟨old, hRole⟩ := reduction.vertex_mem_original o
  exact ⟨old, hRole ▸ hUsed⟩

/-- For a fixed used-role set, the simple-path hitting condition is equivalent
to the original separator definition over arbitrary walk-like paths. -/
theorem usedRoles_meetEverySimplePath_iff_isRightLeftSeparator
    (family : G.VertexDisjointRightToLeftPaths s) :
    family.UsedRolesMeetEverySimplePath ↔
      G.IsRightLeftSeparator family.usedRoles := by
  constructor
  · exact family.usedRoles_isRightLeftSeparator_of_meetEverySimplePath
  · intro hSeparator v hRight path _hSimple
    exact hSeparator v hRight path

/-- The cardinality comparison supplied by the full used-role set points in
the non-sharp direction: there is at least one used occurrence per path. -/
theorem pathCount_le_usedRoles_card
    (family : G.VertexDisjointRightToLeftPaths s) :
    s ≤ family.usedRoles.card := by
  let headOccurrence : Fin s → family.Occurrence :=
    fun i => ⟨i, (family.path i).headOccurrence⟩
  have hHeadInjective : Function.Injective headOccurrence := by
    intro i j h
    exact congrArg Sigma.fst h
  calc
    s = Fintype.card (Fin s) := by simp
    _ ≤ Fintype.card family.Occurrence :=
      Fintype.card_le_of_injective headOccurrence hHeadInjective
    _ = family.usedRoles.card := family.usedRoles_card.symm

/-- The complete used-role set of a maximum packing is a genuine separator.
This is a non-sharp cut: its cardinality counts all path vertices. -/
theorem maximum_usedRoles_isRightLeftSeparator (G : PartiteShape) :
    G.IsRightLeftSeparator G.maximumRightLeftPathPacking.usedRoles :=
  usedRoles_isRightLeftSeparator_of_meetEverySimplePath
    G.maximumRightLeftPathPacking
    (maximum_usedRoles_meetEverySimplePath G)

theorem rightLeftSeparatorNumber_le_maximum_usedRoles_card
    (G : PartiteShape) :
    G.rightLeftSeparatorNumber ≤
      G.maximumRightLeftPathPacking.usedRoles.card :=
  G.minimumRightLeftSeparator_isMinimum.2
    G.maximumRightLeftPathPacking.usedRoles
    (maximum_usedRoles_isRightLeftSeparator G)

end PartiteShape.VertexDisjointRightToLeftPaths

#print axioms PartiteShape.EdgePathToLeft.suffixAt_vertex_mem
#print axioms PartiteShape.EdgePathToLeft.suffixAt_isVertexSimple
#print axioms PartiteShape.EdgePathToLeft.loopErase
#print axioms
  PartiteShape.VertexDisjointRightToLeftPaths.maximum_usedRoles_isRightLeftSeparator
#print axioms
  PartiteShape.VertexDisjointRightToLeftPaths.pathCount_le_usedRoles_card

end GraphMatrixReplica
