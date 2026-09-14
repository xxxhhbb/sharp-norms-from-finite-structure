import GraphMatrix.FinitePathLoopErasure

/-! # The alternating residual cut for finite vertex Menger

The residual graph uses split role nodes.  An unused role can be crossed from
its input to its output; an occupied role can be crossed backwards.  Graph
edges go from output to input, while every edge used by a packed path also has
the reverse residual transition.  All right-boundary inputs are reachable
from the source and all left-boundary outputs lead to the sink.

If the sink is unreachable, the occupied roles whose input is reachable but
whose output is not form a separator.  Reverse packed-edge transitions imply
that this frontier contains at most one role on each packed path, giving the
sharp cardinality bound.  The sole remaining augmentation obligation is that
a reachable residual sink can be converted into a packing with one additional
path.
-/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.EdgePathToLeft

variable {G : PartiteShape} {v : Fin G.roles}

/-- An oriented consecutive role pair in the old inductive path. -/
def HasForwardStep {G : PartiteShape} :
    {v : Fin G.roles} → G.EdgePathToLeft v →
      Fin G.roles → Fin G.roles → Prop
  | _, .finish _ _, _, _ => False
  | _, .step (v := head) _ next _ _ tail, a, b =>
      (a = head ∧ b = next) ∨ HasForwardStep tail a b

theorem hasForwardStep_head
    {e : Fin G.edges} {w : Fin G.roles}
    {hAtStart : G.EdgeIncident e v} {hAtEnd : G.EdgeIncident e w}
    (tail : G.EdgePathToLeft w) :
    HasForwardStep
      (PartiteShape.EdgePathToLeft.step e w hAtStart hAtEnd tail) v w := by
  simp [HasForwardStep]

theorem hasForwardStep_tail
    {e : Fin G.edges} {w a b : Fin G.roles}
    {hAtStart : G.EdgeIncident e v} {hAtEnd : G.EdgeIncident e w}
    {tail : G.EdgePathToLeft w} (h : tail.HasForwardStep a b) :
    HasForwardStep
      (PartiteShape.EdgePathToLeft.step e w hAtStart hAtEnd tail) a b := by
  exact Or.inr h

end PartiteShape.EdgePathToLeft

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

/-- A graph edge used in the forward orientation by one packed path. -/
def PackedForwardStep (family : G.VertexDisjointRightToLeftPaths s)
    (a b : Fin G.roles) : Prop :=
  ∃ i : Fin s, (family.path i).HasForwardStep a b

/-- Split nodes of the residual vertex-capacity network. -/
inductive ResidualNode (G : PartiteShape) where
  | source
  | sink
  | input (v : Fin G.roles)
  | output (v : Fin G.roles)
  deriving DecidableEq, Fintype

/-- One transition of the alternating residual graph. -/
inductive ResidualTransition
    (family : G.VertexDisjointRightToLeftPaths s) :
    ResidualNode G → ResidualNode G → Prop
  | fromSource {v} (hRight : v ∈ G.rightBoundary) :
      ResidualTransition family .source (.input v)
  | throughUnused {v} (hUnused : v ∉ family.usedRoles) :
      ResidualTransition family (.input v) (.output v)
  | backThroughUsed {v} (hUsed : v ∈ family.usedRoles) :
      ResidualTransition family (.output v) (.input v)
  | alongEdge {e a b}
      (hAtA : G.EdgeIncident e a) (hAtB : G.EdgeIncident e b) :
      ResidualTransition family (.output a) (.input b)
  | reversePackedStep {a b} (hPacked : family.PackedForwardStep a b) :
      ResidualTransition family (.input b) (.output a)
  | toSink {v} (hLeft : v ∈ G.leftBoundary) :
      ResidualTransition family (.output v) .sink

abbrev ResidualReachable
    (family : G.VertexDisjointRightToLeftPaths s)
    (z : ResidualNode G) : Prop :=
  Relation.ReflTransGen family.ResidualTransition .source z

def HasResidualAugmentingWalk
    (family : G.VertexDisjointRightToLeftPaths s) : Prop :=
  family.ResidualReachable .sink

/-- The sharp frontier: occupied roles entered by the residual search but not
crossed in the forward direction. -/
def residualFrontier
    (family : G.VertexDisjointRightToLeftPaths s) :
    Finset (Fin G.roles) := by
  classical
  exact family.usedRoles.filter (fun v =>
    family.ResidualReachable (.input v) ∧
      ¬ family.ResidualReachable (.output v))

theorem mem_residualFrontier_iff
    (family : G.VertexDisjointRightToLeftPaths s) (v : Fin G.roles) :
    v ∈ family.residualFrontier ↔
      v ∈ family.usedRoles ∧
      family.ResidualReachable (.input v) ∧
      ¬ family.ResidualReachable (.output v) := by
  classical
  simp [residualFrontier]

theorem residualReachable_step
    (family : G.VertexDisjointRightToLeftPaths s)
    {x y : ResidualNode G} (hx : family.ResidualReachable x)
    (hxy : family.ResidualTransition x y) :
    family.ResidualReachable y :=
  Relation.ReflTransGen.tail hx hxy

theorem input_reachable_of_right
    (family : G.VertexDisjointRightToLeftPaths s)
    {v : Fin G.roles} (hRight : v ∈ G.rightBoundary) :
    family.ResidualReachable (.input v) :=
  family.residualReachable_step
    (Relation.ReflTransGen.refl)
    (.fromSource hRight)

theorem output_reachable_of_input_reachable_of_unused
    (family : G.VertexDisjointRightToLeftPaths s)
    {v : Fin G.roles} (hIn : family.ResidualReachable (.input v))
    (hUnused : v ∉ family.usedRoles) :
    family.ResidualReachable (.output v) :=
  family.residualReachable_step hIn (.throughUnused hUnused)

theorem input_reachable_of_output_reachable_of_used
    (family : G.VertexDisjointRightToLeftPaths s)
    {v : Fin G.roles} (hOut : family.ResidualReachable (.output v))
    (hUsed : v ∈ family.usedRoles) :
    family.ResidualReachable (.input v) :=
  family.residualReachable_step hOut (.backThroughUsed hUsed)

theorem input_reachable_along_edge
    (family : G.VertexDisjointRightToLeftPaths s)
    {e : Fin G.edges} {a b : Fin G.roles}
    (hOut : family.ResidualReachable (.output a))
    (hAtA : G.EdgeIncident e a) (hAtB : G.EdgeIncident e b) :
    family.ResidualReachable (.input b) :=
  family.residualReachable_step hOut (.alongEdge hAtA hAtB)

theorem output_reachable_reverse_packed_step
    (family : G.VertexDisjointRightToLeftPaths s)
    {a b : Fin G.roles}
    (hIn : family.ResidualReachable (.input b))
    (hPacked : family.PackedForwardStep a b) :
    family.ResidualReachable (.output a) :=
  family.residualReachable_step hIn (.reversePackedStep hPacked)

/-- Every occurrence of a packed path belongs to the used-role set. -/
theorem path_vertex_mem_usedRoles
    (family : G.VertexDisjointRightToLeftPaths s) (i : Fin s)
    (o : Fin (family.path i).vertexCount) :
    (family.path i).vertexAt o ∈ family.usedRoles := by
  rw [family.mem_usedRoles_iff]
  exact ⟨i, o, rfl⟩

/-- Every forward step of a packed path is a packed forward step. -/
theorem path_forwardStep_isPacked
    (family : G.VertexDisjointRightToLeftPaths s) (i : Fin s)
    {a b : Fin G.roles} (h : (family.path i).HasForwardStep a b) :
    family.PackedForwardStep a b :=
  ⟨i, h⟩

/-- Along a path whose roles and forward steps belong to the packing,
reachability of any input occurrence propagates back to the input of the
path's head. -/
theorem input_head_reachable_of_input_occurrence
    (family : G.VertexDisjointRightToLeftPaths s)
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (hUsed : ∀ o, path.vertexAt o ∈ family.usedRoles)
    (hPacked : ∀ {a b}, path.HasForwardStep a b →
      family.PackedForwardStep a b)
    (o : Fin path.vertexCount)
    (hIn : family.ResidualReachable (.input (path.vertexAt o))) :
    family.ResidualReachable (.input v) := by
  induction path with
  | finish v hLeft =>
      simpa [PartiteShape.EdgePathToLeft.vertexAt] using hIn
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o using Fin.cases with
      | zero =>
          simpa [PartiteShape.EdgePathToLeft.vertexAt] using hIn
      | succ o =>
          have hTailUsed : ∀ u, tail.vertexAt u ∈ family.usedRoles := by
            intro u
            exact hUsed (Fin.succ u)
          have hTailPacked : ∀ {a b}, tail.HasForwardStep a b →
              family.PackedForwardStep a b := by
            intro a b hab
            exact hPacked (PartiteShape.EdgePathToLeft.hasForwardStep_tail hab)
          have hInW : family.ResidualReachable (.input w) :=
            ih hTailUsed hTailPacked o hIn
          have hOutV : family.ResidualReachable (.output v) :=
            family.output_reachable_reverse_packed_step hInW
              (hPacked
                (PartiteShape.EdgePathToLeft.hasForwardStep_head tail))
          exact family.input_reachable_of_output_reachable_of_used hOutV
            (hUsed
              (PartiteShape.EdgePathToLeft.headOccurrence
                (.step e w hAtStart hAtEnd tail)))

/-- If the residual sink is unreachable, every old right-to-left path hits the
frontier.  This proof works directly on possibly repeating paths. -/
theorem path_hits_residualFrontier_of_no_augment
    (family : G.VertexDisjointRightToLeftPaths s)
    (hNoAugment : ¬ family.HasResidualAugmentingWalk)
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (hIn : family.ResidualReachable (.input v)) :
    ∃ o : Fin path.vertexCount,
      path.vertexAt o ∈ family.residualFrontier := by
  induction path with
  | finish v hLeft =>
      by_cases hOut : family.ResidualReachable (.output v)
      · exfalso
        apply hNoAugment
        exact family.residualReachable_step hOut (.toSink hLeft)
      · have hUsed : v ∈ family.usedRoles := by
          by_contra hUnused
          exact hOut
            (family.output_reachable_of_input_reachable_of_unused hIn hUnused)
        refine ⟨PartiteShape.EdgePathToLeft.headOccurrence (.finish v hLeft), ?_⟩
        rw [family.mem_residualFrontier_iff]
        exact ⟨hUsed, hIn, hOut⟩
  | @step v e w hAtStart hAtEnd tail ih =>
      by_cases hOut : family.ResidualReachable (.output v)
      · obtain ⟨o, ho⟩ := ih
          (family.input_reachable_along_edge hOut hAtStart hAtEnd)
        exact ⟨Fin.succ o, ho⟩
      · have hUsed : v ∈ family.usedRoles := by
          by_contra hUnused
          exact hOut
            (family.output_reachable_of_input_reachable_of_unused hIn hUnused)
        refine ⟨PartiteShape.EdgePathToLeft.headOccurrence
          (.step e w hAtStart hAtEnd tail), ?_⟩
        rw [family.mem_residualFrontier_iff]
        exact ⟨hUsed, hIn, hOut⟩

theorem residualFrontier_isRightLeftSeparator_of_no_augment
    (family : G.VertexDisjointRightToLeftPaths s)
    (hNoAugment : ¬ family.HasResidualAugmentingWalk) :
    G.IsRightLeftSeparator family.residualFrontier := by
  intro v hRight path
  exact family.path_hits_residualFrontier_of_no_augment hNoAugment path
    (family.input_reachable_of_right hRight)

/-- The frontier occurs at most once on a path all of whose roles and forward
steps belong to the packing. -/
theorem residualFrontier_occurrence_unique_aux
    (family : G.VertexDisjointRightToLeftPaths s)
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (hUsed : ∀ o, path.vertexAt o ∈ family.usedRoles)
    (hPacked : ∀ {a b}, path.HasForwardStep a b →
      family.PackedForwardStep a b)
    {o₁ o₂ : Fin path.vertexCount}
    (h₁ : path.vertexAt o₁ ∈ family.residualFrontier)
    (h₂ : path.vertexAt o₂ ∈ family.residualFrontier) :
    o₁ = o₂ := by
  induction path with
  | finish v hLeft =>
      apply Fin.ext
      have hFirst : o₁.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using o₁.isLt
      have hSecond : o₂.val < 1 := by
        simpa [PartiteShape.EdgePathToLeft.vertexCount] using o₂.isLt
      omega
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o₁ using Fin.cases with
      | zero =>
          cases o₂ using Fin.cases with
          | zero => rfl
          | succ o₂ =>
              have hInTail :
                  family.ResidualReachable (.input (tail.vertexAt o₂)) :=
                (family.mem_residualFrontier_iff _).mp h₂ |>.2.1
              have hTailUsed : ∀ o, tail.vertexAt o ∈ family.usedRoles := by
                intro o
                exact hUsed (Fin.succ o)
              have hTailPacked : ∀ {a b}, tail.HasForwardStep a b →
                  family.PackedForwardStep a b := by
                intro a b hab
                exact hPacked
                  (PartiteShape.EdgePathToLeft.hasForwardStep_tail hab)
              have hInW := family.input_head_reachable_of_input_occurrence
                tail hTailUsed hTailPacked o₂ hInTail
              have hOutV := family.output_reachable_reverse_packed_step hInW
                (hPacked
                  (PartiteShape.EdgePathToLeft.hasForwardStep_head tail))
              exact False.elim
                ((family.mem_residualFrontier_iff _).mp h₁ |>.2.2 hOutV)
      | succ o₁ =>
          cases o₂ using Fin.cases with
          | zero =>
              have hInTail :
                  family.ResidualReachable (.input (tail.vertexAt o₁)) :=
                (family.mem_residualFrontier_iff _).mp h₁ |>.2.1
              have hTailUsed : ∀ o, tail.vertexAt o ∈ family.usedRoles := by
                intro o
                exact hUsed (Fin.succ o)
              have hTailPacked : ∀ {a b}, tail.HasForwardStep a b →
                  family.PackedForwardStep a b := by
                intro a b hab
                exact hPacked
                  (PartiteShape.EdgePathToLeft.hasForwardStep_tail hab)
              have hInW := family.input_head_reachable_of_input_occurrence
                tail hTailUsed hTailPacked o₁ hInTail
              have hOutV := family.output_reachable_reverse_packed_step hInW
                (hPacked
                  (PartiteShape.EdgePathToLeft.hasForwardStep_head tail))
              exact False.elim
                ((family.mem_residualFrontier_iff _).mp h₂ |>.2.2 hOutV)
          | succ o₂ =>
              have hTailUsed : ∀ o, tail.vertexAt o ∈ family.usedRoles := by
                intro o
                exact hUsed (Fin.succ o)
              have hTailPacked : ∀ {a b}, tail.HasForwardStep a b →
                  family.PackedForwardStep a b := by
                intro a b hab
                exact hPacked
                  (PartiteShape.EdgePathToLeft.hasForwardStep_tail hab)
              exact congrArg Fin.succ
                (ih hTailUsed hTailPacked h₁ h₂)

/-- The frontier occurs at most once on any fixed packed path. -/
theorem residualFrontier_occurrence_unique
    (family : G.VertexDisjointRightToLeftPaths s) (i : Fin s)
    {o₁ o₂ : Fin (family.path i).vertexCount}
    (h₁ : (family.path i).vertexAt o₁ ∈ family.residualFrontier)
    (h₂ : (family.path i).vertexAt o₂ ∈ family.residualFrontier) :
    o₁ = o₂ := by
  apply family.residualFrontier_occurrence_unique_aux (family.path i)
  · intro o
    exact family.path_vertex_mem_usedRoles i o
  · intro a b hab
    exact family.path_forwardStep_isPacked i hab
  · exact h₁
  · exact h₂

/-- A used role has a (necessarily unique) occurrence in the globally
injective packed family.  We package existence as `Nonempty` so that choosing
the occurrence does not eliminate an existential proposition into data. -/
theorem nonempty_occurrence_eq_of_mem_usedRoles
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : {v : Fin G.roles // v ∈ family.usedRoles}) :
    Nonempty {z : family.Occurrence // family.occurrenceRole z = v.1} := by
  have hv := v.property
  rw [family.mem_usedRoles_iff] at hv
  rcases hv with ⟨i, o, hRole⟩
  exact ⟨⟨⟨i, o⟩, hRole⟩⟩

def chosenUsedOccurrence
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : {v : Fin G.roles // v ∈ family.usedRoles}) :
    family.Occurrence :=
  (Classical.choice (family.nonempty_occurrence_eq_of_mem_usedRoles v)).1

theorem chosenUsedOccurrence_role
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : {v : Fin G.roles // v ∈ family.usedRoles}) :
    family.occurrenceRole (family.chosenUsedOccurrence v) = v.1 :=
  (Classical.choice (family.nonempty_occurrence_eq_of_mem_usedRoles v)).2

def frontierUsedRole
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : {v : Fin G.roles // v ∈ family.residualFrontier}) :
    {v : Fin G.roles // v ∈ family.usedRoles} :=
  ⟨v.1, (family.mem_residualFrontier_iff v.1).mp v.2 |>.1⟩

def frontierOccurrence
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : {v : Fin G.roles // v ∈ family.residualFrontier}) :
    family.Occurrence :=
  family.chosenUsedOccurrence (family.frontierUsedRole v)

theorem frontierOccurrence_role
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : {v : Fin G.roles // v ∈ family.residualFrontier}) :
    family.occurrenceRole (family.frontierOccurrence v) = v.1 :=
  family.chosenUsedOccurrence_role (family.frontierUsedRole v)

def frontierPathIndex
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : {v : Fin G.roles // v ∈ family.residualFrontier}) : Fin s :=
  (family.frontierOccurrence v).1

/-- Two frontier occurrences on the same packed path are equal as dependent
occurrences. -/
theorem frontier_occurrences_eq_of_path_eq
    (family : G.VertexDisjointRightToLeftPaths s)
    {z₁ z₂ : family.Occurrence}
    (h₁ : family.occurrenceRole z₁ ∈ family.residualFrontier)
    (h₂ : family.occurrenceRole z₂ ∈ family.residualFrontier)
    (hPath : z₁.1 = z₂.1) : z₁ = z₂ := by
  rcases z₁ with ⟨i, o₁⟩
  rcases z₂ with ⟨j, o₂⟩
  dsimp at hPath
  subst j
  have hOccurrence : o₁ = o₂ :=
    family.residualFrontier_occurrence_unique i h₁ h₂
  subst o₂
  rfl

theorem frontierPathIndex_injective
    (family : G.VertexDisjointRightToLeftPaths s) :
    Function.Injective family.frontierPathIndex := by
  intro v w hPath
  have hvFrontier :
      family.occurrenceRole (family.frontierOccurrence v) ∈
        family.residualFrontier := by
    rw [family.frontierOccurrence_role]
    exact v.2
  have hwFrontier :
      family.occurrenceRole (family.frontierOccurrence w) ∈
        family.residualFrontier := by
    rw [family.frontierOccurrence_role]
    exact w.2
  have hOccurrence :
      family.frontierOccurrence v = family.frontierOccurrence w :=
    family.frontier_occurrences_eq_of_path_eq hvFrontier hwFrontier hPath
  apply Subtype.ext
  calc
    v.1 = family.occurrenceRole (family.frontierOccurrence v) :=
      (family.frontierOccurrence_role v).symm
    _ = family.occurrenceRole (family.frontierOccurrence w) :=
      congrArg family.occurrenceRole hOccurrence
    _ = w.1 := family.frontierOccurrence_role w

/-- Sharp residual count: at most one frontier role per packed path. -/
theorem residualFrontier_card_le_pathCount
    (family : G.VertexDisjointRightToLeftPaths s) :
    family.residualFrontier.card ≤ s := by
  classical
  simpa using
    (Fintype.card_le_of_injective family.frontierPathIndex
      family.frontierPathIndex_injective)

theorem residualFrontier_smallSeparator_of_no_augment
    (family : G.VertexDisjointRightToLeftPaths s)
    (hNoAugment : ¬ family.HasResidualAugmentingWalk) :
    G.IsRightLeftSeparator family.residualFrontier ∧
      family.residualFrontier.card ≤ s :=
  ⟨family.residualFrontier_isRightLeftSeparator_of_no_augment hNoAugment,
    family.residualFrontier_card_le_pathCount⟩

end PartiteShape.VertexDisjointRightToLeftPaths

namespace PartiteShape

/-- The one remaining augmentation lemma: a source-to-sink residual walk can
be toggled/decomposed into one more vertex-disjoint right-to-left path. -/
def ResidualAugmentationSound (G : PartiteShape) : Prop :=
  ∀ {s : ℕ} (family : G.VertexDisjointRightToLeftPaths s),
    family.HasResidualAugmentingWalk →
      G.HasRightLeftPathPacking (s + 1)

theorem hasMengerAugmentOrCut_of_residualAugmentationSound
    (G : PartiteShape) (hSound : G.ResidualAugmentationSound) :
    G.HasMengerAugmentOrCut := by
  intro s family
  by_cases hAugment : family.HasResidualAugmentingWalk
  · exact Or.inl (hSound family hAugment)
  · exact Or.inr
      ⟨family.residualFrontier,
        family.residualFrontier_isRightLeftSeparator_of_no_augment hAugment,
        family.residualFrontier_card_le_pathCount⟩

theorem hasMaximumPackingCut_of_residualAugmentationSound
    (G : PartiteShape) (hSound : G.ResidualAugmentationSound) :
    G.HasMaximumPackingCut := by
  have hNoAugment :
      ¬ G.maximumRightLeftPathPacking.HasResidualAugmentingWalk := by
    intro hReachable
    obtain ⟨larger⟩ := hSound G.maximumRightLeftPathPacking hReachable
    have hBound := G.pathCount_le_rightLeftPathPackingNumber larger
    omega
  exact
    ⟨G.maximumRightLeftPathPacking.residualFrontier,
      VertexDisjointRightToLeftPaths.residualFrontier_isRightLeftSeparator_of_no_augment
        G.maximumRightLeftPathPacking hNoAugment,
      VertexDisjointRightToLeftPaths.residualFrontier_card_le_pathCount
        G.maximumRightLeftPathPacking⟩

theorem rightLeftOptima_eq_of_residualAugmentationSound
    (G : PartiteShape) (hSound : G.ResidualAugmentationSound) :
    G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber :=
  G.rightLeftOptima_eq_of_maximumPackingCut
    (G.hasMaximumPackingCut_of_residualAugmentationSound hSound)

def rightLeftMengerCertificateOfResidualAugmentationSound
    (G : PartiteShape) (hSound : G.ResidualAugmentationSound) :
    G.RightLeftMengerCertificate :=
  G.rightLeftMengerCertificateOfMaximumPackingCut
    (G.hasMaximumPackingCut_of_residualAugmentationSound hSound)

def boundaryCleanRightLeftMengerCertificateOfResidualAugmentationSound
    (G : PartiteShape) (hSound : G.ResidualAugmentationSound) :
    G.BoundaryCleanRightLeftMengerCertificate :=
  G.boundaryCleanRightLeftMengerCertificateOfMaximumPackingCut
    (G.hasMaximumPackingCut_of_residualAugmentationSound hSound)

end PartiteShape


end GraphMatrixReplica
