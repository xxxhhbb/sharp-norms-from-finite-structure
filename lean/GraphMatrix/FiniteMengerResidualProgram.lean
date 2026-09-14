import GraphMatrix.FiniteMengerResidualAugmentation

/-! # Simple type-valued residual edit programs

The proposition-valued reachability relation is converted to a dependent
type-valued program which retains the concrete edit at every step.  We then
erase loops at the level of split residual nodes.  The resulting source-to-
sink program is node-simple, a prerequisite for proving that every vertex or
edge capacity is toggled at most once.
-/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

/-- A concrete residual edit program from `x` to `z`. -/
inductive ResidualProgram
    (family : G.VertexDisjointRightToLeftPaths s) :
    ResidualNode G → ResidualNode G → Type
  | finish (x) : ResidualProgram family x x
  | step {x y z} (head : ResidualStepData family x y)
      (tail : ResidualProgram family y z) : ResidualProgram family x z

namespace ResidualProgram

variable {family : G.VertexDisjointRightToLeftPaths s}
variable {x y z : ResidualNode G}

def nodeCount {family : G.VertexDisjointRightToLeftPaths s} :
    {x z : ResidualNode G} → family.ResidualProgram x z → ℕ
  | _, _, .finish _ => 1
  | _, _, .step _ tail => nodeCount tail + 1

def nodeAt {family : G.VertexDisjointRightToLeftPaths s} :
    {x z : ResidualNode G} → (program : family.ResidualProgram x z) →
      Fin program.nodeCount → ResidualNode G
  | _, _, .finish x => fun _ => x
  | x, _, .step _ tail => Fin.cases x (nodeAt tail)

def headOccurrence (program : family.ResidualProgram x z) :
    Fin program.nodeCount :=
  ⟨0, by cases program <;> simp [nodeCount]⟩

@[simp] theorem nodeAt_headOccurrence
    (program : family.ResidualProgram x z) :
    program.nodeAt program.headOccurrence = x := by
  cases program <;> rfl

def IsNodeSimple (program : family.ResidualProgram x z) : Prop :=
  Function.Injective program.nodeAt

theorem finish_isNodeSimple (x : ResidualNode G) :
    (ResidualProgram.finish (family := family) x).IsNodeSimple := by
  intro a b _
  apply Fin.ext
  have ha : a.val < 1 := by simpa [nodeCount] using a.isLt
  have hb : b.val < 1 := by simpa [nodeCount] using b.isLt
  omega

/-- Append a concrete final edit to a program. -/
def snoc {family : G.VertexDisjointRightToLeftPaths s} :
    {x y z : ResidualNode G} → family.ResidualProgram x y →
      ResidualStepData family y z → family.ResidualProgram x z
  | _, _, _, .finish _, last => .step last (.finish _)
  | _, _, _, .step head tail, last => .step head (snoc tail last)

theorem toReachable (program : family.ResidualProgram x z) :
    Relation.ReflTransGen family.ResidualTransition x z := by
  induction program with
  | finish x => exact .refl
  | step head tail ih => exact .head head.toTransition ih

theorem nonempty_residualProgram_iff_reachable
    (family : G.VertexDisjointRightToLeftPaths s)
    (x z : ResidualNode G) :
    Nonempty (family.ResidualProgram x z) ↔
      Relation.ReflTransGen family.ResidualTransition x z := by
  constructor
  · rintro ⟨program⟩
    exact program.toReachable
  · intro hReachable
    induction hReachable with
    | refl => exact ⟨.finish _⟩
    | @tail b c hPrefix hStep ih =>
        obtain ⟨stepData⟩ :=
          (family.nonempty_residualStepData_iff_transition b c).2 hStep
        obtain ⟨prefixProgram⟩ := ih
        exact ⟨prefixProgram.snoc stepData⟩

/-- Suffix beginning at a selected node occurrence. -/
def suffixAt : {x z : ResidualNode G} →
    (program : family.ResidualProgram x z) →
      (o : Fin program.nodeCount) →
        family.ResidualProgram (program.nodeAt o) z
  | _, _, .finish x, _ => .finish x
  | _, _, .step head tail, o =>
      Fin.cases (.step head tail) (fun j => tail.suffixAt j) o

theorem suffixAt_node_mem
    (program : family.ResidualProgram x z)
    (o : Fin program.nodeCount)
    (u : Fin (program.suffixAt o).nodeCount) :
    ∃ old : Fin program.nodeCount,
      (program.suffixAt o).nodeAt u = program.nodeAt old := by
  induction program with
  | finish x => exact ⟨u, rfl⟩
  | step head tail ih =>
      cases o using Fin.cases with
      | zero => exact ⟨u, rfl⟩
      | succ o =>
          obtain ⟨old, hOld⟩ := ih o u
          exact ⟨Fin.succ old, hOld⟩

theorem suffixAt_isNodeSimple
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple)
    (o : Fin program.nodeCount) :
    (program.suffixAt o).IsNodeSimple := by
  induction program with
  | finish x => exact finish_isNodeSimple x
  | @step x y z head tail ih =>
      cases o using Fin.cases with
      | zero => exact hSimple
      | succ o =>
          apply ih
          intro a b hNode
          have hShifted :
              (ResidualProgram.step head tail).nodeAt (Fin.succ a) =
                (ResidualProgram.step head tail).nodeAt (Fin.succ b) := hNode
          exact Fin.succ_injective _ (hSimple hShifted)

structure SimpleReduction (original : family.ResidualProgram x z) where
  reduced : family.ResidualProgram x z
  isNodeSimple : reduced.IsNodeSimple
  node_mem_original :
    ∀ o : Fin reduced.nodeCount,
      ∃ old : Fin original.nodeCount,
        reduced.nodeAt o = original.nodeAt old

def SimpleReduction.ofStartEq
    {w : ResidualNode G} (original : family.ResidualProgram x z)
    (candidate : family.ResidualProgram w z) (hStart : w = x)
    (hSimple : candidate.IsNodeSimple)
    (hMem : ∀ o : Fin candidate.nodeCount,
      ∃ old : Fin original.nodeCount,
        candidate.nodeAt o = original.nodeAt old) :
    SimpleReduction original := by
  subst x
  exact
    { reduced := candidate
      isNodeSimple := hSimple
      node_mem_original := hMem }

/-- Node-level loop erasure for a concrete residual edit program. -/
def loopErase (program : family.ResidualProgram x z) :
    SimpleReduction program := by
  classical
  induction program with
  | finish x =>
      exact
        { reduced := .finish x
          isNodeSimple := finish_isNodeSimple x
          node_mem_original := fun o => ⟨o, rfl⟩ }
  | @step x y z head tail tailReduction =>
      let original : family.ResidualProgram x z := .step head tail
      by_cases hHeadOccurs :
          ∃ o : Fin tailReduction.reduced.nodeCount,
            tailReduction.reduced.nodeAt o = x
      · have hWitness : Nonempty
            {o : Fin tailReduction.reduced.nodeCount //
              tailReduction.reduced.nodeAt o = x} := by
          rcases hHeadOccurs with ⟨o, hNode⟩
          exact ⟨⟨o, hNode⟩⟩
        let witness := Classical.choice hWitness
        let o : Fin tailReduction.reduced.nodeCount := witness.1
        have hNode : tailReduction.reduced.nodeAt o = x := witness.2
        let candidate := tailReduction.reduced.suffixAt o
        have hCandidateSimple : candidate.IsNodeSimple :=
          tailReduction.reduced.suffixAt_isNodeSimple
            tailReduction.isNodeSimple o
        have hCandidateMem :
            ∀ u : Fin candidate.nodeCount,
              ∃ old : Fin original.nodeCount,
                candidate.nodeAt u = original.nodeAt old := by
          intro u
          obtain ⟨middle, hMiddle⟩ :=
            tailReduction.reduced.suffixAt_node_mem o u
          obtain ⟨old, hOld⟩ := tailReduction.node_mem_original middle
          exact ⟨Fin.succ old, hMiddle.trans hOld⟩
        simpa [original] using
          SimpleReduction.ofStartEq original candidate hNode
            hCandidateSimple hCandidateMem
      · refine
          { reduced := .step head tailReduction.reduced
            isNodeSimple := ?_
            node_mem_original := ?_ }
        · intro a b hNodes
          cases a using Fin.cases with
          | zero =>
              cases b using Fin.cases with
              | zero => rfl
              | succ b =>
                  exfalso
                  apply hHeadOccurs
                  exact ⟨b, hNodes.symm⟩
          | succ a =>
              cases b using Fin.cases with
              | zero =>
                  exfalso
                  apply hHeadOccurs
                  exact ⟨a, hNodes⟩
              | succ b =>
                  have hab : a = b := tailReduction.isNodeSimple hNodes
                  subst b
                  rfl
        · intro u
          cases u using Fin.cases with
          | zero => exact ⟨original.headOccurrence, rfl⟩
          | succ u =>
              obtain ⟨old, hOld⟩ := tailReduction.node_mem_original u
              exact ⟨Fin.succ old, hOld⟩

/-- Every residual augmenting reachability proof yields a concrete simple
source-to-sink edit program. -/
def simpleAugmentingProgram
    (family : G.VertexDisjointRightToLeftPaths s)
    (hReachable : family.HasResidualAugmentingWalk) :
    {program : family.ResidualProgram .source .sink //
      program.IsNodeSimple} := by
  let original := Classical.choice
    ((nonempty_residualProgram_iff_reachable family .source .sink).2 hReachable)
  exact ⟨original.loopErase.reduced, original.loopErase.isNodeSimple⟩


end ResidualProgram

end PartiteShape.VertexDisjointRightToLeftPaths

end GraphMatrixReplica
