import R6.FiniteMengerResidualCut
import Mathlib.Data.List.Chain

/-! # Finite witnesses and the residual symmetric-difference invariant

This file advances the remaining augmentation direction.  A residual
source-to-sink reachability proof is converted to an explicit finite chain.
The chain is normalized to begin at a right-boundary input and end at a
left-boundary output.

We also formalize the Euler-characteristic invariant behind toggling the
chain.  Input-to-output transitions either add a vertex or delete a packed
edge and have edit delta `+1`; output-to-input transitions either delete a
vertex or add a graph edge and have edit delta `-1`.  Boundary transitions
have delta zero.  These deltas telescope, so every source-to-sink residual
chain has total edit delta exactly one.
-/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}

/-- An explicit finite residual chain starting at the source and ending at
the sink. -/
structure ResidualWalkWitness
    (family : G.VertexDisjointRightToLeftPaths s) where
  tail : List (ResidualNode G)
  isChain : (ResidualNode.source :: tail).IsChain family.ResidualTransition
  getLast_eq_sink :
    (ResidualNode.source :: tail).getLast (by simp) = ResidualNode.sink

/-- Type-valued data behind the proposition-valued residual relation.  This
is the form needed by the eventual symmetric-difference program: it retains
the graph edge or packed-step witness selected at every transition. -/
inductive ResidualStepData
    (family : G.VertexDisjointRightToLeftPaths s) :
    ResidualNode G → ResidualNode G → Type
  | fromSource {v} (hRight : v ∈ G.rightBoundary) :
      ResidualStepData family .source (.input v)
  | throughUnused {v} (hUnused : v ∉ family.usedRoles) :
      ResidualStepData family (.input v) (.output v)
  | backThroughUsed {v} (hUsed : v ∈ family.usedRoles) :
      ResidualStepData family (.output v) (.input v)
  | alongEdge {e a b}
      (hAtA : G.EdgeIncident e a) (hAtB : G.EdgeIncident e b) :
      ResidualStepData family (.output a) (.input b)
  | reversePackedStep {a b} (hPacked : family.PackedForwardStep a b) :
      ResidualStepData family (.input b) (.output a)
  | toSink {v} (hLeft : v ∈ G.leftBoundary) :
      ResidualStepData family (.output v) .sink

theorem ResidualStepData.toTransition
    {family : G.VertexDisjointRightToLeftPaths s}
    {x y : ResidualNode G} :
    ResidualStepData family x y → family.ResidualTransition x y
  | .fromSource h => .fromSource h
  | .throughUnused h => .throughUnused h
  | .backThroughUsed h => .backThroughUsed h
  | .alongEdge ha hb => .alongEdge ha hb
  | .reversePackedStep h => .reversePackedStep h
  | .toSink h => .toSink h

theorem nonempty_residualStepData_iff_transition
    (family : G.VertexDisjointRightToLeftPaths s)
    (x y : ResidualNode G) :
    Nonempty (ResidualStepData family x y) ↔
      family.ResidualTransition x y := by
  constructor
  · rintro ⟨step⟩
    exact step.toTransition
  · intro h
    cases h with
    | fromSource hRight => exact ⟨.fromSource hRight⟩
    | throughUnused hUnused => exact ⟨.throughUnused hUnused⟩
    | backThroughUsed hUsed => exact ⟨.backThroughUsed hUsed⟩
    | alongEdge hAtA hAtB => exact ⟨.alongEdge hAtA hAtB⟩
    | reversePackedStep hPacked => exact ⟨.reversePackedStep hPacked⟩
    | toSink hLeft => exact ⟨.toSink hLeft⟩

/-- A type-valued chain retaining one concrete residual edit at every adjacent
pair of nodes. -/
inductive ResidualStepChain
    (family : G.VertexDisjointRightToLeftPaths s) :
    List (ResidualNode G) → Type
  | nil : ResidualStepChain family []
  | singleton (x) : ResidualStepChain family [x]
  | cons {x y rest} (head : ResidualStepData family x y)
      (tail : ResidualStepChain family (y :: rest)) :
      ResidualStepChain family (x :: y :: rest)

theorem nonempty_residualStepChain_iff_isChain
    (family : G.VertexDisjointRightToLeftPaths s)
    (nodes : List (ResidualNode G)) :
    Nonempty (ResidualStepChain family nodes) ↔
      nodes.IsChain family.ResidualTransition := by
  constructor
  · rintro ⟨chain⟩
    induction chain with
    | nil => exact .nil
    | singleton x => exact .singleton x
    | cons head tail ih => exact .cons_cons head.toTransition ih
  · intro hChain
    induction nodes with
    | nil => exact ⟨.nil⟩
    | cons x rest ih =>
        cases rest with
        | nil => exact ⟨.singleton x⟩
        | cons y rest =>
            have hHead : family.ResidualTransition x y :=
              (List.isChain_cons_cons.mp hChain).1
            have hTail : (y :: rest).IsChain family.ResidualTransition :=
              (List.isChain_cons_cons.mp hChain).2
            obtain ⟨headData⟩ :=
              (family.nonempty_residualStepData_iff_transition x y).2 hHead
            obtain ⟨tailData⟩ := ih hTail
            exact ⟨.cons headData tailData⟩

def ResidualWalkWitness.stepChain
    {family : G.VertexDisjointRightToLeftPaths s}
    (witness : family.ResidualWalkWitness) :
    ResidualStepChain family (ResidualNode.source :: witness.tail) :=
  Classical.choice
    ((family.nonempty_residualStepChain_iff_isChain _).2 witness.isChain)

theorem nonempty_residualWalkWitness_iff
    (family : G.VertexDisjointRightToLeftPaths s) :
    Nonempty family.ResidualWalkWitness ↔
      family.HasResidualAugmentingWalk := by
  constructor
  · rintro ⟨witness⟩
    exact List.relationReflTransGen_of_exists_isChain_cons
      witness.tail witness.isChain witness.getLast_eq_sink
  · intro hReachable
    rcases List.exists_isChain_cons_of_relationReflTransGen hReachable with
      ⟨tail, hChain, hLast⟩
    exact ⟨⟨tail, hChain, hLast⟩⟩

/-- Source-to-sink reachability has a boundary-normalized middle residual
walk, from some right input to some left output. -/
theorem residualAugmentingWalk_decomposition
    (family : G.VertexDisjointRightToLeftPaths s)
    (hReachable : family.HasResidualAugmentingWalk) :
    ∃ u : Fin G.roles, u ∈ G.rightBoundary ∧
      ∃ v : Fin G.roles, v ∈ G.leftBoundary ∧
        Relation.ReflTransGen family.ResidualTransition
          (.input u) (.output v) := by
  rcases Relation.ReflTransGen.cases_head hReachable with
    hSourceSink | ⟨first, hFirst, hRest⟩
  · cases hSourceSink
  · cases hFirst with
    | fromSource hRight =>
        rcases Relation.ReflTransGen.cases_tail hRest with
          hInputSink | ⟨last, hMiddle, hLast⟩
        · cases hInputSink
        · cases hLast with
          | toSink hLeft => exact ⟨_, hRight, _, hLeft, hMiddle⟩

/-- Potential distinguishing the input and output sides of the split
network.  The sink is placed on the output side and the source on the input
side. -/
def residualPotential : ResidualNode G → ℤ
  | .source => 0
  | .sink => 1
  | .input _ => 0
  | .output _ => 1

/-- Euler edit delta of a residual transition.  The `+1` cases correspond to
adding a vertex or deleting a packed edge; the `-1` cases correspond to
deleting a packed vertex or adding a graph edge. -/
def residualEditDelta : ResidualNode G → ResidualNode G → ℤ
  | .input _, .output _ => 1
  | .output _, .input _ => -1
  | _, _ => 0

theorem residualTransition_editDelta
    (family : G.VertexDisjointRightToLeftPaths s)
    {x y : ResidualNode G} (h : family.ResidualTransition x y) :
    residualEditDelta x y = residualPotential y - residualPotential x := by
  cases h <;> rfl

/-- Constructor-level edit delta.  Unlike the node-only delta, this definition
remembers which symmetric-difference operation is performed. -/
def ResidualStepData.editDelta
    {family : G.VertexDisjointRightToLeftPaths s}
    {x y : ResidualNode G} : ResidualStepData family x y → ℤ
  | .fromSource _ => 0
  | .throughUnused _ => 1
  | .backThroughUsed _ => -1
  | .alongEdge _ _ => -1
  | .reversePackedStep _ => 1
  | .toSink _ => 0

theorem ResidualStepData.editDelta_eq
    {family : G.VertexDisjointRightToLeftPaths s}
    {x y : ResidualNode G} (step : ResidualStepData family x y) :
    step.editDelta = residualEditDelta x y := by
  cases step <;> rfl

/-- Total constructor-level delta of a typed residual chain. -/
def ResidualStepChain.editDelta
    {family : G.VertexDisjointRightToLeftPaths s} :
    {nodes : List (ResidualNode G)} → ResidualStepChain family nodes → ℤ
  | _, .nil => 0
  | _, .singleton _ => 0
  | _, .cons head tail => head.editDelta + tail.editDelta

/-- Sum the edit deltas of consecutive nodes of a finite walk. -/
def residualWalkEditDelta : List (ResidualNode G) → ℤ
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
      residualEditDelta x y + residualWalkEditDelta (y :: rest)

theorem ResidualStepChain.editDelta_eq_walkEditDelta
    {family : G.VertexDisjointRightToLeftPaths s}
    {nodes : List (ResidualNode G)}
    (chain : ResidualStepChain family nodes) :
    chain.editDelta = residualWalkEditDelta nodes := by
  induction chain with
  | nil => rfl
  | singleton x => rfl
  | cons head tail ih =>
      simp only [ResidualStepChain.editDelta, residualWalkEditDelta,
        head.editDelta_eq, ih]

/-- The local symmetric-difference edit invariant telescopes along any
residual chain. -/
theorem residualWalkEditDelta_eq_potential_sub
    (family : G.VertexDisjointRightToLeftPaths s)
    (nodes : List (ResidualNode G)) (hNonempty : nodes ≠ [])
    (hChain : nodes.IsChain family.ResidualTransition) :
    residualWalkEditDelta nodes =
      residualPotential (nodes.getLast hNonempty) -
        residualPotential (nodes.head hNonempty) := by
  induction nodes using List.twoStepInduction with
  | nil => exact (hNonempty rfl).elim
  | singleton x => simp [residualWalkEditDelta]
  | cons_cons x y rest _ih ihTail =>
      have hStep : family.ResidualTransition x y :=
        (List.isChain_cons_cons.mp hChain).1
      have hTail : (y :: rest).IsChain family.ResidualTransition :=
        (List.isChain_cons_cons.mp hChain).2
      rw [residualWalkEditDelta,
        ihTail y (by simp) hTail,
        family.residualTransition_editDelta hStep]
      simp only [List.getLast_cons_cons, List.head_cons]
      ring

/-- The symmetric-difference Euler characteristic of a source-to-sink
residual witness increases by exactly one. -/
theorem ResidualWalkWitness.editDelta_eq_one
    {family : G.VertexDisjointRightToLeftPaths s}
    (witness : family.ResidualWalkWitness) :
    residualWalkEditDelta (ResidualNode.source :: witness.tail) = 1 := by
  rw [family.residualWalkEditDelta_eq_potential_sub
    (ResidualNode.source :: witness.tail) (by simp) witness.isChain]
  rw [witness.getLast_eq_sink]
  rfl

/-- The retained type-valued edit program has net Euler delta one. -/
theorem ResidualWalkWitness.stepChain_editDelta_eq_one
    {family : G.VertexDisjointRightToLeftPaths s}
    (witness : family.ResidualWalkWitness) :
    witness.stepChain.editDelta = 1 := by
  rw [witness.stepChain.editDelta_eq_walkEditDelta]
  exact witness.editDelta_eq_one

#print axioms nonempty_residualWalkWitness_iff
#print axioms residualAugmentingWalk_decomposition
#print axioms ResidualWalkWitness.editDelta_eq_one
#print axioms ResidualWalkWitness.stepChain_editDelta_eq_one

end PartiteShape.VertexDisjointRightToLeftPaths

end GraphMatrixReplica
