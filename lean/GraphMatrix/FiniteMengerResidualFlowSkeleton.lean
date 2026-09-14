import GraphMatrix.FiniteMengerResidualGlobalCapacity

/-! # Counted residual flow edits -/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}
variable {family : G.VertexDisjointRightToLeftPaths s}
variable {x y z : ResidualNode G}

def ResidualStepData.removedFlowArc?
    {x y : ResidualNode G} :
    ResidualStepData family x y →
      Option (ResidualNode G × ResidualNode G)
  | .backThroughUsed (v := v) _ => some (.input v, .output v)
  | .reversePackedStep (a := a) (b := b) _ =>
      some (.output a, .input b)
  | _ => none

def ResidualStepData.addedFlowArc?
    {x y : ResidualNode G} :
    ResidualStepData family x y →
      Option (ResidualNode G × ResidualNode G)
  | .fromSource (v := v) _ => some (.source, .input v)
  | .throughUnused (v := v) _ => some (.input v, .output v)
  | .alongEdge (a := a) (b := b) _ _ =>
      some (.output a, .input b)
  | .toSink (v := v) _ => some (.output v, .sink)
  | _ => none

def ResidualStepData.addsArc
    {x y : ResidualNode G} (step : ResidualStepData family x y)
    (arc : ResidualNode G × ResidualNode G) : ℕ :=
  if step.addedFlowArc? = some arc then 1 else 0

def ResidualStepData.removesArc
    {x y : ResidualNode G} (step : ResidualStepData family x y)
    (arc : ResidualNode G × ResidualNode G) : ℕ :=
  if step.removedFlowArc? = some arc then 1 else 0

theorem ResidualStepData.flowArcDelta_eq_counts
    {x y : ResidualNode G} (step : ResidualStepData family x y)
    (arc : ResidualNode G × ResidualNode G) :
    step.flowArcDelta arc.1 arc.2 =
      (step.addsArc arc : ℤ) - (step.removesArc arc : ℤ) := by
  cases step <;>
    simp [ResidualStepData.flowArcDelta, ResidualStepData.addsArc,
      ResidualStepData.removesArc, ResidualStepData.addedFlowArc?,
      ResidualStepData.removedFlowArc?] <;>
    aesop

namespace ResidualProgram

def addCount {x z : ResidualNode G} :
    family.ResidualProgram x z →
      (ResidualNode G × ResidualNode G) → ℕ
  | .finish _, _ => 0
  | .step head tail, arc => head.addsArc arc + tail.addCount arc

def removeCount {x z : ResidualNode G} :
    family.ResidualProgram x z →
      (ResidualNode G × ResidualNode G) → ℕ
  | .finish _, _ => 0
  | .step head tail, arc => head.removesArc arc + tail.removeCount arc

theorem flowArcDelta_eq_counts
    (program : family.ResidualProgram x z)
    (arc : ResidualNode G × ResidualNode G) :
    program.flowArcDelta arc.1 arc.2 =
      (program.addCount arc : ℤ) - (program.removeCount arc : ℤ) := by
  induction program with
  | finish x => simp [flowArcDelta, addCount, removeCount]
  | step head tail ih =>
      rw [flowArcDelta, addCount, removeCount,
        head.flowArcDelta_eq_counts arc, ih]
      push_cast
      ring

theorem nodes_of_removeCount_pos
    (program : family.ResidualProgram x z)
    (arc : ResidualNode G × ResidualNode G)
    (hPos : 0 < program.removeCount arc) :
    (∃ o : Fin program.nodeCount, program.nodeAt o = arc.1) ∧
      ∃ o : Fin program.nodeCount, program.nodeAt o = arc.2 := by
  induction program with
  | finish x => simp [removeCount] at hPos
  | @step x y z head tail ih =>
      by_cases hHead : head.removedFlowArc? = some arc
      · have hEnds : arc = (y, x) := by
          cases head <;>
            simp [ResidualStepData.removedFlowArc?] at hHead ⊢ <;>
            aesop
        subst arc
        constructor
        · exact ⟨Fin.succ tail.headOccurrence, by
            change tail.nodeAt tail.headOccurrence = y
            simp⟩
        · exact ⟨(ResidualProgram.step head tail).headOccurrence, by simp⟩
      · have hTailPos : 0 < tail.removeCount arc := by
          simpa [removeCount, ResidualStepData.removesArc, hHead] using hPos
        obtain ⟨⟨oa, ha⟩, ⟨ob, hb⟩⟩ := ih hTailPos
        exact ⟨⟨Fin.succ oa, ha⟩, ⟨Fin.succ ob, hb⟩⟩

theorem removeCount_le_one
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple)
    (arc : ResidualNode G × ResidualNode G) :
    program.removeCount arc ≤ 1 := by
  induction program with
  | finish x => simp [removeCount]
  | @step x y z head tail ih =>
      have hTailSimple := tail_isNodeSimple head tail hSimple
      by_cases hHead : head.removedFlowArc? = some arc
      · have hEnds : arc = (y, x) := by
          cases head <;>
            simp [ResidualStepData.removedFlowArc?] at hHead ⊢ <;>
            aesop
        have hTailZero : tail.removeCount arc = 0 := by
          by_contra hNe
          have hPos : 0 < tail.removeCount arc := Nat.pos_of_ne_zero hNe
          obtain ⟨_, ⟨o, ho⟩⟩ := tail.nodes_of_removeCount_pos arc hPos
          apply head_ne_tail_node head tail hSimple o
          have hox : tail.nodeAt o = x := by
            simpa [hEnds] using ho
          exact hox.symm
        simp [removeCount, ResidualStepData.removesArc, hHead, hTailZero]
      · have hLe := ih hTailSimple
        simpa [removeCount, ResidualStepData.removesArc, hHead] using hLe

def oldInteriorFlowSupport
    (family : G.VertexDisjointRightToLeftPaths s) :
    Finset (ResidualNode G × ResidualNode G) := by
  classical
  exact Finset.univ.filter fun arc =>
    match arc with
    | (.input v, .output w) => v = w ∧ v ∈ family.usedRoles
    | (.output a, .input b) => family.PackedForwardStep a b
    | _ => False

theorem removedFlowArc_mem_oldSupport
    {x y : ResidualNode G} (step : ResidualStepData family x y)
    (arc : ResidualNode G × ResidualNode G)
    (hRemove : step.removedFlowArc? = some arc) :
    arc ∈ oldInteriorFlowSupport family := by
  cases step <;>
    simp [ResidualStepData.removedFlowArc?, oldInteriorFlowSupport] at hRemove ⊢ <;>
    aesop

theorem removeCount_pos_mem_oldSupport
    (program : family.ResidualProgram x z)
    (arc : ResidualNode G × ResidualNode G)
    (hPos : 0 < program.removeCount arc) :
    arc ∈ oldInteriorFlowSupport family := by
  induction program with
  | finish x => simp [removeCount] at hPos
  | step head tail ih =>
      by_cases hHead : head.removedFlowArc? = some arc
      · exact removedFlowArc_mem_oldSupport head arc hHead
      · apply ih
        simpa [removeCount, ResidualStepData.removesArc, hHead] using hPos

theorem augmentingProgram_source_value
    (program : family.ResidualProgram .source .sink) :
    (s : ℤ) +
        (program.outDegreeDelta .source - program.inDegreeDelta .source) =
      s + 1 := by
  rw [program.augmentingProgram_source_balance]

theorem augmentingProgram_sink_value
    (program : family.ResidualProgram .source .sink) :
    (-(s : ℤ)) +
        (program.outDegreeDelta .sink - program.inDegreeDelta .sink) =
      -(s : ℤ) - 1 := by
  rw [program.augmentingProgram_sink_balance]
  ring

theorem finalInteriorFlow_nonneg
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple)
    (arc : ResidualNode G × ResidualNode G) :
    0 ≤ (if arc ∈ oldInteriorFlowSupport family then (1 : ℤ) else 0) +
      program.flowArcDelta arc.1 arc.2 := by
  rw [program.flowArcDelta_eq_counts arc]
  have hRemoveLe := program.removeCount_le_one hSimple arc
  by_cases hZero : program.removeCount arc = 0
  · have hAddNonneg : 0 ≤ (program.addCount arc : ℤ) := by omega
    by_cases hMem : arc ∈ oldInteriorFlowSupport family <;>
      simp [hZero, hMem] <;> omega
  · have hPos : 0 < program.removeCount arc := Nat.pos_of_ne_zero hZero
    have hMem := program.removeCount_pos_mem_oldSupport arc hPos
    have hOne : program.removeCount arc = 1 := by omega
    simp [hMem, hOne]

end ResidualProgram

end PartiteShape.VertexDisjointRightToLeftPaths

end GraphMatrixReplica
