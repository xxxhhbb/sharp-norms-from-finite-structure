import R6.FiniteMengerResidualBalance

/-! # Global unit capacity along a node-simple residual program -/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}
variable {family : G.VertexDisjointRightToLeftPaths s}
variable {x y z : ResidualNode G}

namespace ResidualProgram

theorem tail_isNodeSimple
    (head : ResidualStepData family x y)
    (tail : family.ResidualProgram y z)
    (hSimple : (ResidualProgram.step head tail).IsNodeSimple) :
    tail.IsNodeSimple := by
  intro a b hEq
  apply Fin.succ_injective _
  apply hSimple
  exact hEq

theorem head_ne_tail_node
    (head : ResidualStepData family x y)
    (tail : family.ResidualProgram y z)
    (hSimple : (ResidualProgram.step head tail).IsNodeSimple)
    (o : Fin tail.nodeCount) :
    x ≠ tail.nodeAt o := by
  intro hEq
  have hNodes :
      (ResidualProgram.step head tail).nodeAt
          (ResidualProgram.step head tail).headOccurrence =
        (ResidualProgram.step head tail).nodeAt (Fin.succ o) := by
    change x = tail.nodeAt o
    exact hEq
  have hIndices := hSimple hNodes
  have hVals := congrArg Fin.val hIndices
  simp [headOccurrence] at hVals

theorem addedVertex?_eq_some
    (head : ResidualStepData family x y) (v : Fin G.roles) :
    head.addedVertex? = some v → x = .input v ∧ y = .output v := by
  cases head <;> simp [ResidualStepData.addedVertex?]

theorem removedVertex?_eq_some
    (head : ResidualStepData family x y) (v : Fin G.roles) :
    head.removedVertex? = some v → x = .output v ∧ y = .input v := by
  cases head <;> simp [ResidualStepData.removedVertex?]

theorem input_node_of_mem_addedVertexRoles
    (program : family.ResidualProgram x z) {v : Fin G.roles}
    (hMem : v ∈ program.addedVertexRoles) :
    ∃ o : Fin program.nodeCount, program.nodeAt o = .input v := by
  induction program with
  | finish x => simp [addedVertexRoles] at hMem
  | @step x y z head tail ih =>
      cases hHead : head.addedVertex? with
      | none =>
          have hTail : v ∈ tail.addedVertexRoles := by
            simpa [addedVertexRoles, hHead] using hMem
          obtain ⟨o, ho⟩ := ih hTail
          exact ⟨Fin.succ o, ho⟩
      | some v₀ =>
          have hEnds := addedVertex?_eq_some head v₀ hHead
          have h : v = v₀ ∨ v ∈ tail.addedVertexRoles := by
            simpa [addedVertexRoles, hHead] using hMem
          rcases h with rfl | hTail
          · exact ⟨(ResidualProgram.step head tail).headOccurrence, by
              simpa [hEnds.1]⟩
          · obtain ⟨o, ho⟩ := ih hTail
            exact ⟨Fin.succ o, ho⟩

theorem output_node_of_mem_addedVertexRoles
    (program : family.ResidualProgram x z) {v : Fin G.roles}
    (hMem : v ∈ program.addedVertexRoles) :
    ∃ o : Fin program.nodeCount, program.nodeAt o = .output v := by
  induction program with
  | finish x => simp [addedVertexRoles] at hMem
  | @step x y z head tail ih =>
      cases hHead : head.addedVertex? with
      | none =>
          have hTail : v ∈ tail.addedVertexRoles := by
            simpa [addedVertexRoles, hHead] using hMem
          obtain ⟨o, ho⟩ := ih hTail
          exact ⟨Fin.succ o, ho⟩
      | some v₀ =>
          have hEnds := addedVertex?_eq_some head v₀ hHead
          have h : v = v₀ ∨ v ∈ tail.addedVertexRoles := by
            simpa [addedVertexRoles, hHead] using hMem
          rcases h with rfl | hTail
          · exact ⟨Fin.succ tail.headOccurrence, by
              change tail.nodeAt tail.headOccurrence = .output v
              simpa [hEnds.2]⟩
          · obtain ⟨o, ho⟩ := ih hTail
            exact ⟨Fin.succ o, ho⟩

theorem input_node_of_mem_removedVertexRoles
    (program : family.ResidualProgram x z) {v : Fin G.roles}
    (hMem : v ∈ program.removedVertexRoles) :
    ∃ o : Fin program.nodeCount, program.nodeAt o = .input v := by
  induction program with
  | finish x => simp [removedVertexRoles] at hMem
  | @step x y z head tail ih =>
      cases hHead : head.removedVertex? with
      | none =>
          have hTail : v ∈ tail.removedVertexRoles := by
            simpa [removedVertexRoles, hHead] using hMem
          obtain ⟨o, ho⟩ := ih hTail
          exact ⟨Fin.succ o, ho⟩
      | some v₀ =>
          have hEnds := removedVertex?_eq_some head v₀ hHead
          have h : v = v₀ ∨ v ∈ tail.removedVertexRoles := by
            simpa [removedVertexRoles, hHead] using hMem
          rcases h with rfl | hTail
          · exact ⟨Fin.succ tail.headOccurrence, by
              change tail.nodeAt tail.headOccurrence = .input v
              simpa [hEnds.2]⟩
          · obtain ⟨o, ho⟩ := ih hTail
            exact ⟨Fin.succ o, ho⟩

theorem output_node_of_mem_removedVertexRoles
    (program : family.ResidualProgram x z) {v : Fin G.roles}
    (hMem : v ∈ program.removedVertexRoles) :
    ∃ o : Fin program.nodeCount, program.nodeAt o = .output v := by
  induction program with
  | finish x => simp [removedVertexRoles] at hMem
  | @step x y z head tail ih =>
      cases hHead : head.removedVertex? with
      | none =>
          have hTail : v ∈ tail.removedVertexRoles := by
            simpa [removedVertexRoles, hHead] using hMem
          obtain ⟨o, ho⟩ := ih hTail
          exact ⟨Fin.succ o, ho⟩
      | some v₀ =>
          have hEnds := removedVertex?_eq_some head v₀ hHead
          have h : v = v₀ ∨ v ∈ tail.removedVertexRoles := by
            simpa [removedVertexRoles, hHead] using hMem
          rcases h with rfl | hTail
          · exact ⟨(ResidualProgram.step head tail).headOccurrence, by
              simpa [hEnds.1]⟩
          · obtain ⟨o, ho⟩ := ih hTail
            exact ⟨Fin.succ o, ho⟩

theorem throughUnused_not_mem_tail_added
    {v : Fin G.roles} (hUnused : v ∉ family.usedRoles)
    (tail : family.ResidualProgram (.output v) z)
    (hSimple :
      (ResidualProgram.step
        (ResidualStepData.throughUnused hUnused) tail).IsNodeSimple) :
    v ∉ tail.addedVertexRoles := by
  intro hMem
  obtain ⟨o, ho⟩ := tail.input_node_of_mem_addedVertexRoles hMem
  exact
    ((head_ne_tail_node (ResidualStepData.throughUnused hUnused)
      tail hSimple o) ho.symm)

theorem throughUnused_not_mem_tail_removed
    {v : Fin G.roles} (hUnused : v ∉ family.usedRoles)
    (tail : family.ResidualProgram (.output v) z)
    (hSimple :
      (ResidualProgram.step
        (ResidualStepData.throughUnused hUnused) tail).IsNodeSimple) :
    v ∉ tail.removedVertexRoles := by
  intro hMem
  obtain ⟨o, ho⟩ := tail.input_node_of_mem_removedVertexRoles hMem
  exact
    ((head_ne_tail_node (ResidualStepData.throughUnused hUnused)
      tail hSimple o) ho.symm)

theorem backThroughUsed_not_mem_tail_added
    {v : Fin G.roles} (hUsed : v ∈ family.usedRoles)
    (tail : family.ResidualProgram (.input v) z)
    (hSimple :
      (ResidualProgram.step
        (ResidualStepData.backThroughUsed hUsed) tail).IsNodeSimple) :
    v ∉ tail.addedVertexRoles := by
  intro hMem
  obtain ⟨o, ho⟩ := tail.output_node_of_mem_addedVertexRoles hMem
  exact
    ((head_ne_tail_node (ResidualStepData.backThroughUsed hUsed)
      tail hSimple o) ho.symm)

theorem backThroughUsed_not_mem_tail_removed
    {v : Fin G.roles} (hUsed : v ∈ family.usedRoles)
    (tail : family.ResidualProgram (.input v) z)
    (hSimple :
      (ResidualProgram.step
        (ResidualStepData.backThroughUsed hUsed) tail).IsNodeSimple) :
    v ∉ tail.removedVertexRoles := by
  intro hMem
  obtain ⟨o, ho⟩ := tail.output_node_of_mem_removedVertexRoles hMem
  exact
    ((head_ne_tail_node (ResidualStepData.backThroughUsed hUsed)
      tail hSimple o) ho.symm)

/-- On a node-simple program, the signed change of a vertex-capacity arc is
exactly its add-indicator minus its remove-indicator. -/
theorem flowArcDelta_vertex_eq_indicators
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple) (v : Fin G.roles) :
    program.flowArcDelta (.input v) (.output v) =
      (if v ∈ program.addedVertexRoles then 1 else 0) -
        (if v ∈ program.removedVertexRoles then 1 else 0) := by
  induction program with
  | finish x =>
      simp [flowArcDelta, addedVertexRoles, removedVertexRoles]
  | @step x y z head tail ih =>
      have hTailSimple := tail_isNodeSimple head tail hSimple
      have hIH := ih hTailSimple
      cases head with
      | fromSource hRight =>
          simp only [flowArcDelta, addedVertexRoles, removedVertexRoles,
            ResidualStepData.flowArcDelta,
            ResidualStepData.addedVertex?, ResidualStepData.removedVertex?]
          rw [hIH]
          by_cases hAdd : v ∈ tail.addedVertexRoles <;>
            by_cases hRemove : v ∈ tail.removedVertexRoles <;>
            simp [hAdd, hRemove]

      | @throughUnused v₀ hUnused =>
          have hNoAdd := throughUnused_not_mem_tail_added hUnused tail hSimple
          have hNoRemove :=
            throughUnused_not_mem_tail_removed hUnused tail hSimple
          by_cases hv : v = v₀
          · subst v
            simp [flowArcDelta, addedVertexRoles, removedVertexRoles,
              ResidualStepData.flowArcDelta,
              ResidualStepData.addedVertex?, ResidualStepData.removedVertex?,
              hNoAdd, hNoRemove, hIH]
          · simp only [flowArcDelta, addedVertexRoles, removedVertexRoles,
              ResidualStepData.flowArcDelta,
              ResidualStepData.addedVertex?, ResidualStepData.removedVertex?]
            rw [hIH]
            simp [hv]
            rfl
      | @backThroughUsed v₀ hUsed =>
          have hNoAdd := backThroughUsed_not_mem_tail_added hUsed tail hSimple
          have hNoRemove :=
            backThroughUsed_not_mem_tail_removed hUsed tail hSimple
          by_cases hv : v = v₀
          · subst v
            simp [flowArcDelta, addedVertexRoles, removedVertexRoles,
              ResidualStepData.flowArcDelta,
              ResidualStepData.addedVertex?, ResidualStepData.removedVertex?,
              hNoAdd, hNoRemove, hIH]
          · simp only [flowArcDelta, addedVertexRoles, removedVertexRoles,
              ResidualStepData.flowArcDelta,
              ResidualStepData.addedVertex?, ResidualStepData.removedVertex?]
            rw [hIH]
            simp [hv]
            rfl
      | alongEdge hAtA hAtB =>
          simp only [flowArcDelta, addedVertexRoles, removedVertexRoles,
            ResidualStepData.flowArcDelta,
            ResidualStepData.addedVertex?, ResidualStepData.removedVertex?]
          rw [hIH]
          by_cases hAdd : v ∈ tail.addedVertexRoles <;>
            by_cases hRemove : v ∈ tail.removedVertexRoles <;>
            simp [hAdd, hRemove]
      | reversePackedStep hPacked =>
          simp only [flowArcDelta, addedVertexRoles, removedVertexRoles,
            ResidualStepData.flowArcDelta,
            ResidualStepData.addedVertex?, ResidualStepData.removedVertex?]
          rw [hIH]
          by_cases hAdd : v ∈ tail.addedVertexRoles <;>
            by_cases hRemove : v ∈ tail.removedVertexRoles <;>
            simp [hAdd, hRemove]
      | toSink hLeft =>
          simp only [flowArcDelta, addedVertexRoles, removedVertexRoles,
            ResidualStepData.flowArcDelta,
            ResidualStepData.addedVertex?, ResidualStepData.removedVertex?]
          rw [hIH]
          by_cases hAdd : v ∈ tail.addedVertexRoles <;>
            by_cases hRemove : v ∈ tail.removedVertexRoles <;>
            simp [hAdd, hRemove]

/-- Occupancy of a vertex-capacity arc after executing the signed program. -/
def finalVertexOccupancy
    (program : family.ResidualProgram x z) (v : Fin G.roles) : ℤ :=
  family.oldVertexOccupancy v +
    program.flowArcDelta (.input v) (.output v)

/-- A node-simple residual edit program realizes exactly the set-theoretic
toggle constructed in `FiniteMengerResidualToggle`. -/
theorem finalVertexOccupancy_eq_toggled_indicator
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple) (v : Fin G.roles) :
    program.finalVertexOccupancy v =
      if v ∈ program.toggledUsedRoles then 1 else 0 := by
  rw [finalVertexOccupancy,
    program.flowArcDelta_vertex_eq_indicators hSimple]
  have hAddOld :
      v ∈ program.addedVertexRoles → v ∉ family.usedRoles := by
    intro hAdd hOld
    exact Finset.disjoint_left.mp
      program.addedVertexRoles_disjoint_usedRoles hAdd hOld
  have hRemoveOld :
      v ∈ program.removedVertexRoles → v ∈ family.usedRoles := by
    exact fun h => program.removedVertexRoles_subset_usedRoles h
  have hAddRemove :
      v ∈ program.addedVertexRoles →
        v ∉ program.removedVertexRoles := by
    intro hAdd hRemove
    exact Finset.disjoint_left.mp
      program.addedVertexRoles_disjoint_removedVertexRoles hAdd hRemove
  by_cases hOld : v ∈ family.usedRoles <;>
    by_cases hAdd : v ∈ program.addedVertexRoles <;>
    by_cases hRemove : v ∈ program.removedVertexRoles <;>
    simp [oldVertexOccupancy, toggledUsedRoles, hOld, hAdd, hRemove] at *

theorem finalVertexOccupancy_isUnit
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple) (v : Fin G.roles) :
    program.finalVertexOccupancy v = 0 ∨
      program.finalVertexOccupancy v = 1 := by
  rw [program.finalVertexOccupancy_eq_toggled_indicator hSimple]
  by_cases hMem : v ∈ program.toggledUsedRoles <;> simp [hMem]

theorem finalVertexOccupancy_nonneg
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple) (v : Fin G.roles) :
    0 ≤ program.finalVertexOccupancy v := by
  rcases program.finalVertexOccupancy_isUnit hSimple v with h | h <;>
    omega

theorem finalVertexOccupancy_le_one
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple) (v : Fin G.roles) :
    program.finalVertexOccupancy v ≤ 1 := by
  rcases program.finalVertexOccupancy_isUnit hSimple v with h | h <;>
    omega

#print axioms flowArcDelta_vertex_eq_indicators
#print axioms finalVertexOccupancy_eq_toggled_indicator
#print axioms finalVertexOccupancy_isUnit

end ResidualProgram

end PartiteShape.VertexDisjointRightToLeftPaths

end GraphMatrixReplica
