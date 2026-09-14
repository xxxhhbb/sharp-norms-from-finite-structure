import R6.FiniteIntegralFlowPathDecomposition

/-! # The concrete augmented split-network flow

The old disjoint path family is encoded as an integral flow in the split
network.  The residual edit counts are then applied to it.  This is the
bridge from the residual program to the generic integral-flow decomposition.
-/

noncomputable section

open scoped BigOperators

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

open FiniteIntegralFlow

variable {G : PartiteShape} {s : ℕ}
variable {family : G.VertexDisjointRightToLeftPaths s}

def arcUnit (a b : ResidualNode G) : ResidualNode G → ResidualNode G → ℕ :=
  fun u v => if u = a ∧ v = b then 1 else 0

def addFlow (f g : ResidualNode G → ResidualNode G → ℕ) :
    ResidualNode G → ResidualNode G → ℕ :=
  fun u v => f u v + g u v

@[simp] theorem Out_addFlow (f g : ResidualNode G → ResidualNode G → ℕ)
    (v : ResidualNode G) :
    Out (addFlow f g) v = Out f v + Out g v := by
  simp [Out, addFlow, Finset.sum_add_distrib]

@[simp] theorem In_addFlow (f g : ResidualNode G → ResidualNode G → ℕ)
    (v : ResidualNode G) :
    In (addFlow f g) v = In f v + In g v := by
  simp [In, addFlow, Finset.sum_add_distrib]

@[simp] theorem Out_arcUnit (a b v : ResidualNode G) :
    Out (arcUnit a b) v = if v = a then 1 else 0 := by
  classical
  by_cases hva : v = a
  · subst v
    simp [Out, arcUnit]
  · simp [Out, arcUnit, hva]

@[simp] theorem In_arcUnit (a b v : ResidualNode G) :
    In (arcUnit a b) v = if v = b then 1 else 0 := by
  classical
  by_cases hvb : v = b
  · subst v
    simp [In, arcUnit]
  · simp [In, arcUnit, hvb]

theorem Excess_addFlow (f g : ResidualNode G → ResidualNode G → ℕ)
    (v : ResidualNode G) :
    Excess (addFlow f g) v = Excess f v + Excess g v := by
  change
    (Out (addFlow f g) v : ℤ) - (In (addFlow f g) v : ℤ) =
      ((Out f v : ℤ) - (In f v : ℤ)) +
        ((Out g v : ℤ) - (In g v : ℤ))
  rw [Out_addFlow, In_addFlow]
  push_cast
  ring

theorem Excess_arcUnit (a b v : ResidualNode G) :
    Excess (arcUnit a b) v =
      ((if v = a then 1 else 0) - (if v = b then 1 else 0) : ℤ) := by
  change
    (Out (arcUnit a b) v : ℤ) - (In (arcUnit a b) v : ℤ) = _
  rw [Out_arcUnit, In_arcUnit]
  split <;> split <;> simp

/-- Split-network flow of one old graph path, excluding its source arc. -/
def edgePathSplitFlow :
    {v : Fin G.roles} → G.EdgePathToLeft v →
      ResidualNode G → ResidualNode G → ℕ
  | v, .finish _ _ =>
      addFlow (arcUnit (.input v) (.output v))
        (arcUnit (.output v) .sink)
  | v, .step _ w _ _ tail =>
      addFlow (arcUnit (.input v) (.output v))
        (addFlow (arcUnit (.output v) (.input w)) (edgePathSplitFlow tail))

/-- One old path together with its source arc. -/
def edgePathFullSplitFlow
    {v : Fin G.roles} (path : G.EdgePathToLeft v) :
    ResidualNode G → ResidualNode G → ℕ :=
  addFlow (arcUnit .source (.input v)) (edgePathSplitFlow path)

theorem edgePathSplitFlow_excess
    {v : Fin G.roles} (path : G.EdgePathToLeft v) (node : ResidualNode G) :
    Excess (edgePathSplitFlow path) node =
      ((if node = .input v then 1 else 0) -
        (if node = .sink then 1 else 0) : ℤ) := by
  induction path with
  | finish v hLeft =>
      rw [edgePathSplitFlow, Excess_addFlow, Excess_arcUnit, Excess_arcUnit]
      split <;> split <;> split <;> simp_all <;> omega
  | @step v e w hAtStart hAtEnd tail ih =>
      rw [edgePathSplitFlow, Excess_addFlow, Excess_arcUnit,
        Excess_addFlow, Excess_arcUnit, ih]
      split <;> split <;> split <;> split <;>
        simp_all <;> omega

theorem edgePathFullSplitFlow_excess
    {v : Fin G.roles} (path : G.EdgePathToLeft v) (node : ResidualNode G) :
    Excess (edgePathFullSplitFlow path) node =
      ((if node = .source then 1 else 0) -
        (if node = .sink then 1 else 0) : ℤ) := by
  rw [edgePathFullSplitFlow, Excess_addFlow, Excess_arcUnit,
    edgePathSplitFlow_excess]
  split <;> split <;> split <;> simp_all <;> omega

/-- Integral split flow carried by the old path packing. -/
def oldSplitFlow (family : G.VertexDisjointRightToLeftPaths s) :
    ResidualNode G → ResidualNode G → ℕ :=
  fun u v => ∑ i : Fin s, edgePathFullSplitFlow (family.path i) u v

theorem Out_oldSplitFlow (family : G.VertexDisjointRightToLeftPaths s)
    (node : ResidualNode G) :
    Out (oldSplitFlow family) node =
      ∑ i : Fin s, Out (edgePathFullSplitFlow (family.path i)) node := by
  simp only [Out, oldSplitFlow]
  rw [Finset.sum_comm]

theorem In_oldSplitFlow (family : G.VertexDisjointRightToLeftPaths s)
    (node : ResidualNode G) :
    In (oldSplitFlow family) node =
      ∑ i : Fin s, In (edgePathFullSplitFlow (family.path i)) node := by
  simp only [In, oldSplitFlow]
  rw [Finset.sum_comm]

theorem oldSplitFlow_excess (family : G.VertexDisjointRightToLeftPaths s)
    (node : ResidualNode G) :
    Excess (oldSplitFlow family) node =
      (s : ℤ) * ((if node = .source then 1 else 0) -
        (if node = .sink then 1 else 0) : ℤ) := by
  change
    (Out (oldSplitFlow family) node : ℤ) -
        (In (oldSplitFlow family) node : ℤ) = _
  rw [Out_oldSplitFlow, In_oldSplitFlow]
  push_cast
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ _i : Fin s,
        ((if node = .source then 1 else 0) -
          (if node = .sink then 1 else 0) : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      change Excess (edgePathFullSplitFlow (family.path i)) node =
        ((if node = .source then 1 else 0) -
          (if node = .sink then 1 else 0) : ℤ)
      exact edgePathFullSplitFlow_excess (family.path i) node
    _ = _ := by split <;> split <;> simp_all

theorem edgePathSplitFlow_vertexArc_pos
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (o : Fin path.vertexCount) :
    0 < edgePathSplitFlow path (.input (path.vertexAt o))
      (.output (path.vertexAt o)) := by
  induction path with
  | finish v hLeft => simp [edgePathSplitFlow, addFlow, arcUnit,
      PartiteShape.EdgePathToLeft.vertexAt]
  | @step v e w hAtStart hAtEnd tail ih =>
      cases o using Fin.cases with
      | zero => simp [edgePathSplitFlow, addFlow, arcUnit,
          PartiteShape.EdgePathToLeft.vertexAt]
      | succ o =>
          have hTail := ih o
          change 0 < edgePathSplitFlow
            (PartiteShape.EdgePathToLeft.step e w hAtStart hAtEnd tail)
              (.input (tail.vertexAt o)) (.output (tail.vertexAt o))
          simp only [edgePathSplitFlow, addFlow]
          omega

theorem edgePathSplitFlow_forwardArc_pos
    {v a b : Fin G.roles} (path : G.EdgePathToLeft v)
    (hStep : path.HasForwardStep a b) :
    0 < edgePathSplitFlow path (.output a) (.input b) := by
  induction path with
  | finish v hLeft => simp [PartiteShape.EdgePathToLeft.HasForwardStep] at hStep
  | @step v e w hAtStart hAtEnd tail ih =>
      rcases hStep with hHead | hTail
      · rcases hHead with ⟨rfl, rfl⟩
        simp [edgePathSplitFlow, addFlow, arcUnit]
      · have hPos := ih hTail
        simp only [edgePathSplitFlow, addFlow]
        omega

theorem oldSplitFlow_vertexArc_pos (family : G.VertexDisjointRightToLeftPaths s)
    {v : Fin G.roles} (hUsed : v ∈ family.usedRoles) :
    0 < oldSplitFlow family (.input v) (.output v) := by
  obtain ⟨i, o, hRole⟩ := (family.mem_usedRoles_iff v).1 hUsed
  have hPath := edgePathSplitFlow_vertexArc_pos (family.path i) o
  have hFull : 0 < edgePathFullSplitFlow (family.path i)
      (.input v) (.output v) := by
    simp only [edgePathFullSplitFlow, addFlow]
    rw [← hRole]
    omega
  rw [oldSplitFlow]
  apply Finset.sum_pos'
  · exact fun _ _ => Nat.zero_le _
  · exact ⟨i, Finset.mem_univ i, hFull⟩

theorem oldSplitFlow_forwardArc_pos (family : G.VertexDisjointRightToLeftPaths s)
    {a b : Fin G.roles} (hPacked : family.PackedForwardStep a b) :
    0 < oldSplitFlow family (.output a) (.input b) := by
  obtain ⟨i, hStep⟩ := hPacked
  have hPath := edgePathSplitFlow_forwardArc_pos (family.path i) hStep
  have hFull : 0 < edgePathFullSplitFlow (family.path i)
      (.output a) (.input b) := by
    simp only [edgePathFullSplitFlow, addFlow]
    omega
  rw [oldSplitFlow]
  apply Finset.sum_pos'
  · exact fun _ _ => Nat.zero_le _
  · exact ⟨i, Finset.mem_univ i, hFull⟩

theorem oldSplitFlow_pos_of_mem_oldInteriorSupport
    (family : G.VertexDisjointRightToLeftPaths s)
    (arc : ResidualNode G × ResidualNode G)
    (hMem : arc ∈ ResidualProgram.oldInteriorFlowSupport family) :
    0 < oldSplitFlow family arc.1 arc.2 := by
  rcases arc with ⟨u, v⟩
  cases u <;> cases v <;>
    simp [ResidualProgram.oldInteriorFlowSupport] at hMem ⊢
  · rcases hMem with ⟨rfl, hUsed⟩
    exact oldSplitFlow_vertexArc_pos family hUsed
  · exact oldSplitFlow_forwardArc_pos family hMem

namespace ResidualProgram

theorem sum_if_fixed_target (P : Prop) [Decidable P]
    (a : ResidualNode G) (c : ℤ) :
    (∑ v : ResidualNode G, if P ∧ v = a then c else 0) =
      if P then c else 0 := by
  by_cases hP : P
  · simp [hP]
  · simp [hP]

theorem sum_if_fixed_source (P : Prop) [Decidable P]
    (a : ResidualNode G) (c : ℤ) :
    (∑ u : ResidualNode G, if u = a ∧ P then c else 0) =
      if P then c else 0 := by
  by_cases hP : P
  · simp [hP]
  · simp [hP]

theorem removeCount_le_oldSplitFlow
    (program : family.ResidualProgram x z) (hSimple : program.IsNodeSimple)
    (arc : ResidualNode G × ResidualNode G) :
    program.removeCount arc ≤ oldSplitFlow family arc.1 arc.2 := by
  by_cases hZero : program.removeCount arc = 0
  · simp [hZero]
  · have hPos : 0 < program.removeCount arc := Nat.pos_of_ne_zero hZero
    have hMem := program.removeCount_pos_mem_oldSupport arc hPos
    have hOldPos := oldSplitFlow_pos_of_mem_oldInteriorSupport family arc hMem
    have hAtMostOne := program.removeCount_le_one hSimple arc
    omega

/-- The nonnegative integral flow after applying all residual toggles. -/
def finalSplitFlow (program : family.ResidualProgram x z) :
    ResidualNode G → ResidualNode G → ℕ := fun u v =>
  oldSplitFlow family u v + program.addCount (u, v) -
    program.removeCount (u, v)

theorem finalSplitFlow_add_remove
    (program : family.ResidualProgram x z) (hSimple : program.IsNodeSimple)
    (u v : ResidualNode G) :
    program.finalSplitFlow u v + program.removeCount (u, v) =
      oldSplitFlow family u v + program.addCount (u, v) := by
  exact Nat.sub_add_cancel ((program.removeCount_le_oldSplitFlow hSimple (u, v)).trans
    (Nat.le_add_right _ _))

theorem finalSplitFlow_cast
    (program : family.ResidualProgram x z) (hSimple : program.IsNodeSimple)
    (u v : ResidualNode G) :
    (program.finalSplitFlow u v : ℤ) =
      (oldSplitFlow family u v : ℤ) + program.flowArcDelta u v := by
  rw [program.flowArcDelta_eq_counts (u, v)]
  have hRemoveLe : program.removeCount (u, v) ≤
      oldSplitFlow family u v + program.addCount (u, v) :=
    (program.removeCount_le_oldSplitFlow hSimple (u, v)).trans
      (Nat.le_add_right _ _)
  simp only [finalSplitFlow]
  rw [Int.ofNat_sub hRemoveLe]
  push_cast
  ring

theorem sum_flowArcDelta_out
    (program : family.ResidualProgram x z) (q : ResidualNode G) :
    (∑ v, program.flowArcDelta q v) = program.outDegreeDelta q := by
  induction program with
  | finish x => simp [flowArcDelta, outDegreeDelta]
  | step head tail ih =>
      simp only [flowArcDelta, outDegreeDelta, Finset.sum_add_distrib, ih]
      congr 1
      cases head <;>
        simp only [ResidualStepData.flowArcDelta,
          ResidualStepData.outDegreeDelta, sum_if_fixed_target]

theorem sum_flowArcDelta_in
    (program : family.ResidualProgram x z) (q : ResidualNode G) :
    (∑ u, program.flowArcDelta u q) = program.inDegreeDelta q := by
  induction program with
  | finish x => simp [flowArcDelta, inDegreeDelta]
  | step head tail ih =>
      simp only [flowArcDelta, inDegreeDelta, Finset.sum_add_distrib, ih]
      congr 1
      cases head <;>
        simp only [ResidualStepData.flowArcDelta,
          ResidualStepData.inDegreeDelta, sum_if_fixed_source]

theorem finalSplitFlow_excess
    (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple) (q : ResidualNode G) :
    Excess program.finalSplitFlow q =
      Excess (oldSplitFlow family) q +
        (program.outDegreeDelta q - program.inDegreeDelta q) := by
  change
    (Out program.finalSplitFlow q : ℤ) -
        (In program.finalSplitFlow q : ℤ) =
      ((Out (oldSplitFlow family) q : ℤ) -
        (In (oldSplitFlow family) q : ℤ)) + _
  simp only [Out, In]
  push_cast
  simp_rw [program.finalSplitFlow_cast hSimple]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    program.sum_flowArcDelta_out q, program.sum_flowArcDelta_in q]
  ring

theorem addCount_to_source_zero (program : family.ResidualProgram x z)
    (u : ResidualNode G) : program.addCount (u, .source) = 0 := by
  induction program with
  | finish x => simp [addCount]
  | step head tail ih =>
      cases head <;> simp [addCount, ResidualStepData.addsArc,
        ResidualStepData.addedFlowArc?, ih]

theorem removeCount_to_source_zero (program : family.ResidualProgram x z)
    (u : ResidualNode G) : program.removeCount (u, .source) = 0 := by
  induction program with
  | finish x => simp [removeCount]
  | step head tail ih =>
      cases head <;> simp [removeCount, ResidualStepData.removesArc,
        ResidualStepData.removedFlowArc?, ih]

theorem addCount_from_sink_zero (program : family.ResidualProgram x z)
    (v : ResidualNode G) : program.addCount (.sink, v) = 0 := by
  induction program with
  | finish x => simp [addCount]
  | step head tail ih =>
      cases head <;> simp [addCount, ResidualStepData.addsArc,
        ResidualStepData.addedFlowArc?, ih]

theorem removeCount_from_sink_zero (program : family.ResidualProgram x z)
    (v : ResidualNode G) : program.removeCount (.sink, v) = 0 := by
  induction program with
  | finish x => simp [removeCount]
  | step head tail ih =>
      cases head <;> simp [removeCount, ResidualStepData.removesArc,
        ResidualStepData.removedFlowArc?, ih]

end ResidualProgram

theorem edgePathSplitFlow_to_source_zero
    {v : Fin G.roles} (path : G.EdgePathToLeft v) (u : ResidualNode G) :
    edgePathSplitFlow path u .source = 0 := by
  induction path with
  | finish v hLeft => simp [edgePathSplitFlow, addFlow, arcUnit]
  | step e w hAtStart hAtEnd tail ih =>
      simp [edgePathSplitFlow, addFlow, arcUnit, ih]

theorem edgePathSplitFlow_from_sink_zero
    {v : Fin G.roles} (path : G.EdgePathToLeft v) (w : ResidualNode G) :
    edgePathSplitFlow path .sink w = 0 := by
  induction path with
  | finish v hLeft => simp [edgePathSplitFlow, addFlow, arcUnit]
  | step e w hAtStart hAtEnd tail ih =>
      simp [edgePathSplitFlow, addFlow, arcUnit, ih]

theorem oldSplitFlow_to_source_zero
    (family : G.VertexDisjointRightToLeftPaths s) (u : ResidualNode G) :
    oldSplitFlow family u .source = 0 := by
  simp [oldSplitFlow, edgePathFullSplitFlow, addFlow, arcUnit,
    edgePathSplitFlow_to_source_zero]

theorem oldSplitFlow_from_sink_zero
    (family : G.VertexDisjointRightToLeftPaths s) (v : ResidualNode G) :
    oldSplitFlow family .sink v = 0 := by
  simp [oldSplitFlow, edgePathFullSplitFlow, addFlow, arcUnit,
    edgePathSplitFlow_from_sink_zero]

theorem ResidualProgram.finalSplitFlow_noIn_source
    (program : family.ResidualProgram .source .sink) :
    In program.finalSplitFlow .source = 0 := by
  simp [In, ResidualProgram.finalSplitFlow, oldSplitFlow_to_source_zero,
    program.addCount_to_source_zero, program.removeCount_to_source_zero]

theorem ResidualProgram.finalSplitFlow_noOut_sink
    (program : family.ResidualProgram .source .sink) :
    Out program.finalSplitFlow .sink = 0 := by
  simp [Out, ResidualProgram.finalSplitFlow, oldSplitFlow_from_sink_zero,
    program.addCount_from_sink_zero, program.removeCount_from_sink_zero]

theorem ResidualProgram.finalSplitFlow_source_value
    (program : family.ResidualProgram .source .sink)
    (hSimple : program.IsNodeSimple) :
    Out program.finalSplitFlow .source = s + 1 := by
  have hExcess := program.finalSplitFlow_excess hSimple (.source)
  rw [oldSplitFlow_excess] at hExcess
  rw [program.augmentingProgram_source_balance] at hExcess
  have hNoIn := program.finalSplitFlow_noIn_source
  change (Out program.finalSplitFlow .source : ℤ) -
      (In program.finalSplitFlow .source : ℤ) = _ at hExcess
  rw [hNoIn] at hExcess
  simp at hExcess
  exact_mod_cast hExcess

theorem ResidualProgram.finalSplitFlow_internal_conserve
    (program : family.ResidualProgram .source .sink)
    (hSimple : program.IsNodeSimple) (q : ResidualNode G)
    (hSource : q ≠ .source) (hSink : q ≠ .sink) :
    Excess program.finalSplitFlow q = 0 := by
  rw [program.finalSplitFlow_excess hSimple,
    oldSplitFlow_excess, program.augmentingProgram_internal_balance q hSource hSink]
  simp [hSource, hSink]

/-- The concrete augmented flow decomposes into exactly `s+1` simple split
source-to-sink paths. -/
theorem ResidualProgram.exists_augmentedSplitPathDecomposition
    (program : family.ResidualProgram .source .sink)
    (hSimple : program.IsNodeSimple) :
    Nonempty (UnitPathDecomposition (.source : ResidualNode G) .sink
      program.finalSplitFlow (s + 1)) := by
  have h := exists_unitPathDecomposition program.finalSplitFlow
    (.source : ResidualNode G) .sink (by simp)
    program.finalSplitFlow_noIn_source program.finalSplitFlow_noOut_sink
    (program.finalSplitFlow_internal_conserve hSimple)
  simpa [program.finalSplitFlow_source_value hSimple] using h

end PartiteShape.VertexDisjointRightToLeftPaths

end GraphMatrixReplica
