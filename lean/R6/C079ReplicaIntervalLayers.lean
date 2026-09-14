import R6.C079PartitionInterval
import R6.C079DisjointPathLayerCount

/-! # C079 interval layers for actual fully-partite replica states

This module constructs the abstract interval certificate from an actual
`ReplicaState`.  It therefore closes the interval/separator/double-counting
part of C079 for the fully-partite edgewise-parity model.

It does not identify that model with the paper's globally injective,
shared-unordered-edge state space; such an identification is false without an
additional projectability hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Actual C079 interval certificate attached to a fully-partite replica
state.  `RoleCovered` is exactly what supplies the even-partition block cap at
every role, including boundary-isolated roles. -/
def ReplicaState.c079IntervalCertificate
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    C079IntervalCertificate G p where
  ell := fun v => c079PartitionLower (S.partition v)
  upper := fun v => c079PartitionUpper (S.partition v)
  upper_le := fun v => c079PartitionUpper_le_orderMinusOne (S.partition v)
  left_ell_zero := fun v hv =>
    leftTrace_c079PartitionLower_eq_zero (S.partition v) (S.leftGlue v hv)
  right_upper_eq := fun v hv =>
    rightTrace_c079PartitionUpper_eq_orderMinusOne
      (S.partition v) (S.rightGlue v hv)
  edge_intersects := by
    intro e v w hv hw
    have hSourceBlocks :
        partitionBlockCount (S.partition (G.source e)) ≤ p + 1 :=
      S.coveredRole_blockCount_le (G.source e) (hCovered (G.source e))
    have hTargetBlocks :
        partitionBlockCount (S.partition (G.target e)) ≤ p + 1 :=
      S.coveredRole_blockCount_le (G.target e) (hCovered (G.target e))
    have hST := edgeParity_c079PartitionIntervals_intersect
      (S.partition (G.source e)) (S.partition (G.target e)) (S.edgeParity e)
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · subst v
      subst w
      exact ⟨c079PartitionLower_le_upper _ hSourceBlocks,
        c079PartitionLower_le_upper _ hSourceBlocks⟩
    · subst v
      subst w
      exact hST
    · subst v
      subst w
      exact ⟨hST.2, hST.1⟩
    · subst v
      subst w
      exact ⟨c079PartitionLower_le_upper _ hTargetBlocks,
        c079PartitionLower_le_upper _ hTargetBlocks⟩

/-- The sum of actual C079 interval widths is exactly the state's total
partition defect. -/
theorem ReplicaState.c079_sum_intervalWidths_eq_totalDefect
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    (∑ v : Fin G.roles,
      (c079PartitionUpper (S.partition v) -
        c079PartitionLower (S.partition v))) = S.totalDefect := by
  unfold ReplicaState.totalDefect
  apply Finset.sum_congr rfl
  intro v _
  exact c079PartitionUpper_sub_lower (S.partition v)
    (S.coveredRole_blockCount_le v (hCovered v))

/-- Fully instantiated C079 equation (6): every horizontal layer is forced by
the actual parity and boundary data, and its total excess over an `s`-path
packing equals the state's total defect minus `s*p`. -/
theorem ReplicaState.c079_sum_layerExcess_eq_totalDefect_sub_paths
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s) :
    let C := S.c079IntervalCertificate hCovered
    (∑ k ∈ Finset.Icc 1 p,
      ((c079IntervalLayer C.ell C.upper k).card - s)) =
      S.totalDefect - s * p := by
  let C := S.c079IntervalCertificate hCovered
  have hExcess := C.sum_layer_excess_eq_of_disjointPaths family
  have hWidths := S.c079_sum_intervalWidths_eq_totalDefect hCovered
  simpa [C, ReplicaState.c079IntervalCertificate, hWidths] using hExcess

#print axioms ReplicaState.c079IntervalCertificate
#print axioms ReplicaState.c079_sum_intervalWidths_eq_totalDefect
#print axioms
  ReplicaState.c079_sum_layerExcess_eq_totalDefect_sub_paths

end GraphMatrixReplica
