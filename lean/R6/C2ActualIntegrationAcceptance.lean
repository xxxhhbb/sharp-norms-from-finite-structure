import R6.C2ActualAssignmentSplit
import R6.C2AllSeparatorContraction
import R6.C2ActualChaosReindex
import R6.C2ActualMatrixExpansion
import R6.C2ActualMixedFlattening
import R6.C2ActualWeightedFlattening
import R6.C2Actual

/-!
# C2-ACTUAL integration acceptance entry

This file is intentionally outside `lean/R6`: local Codex should merge the
new `lean/R6/*.lean` files into the current project source tree, then elaborate
this file against the same project.  The acceptance theorems below restate the
substantive A/B/C/D targets using the actual model objects; they do not add any
bridge hypothesis that the task asks to eliminate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.PaperR16.C2ActualIntegrationCheck

open GraphMatrixReplica
open GraphMatrixReplica.P2a
open GraphMatrixReplica.PaperR16
open GraphMatrixReplica.PaperR16.ActualPrimitiveObservations
open GraphMatrixReplica.PaperR16.C2Actual


attribute [local instance] Classical.propDecidable

/-! ## A. Arbitrary separator contraction and P2a diagonal specialization -/

/-- Acceptance A1: for every separator assignment, the contraction assembled
from actual owner edges equals the all-separator contraction. -/
theorem accept_A_all_separator_contraction
    {G : PartiteShape} (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (ω : FrozenSample cut dimension)
    (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) :
    ownedComponentContraction cut dimension ω s K =
      actualComponentContraction cut dimension ω s K := by
  exact ownedComponentContraction_eq_actual cut dimension ω s K

/-- Acceptance A2: on an actual P2a diagonal separator trial, the arbitrary
separator contraction is exactly the pre-existing P2a contraction, using the
restrictions of the same frozen primitive sample. -/
theorem accept_A_p2a_diagonal_specialization
    {G : PartiteShape} (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (ω : FrozenSample cut dimension)
    (N : ℕ) (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (i : Fin N) (K : ActiveComponent G cut) :
    actualComponentContraction cut dimension ω
        (separatorTrial dimension N hN i) K =
      componentContraction dimension N hN
        (frozenInternalCube cut dimension ω)
        (frozenRestCube cut dimension ω) i K := by
  exact actualComponentContraction_eq_p2a cut dimension ω N hN i K

/-! ## B. Actual fresh chaos equals the original typed matrix -/

/-- Acceptance B: after the concrete fresh-coordinate encoding, the generated
heterogeneous chaos is literally the real coercion of the current
`partiteBoundaryMatrix` at the assembled original edge sample. -/
theorem accept_B_actual_matrix_connection
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (ξ : FreshSample (G := P.toPartiteShape) S dimension) :
    lowerHeteroChaos (freshCount P S) (freshSize P S dimension)
        (actualCoefficientFamily P S dimension ω)
        (freshSampleNoiseEquiv P S dimension ξ) =
      partiteBoundaryMatrixReal P dimension
        (assembleSample (G := P.toPartiteShape) S dimension ω ξ) := by
  exact lowerHeteroChaos_actual_eq_partiteBoundaryMatrixReal
    P S dimension ω ξ

/-! ## C. Actual mixed flattening reindex and removal of hReindexNorm -/

/-- Acceptance C1: the concrete mixed flattening is the actual retained-address
coefficient after the semantic row/column reindex. -/
theorem accept_C_entrywise_reindex
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    lowerMixedFlatten (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (actualCoefficientFamily P S dimension ω) =
      Matrix.reindex (actualRowEquiv P dimension S) (actualColEquiv P dimension S)
        (C1C2.retainedAddressCoefficient P S (X dimension)
          (c1c2ActualWeight P S dimension ω)) := by
  exact lowerMixedFlatten_actual_reindex P dimension S ω

/-- Acceptance C2: the old external `hReindexNorm` premise is now a theorem in
the native Euclidean L2 operator norm. -/
theorem accept_C_norm_reindex
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    (@norm (Matrix (lowerMixedRows (freshCount P S) (freshSize P S dimension) (freshDir P S) (PartiteBoundaryRow (G := P.toPartiteShape) dimension)) (lowerMixedCols (freshCount P S) (freshSize P S dimension) (freshDir P S) (PartiteBoundaryCol (G := P.toPartiteShape) dimension)) ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm (lowerMixedFlatten (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (actualCoefficientFamily P S dimension ω))) =
      @norm (Matrix (RowAddress P S (X dimension)) (ColAddress P S (X dimension)) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm
        (C1C2.retainedAddressCoefficient P S (X dimension) (c1c2ActualWeight P S dimension ω)) := by
  exact actual_mixed_reindex_norm P dimension S ω

/-! ## D. Final actual C2 lower bound -/

/-- Acceptance D / final task target.  The only hypotheses are the legal
geometry assumptions from the prompt, positive heterogeneous role dimensions,
and the fixed nonfresh realization.  In particular, there is no input named or
equivalent to `hCover`, `hInter`, or `hReindexNorm`. -/
theorem accept_D_actual_C2_lower_bound
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v : Fin P.roles, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    actualC2CoefficientScale P S dimension ω ≤
      Real.sqrt 3 ^ freshCount P S * actualC2FreshMean P S dimension ω := by
  exact actual_C2_lower_bound P S dimension hNoIsolated hMin hdim ω

/-! ## Required declaration/axiom inspection -/

#check GraphMatrixReplica.PaperR16.C2Actual.ownedComponentContraction_eq_actual
#check GraphMatrixReplica.PaperR16.C2Actual.actualComponentContraction_eq_p2a
#check GraphMatrixReplica.PaperR16.C2Actual.lowerHeteroChaos_actual_eq_partiteBoundaryMatrixReal
#check GraphMatrixReplica.PaperR16.C2Actual.lowerMixedFlatten_actual_reindex
#check GraphMatrixReplica.PaperR16.C2Actual.actual_mixed_reindex_norm
#check GraphMatrixReplica.PaperR16.C2Actual.actualRetainedCoefficientNormProof
#check GraphMatrixReplica.PaperR16.C2Actual.actualCoefficientNormProof
#check GraphMatrixReplica.PaperR16.C2Actual.actual_C2_lower_bound

#print GraphMatrixReplica.PaperR16.C2Actual.ownedComponentContraction_eq_actual
#print axioms GraphMatrixReplica.PaperR16.C2Actual.ownedComponentContraction_eq_actual
#print GraphMatrixReplica.PaperR16.C2Actual.actualComponentContraction_eq_p2a
#print axioms GraphMatrixReplica.PaperR16.C2Actual.actualComponentContraction_eq_p2a

#print GraphMatrixReplica.PaperR16.C2Actual.lowerHeteroChaos_actual_eq_partiteBoundaryMatrixReal
#print axioms GraphMatrixReplica.PaperR16.C2Actual.lowerHeteroChaos_actual_eq_partiteBoundaryMatrixReal

#print GraphMatrixReplica.PaperR16.C2Actual.lowerMixedFlatten_actual_reindex
#print axioms GraphMatrixReplica.PaperR16.C2Actual.lowerMixedFlatten_actual_reindex
#print GraphMatrixReplica.PaperR16.C2Actual.actual_mixed_reindex_norm
#print axioms GraphMatrixReplica.PaperR16.C2Actual.actual_mixed_reindex_norm

#print GraphMatrixReplica.PaperR16.C2Actual.actualRetainedCoefficientNormProof
#print axioms GraphMatrixReplica.PaperR16.C2Actual.actualRetainedCoefficientNormProof
#print GraphMatrixReplica.PaperR16.C2Actual.actualCoefficientNormProof
#print axioms GraphMatrixReplica.PaperR16.C2Actual.actualCoefficientNormProof

#print GraphMatrixReplica.PaperR16.C2Actual.actual_C2_lower_bound
#print axioms GraphMatrixReplica.PaperR16.C2Actual.actual_C2_lower_bound

#check accept_A_all_separator_contraction
#check accept_A_p2a_diagonal_specialization
#check accept_B_actual_matrix_connection
#check accept_C_entrywise_reindex
#check accept_C_norm_reindex
#check accept_D_actual_C2_lower_bound

#print accept_A_all_separator_contraction
#print axioms accept_A_all_separator_contraction
#print accept_A_p2a_diagonal_specialization
#print axioms accept_A_p2a_diagonal_specialization
#print accept_B_actual_matrix_connection
#print axioms accept_B_actual_matrix_connection
#print accept_C_entrywise_reindex
#print axioms accept_C_entrywise_reindex
#print accept_C_norm_reindex
#print axioms accept_C_norm_reindex
#print accept_D_actual_C2_lower_bound
#print axioms accept_D_actual_C2_lower_bound

end GraphMatrixReplica.PaperR16.C2ActualIntegrationCheck
