import GraphMatrix.Lower.Flattening.ActualAssignmentSplit
import GraphMatrix.Lower.Flattening.AllSeparatorContraction
import GraphMatrix.Lower.Flattening.ActualChaosReindex
import GraphMatrix.Lower.Flattening.ActualMatrixExpansion
import GraphMatrix.Lower.Flattening.ActualMixedFlattening
import GraphMatrix.Lower.Flattening.ActualWeightedFlattening
import GraphMatrix.Lower.Flattening.ContractionBound

/-!
# Separator contraction and weighted flattening

The theorems identify the contractions, sample reindexings and retained-address
matrices used in the lower bound, and assemble the weighted flattening estimate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model.FlatteningTheorems

open GraphMatrixReplica
open GraphMatrixReplica.P2a
open GraphMatrixReplica.Model
open GraphMatrixReplica.Model.ActualPrimitiveObservations
open GraphMatrixReplica.Model.C2Actual


attribute [local instance] Classical.propDecidable

/-!
# Separator contraction and weighted flattening

The theorems identify the contractions, sample reindexings and retained-address
matrices used in the lower bound, and assemble the weighted flattening estimate.
-/

/-- for every separator assignment, the contraction assembled
from actual owner edges equals the all-separator contraction. -/
theorem all_separator_contraction_eq
    {G : PartiteShape} (cut : Finset (Fin G.roles))
    (dimension : Fin G.roles → ℕ)
    (ω : FrozenSample cut dimension)
    (s : CutAssignment cut dimension)
    (K : ActiveComponent G cut) :
    ownedComponentContraction cut dimension ω s K =
      actualComponentContraction cut dimension ω s K := by
  exact ownedComponentContraction_eq_actual cut dimension ω s K

/-- on an actual diagonal separator trial, the arbitrary
separator contraction is exactly the pre-existing contraction, using the
restrictions of the same frozen primitive sample. -/
theorem diagonal_contraction_eq
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

/-!
# Separator contraction and weighted flattening

The theorems identify the contractions, sample reindexings and retained-address
matrices used in the lower bound, and assemble the weighted flattening estimate.
-/

/-- after the concrete fresh-coordinate encoding, the generated
heterogeneous chaos is literally the real coercion of the current
`partiteBoundaryMatrix` at the assembled original edge sample. -/
theorem matrix_expansion_eq
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

/-!
# Separator contraction and weighted flattening

The theorems identify the contractions, sample reindexings and retained-address
matrices used in the lower bound, and assemble the weighted flattening estimate.
-/

/-- the concrete mixed flattening is the actual retained-address
coefficient after the semantic row/column reindex. -/
theorem flattening_entry_reindex
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    lowerMixedFlatten (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (actualCoefficientFamily P S dimension ω) =
      Matrix.reindex (actualRowEquiv P dimension S) (actualColEquiv P dimension S)
        (C1C2.retainedAddressCoefficient P S (X dimension)
          (c1c2ActualWeight P S dimension ω)) := by
  exact lowerMixedFlatten_actual_reindex P dimension S ω

/-- the old external `hReindexNorm` premise is now a theorem in
the native Euclidean L2 operator norm. -/
theorem flattening_norm_reindex
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    (@norm (Matrix (lowerMixedRows (freshCount P S) (freshSize P S dimension) (freshDir P S) (PartiteBoundaryRow (G := P.toPartiteShape) dimension)) (lowerMixedCols (freshCount P S) (freshSize P S dimension) (freshDir P S) (PartiteBoundaryCol (G := P.toPartiteShape) dimension)) ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm (lowerMixedFlatten (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (actualCoefficientFamily P S dimension ω))) =
      @norm (Matrix (RowAddress P S (X dimension)) (ColAddress P S (X dimension)) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm
        (C1C2.retainedAddressCoefficient P S (X dimension) (c1c2ActualWeight P S dimension ω)) := by
  exact actual_mixed_reindex_norm P dimension S ω

/-!
# Separator contraction and weighted flattening

The theorems identify the contractions, sample reindexings and retained-address
matrices used in the lower bound, and assemble the weighted flattening estimate.
-/

/-- Weighted flattening bound.  The only hypotheses are the legal
geometry assumptions from the prompt, positive heterogeneous role dimensions,
and the fixed nonfresh realization.  In particular, there is no input named or
equivalent to `hCover`, `hInter`, or `hReindexNorm`. -/
theorem weighted_flattening_lower_bound
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v : Fin P.roles, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    actualC2CoefficientScale P S dimension ω ≤
      Real.sqrt 3 ^ freshCount P S * actualC2FreshMean P S dimension ω := by
  exact actual_C2_lower_bound P S dimension hNoIsolated hMin hdim ω

/-!
# Separator contraction and weighted flattening

The theorems identify the contractions, sample reindexings and retained-address
matrices used in the lower bound, and assemble the weighted flattening estimate.
-/


end GraphMatrixReplica.Model.FlatteningTheorems
