import GraphMatrix.FiniteMengerResidualPathProjection
import GraphMatrix.IsolatedFormula21Application

/-! # Unconditional Menger-based intermediate flattening endpoints

The finite vertex-Menger theorem is now internal.  This file specializes the
paper's edge-ordering, role-side, exponent, and general isolated-middle
formula-(21) interfaces to the canonical clean certificate, leaving only the
genuinely analytic/row-column parameters in downstream statements.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The canonical clean right-left Menger certificate for a paper shape. -/
def PaperShape.unconditionalBoundaryCleanMengerCertificate (G : PaperShape) :
    G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate :=
  G.toPartiteShape.boundaryCleanRightLeftMengerCertificate

namespace PaperShape

variable (G : PaperShape)

abbrev UnconditionalMengerCertificate :=
  G.unconditionalBoundaryCleanMengerCertificate

abbrev UnconditionalIntermediateRoleSides :=
  G.toPartiteShape.IntermediateFlatteningRoleSides
    G.unconditionalBoundaryCleanMengerCertificate.paths

/-- The cut in the unconditional certificate has the internally defined
minimum-separator cardinality. -/
theorem unconditionalMengerCut_card_eq_separatorNumber :
    G.unconditionalBoundaryCleanMengerCertificate.cut.card =
      G.toPartiteShape.rightLeftSeparatorNumber := by
  let certificate := G.unconditionalBoundaryCleanMengerCertificate
  apply Nat.le_antisymm
  · exact certificate.cut_minimum.2
      G.toPartiteShape.minimumRightLeftSeparator
      G.toPartiteShape.minimumRightLeftSeparator_isMinimum.1
  · exact G.toPartiteShape.minimumRightLeftSeparator_isMinimum.2
      certificate.cut certificate.cut_minimum.1

/-- The canonical clean path family covers every nonisolated middle role by
the selected ordering prefix. -/
theorem unconditionalOrderingEdges_cover :
    G.toPartiteShape.CoversNonisolatedMiddle
      G.unconditionalBoundaryCleanMengerCertificate.paths.orderingEdges :=
  G.unconditionalBoundaryCleanMengerCertificate.paths.orderingEdges_cover

/-- BLNvH's special-edge prefix bound, with the external certificate removed
and its cut cardinality rewritten as the separator optimum. -/
theorem unconditionalOrderingEdges_card_le :
    G.unconditionalBoundaryCleanMengerCertificate.paths.orderingEdges.card ≤
      G.toPartiteShape.rightLeftSeparatorNumber -
          (G.toPartiteShape.leftBoundary ∩
            G.toPartiteShape.rightBoundary).card +
        (G.toPartiteShape.middleRoles.card -
          G.toPartiteShape.isolatedMiddleRoles.card) := by
  have h :=
    G.unconditionalBoundaryCleanMengerCertificate.card_orderingEdges_le
  have hCut := G.unconditionalMengerCut_card_eq_separatorNumber
  omega

/-- Every row/column assignment of the canonical ordering has overlap at
least the minimum separator. -/
theorem unconditionalSeparator_le_rowColOverlap
    (D : G.UnconditionalIntermediateRoleSides) :
    G.toPartiteShape.rightLeftSeparatorNumber ≤
      (D.rowRoles ∩ D.colRoles).card := by
  have h := D.cut_card_le_card_rowRoles_inter_colRoles
    G.unconditionalBoundaryCleanMengerCertificate
  have hCut := G.unconditionalMengerCut_card_eq_separatorNumber
  omega

/-- All roles outside the isolated middle set occur on at least one side of
every canonical intermediate flattening. -/
theorem unconditionalNonisolatedRoles_covered
    (D : G.UnconditionalIntermediateRoleSides) :
    Finset.univ \ G.toPartiteShape.isolatedMiddleRoles ⊆
      D.rowRoles ∪ D.colRoles :=
  D.univ_sdiff_isolatedMiddleRoles_subset_rowRoles_union_colRoles

/-- The paper exponent bound for arbitrary row/column choices, with no
Menger hypothesis. -/
theorem unconditionalExponentNumerator_le
    (D : G.UnconditionalIntermediateRoleSides) :
    D.exponentNumerator ≤
      G.roles - G.toPartiteShape.rightLeftSeparatorNumber +
        G.toPartiteShape.isolatedMiddleRoles.card := by
  have h := D.exponentNumerator_le_roles_sub_cut_add_isolated
    G.unconditionalBoundaryCleanMengerCertificate
  have hCut := G.unconditionalMengerCut_card_eq_separatorNumber
  change D.exponentNumerator ≤
    G.toPartiteShape.roles - G.toPartiteShape.rightLeftSeparatorNumber +
      G.toPartiteShape.isolatedMiddleRoles.card
  omega

/-- Formula (21) on the covered core is unconditional for every paper shape
and every row/column assignment of the canonical ordering. -/
theorem unconditionalCoveredCore_formula21_squaredNorm_le
    (D : G.UnconditionalIntermediateRoleSides)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖(paperIntermediateCoveredCoreData
        G G.unconditionalBoundaryCleanMengerCertificate
          D n orientation w).matrix‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent
        D.coveredRowRoles D.coveredColRoles :=
  paperIntermediateCoveredCore_formula21_squaredNorm_le
    G G.unconditionalBoundaryCleanMengerCertificate D n orientation w

/-- General-`W_iso` formula-(21) endpoint with the finite Menger certificate
fully discharged. -/
theorem unconditionalMarginalizedOriented_squaredNorm_le_separatorPower
    (D : G.UnconditionalIntermediateRoleSides)
    (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖paperIntermediateMarginalizedOrientedMatrix
        G G.unconditionalBoundaryCleanMengerCertificate
          D n orientation w‖ ^ 2 ≤
      (n : ℝ) ^
        (G.roles - G.toPartiteShape.rightLeftSeparatorNumber +
          G.isolatedMiddleRoles.card) := by
  have h :=
    paperIntermediateMarginalizedOriented_squaredNorm_le_minSeparatorPower
      G G.unconditionalBoundaryCleanMengerCertificate D n hn orientation w
  have hExponent :
      G.roles - G.unconditionalBoundaryCleanMengerCertificate.cut.card +
          G.isolatedMiddleRoles.card =
        G.roles - G.toPartiteShape.rightLeftSeparatorNumber +
          G.isolatedMiddleRoles.card := by
    have hCut := G.unconditionalMengerCut_card_eq_separatorNumber
    omega
  exact h.trans_eq (congrArg (fun e : ℕ => (n : ℝ) ^ e) hExponent)

end PaperShape


end GraphMatrixReplica
