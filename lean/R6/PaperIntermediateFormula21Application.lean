import R6.PaperIntermediateFlattening
import R6.PaperNearlyCombinatorialFlatteningSupport

/-! # Formula (21) for intermediate flattening role sides

This file connects the combinatorial role-side estimates for the BLNvH
intermediate flattening to the deterministic formula-(21) support bound.
When there are no isolated middle roles, the row and column sides cover every
role, so the concrete oriented assignment flattening from
`PaperNearlyCombinatorialFlatteningSupport` applies directly.

For a general shape the uncovered coordinates are not discarded: they form
an explicit factor indexed by omitted isolated middle roles.  Marginalizing
that factor is a separate later step, rather than an implicit decoupling or
NCK assertion here.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- A visible tuple has decidable equality because both its finite coordinate
domain and `Fin n` do.  Naming the noncomputable instance here makes the
operator-norm instance available already while elaborating theorem types. -/
noncomputable local instance paperIntermediateVisibleTupleDecidableEq
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (visible : Finset α) :
    DecidableEq (PaperVisibleTuple n visible) :=
  Classical.decEq _

namespace PartiteShape
namespace IntermediateFlatteningRoleSides

variable {H : PartiteShape} {s : ℕ}
    {family : H.BoundaryCleanRightToLeftPaths s}

/-- The generic complement-card exponent is exactly the intermediate
flattening's previously defined exponent numerator. -/
theorem complementExponent_eq_exponentNumerator
    (D : H.IntermediateFlatteningRoleSides family) :
    flatteningComplementExponent D.rowRoles D.colRoles =
      D.exponentNumerator := by
  have hRow : D.rowRoles ⊆ (Finset.univ : Finset (Fin H.roles)) :=
    Finset.subset_univ D.rowRoles
  have hCol : D.colRoles ⊆ (Finset.univ : Finset (Fin H.roles)) :=
    Finset.subset_univ D.colRoles
  have hRowCard : D.rowRoles.card ≤ H.roles := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card hRow
  have hColCard : D.colRoles.card ≤ H.roles := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card hCol
  unfold flatteningComplementExponent exponentNumerator
  rw [Finset.card_sdiff_of_subset hRow,
    Finset.card_sdiff_of_subset hCol]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- The omitted-coordinate set has at most one coordinate for each isolated
middle role. -/
theorem omittedRoles_card_le_isolatedMiddleRoles_card
    (D : H.IntermediateFlatteningRoleSides family) :
    (Finset.univ \ (D.rowRoles ∪ D.colRoles)).card ≤
      H.isolatedMiddleRoles.card :=
  Finset.card_le_card D.omittedRoles_subset_isolatedMiddleRoles

/-- Exact separation of formula (21)'s power into its covered-role core and
the factor belonging to coordinates omitted from both sides. -/
theorem complementRealPower_eq_core_mul_omittedPower
    (D : H.IntermediateFlatteningRoleSides family) (n : ℕ) :
    (n : ℝ) ^ flatteningComplementExponent D.rowRoles D.colRoles =
      (n : ℝ) ^
          (H.roles - (D.rowRoles ∩ D.colRoles).card) *
        (n : ℝ) ^
          (Finset.univ \ (D.rowRoles ∪ D.colRoles)).card := by
  rw [flatteningComplementExponent_eq, Fintype.card_fin, pow_add]

/-- Consequently the only extra power beyond the covered-role core is
bounded by `n ^ |W_iso|`.  This is the precise isolated-role marginalization
factor left for the general case. -/
theorem complementRealPower_le_core_mul_isolatedPower
    (D : H.IntermediateFlatteningRoleSides family)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ flatteningComplementExponent D.rowRoles D.colRoles ≤
      (n : ℝ) ^
          (H.roles - (D.rowRoles ∩ D.colRoles).card) *
        (n : ℝ) ^ H.isolatedMiddleRoles.card := by
  rw [D.complementRealPower_eq_core_mul_omittedPower n]
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_right₀
    · exact_mod_cast hn
    · exact D.omittedRoles_card_le_isolatedMiddleRoles_card
  · positivity

/-- With no isolated middle roles, the two intermediate sides cover the
entire role set. -/
theorem rowRoles_union_colRoles_eq_univ_of_isolatedMiddleRoles_eq_empty
    (D : H.IntermediateFlatteningRoleSides family)
    (hNoIso : H.isolatedMiddleRoles = ∅) :
    D.rowRoles ∪ D.colRoles = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  by_contra hNotMem
  have hOmitted :
      v ∈ Finset.univ \ (D.rowRoles ∪ D.colRoles) :=
    Finset.mem_sdiff.2 ⟨Finset.mem_univ v, hNotMem⟩
  have hIso : v ∈ H.isolatedMiddleRoles :=
    D.omittedRoles_subset_isolatedMiddleRoles hOmitted
  rw [hNoIso] at hIso
  simpa using hIso

/-- Any formula-(21) estimate on intermediate role sides inherits the
minimum-separator exponent, including the exact isolated-middle correction. -/
theorem formula21_squaredNorm_le_minSeparatorPower
    (certificate : H.BoundaryCleanRightLeftMengerCertificate)
    (D : H.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (hn : 1 ≤ n) (squaredNorm : ℝ)
    (hFormula21 : squaredNorm ≤
      (n : ℝ) ^ flatteningComplementExponent D.rowRoles D.colRoles) :
    squaredNorm ≤
      (n : ℝ) ^
        (H.roles - certificate.cut.card + H.isolatedMiddleRoles.card) := by
  refine hFormula21.trans ?_
  apply pow_le_pow_right₀
  · exact_mod_cast hn
  · rw [D.complementExponent_eq_exponentNumerator]
    exact D.exponentNumerator_le_roles_sub_cut_add_isolated certificate

end IntermediateFlatteningRoleSides
end PartiteShape

/-- Squared L2 operator norm of the concrete oriented intermediate
coordinate flattening.  Packaging the noncomputable finite-index norm in a
definition keeps later theorem statements independent of synthesized
classical equality instances. -/
noncomputable def paperIntermediateOrientedSquaredNorm
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (hCover : D.rowRoles ∪ D.colRoles = Finset.univ) : ℝ := by
  classical
  exact ‖(paperOrientedNearlyCombinatorialFlatteningData
    G n orientation w D.rowRoles D.colRoles hCover).matrix‖ ^ 2

/-- In the no-isolated-middle case, intermediate role sides cover every
paper role and therefore instantiate the concrete oriented assignment
flattening.  Given its raw formula-(21) estimate, the minimum-separator
exponent follows with no correction term. -/
theorem paperIntermediateOriented_formula21_squaredNorm_le_minSeparatorPower_of_no_isolated
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (hNoIso : G.toPartiteShape.isolatedMiddleRoles = ∅)
    (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (hFormula21 :
      paperIntermediateOrientedSquaredNorm
          G certificate D n orientation w
            (D.rowRoles_union_colRoles_eq_univ_of_isolatedMiddleRoles_eq_empty
              hNoIso) ≤
        (n : ℝ) ^ flatteningComplementExponent D.rowRoles D.colRoles) :
    paperIntermediateOrientedSquaredNorm
        G certificate D n orientation w
          (D.rowRoles_union_colRoles_eq_univ_of_isolatedMiddleRoles_eq_empty
            hNoIso) ≤
      (n : ℝ) ^ (G.roles - certificate.cut.card) := by
  classical
  have hBound :=
    D.formula21_squaredNorm_le_minSeparatorPower
      certificate n hn
        (paperIntermediateOrientedSquaredNorm
          G certificate D n orientation w
            (D.rowRoles_union_colRoles_eq_univ_of_isolatedMiddleRoles_eq_empty
              hNoIso))
        hFormula21
  have hExponent :
      G.toPartiteShape.roles - certificate.cut.card +
          G.toPartiteShape.isolatedMiddleRoles.card =
        G.roles - certificate.cut.card := by
    have hCardIso : G.toPartiteShape.isolatedMiddleRoles.card = 0 := by
      simpa only [Finset.card_empty] using congrArg Finset.card hNoIso
    rw [hCardIso, Nat.add_zero]
    rfl
  rw [hExponent] at hBound
  exact hBound

#print axioms
  PartiteShape.IntermediateFlatteningRoleSides.complementExponent_eq_exponentNumerator
#print axioms
  PartiteShape.IntermediateFlatteningRoleSides.complementRealPower_le_core_mul_isolatedPower
#print axioms
  PartiteShape.IntermediateFlatteningRoleSides.formula21_squaredNorm_le_minSeparatorPower
#print axioms
  paperIntermediateOriented_formula21_squaredNorm_le_minSeparatorPower_of_no_isolated

end GraphMatrixReplica
