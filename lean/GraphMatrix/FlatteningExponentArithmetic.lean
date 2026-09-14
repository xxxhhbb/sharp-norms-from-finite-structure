import GraphMatrix.FinalFlattening

/-! # Exponent arithmetic for paper flattenings

BLNvH v2, formula (21), bounds the squared norm of a flattening by the
uniform-size power whose exponent is the sum of the numbers of row-only and
column-only complementary roles.  This file proves the finite-set identity
that rewrites that exponent as

`|V| - |rowRoles ∩ colRoles| + |V \ (rowRoles ∪ colRoles)|`.

The generic lemmas are independent of `PaperFinalFlattening`, so the same
arithmetic can be reused for intermediate flattenings.  The final theorems
combine the identity with `PaperFinalFlattening.exponentNumerator_le` and give
both natural-valued and real-valued squared-norm transport interfaces.  No
square-root or half-exponent convention is introduced here.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Formula (21)'s squared-norm exponent for two finite sets of visible
coordinates, with complements taken inside the ambient finite type. -/
def flatteningComplementExponent
    {α : Type*} [Fintype α] [DecidableEq α]
    (row col : Finset α) : ℕ :=
  (Finset.univ \ row).card + (Finset.univ \ col).card

/-- Inclusion-exclusion form of the complement exponent.  This is stated for
an arbitrary finite type so that final and intermediate flattenings can share
the same arithmetic layer. -/
theorem flatteningComplementExponent_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (row col : Finset α) :
    flatteningComplementExponent row col =
      Fintype.card α - (row ∩ col).card +
        (Finset.univ \ (row ∪ col)).card := by
  have hRow : row.card ≤ Fintype.card α := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ row)
  have hCol : col.card ≤ Fintype.card α := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ col)
  have hUnion : (row ∪ col).card ≤ Fintype.card α := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ (row ∪ col))
  have hInterRow : (row ∩ col).card ≤ row.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hInterCol : (row ∩ col).card ≤ col.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hRowUnion : row.card ≤ (row ∪ col).card :=
    Finset.card_le_card Finset.subset_union_left
  have hColUnion : col.card ≤ (row ∪ col).card :=
    Finset.card_le_card Finset.subset_union_right
  have hInclusionExclusion := Finset.card_union_add_card_inter row col
  unfold flatteningComplementExponent
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ row),
    Finset.card_sdiff_of_subset (Finset.subset_univ col),
    Finset.card_sdiff_of_subset (Finset.subset_univ (row ∪ col))]
  simp only [Finset.card_univ]
  omega

/-- Reusable power comparison: a lower bound on the row/column overlap and an
upper bound on the omitted set give the corresponding uniform-size exponent
bound. -/
theorem flatteningComplementPower_le_of_card_bounds
    {α : Type*} [Fintype α] [DecidableEq α]
    (row col : Finset α) (n overlapCap omittedCap : ℕ)
    (hn : 1 ≤ n)
    (hOverlap : overlapCap ≤ (row ∩ col).card)
    (hOmitted : (Finset.univ \ (row ∪ col)).card ≤ omittedCap) :
    n ^ flatteningComplementExponent row col ≤
      n ^ (Fintype.card α - overlapCap + omittedCap) := by
  apply Nat.pow_le_pow_right hn
  rw [flatteningComplementExponent_eq]
  exact Nat.add_le_add
    (Nat.sub_le_sub_left hOverlap (Fintype.card α)) hOmitted

/-- Real-valued version of the same power comparison, intended for direct use
after a squared operator/Frobenius norm estimate. -/
theorem flatteningComplementRealPower_le_of_card_bounds
    {α : Type*} [Fintype α] [DecidableEq α]
    (row col : Finset α) (n overlapCap omittedCap : ℕ)
    (hn : 1 ≤ n)
    (hOverlap : overlapCap ≤ (row ∩ col).card)
    (hOmitted : (Finset.univ \ (row ∪ col)).card ≤ omittedCap) :
    (n : ℝ) ^ flatteningComplementExponent row col ≤
      (n : ℝ) ^ (Fintype.card α - overlapCap + omittedCap) := by
  apply pow_le_pow_right₀
  · exact_mod_cast hn
  · rw [flatteningComplementExponent_eq]
    exact Nat.add_le_add
      (Nat.sub_le_sub_left hOverlap (Fintype.card α)) hOmitted

/-- For a paper final flattening, the generic complement exponent is exactly
the numerator bounded in `PaperFinalFlattening.exponentNumerator_le`. -/
theorem PaperFinalFlattening.complementExponent_eq_exponentNumerator
    {G : PaperShape} (F : PaperFinalFlattening G) :
    flatteningComplementExponent F.rowRoles F.colRoles =
      G.roles - F.separatorRoles.card + F.omittedRoles.card := by
  simpa only [flatteningComplementExponent_eq, Fintype.card_fin,
    PaperFinalFlattening.separatorRoles,
    PaperFinalFlattening.omittedRoles]

/-- Natural-power form of the final formula (21) exponent comparison. -/
theorem PaperFinalFlattening.complementPower_le_minSeparatorPower
    {G : PaperShape} (F : PaperFinalFlattening G)
    (cut : Finset (Fin G.roles))
    (hCut : G.toPartiteShape.IsMinimumRightLeftSeparator cut)
    (n : ℕ) (hn : 1 ≤ n) :
    n ^ flatteningComplementExponent F.rowRoles F.colRoles ≤
      n ^ (G.roles - cut.card + G.isolatedMiddleRoles.card) := by
  apply Nat.pow_le_pow_right hn
  rw [F.complementExponent_eq_exponentNumerator]
  exact F.exponentNumerator_le cut hCut

/-- Real-power form used by squared-norm estimates. -/
theorem PaperFinalFlattening.complementRealPower_le_minSeparatorPower
    {G : PaperShape} (F : PaperFinalFlattening G)
    (cut : Finset (Fin G.roles))
    (hCut : G.toPartiteShape.IsMinimumRightLeftSeparator cut)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ flatteningComplementExponent F.rowRoles F.colRoles ≤
      (n : ℝ) ^
        (G.roles - cut.card + G.isolatedMiddleRoles.card) := by
  apply pow_le_pow_right₀
  · exact_mod_cast hn
  · rw [F.complementExponent_eq_exponentNumerator]
    exact F.exponentNumerator_le cut hCut

/-- Direct reusable endpoint for formula (21): any nonnegative quantity whose
squared-norm estimate has the raw complement exponent inherits the uniform
minimum-separator exponent. -/
theorem PaperFinalFlattening.formula21_squaredNorm_le_minSeparatorPower
    {G : PaperShape} (F : PaperFinalFlattening G)
    (cut : Finset (Fin G.roles))
    (hCut : G.toPartiteShape.IsMinimumRightLeftSeparator cut)
    (n : ℕ) (hn : 1 ≤ n) (squaredNorm : ℝ)
    (hFormula21 : squaredNorm ≤
      (n : ℝ) ^ flatteningComplementExponent F.rowRoles F.colRoles) :
    squaredNorm ≤
      (n : ℝ) ^
        (G.roles - cut.card + G.isolatedMiddleRoles.card) :=
  hFormula21.trans
    (F.complementRealPower_le_minSeparatorPower cut hCut n hn)


end GraphMatrixReplica
