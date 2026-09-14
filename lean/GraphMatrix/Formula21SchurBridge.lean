import GraphMatrix.SchurTest
import GraphMatrix.FlatteningExponentArithmetic

/-! # Schur bridge to BLNvH formula (21)

The row and column nonzero degrees of a nearly-combinatorial flattening are
powers of the uniform ambient size indexed by roles missing from the
respective side.  The finite Schur test turns their product into exactly the
complement exponent appearing in formula (21).
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Generic formula (21) bridge.  The matrix index types need not themselves
be role types; all dependence on role visibility is carried by the two
explicit degree hypotheses. -/
theorem matrix_l2_opNorm_sq_le_flatteningComplementPower
    {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
    [DecidableEq α] [DecidableEq ι] [DecidableEq κ]
    (rowRoles colRoles : Finset α)
    (A : Matrix ι κ ℝ) (n : ℕ)
    (hEntry : ∀ i j, |A i j| ≤ 1)
    (hRow : ∀ i, (matrixRowSupport A i).card ≤
      n ^ (Finset.univ \ rowRoles).card)
    (hCol : ∀ j, (matrixColSupport A j).card ≤
      n ^ (Finset.univ \ colRoles).card) :
    ‖A‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent rowRoles colRoles := by
  have hSchur :=
    matrix_l2_opNorm_sq_le_entry_sq_mul_rowDegree_mul_colDegree
      A 1
        (n ^ (Finset.univ \ rowRoles).card)
        (n ^ (Finset.univ \ colRoles).card)
        (by norm_num) hEntry hRow hCol
  simpa [flatteningComplementExponent, Nat.cast_pow, pow_add] using hSchur

/-- Final-flattening specialization: degree bounds with the two complement
exponents feed formula (21), and the already-proved separator arithmetic
then yields the minimum-separator power. -/
theorem PaperFinalFlattening.formula21_schur_squaredNorm_le_minSeparatorPower
    {G : PaperShape} (F : PaperFinalFlattening G)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ)
    (cut : Finset (Fin G.roles))
    (hCut : G.toPartiteShape.IsMinimumRightLeftSeparator cut)
    (n : ℕ) (hn : 1 ≤ n)
    (hEntry : ∀ i j, |A i j| ≤ 1)
    (hRow : ∀ i, (matrixRowSupport A i).card ≤
      n ^ (Finset.univ \ F.rowRoles).card)
    (hCol : ∀ j, (matrixColSupport A j).card ≤
      n ^ (Finset.univ \ F.colRoles).card) :
    ‖A‖ ^ 2 ≤
      (n : ℝ) ^
        (G.roles - cut.card + G.isolatedMiddleRoles.card) := by
  apply F.formula21_squaredNorm_le_minSeparatorPower
    cut hCut n hn (‖A‖ ^ 2)
  exact matrix_l2_opNorm_sq_le_flatteningComplementPower
    F.rowRoles F.colRoles A n hEntry hRow hCol


end GraphMatrixReplica
