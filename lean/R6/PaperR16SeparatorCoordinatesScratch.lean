import R6.PaperR16ColorLowerCompressionContractive
import R6.PaperR16SeparatorBlockScratch
import R6.PaperR16SeparatorBlockNormScratch

/-! Zero-padding and coordinate recovery interface for separator blocks. -/

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace GraphMatrixReplica.PaperR16.SeparatorScratch

/-- If exactly the consistent raw coordinates are embedded images of the
canonical separator, row-only, and column-only assignments, then deleting
the inconsistent zero coordinates preserves the *exact* operator norm. -/
theorem norm_of_consistency_zero_padding
    {S L R RawRow RawCol : Type*}
    [Fintype S] [Fintype L] [Fintype R]
    [Fintype RawRow] [Fintype RawCol]
    [DecidableEq S] [DecidableEq R] [DecidableEq RawCol]
    (er : (L × S) ↪ RawRow) (ec : (R × S) ↪ RawCol)
    (A : Matrix RawRow RawCol ℝ) (w : S → ℝ)
    (hEntry : ∀ s t l r, A (er (l, s)) (ec (r, t)) =
      if s = t then w s else 0)
    (hRowZero : ∀ i, i ∉ Set.range er → ∀ j, A i j = 0)
    (hColZero : ∀ j, j ∉ Set.range ec → ∀ i, A i j = 0) :
    ‖A‖ = ‖coefficientBlock (L := L) (R := R) w‖ := by
  classical
  have hMain : ∀ i j,
      A (er i) (ec j) = coefficientBlock (L := L) (R := R) w i j := by
    intro ⟨l, s⟩ ⟨r, t⟩
    exact hEntry s t l r
  apply le_antisymm
  · exact paper_l2_opNorm_le_of_embedded_support er ec
      (coefficientBlock w) A hMain hRowZero hColZero
  · have hSub : A.submatrix er ec = coefficientBlock w := by
      ext i j
      exact hMain i j
    rw [← hSub]
    exact paper_l2_opNorm_submatrix_le er ec A

/-- The exact R16-shaped norm formula under explicit coordinate recovery,
zero-padding, and nonempty separator assignments. The paper's graph-specific
proof must produce these premises for its actual coefficient tensor. -/
theorem norm_of_consistency_zero_padding_eq_sqrt_product
    {S L R RawRow RawCol : Type*}
    [Fintype S] [Fintype L] [Fintype R]
    [Fintype RawRow] [Fintype RawCol]
    [DecidableEq S] [DecidableEq R] [DecidableEq RawCol]
    [Nonempty S]
    (er : (L × S) ↪ RawRow) (ec : (R × S) ↪ RawCol)
    (A : Matrix RawRow RawCol ℝ) (w : S → ℝ)
    (hEntry : ∀ s t l r, A (er (l, s)) (ec (r, t)) =
      if s = t then w s else 0)
    (hRowZero : ∀ i, i ∉ Set.range er → ∀ j, A i j = 0)
    (hColZero : ∀ j, j ∉ Set.range ec → ∀ i, A i j = 0) :
    ‖A‖ =
      Real.sqrt ((Fintype.card L : ℝ) * (Fintype.card R : ℝ)) *
        Finset.univ.sup' Finset.univ_nonempty (fun s : S => |w s|) := by
  rw [norm_of_consistency_zero_padding er ec A w hEntry hRowZero hColZero,
    coefficientBlock_norm_eq_sqrt_product]

theorem norm_of_consistency_zero_padding_eq_zero_of_isEmpty
    {S L R RawRow RawCol : Type*}
    [Fintype S] [Fintype L] [Fintype R]
    [Fintype RawRow] [Fintype RawCol]
    [DecidableEq S] [DecidableEq R] [DecidableEq RawCol]
    [IsEmpty S]
    (er : (L × S) ↪ RawRow) (ec : (R × S) ↪ RawCol)
    (A : Matrix RawRow RawCol ℝ) (w : S → ℝ)
    (hEntry : ∀ s t l r, A (er (l, s)) (ec (r, t)) =
      if s = t then w s else 0)
    (hRowZero : ∀ i, i ∉ Set.range er → ∀ j, A i j = 0)
    (hColZero : ∀ j, j ∉ Set.range ec → ∀ i, A i j = 0) :
    ‖A‖ = 0 := by
  rw [norm_of_consistency_zero_padding er ec A w hEntry hRowZero hColZero,
    coefficientBlock_norm_eq_zero_of_isEmpty]

#print axioms norm_of_consistency_zero_padding
#print axioms norm_of_consistency_zero_padding_eq_sqrt_product
#print axioms norm_of_consistency_zero_padding_eq_zero_of_isEmpty

end GraphMatrixReplica.PaperR16.SeparatorScratch
