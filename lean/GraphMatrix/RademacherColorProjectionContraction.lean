import GraphMatrix.RademacherDecoupling

/-! # Color-read representation of Rademacher pattern projections

The `q` independent noise copies contain one distinguished coordinate for
each ambient coordinate: copy `color i` at `i`.  Reading precisely those
coordinates gives one coupled Rademacher array, while all remaining bits form
an explicit unused finite factor.  This is the exact finite-product bridge
needed before applying a contraction argument.

A noninjective color pattern is intentionally not called a permutation:
several tensor positions then read the same noise copy.  Such a pattern
requires a further lower-order decoupling or a rainbow-polarization argument;
plain copy reindexing is mathematically insufficient.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

section ColorRead

variable {q : ℕ} {ι τ E : Type} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unused coordinates after reading copy `color i` at ambient index
`i`. -/
abbrev PaperUnusedColorCoordinate (color : ι → Fin q) :=
  {x : Fin q × ι // x.1 ≠ color x.2}

/-- Read one coupled sign field out of `q` independent copies. -/
def paperColorReadNoise (color : ι → Fin q)
    (eta : Fin q → ι → Bool) : ι → Bool :=
  fun i => eta (color i) i

/-- Split the full independent field into its color-read coupled field and
all unused bits. -/
def paperColorReadNoiseEquiv (color : ι → Fin q) :
    (Fin q → ι → Bool) ≃
      ((ι → Bool) × (PaperUnusedColorCoordinate color → Bool)) where
  toFun eta :=
    (paperColorReadNoise color eta, fun x => eta x.1.1 x.1.2)
  invFun x := fun k i =>
    if h : k = color i then x.1 i else x.2 ⟨(k, i), h⟩
  left_inv eta := by
    funext k i
    by_cases h : k = color i
    · subst k
      simp [paperColorReadNoise]
    · simp [h, paperColorReadNoise]
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [paperColorReadNoise]
    · funext z
      simp [z.2, paperColorReadNoise]

/-- Averaging a function over an unused nonempty finite product factor does
not change its normalized mean. -/
theorem paperMean_prod_fst
    {α β : Type} [Fintype α] [Fintype β] [Nonempty β]
    (f : α → ℝ) :
    paperMean (fun x : α × β => f x.1) = paperMean f := by
  classical
  unfold paperMean
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hβ]
  simp

/-- The color-read field is uniformly distributed: unused independent bits
integrate out exactly. -/
theorem paperMean_colorReadNoise
    (color : ι → Fin q) (f : (ι → Bool) → ℝ) :
    paperMean (fun eta : Fin q → ι → Bool =>
        f (paperColorReadNoise color eta)) = paperMean f := by
  calc
    paperMean (fun eta : Fin q → ι → Bool =>
        f (paperColorReadNoise color eta)) =
        paperMean (fun x :
            (ι → Bool) × (PaperUnusedColorCoordinate color → Bool) =>
          f x.1) := by
      exact paperMean_equiv (paperColorReadNoiseEquiv color)
        (fun x : (ι → Bool) ×
          (PaperUnusedColorCoordinate color → Bool) => f x.1)
    _ = paperMean f := paperMean_prod_fst f

/-- A color-pattern piece written with the noise-copy assignment specified by
the pattern.  Repeated pattern values deliberately reuse the same copy. -/
def paperPatternDecoupledColorPiece
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (pattern : Fin q → Fin q)
    (eta : Fin q → ι → Bool) : E :=
  ∑ t : τ,
    if pattern = paperTermColorPattern D color t then
      (∏ k : Fin q, paperSign (eta (pattern k) (D.coordinate t k))) •
        D.coefficient t
    else 0

/-- Exact pointwise representation: a coupled color-pattern projection read
from the independent field is the corresponding repeated-copy chaos. -/
theorem paperCoupledColorPatternPiece_colorRead_eq
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (pattern : Fin q → Fin q)
    (eta : Fin q → ι → Bool) :
    paperCoupledColorPatternPiece D color pattern
        (paperColorReadNoise color eta) =
      paperPatternDecoupledColorPiece D color pattern eta := by
  classical
  unfold paperCoupledColorPatternPiece paperPatternDecoupledColorPiece
    paperCoupledSignMonomial paperColorReadNoise
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hPattern : pattern = paperTermColorPattern D color t
  · rw [if_pos hPattern, if_pos hPattern]
    congr 2
    funext k
    rw [hPattern]
    rfl
  · rw [if_neg hPattern, if_neg hPattern]

/-- Exact finite-mean form of the color-read representation. -/
theorem paperMean_norm_coupledColorPatternPiece_eq_patternDecoupled
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (pattern : Fin q → Fin q) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledColorPatternPiece D color pattern epsilon‖) =
      paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperPatternDecoupledColorPiece D color pattern eta‖) := by
  calc
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledColorPatternPiece D color pattern epsilon‖) =
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperCoupledColorPatternPiece D color pattern
            (paperColorReadNoise color eta)‖) := by
      symm
      exact paperMean_colorReadNoise color
        (fun epsilon : ι → Bool =>
          ‖paperCoupledColorPatternPiece D color pattern epsilon‖)
    _ = paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperPatternDecoupledColorPiece D color pattern eta‖) := by
      congr 1
      funext eta
      rw [paperCoupledColorPatternPiece_colorRead_eq]

/-- Repeated-copy positions are genuinely distinct exactly for permutation
patterns.  This makes the obstruction from noninjective patterns explicit. -/
theorem paperPattern_copies_distinct_iff
    (pattern : Fin q → Fin q) :
    (∀ ⦃k l⦄, pattern k = pattern l → k = l) ↔
      Function.Injective pattern := by
  rfl

end ColorRead

/-! ## Sharp audit of the missing contraction constant -/

/-- Two reversed ordered quadratic terms coincide in the coupled field. -/
def paperQuadraticCoupledAudit (epsilon : Bool × Bool) : ℝ :=
  paperSign epsilon.1 * paperSign epsilon.2 +
    paperSign epsilon.2 * paperSign epsilon.1

/-- The same two terms use four independent signs after full decoupling. -/
def paperQuadraticDecoupledAudit
    (eta : (Bool × Bool) × (Bool × Bool)) : ℝ :=
  paperSign eta.1.1 * paperSign eta.2.2 +
    paperSign eta.1.2 * paperSign eta.2.1

/-- The coupled expected absolute value in the audit example is two. -/
theorem paperMean_abs_quadraticCoupledAudit :
    paperMean (fun epsilon : Bool × Bool =>
      |paperQuadraticCoupledAudit epsilon|) = 2 := by
  norm_num [paperMean, paperQuadraticCoupledAudit, paperSign,
    Fintype.sum_prod_type]

/-- The fully decoupled expected absolute value is only one.  Thus a
coefficient-one deterministic pattern contraction is false already in degree
two; a valid proof must pay a permutation/symmetrization constant. -/
theorem paperMean_abs_quadraticDecoupledAudit :
    paperMean (fun eta : (Bool × Bool) × (Bool × Bool) =>
      |paperQuadraticDecoupledAudit eta|) = 1 := by
  norm_num [paperMean, paperQuadraticDecoupledAudit, paperSign,
    Fintype.sum_prod_type]

theorem paperQuadraticAudit_strictly_exceeds :
    paperMean (fun epsilon : Bool × Bool =>
        |paperQuadraticCoupledAudit epsilon|) >
      paperMean (fun eta : (Bool × Bool) × (Bool × Bool) =>
        |paperQuadraticDecoupledAudit eta|) := by
  rw [paperMean_abs_quadraticCoupledAudit,
    paperMean_abs_quadraticDecoupledAudit]
  norm_num


end GraphMatrixReplica
