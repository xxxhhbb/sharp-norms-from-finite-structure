import GraphMatrix.RademacherSymmetrizedDecoupling

/-! # Rainbow projections for finite Rademacher chaos

A color pattern is rainbow precisely when it is a permutation of the `q`
copy labels.  This file records the exact rainbow decomposition that is valid
without coefficient symmetry.  Importantly, a global coloring has free values
away from the `q` active coordinates of a square-free monomial; consequently
raw global-coloring counts contain that extension factor.  The local rainbow
count itself is exactly `q!`.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

section GenericChaos

variable {q : ℕ} {ι τ E : Type} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A rainbow word uses every copy label exactly once. -/
def PaperRainbowPattern (pattern : Fin q → Fin q) : Prop :=
  Function.Bijective pattern

noncomputable instance paperRainbowPatternDecidable
    (pattern : Fin q → Fin q) : Decidable (PaperRainbowPattern pattern) :=
  Classical.propDecidable _

/-- Rainbow patterns are canonically the permutations of the slots. -/
def paperRainbowPatternEquivPerm :
    {pattern : Fin q → Fin q // PaperRainbowPattern pattern} ≃
      Equiv.Perm (Fin q) where
  toFun pattern := Equiv.ofBijective pattern.1 pattern.2
  invFun σ := ⟨σ, σ.bijective⟩
  left_inv pattern := by
    apply Subtype.ext
    rfl
  right_inv σ := by
    ext k
    rfl

/-- There are exactly `q!` local rainbow color words. -/
@[simp] theorem paperRainbowPattern_card :
    Nat.card {pattern : Fin q → Fin q // PaperRainbowPattern pattern} =
      Nat.factorial q := by
  rw [Nat.card_congr paperRainbowPatternEquivPerm, Nat.card_perm]
  simp

/-- Ambient coordinates not used by one square-free monomial. -/
abbrev PaperRainbowColoringComplement
    (coordinate : Fin q ↪ ι) :=
  {i : ι // ¬ ∃ k, coordinate k = i}

/-- A global coloring is exactly its word on the active coordinates together
with its unrestricted coloring of the unused coordinates. -/
noncomputable def paperColoringRestrictionEquiv
    (coordinate : Fin q ↪ ι) :
    (ι → Fin q) ≃
      ((Fin q → Fin q) ×
        (PaperRainbowColoringComplement coordinate → Fin q)) where
  toFun color :=
    (fun k => color (coordinate k), fun i => color i.1)
  invFun data := fun i =>
    if h : ∃ k, coordinate k = i then
      data.1 (Classical.choose h)
    else data.2 ⟨i, h⟩
  left_inv color := by
    funext i
    by_cases h : ∃ k, coordinate k = i
    · obtain ⟨k, rfl⟩ := h
      have hmem : ∃ j, coordinate j = coordinate k := ⟨k, rfl⟩
      change (if h : ∃ j, coordinate j = coordinate k then
          color (coordinate (Classical.choose h))
        else color (coordinate k)) = color (coordinate k)
      rw [dif_pos hmem]
      congr 1
      exact Classical.choose_spec hmem
    · simp [h]
  right_inv data := by
    apply Prod.ext
    · funext k
      have hmem : ∃ j, coordinate j = coordinate k := ⟨k, rfl⟩
      simp only [hmem, dite_true]
      have hk : Classical.choose hmem = k := by
        apply coordinate.injective
        exact Classical.choose_spec hmem
      rw [hk]
    · funext i
      simp [i.2]

/-- Global colorings which are rainbow on one active monomial split as a
local permutation and an arbitrary coloring of the unused coordinates. -/
noncomputable def paperRainbowGlobalColoringEquiv
    (coordinate : Fin q ↪ ι) :
    {color : ι → Fin q //
      PaperRainbowPattern (fun k => color (coordinate k))} ≃
      ({pattern : Fin q → Fin q // PaperRainbowPattern pattern} ×
        (PaperRainbowColoringComplement coordinate → Fin q)) where
  toFun color :=
    (⟨fun k => color.1 (coordinate k), color.2⟩,
      fun i => color.1 i.1)
  invFun data := ⟨
    (paperColoringRestrictionEquiv coordinate).symm
      (data.1.1, data.2),
    by
      change PaperRainbowPattern
        ((paperColoringRestrictionEquiv coordinate
          ((paperColoringRestrictionEquiv coordinate).symm
            (data.1.1, data.2))).1)
      rw [(paperColoringRestrictionEquiv coordinate).apply_symm_apply]
      exact data.1.2⟩
  left_inv color := by
    apply Subtype.ext
    exact (paperColoringRestrictionEquiv coordinate).left_inv color.1
  right_inv data := by
    rcases data with ⟨pattern, rest⟩
    apply Prod.ext
    · apply Subtype.ext
      change (fun k =>
          (paperColoringRestrictionEquiv coordinate).symm
            (pattern.1, rest) (coordinate k)) = pattern.1
      exact congrArg Prod.fst
        ((paperColoringRestrictionEquiv coordinate).apply_symm_apply
          (pattern.1, rest))
    · change (fun i =>
          (paperColoringRestrictionEquiv coordinate).symm
            (pattern.1, rest) i.1) = rest
      exact congrArg Prod.snd
        ((paperColoringRestrictionEquiv coordinate).apply_symm_apply
          (pattern.1, rest))

/-- The free coloring coordinates are exactly the ambient coordinates outside
the `q`-element active image. -/
theorem paperRainbowColoringComplement_card
    (coordinate : Fin q ↪ ι) :
    Nat.card (PaperRainbowColoringComplement coordinate) =
      Nat.card ι - q := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hactive :
      Fintype.card {i : ι // ∃ k, coordinate k = i} = q := by
    let e : Fin q ≃ {i : ι // ∃ k, coordinate k = i} := {
      toFun := fun k => ⟨coordinate k, ⟨k, rfl⟩⟩
      invFun := fun i => Classical.choose i.2
      left_inv := by
        intro k
        apply coordinate.injective
        exact Classical.choose_spec
          (show ∃ j, coordinate j = coordinate k from ⟨k, rfl⟩)
      right_inv := by
        intro i
        apply Subtype.ext
        exact Classical.choose_spec i.2 }
    rw [← Fintype.card_congr e]
    simp
  rw [hactive, Nat.card_eq_fintype_card]

/-- Exact global rainbow count for one square-free monomial.  The second
factor is the unavoidable number of extensions away from the active
coordinates. -/
theorem paperRainbowGlobalColoring_card
    (coordinate : Fin q ↪ ι) :
    Nat.card {color : ι → Fin q //
        PaperRainbowPattern (fun k => color (coordinate k))} =
      Nat.factorial q *
        q ^ Nat.card (PaperRainbowColoringComplement coordinate) := by
  rw [Nat.card_congr (paperRainbowGlobalColoringEquiv coordinate),
    Nat.card_prod, paperRainbowPattern_card, Nat.card_fun]
  simp

/-- The same count in ambient-cardinality form. -/
theorem paperRainbowGlobalColoring_card_eq_factorial_mul_pow_sub
    (coordinate : Fin q ↪ ι) :
    Nat.card {color : ι → Fin q //
        PaperRainbowPattern (fun k => color (coordinate k))} =
      Nat.factorial q * q ^ (Nat.card ι - q) := by
  rw [paperRainbowGlobalColoring_card,
    paperRainbowColoringComplement_card]

/-- Summing over all permutations retains a word exactly when it is
rainbow. -/
theorem paperSum_perm_indicator
    (pattern : Fin q → Fin q) (x : E) :
    (∑ σ : Equiv.Perm (Fin q),
        if (σ : Fin q → Fin q) = pattern then x else 0) =
      if PaperRainbowPattern pattern then x else 0 := by
  classical
  by_cases hp : PaperRainbowPattern pattern
  · let σ₀ : Equiv.Perm (Fin q) := Equiv.ofBijective pattern hp
    have hσ₀ : (σ₀ : Fin q → Fin q) = pattern := rfl
    rw [Finset.sum_eq_single σ₀]
    · rw [if_pos hσ₀, if_pos hp]
    · intro σ _hσ hne
      have hfun : (σ : Fin q → Fin q) ≠ pattern := by
        intro h
        apply hne
        apply Equiv.ext
        intro k
        exact (congrFun h k).trans (congrFun hσ₀ k).symm
      simp [hfun]
    · simp
  · have hfun : ∀ σ : Equiv.Perm (Fin q),
        (σ : Fin q → Fin q) ≠ pattern := by
      intro σ h
      apply hp
      rw [← h]
      exact σ.bijective
    simp [hp, hfun]

/-- Exact capture multiplicity for a fixed square-free monomial. -/
theorem paperSum_globalColor_perm_indicator
    (coordinate : Fin q ↪ ι) (x : E) :
    (∑ color : ι → Fin q,
      ∑ σ : Equiv.Perm (Fin q),
        if (σ : Fin q → Fin q) =
            (fun k => color (coordinate k)) then x else 0) =
      (Nat.factorial q * q ^ (Nat.card ι - q)) • x := by
  classical
  simp_rw [paperSum_perm_indicator]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const]
  rw [← Fintype.card_subtype]
  rw [show Fintype.card {color : ι → Fin q //
      PaperRainbowPattern (fun k => color (coordinate k))} =
        Nat.factorial q * q ^ (Nat.card ι - q) by
      simpa [Nat.card_eq_fintype_card] using
        paperRainbowGlobalColoring_card_eq_factorial_mul_pow_sub coordinate]

/-- The sum of the exact color-pattern projections over rainbow words. -/
def paperCoupledRainbowColorSum
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (epsilon : ι → Bool) : E :=
  ∑ σ : Equiv.Perm (Fin q),
    paperCoupledColorPatternPiece D color σ epsilon

/-- The same rainbow sum represented using independent copies selected by
the color word. -/
def paperDecoupledRainbowColorSum
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (eta : Fin q → ι → Bool) : E :=
  ∑ σ : Equiv.Perm (Fin q),
    paperPatternDecoupledColorPiece D color σ eta

/-- Summing the coupled rainbow projection over every global coloring counts
each nonzero square-free monomial with the exact extension multiplicity. -/
theorem paperSum_globalColor_coupledRainbowColorSum
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (epsilon : ι → Bool) :
    (∑ color : ι → Fin q,
        paperCoupledRainbowColorSum D color epsilon) =
      (Nat.factorial q * q ^ (Nat.card ι - q)) •
        paperCoupledRademacherChaos D epsilon := by
  classical
  unfold paperCoupledRainbowColorSum paperCoupledColorPatternPiece
    paperTermColorPattern paperCoupledRademacherChaos
  calc
    (∑ color : ι → Fin q,
        ∑ σ : Equiv.Perm (Fin q),
          ∑ t : τ,
            if (σ : Fin q → Fin q) =
                (fun k => color (D.coordinate t k)) then
              paperCoupledSignMonomial D epsilon t • D.coefficient t
            else 0) =
        ∑ color : ι → Fin q,
          ∑ t : τ,
            ∑ σ : Equiv.Perm (Fin q),
              if (σ : Fin q → Fin q) =
                  (fun k => color (D.coordinate t k)) then
                paperCoupledSignMonomial D epsilon t • D.coefficient t
              else 0 := by
      apply Finset.sum_congr rfl
      intro color _hcolor
      rw [Finset.sum_comm]
    _ = ∑ t : τ,
          ∑ color : ι → Fin q,
            ∑ σ : Equiv.Perm (Fin q),
              if (σ : Fin q → Fin q) =
                  (fun k => color (D.coordinate t k)) then
                paperCoupledSignMonomial D epsilon t • D.coefficient t
              else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t : τ,
          (Nat.factorial q * q ^ (Nat.card ι - q)) •
            (paperCoupledSignMonomial D epsilon t • D.coefficient t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases ht : D.coefficient t = 0
      · simp [ht]
      · let coordinate : Fin q ↪ ι :=
          ⟨D.coordinate t, D.squareFree t ht⟩
        simpa [coordinate] using
          paperSum_globalColor_perm_indicator
            (q := q) coordinate
            (paperCoupledSignMonomial D epsilon t • D.coefficient t)
    _ = (Nat.factorial q * q ^ (Nat.card ι - q)) •
          ∑ t : τ,
            paperCoupledSignMonomial D epsilon t • D.coefficient t := by
      rw [Finset.smul_sum]

/-- Pointwise triangle consequence of the exact rainbow capture identity. -/
theorem paperRainbowMultiplicity_mul_norm_coupled_le
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (epsilon : ι → Bool) :
    (Nat.factorial q * q ^ (Nat.card ι - q) : ℝ) *
        ‖paperCoupledRademacherChaos D epsilon‖ ≤
      ∑ color : ι → Fin q,
        ‖paperCoupledRainbowColorSum D color epsilon‖ := by
  calc
    (Nat.factorial q * q ^ (Nat.card ι - q) : ℝ) *
        ‖paperCoupledRademacherChaos D epsilon‖ =
        ‖(Nat.factorial q * q ^ (Nat.card ι - q)) •
          paperCoupledRademacherChaos D epsilon‖ := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
      simp
    _ = ‖∑ color : ι → Fin q,
          paperCoupledRainbowColorSum D color epsilon‖ := by
      rw [paperSum_globalColor_coupledRainbowColorSum]
    _ ≤ ∑ color : ι → Fin q,
          ‖paperCoupledRainbowColorSum D color epsilon‖ :=
      norm_sum_le _ _

/-- Color-reading identifies the coupled and independent-copy rainbow sums
pointwise. -/
theorem paperCoupledRainbowColorSum_colorRead_eq
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (eta : Fin q → ι → Bool) :
    paperCoupledRainbowColorSum D color
        (paperColorReadNoise color eta) =
      paperDecoupledRainbowColorSum D color eta := by
  classical
  unfold paperCoupledRainbowColorSum paperDecoupledRainbowColorSum
  apply Finset.sum_congr rfl
  intro σ _hσ
  exact paperCoupledColorPatternPiece_colorRead_eq D color σ eta

/-- Exact finite-mean version of the rainbow color-read identity. -/
theorem paperMean_norm_coupledRainbowColorSum_eq_decoupled
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRainbowColorSum D color epsilon‖) =
      paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperDecoupledRainbowColorSum D color eta‖) := by
  calc
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRainbowColorSum D color epsilon‖) =
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperCoupledRainbowColorSum D color
            (paperColorReadNoise color eta)‖) := by
      symm
      exact paperMean_colorReadNoise color
        (fun epsilon : ι → Bool =>
          ‖paperCoupledRainbowColorSum D color epsilon‖)
    _ = paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperDecoupledRainbowColorSum D color eta‖) := by
      congr 1
      funext eta
      rw [paperCoupledRainbowColorSum_colorRead_eq]

/-- Triangle inequality for the independent-copy rainbow sum. -/
theorem paperMean_norm_decoupledRainbowColorSum_le
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) :
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperDecoupledRainbowColorSum D color eta‖) ≤
      ∑ σ : Equiv.Perm (Fin q),
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperPatternDecoupledColorPiece D color σ eta‖) := by
  calc
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperDecoupledRainbowColorSum D color eta‖) ≤
        paperMean (fun eta : Fin q → ι → Bool =>
          ∑ σ : Equiv.Perm (Fin q),
            ‖paperPatternDecoupledColorPiece D color σ eta‖) := by
      apply paperMean_mono
      intro eta
      exact norm_sum_le _ _
    _ = _ := paperMean_sum _

/-- Fully unconditional reduction of decoupling to the single remaining
coefficient-projection contraction.  All coloring multiplicities and copy
reindexings have already been discharged. -/
theorem paperRainbowMultiplicity_mul_coupledMean_le_projectionMeans
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q) :
    (Nat.factorial q * q ^ (Nat.card ι - q) : ℝ) *
        paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledRademacherChaos D epsilon‖) ≤
      ∑ color : ι → Fin q,
        ∑ σ : Equiv.Perm (Fin q),
          paperMean (fun eta : Fin q → ι → Bool =>
            ‖paperPatternDecoupledColorPiece D color σ eta‖) := by
  calc
    (Nat.factorial q * q ^ (Nat.card ι - q) : ℝ) *
        paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledRademacherChaos D epsilon‖) =
        paperMean (fun epsilon : ι → Bool =>
          (Nat.factorial q * q ^ (Nat.card ι - q) : ℝ) *
            ‖paperCoupledRademacherChaos D epsilon‖) := by
      rw [paperMean_const_mul]
    _ ≤ paperMean (fun epsilon : ι → Bool =>
          ∑ color : ι → Fin q,
            ‖paperCoupledRainbowColorSum D color epsilon‖) := by
      apply paperMean_mono
      exact paperRainbowMultiplicity_mul_norm_coupled_le D
    _ = ∑ color : ι → Fin q,
          paperMean (fun epsilon : ι → Bool =>
            ‖paperCoupledRainbowColorSum D color epsilon‖) :=
      paperMean_sum _
    _ = ∑ color : ι → Fin q,
          paperMean (fun eta : Fin q → ι → Bool =>
            ‖paperDecoupledRainbowColorSum D color eta‖) := by
      apply Finset.sum_congr rfl
      intro color _hcolor
      exact paperMean_norm_coupledRainbowColorSum_eq_decoupled D color
    _ ≤ ∑ color : ι → Fin q,
          ∑ σ : Equiv.Perm (Fin q),
            paperMean (fun eta : Fin q → ι → Bool =>
              ‖paperPatternDecoupledColorPiece D color σ eta‖) := by
      exact Finset.sum_le_sum fun color _ =>
        paperMean_norm_decoupledRainbowColorSum_le D color

/-- If the remaining fixed coefficient projections are contractions, the
rainbow reduction yields a completely explicit unnormalized decoupling
bound.  The premise is intentionally visible. -/
theorem paperRainbowMultiplicity_mul_coupledMean_le_of_projectionContraction
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (hProjection : ∀ (color : ι → Fin q) (σ : Equiv.Perm (Fin q)),
      paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperPatternDecoupledColorPiece D color σ eta‖) ≤
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖)) :
    (Nat.factorial q * q ^ (Nat.card ι - q) : ℝ) *
        paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledRademacherChaos D epsilon‖) ≤
      (q ^ Nat.card ι * Nat.factorial q : ℝ) *
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  calc
    _ ≤ ∑ color : ι → Fin q,
          ∑ σ : Equiv.Perm (Fin q),
            paperMean (fun eta : Fin q → ι → Bool =>
              ‖paperPatternDecoupledColorPiece D color σ eta‖) :=
      paperRainbowMultiplicity_mul_coupledMean_le_projectionMeans D
    _ ≤ ∑ _color : ι → Fin q,
          ∑ _σ : Equiv.Perm (Fin q),
            paperMean (fun eta : Fin q → ι → Bool =>
              ‖paperFullyDecoupledRademacherChaos D eta‖) := by
      exact Finset.sum_le_sum fun color _ =>
        Finset.sum_le_sum fun σ _ => hProjection color σ
    _ = _ := by
      simp [Fintype.card_perm, Nat.card_eq_fintype_card]
      ring

/-- A fixed rainbow word uses distinct independent copies.  Reindexing those
copies turns its monomial into the standard slot order. -/
theorem paperRainbowMonomial_reindex
    (σ : Equiv.Perm (Fin q)) (eta : Fin q → ι → Bool)
    (coordinate : Fin q → ι) :
    (∏ k : Fin q, paperSign (eta (σ k) (coordinate k))) =
      ∏ k : Fin q, paperSign
        ((paperPermuteDecoupledCopiesEquiv (ι := ι) σ.symm eta) k
          (coordinate k)) := by
  rfl

/-! The theorem above closes the copy-reindexing part.  Controlling a fixed
coefficient projection `paperPatternDecoupledColorPiece` by the full chaos is
the remaining finite conditional-expectation contraction; no such bound is
silently assumed here. -/


end GenericChaos

/-! ## Fixed-orientation paper endpoint -/

/-- The exact rainbow-coloring capture identity specialized to the paper's
fixed-orientation matrix coefficients. -/
theorem paperSum_globalColor_orientedRainbowColorSum
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (epsilon : Sym2 (Fin n) → Bool) :
    (∑ color : Sym2 (Fin n) → Fin G.edges,
      paperCoupledRainbowColorSum
        (paperOrientedSquareFreeChaosData G n orientation) color epsilon) =
      (Nat.factorial G.edges *
          G.edges ^ (Nat.card (Sym2 (Fin n)) - G.edges)) •
        paperOrientedGraphMatrix G n orientation
          (paperSym2NoiseToPaper epsilon) := by
  rw [paperSum_globalColor_coupledRainbowColorSum]
  rw [paperCoupledOrientedChaos_eq_paperOrientedGraphMatrix]


end GraphMatrixReplica
