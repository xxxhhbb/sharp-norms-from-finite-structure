import GraphMatrix.RademacherRainbowDecoupling

/-! # Walsh projection contraction for decoupled chaos

An exact coordinate restriction of a fully decoupled chaos is a conditional
Walsh expectation.  Auxiliary signs are multiplied into every disallowed
copy/coordinate pair.  Character orthogonality kills precisely the terms
which use a disallowed coordinate.  Since each fixed sign multiplication is
a permutation of the finite noise cube, the norm triangle inequality makes
the restriction an expected-norm contraction with constant one.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

section GenericProjection

variable {q : ℕ} {ι τ E : Type} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite vector-valued normalized average. -/
def paperVectorMean {A : Type} [Fintype A] (f : A → E) : E :=
  (Fintype.card A : ℝ)⁻¹ • ∑ a, f a

/-- Jensen's inequality for the norm of a finite vector mean. -/
theorem norm_paperVectorMean_le_paperMean
    {A : Type} [Fintype A] [Nonempty A] (f : A → E) :
    ‖paperVectorMean f‖ ≤ paperMean (fun a => ‖f a‖) := by
  unfold paperVectorMean paperMean
  rw [norm_smul]
  have hcard : (0 : ℝ) ≤ (Fintype.card A : ℝ)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hcard]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hcard

/-- Boolean multiplication whose paper sign is ordinary multiplication. -/
def paperBoolSignMul (a b : Bool) : Bool := decide (a = b)

@[simp] theorem paperSign_boolSignMul (a b : Bool) :
    paperSign (paperBoolSignMul a b) = paperSign a * paperSign b := by
  cases a <;> cases b <;> norm_num [paperBoolSignMul, paperSign]

/-- Multiply auxiliary signs only into disallowed copy/coordinate pairs. -/
def paperWalshFlip (allowed : Fin q → ι → Bool)
    (eta delta : Fin q → ι → Bool) : Fin q → ι → Bool :=
  fun k i => if allowed k i then eta k i
    else paperBoolSignMul (eta k i) (delta k i)

/-- For fixed auxiliary signs, Walsh flipping is a self-inverse permutation
of the full decoupled noise cube. -/
def paperWalshFlipEquiv (allowed : Fin q → ι → Bool)
    (delta : Fin q → ι → Bool) :
    (Fin q → ι → Bool) ≃ (Fin q → ι → Bool) where
  toFun eta := paperWalshFlip allowed eta delta
  invFun eta := paperWalshFlip allowed eta delta
  left_inv eta := by
    funext k i
    by_cases h : allowed k i
    · simp [paperWalshFlip, h]
    · simp only [paperWalshFlip, h, Bool.false_eq_true, if_false]
      cases eta k i <;> cases delta k i <;> rfl
  right_inv eta := by
    funext k i
    by_cases h : allowed k i
    · simp [paperWalshFlip, h]
    · simp only [paperWalshFlip, h, Bool.false_eq_true, if_false]
      cases eta k i <;> cases delta k i <;> rfl

/-- A coordinate-restricted fully decoupled chaos. -/
def paperDecoupledCoordinateProjection
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool)
    (eta : Fin q → ι → Bool) : E :=
  ∑ t : τ,
    if ∀ k : Fin q, allowed k (D.coordinate t k) then
      (∏ k : Fin q, paperSign (eta k (D.coordinate t k))) •
        D.coefficient t
    else 0

/-- Exponent of one auxiliary character in a fixed chaos term. -/
def paperWalshOutsideExponent
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool) (t : τ)
    (x : Fin q × ι) : ℕ :=
  if ¬ allowed x.1 (D.coordinate t x.1) ∧
      x.2 = D.coordinate t x.1 then 1 else 0

/-- The auxiliary character has nonzero mean exactly when every coordinate
of the term is allowed. -/
theorem paperMean_walshOutsideCharacter
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool) (t : τ) :
    paperMean (fun delta : Fin q × ι → Bool =>
        ∏ x : Fin q × ι,
          paperSign (delta x) ^
            paperWalshOutsideExponent D allowed t x) =
      if ∀ k : Fin q, allowed k (D.coordinate t k) then 1 else 0 := by
  rw [paperMean_sign_monomial]
  congr 1
  apply propext
  constructor
  · intro heven k
    by_contra hk
    have hfalse : ¬ allowed k (D.coordinate t k) := by
      simpa using hk
    have hone : paperWalshOutsideExponent D allowed t
        (k, D.coordinate t k) = 1 := by
      simp [paperWalshOutsideExponent, hfalse]
    have := heven (k, D.coordinate t k)
    rw [hone] at this
    exact Nat.not_even_one this
  · intro hallowed x
    simp [paperWalshOutsideExponent, hallowed x.1]

/-- Product form of the auxiliary character, one factor per slot. -/
theorem paperWalshOutsideCharacter_eq_slotProduct
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool) (t : τ)
    (delta : Fin q × ι → Bool) :
    (∏ x : Fin q × ι,
        paperSign (delta x) ^ paperWalshOutsideExponent D allowed t x) =
      ∏ k : Fin q,
        if allowed k (D.coordinate t k) then 1
        else paperSign (delta (k, D.coordinate t k)) := by
  classical
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro k _hk
  by_cases hallowed : allowed k (D.coordinate t k)
  · simp [paperWalshOutsideExponent, hallowed]
  · simp [paperWalshOutsideExponent, hallowed]

/-- A flipped decoupled monomial factors into the original monomial and its
auxiliary Walsh character. -/
theorem paperWalshFlippedMonomial_eq_mul_character
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool) (t : τ)
    (eta : Fin q → ι → Bool)
    (delta : Fin q × ι → Bool) :
    (∏ k : Fin q, paperSign
        (paperWalshFlip allowed eta (fun k i => delta (k, i)) k
          (D.coordinate t k))) =
      (∏ k : Fin q, paperSign (eta k (D.coordinate t k))) *
        (∏ x : Fin q × ι,
          paperSign (delta x) ^
            paperWalshOutsideExponent D allowed t x) := by
  rw [paperWalshOutsideCharacter_eq_slotProduct]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _hk
  by_cases hallowed : allowed k (D.coordinate t k)
  · simp [paperWalshFlip, hallowed]
  · simp [paperWalshFlip, hallowed]

/-- Orthogonality evaluation of one flipped monomial. -/
theorem paperMean_walshFlippedMonomial
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool) (t : τ)
    (eta : Fin q → ι → Bool) :
    paperMean (fun delta : Fin q × ι → Bool =>
        ∏ k : Fin q, paperSign
          (paperWalshFlip allowed eta (fun k i => delta (k, i)) k
            (D.coordinate t k))) =
      if ∀ k : Fin q, allowed k (D.coordinate t k) then
        ∏ k : Fin q, paperSign (eta k (D.coordinate t k))
      else 0 := by
  simp_rw [paperWalshFlippedMonomial_eq_mul_character]
  rw [paperMean_const_mul]
  rw [paperMean_walshOutsideCharacter]
  by_cases hallowed : ∀ k : Fin q, allowed k (D.coordinate t k)
  · simp [hallowed]
  · simp [hallowed]

/-- Averaging scalar multiples of one vector is scalar averaging. -/
theorem paperVectorMean_smul
    {A : Type} [Fintype A] (f : A → ℝ) (x : E) :
    paperVectorMean (fun a => f a • x) = paperMean f • x := by
  unfold paperVectorMean paperMean
  rw [← Finset.sum_smul]
  rw [smul_smul]

/-- Finite vector averaging commutes with a finite sum. -/
theorem paperVectorMean_sum
    {A B : Type} [Fintype A] [Fintype B] (f : A → B → E) :
    paperVectorMean (fun a => ∑ b, f a b) =
      ∑ b, paperVectorMean (fun a => f a b) := by
  unfold paperVectorMean
  rw [Finset.sum_comm, Finset.smul_sum]

/-- The exact Walsh representation of a coordinate projection. -/
theorem paperDecoupledCoordinateProjection_eq_walshMean
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool)
    (eta : Fin q → ι → Bool) :
    paperDecoupledCoordinateProjection D allowed eta =
      paperVectorMean (fun delta : Fin q × ι → Bool =>
        paperFullyDecoupledRademacherChaos D
          (paperWalshFlip allowed eta (fun k i => delta (k, i)))) := by
  classical
  unfold paperFullyDecoupledRademacherChaos
  rw [paperVectorMean_sum]
  unfold paperDecoupledCoordinateProjection
  apply Finset.sum_congr rfl
  intro t _ht
  rw [paperVectorMean_smul]
  rw [paperMean_walshFlippedMonomial]
  by_cases hallowed : ∀ k : Fin q, allowed k (D.coordinate t k)
  · simp [hallowed]
  · simp [hallowed]

/-- The two normalized finite means commute. -/
theorem paperMean_comm
    {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    paperMean (fun a => paperMean (fun b => f a b)) =
      paperMean (fun b => paperMean (fun a => f a b)) := by
  unfold paperMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-- A normalized finite mean of a constant over a nonempty type is that
constant. -/
theorem paperMean_const_function
    {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    paperMean (fun _ : A => c) = c := by
  unfold paperMean
  simp [Fintype.card_ne_zero]

/-- A fixed Walsh flip preserves the fully decoupled expected norm exactly. -/
theorem paperMean_norm_fullyDecoupled_walshFlip
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool)
    (delta : Fin q → ι → Bool) :
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D
          (paperWalshFlip allowed eta delta)‖) =
      paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  exact paperMean_equiv (paperWalshFlipEquiv allowed delta)
    (fun eta : Fin q → ι → Bool =>
      ‖paperFullyDecoupledRademacherChaos D eta‖)

/-- Pointwise Jensen bound for the exact Walsh projection. -/
theorem norm_paperDecoupledCoordinateProjection_le_walshMean
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool)
    (eta : Fin q → ι → Bool) :
    ‖paperDecoupledCoordinateProjection D allowed eta‖ ≤
      paperMean (fun delta : Fin q × ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D
          (paperWalshFlip allowed eta (fun k i => delta (k, i)))‖) := by
  rw [paperDecoupledCoordinateProjection_eq_walshMean]
  exact norm_paperVectorMean_le_paperMean _

/-- Coordinate restriction is an expected-norm contraction with constant
one, in every degree and every real normed coefficient space. -/
theorem paperMean_norm_decoupledCoordinateProjection_le
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (allowed : Fin q → ι → Bool) :
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperDecoupledCoordinateProjection D allowed eta‖) ≤
      paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  calc
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperDecoupledCoordinateProjection D allowed eta‖) ≤
        paperMean (fun eta : Fin q → ι → Bool =>
          paperMean (fun delta : Fin q × ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos D
              (paperWalshFlip allowed eta
                (fun k i => delta (k, i)))‖)) := by
      apply paperMean_mono
      exact norm_paperDecoupledCoordinateProjection_le_walshMean D allowed
    _ = paperMean (fun delta : Fin q × ι → Bool =>
          paperMean (fun eta : Fin q → ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos D
              (paperWalshFlip allowed eta
                (fun k i => delta (k, i)))‖)) :=
      paperMean_comm _
    _ = paperMean (fun _delta : Fin q × ι → Bool =>
          paperMean (fun eta : Fin q → ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos D eta‖)) := by
      congr 1
      funext delta
      exact paperMean_norm_fullyDecoupled_walshFlip D allowed
        (fun k i => delta (k, i))
    _ = paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) := by
      exact paperMean_const_function _

/-! ## Exact color-pattern projections -/

/-- Allowed coordinates for one fixed rainbow copy word. -/
def paperColorPatternAllowed (color : ι → Fin q)
    (σ : Equiv.Perm (Fin q)) (k : Fin q) (i : ι) : Bool :=
  decide (color i = σ k)

/-- A rainbow pattern piece is exactly a coordinate projection after the
corresponding permutation of independent noise copies. -/
theorem paperPatternDecoupledColorPiece_eq_coordinateProjection
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (σ : Equiv.Perm (Fin q))
    (eta : Fin q → ι → Bool) :
    paperPatternDecoupledColorPiece D color σ eta =
      paperDecoupledCoordinateProjection D
        (paperColorPatternAllowed color σ)
        (paperPermuteDecoupledCopiesEquiv (ι := ι) σ.symm eta) := by
  classical
  unfold paperPatternDecoupledColorPiece
    paperDecoupledCoordinateProjection paperTermColorPattern
  apply Finset.sum_congr rfl
  intro t _ht
  have hiff :
      ((σ : Fin q → Fin q) =
          (fun k => color (D.coordinate t k))) ↔
        (∀ k : Fin q,
          paperColorPatternAllowed color σ k (D.coordinate t k)) := by
    constructor
    · intro h k
      simp only [paperColorPatternAllowed, decide_eq_true_eq]
      exact (congrFun h k).symm
    · intro h
      funext k
      have hk := h k
      simp only [paperColorPatternAllowed, decide_eq_true_eq] at hk
      exact hk.symm
  by_cases hpattern : (σ : Fin q → Fin q) =
      (fun k => color (D.coordinate t k))
  · rw [if_pos hpattern, if_pos (hiff.mp hpattern)]
    rfl
  · rw [if_neg hpattern, if_neg (mt hiff.mpr hpattern)]

/-- The fixed rainbow coefficient projection is an unconditional
expected-norm contraction of the full decoupled chaos. -/
theorem paperMean_norm_patternDecoupledColorPiece_le
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (σ : Equiv.Perm (Fin q)) :
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperPatternDecoupledColorPiece D color σ eta‖) ≤
      paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  calc
    paperMean (fun eta : Fin q → ι → Bool =>
        ‖paperPatternDecoupledColorPiece D color σ eta‖) =
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperDecoupledCoordinateProjection D
            (paperColorPatternAllowed color σ)
            (paperPermuteDecoupledCopiesEquiv (ι := ι) σ.symm eta)‖) := by
      congr 1
      funext eta
      rw [paperPatternDecoupledColorPiece_eq_coordinateProjection]
    _ = paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperDecoupledCoordinateProjection D
            (paperColorPatternAllowed color σ) eta‖) := by
      exact paperMean_equiv
        (paperPermuteDecoupledCopiesEquiv (ι := ι) σ.symm)
        (fun eta : Fin q → ι → Bool =>
          ‖paperDecoupledCoordinateProjection D
            (paperColorPatternAllowed color σ) eta‖)
    _ ≤ _ := paperMean_norm_decoupledCoordinateProjection_le D _

/-! ## Closed rainbow decoupling ledger -/

/-- Substituting the unconditional Walsh contraction closes the rainbow
ledger.  This no-division form is valid in every degree, including `q = 0`. -/
theorem paperRainbowMultiplicity_mul_coupledMean_le_fullyDecoupled
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q) :
    (Nat.factorial q * q ^ (Nat.card ι - q) : ℝ) *
        paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledRademacherChaos D epsilon‖) ≤
      (q ^ Nat.card ι * Nat.factorial q : ℝ) *
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  exact
    paperRainbowMultiplicity_mul_coupledMean_le_of_projectionContraction D
      (fun color σ =>
        paperMean_norm_patternDecoupledColorPiece_le D color σ)

/-- After cancelling the positive rainbow multiplicity, one obtains the
standard explicit `q^q` decoupling constant. -/
theorem paperMean_norm_coupled_le_q_pow_q_mul_fullyDecoupled
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (hq : 0 < q) (hcard : q ≤ Nat.card ι) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
      (q : ℝ) ^ q *
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hMultiplicity :
      (0 : ℝ) < (Nat.factorial q : ℝ) *
        (q : ℝ) ^ (Nat.card ι - q) := by
    exact mul_pos (by positivity) (pow_pos hqReal _)
  have hcoefficient :
      (q ^ Nat.card ι * Nat.factorial q : ℕ) =
        (Nat.factorial q * q ^ (Nat.card ι - q)) * q ^ q := by
    calc
      q ^ Nat.card ι * Nat.factorial q =
          Nat.factorial q * q ^ Nat.card ι := Nat.mul_comm _ _
      _ = Nat.factorial q *
          (q ^ (Nat.card ι - q) * q ^ q) := by
        rw [← pow_add, Nat.sub_add_cancel hcard]
      _ = (Nat.factorial q * q ^ (Nat.card ι - q)) * q ^ q := by
        rw [mul_assoc]
  have hcoefficientReal :
      (q : ℝ) ^ Nat.card ι * (Nat.factorial q : ℝ) =
        ((Nat.factorial q : ℝ) *
          (q : ℝ) ^ (Nat.card ι - q)) * (q : ℝ) ^ q := by
    exact_mod_cast hcoefficient
  have hledger :=
    paperRainbowMultiplicity_mul_coupledMean_le_fullyDecoupled D
  rw [hcoefficientReal] at hledger
  nlinarith [hledger]

/-- Degree two has the explicit universal factor `4` after the complete
rainbow/Walsh argument. -/
theorem paperMean_norm_coupled_degreeTwo_le_four_mul_fullyDecoupled
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 2)
    (hcard : 2 ≤ Nat.card ι) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
      4 * paperMean (fun eta : Fin 2 → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  have h := paperMean_norm_coupled_le_q_pow_q_mul_fullyDecoupled D
    (by omega) hcard
  norm_num at h ⊢
  exact h

/-- In positive degree, the cardinality hypothesis follows automatically
unless every coefficient vanishes. -/
theorem paperMean_norm_coupled_le_q_pow_q_mul_fullyDecoupled_of_pos
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (hq : 0 < q) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
      (q : ℝ) ^ q *
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  classical
  by_cases hzero : ∀ t : τ, D.coefficient t = 0
  · simp [paperCoupledRademacherChaos,
      paperFullyDecoupledRademacherChaos, hzero]
    rw [paperMean_zero, paperMean_zero]
    positivity
  · obtain ⟨t, ht⟩ := not_forall.mp hzero
    have hcardFin : Fintype.card (Fin q) ≤ Fintype.card ι :=
      Fintype.card_le_of_injective (D.coordinate t) (D.squareFree t ht)
    have hcard : q ≤ Nat.card ι := by
      simpa [Nat.card_eq_fintype_card] using hcardFin
    exact paperMean_norm_coupled_le_q_pow_q_mul_fullyDecoupled
      D hq hcard

/-- Degree zero is already fully decoupled: both chaoses are the same
deterministic coefficient sum. -/
theorem paperMean_norm_coupled_eq_fullyDecoupled_degreeZero
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 0) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) =
      paperMean (fun eta : Fin 0 → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  have hc : ∀ epsilon : ι → Bool,
      paperCoupledRademacherChaos D epsilon =
        ∑ t : τ, D.coefficient t := by
    intro epsilon
    simp [paperCoupledRademacherChaos, paperCoupledSignMonomial]
  have hd : ∀ eta : Fin 0 → ι → Bool,
      paperFullyDecoupledRademacherChaos D eta =
        ∑ t : τ, D.coefficient t := by
    intro eta
    simp [paperFullyDecoupledRademacherChaos]
  simp_rw [hc, hd]
  rw [paperMean_const_function, paperMean_const_function]

/-- Unconditional finite square-free Rademacher decoupling with explicit
constant `q^q`. -/
theorem paperMean_norm_coupled_le_q_pow_q_mul_fullyDecoupled_unconditional
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
      (q : ℝ) ^ q *
        paperMean (fun eta : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D eta‖) := by
  cases q with
  | zero =>
      simpa using
        (paperMean_norm_coupled_eq_fullyDecoupled_degreeZero D).le
  | succ q =>
      exact paperMean_norm_coupled_le_q_pow_q_mul_fullyDecoupled_of_pos
        D (Nat.succ_pos q)


end GenericProjection

/-! ## Fixed-orientation paper endpoint -/

/-- The paper's fixed-orientation matrix chaos satisfies the unconditional
`edges^edges` coupled-to-fully-decoupled expected operator-norm bound. -/
theorem paperMean_norm_orientedMatrix_le_edges_pow_edges_mul_fullyDecoupled
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperMean (fun epsilon : Sym2 (Fin n) → Bool =>
        ‖paperOrientedGraphMatrix G n orientation
          (paperSym2NoiseToPaper epsilon)‖) ≤
      (G.edges : ℝ) ^ G.edges *
        paperMean (fun eta : Fin G.edges → Sym2 (Fin n) → Bool =>
          ‖paperFullyDecoupledRademacherChaos
            (paperOrientedSquareFreeChaosData G n orientation) eta‖) := by
  simpa only [paperCoupledOrientedChaos_eq_paperOrientedGraphMatrix] using
    (paperMean_norm_coupled_le_q_pow_q_mul_fullyDecoupled_unconditional
      (paperOrientedSquareFreeChaosData G n orientation))


end GraphMatrixReplica
