import R6.PaperRademacherNoncrossingContribution

/-! # Typed open-word contraction for Catalan matchings

The mutually typed row and column words below implement the standard Catalan
decomposition by completely positive sandwiches.  Their norm recursion is
proved unconditionally with the elementary coefficient-energy constant
`∑ e, ‖A e‖²`.  Replacing that constant by the sharper row/column variance
norm requires the C*-algebra norm theorem for completely positive maps; no
such step is assumed here.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Elementary coefficient-energy constant controlling both sandwich maps. -/
def rademacherCoefficientNormEnergy
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) : ℝ :=
  ∑ e : ε, ‖A e‖ ^ 2

/-- Row-valued completely positive sandwich. -/
def rademacherRowSandwich
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix κ κ ℝ) : Matrix ι ι ℝ :=
  ∑ e : ε, A e * X * (A e).transpose

/-- Column-valued completely positive sandwich. -/
def rademacherColumnSandwich
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  ∑ e : ε, (A e).transpose * X * A e

@[simp] theorem rademacherRowSandwich_one
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    rademacherRowSandwich A (1 : Matrix κ κ ℝ) =
      rademacherRowVariance A := by
  classical
  simp [rademacherRowSandwich, rademacherRowVariance]

@[simp] theorem rademacherColumnSandwich_one
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    rademacherColumnSandwich A (1 : Matrix ι ι ℝ) =
      rademacherColumnVariance A := by
  classical
  simp [rademacherColumnSandwich, rademacherColumnVariance]

theorem rademacherRowSandwich_posSemidef
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {X : Matrix κ κ ℝ}
    (hX : X.PosSemidef) : (rademacherRowSandwich A X).PosSemidef := by
  classical
  unfold rademacherRowSandwich
  apply Matrix.posSemidef_sum
  intro e he
  simpa using hX.mul_mul_conjTranspose_same (A e)

theorem rademacherColumnSandwich_posSemidef
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {X : Matrix ι ι ℝ}
    (hX : X.PosSemidef) : (rademacherColumnSandwich A X).PosSemidef := by
  classical
  unfold rademacherColumnSandwich
  apply Matrix.posSemidef_sum
  intro e he
  simpa using hX.mul_mul_conjTranspose_same (A e).transpose

theorem rademacherRowSandwich_norm_le_energy_mul
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix κ κ ℝ) :
    ‖rademacherRowSandwich A X‖ ≤
      rademacherCoefficientNormEnergy A * ‖X‖ := by
  classical
  calc
    ‖rademacherRowSandwich A X‖ ≤
        ∑ e : ε, ‖A e * X * (A e).transpose‖ := by
      simpa [rademacherRowSandwich] using
        (norm_sum_le Finset.univ (fun e : ε => A e * X * (A e).transpose))
    _ ≤ ∑ e : ε, (‖A e‖ ^ 2) * ‖X‖ := by
      apply Finset.sum_le_sum
      intro e he
      have ht : ‖(A e).transpose‖ = ‖A e‖ := by
        simpa using Matrix.l2_opNorm_conjTranspose (A e)
      calc
        ‖A e * X * (A e).transpose‖ ≤
            ‖A e * X‖ * ‖(A e).transpose‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ (‖A e‖ * ‖X‖) * ‖(A e).transpose‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
        _ = (‖A e‖ ^ 2) * ‖X‖ := by rw [ht]; ring
    _ = rademacherCoefficientNormEnergy A * ‖X‖ := by
      simp [rademacherCoefficientNormEnergy, Finset.sum_mul]

theorem rademacherColumnSandwich_norm_le_energy_mul
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (X : Matrix ι ι ℝ) :
    ‖rademacherColumnSandwich A X‖ ≤
      rademacherCoefficientNormEnergy A * ‖X‖ := by
  classical
  calc
    ‖rademacherColumnSandwich A X‖ ≤
        ∑ e : ε, ‖(A e).transpose * X * A e‖ := by
      simpa [rademacherColumnSandwich] using
        (norm_sum_le Finset.univ (fun e : ε => (A e).transpose * X * A e))
    _ ≤ ∑ e : ε, (‖A e‖ ^ 2) * ‖X‖ := by
      apply Finset.sum_le_sum
      intro e he
      have ht : ‖(A e).transpose‖ = ‖A e‖ := by
        simpa using Matrix.l2_opNorm_conjTranspose (A e)
      calc
        ‖(A e).transpose * X * A e‖ ≤
            ‖(A e).transpose * X‖ * ‖A e‖ :=
          Matrix.l2_opNorm_mul _ _
        _ ≤ (‖(A e).transpose‖ * ‖X‖) * ‖A e‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
        _ = (‖A e‖ ^ 2) * ‖X‖ := by rw [ht]; ring
    _ = rademacherCoefficientNormEnergy A * ‖X‖ := by
      simp [rademacherCoefficientNormEnergy, Finset.sum_mul]

/-- The elementary energy genuinely dominates both sharp variance norms. -/
theorem rademacherVarianceNormMax_le_coefficientNormEnergy
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) :
    rademacherVarianceNormMax A ≤ rademacherCoefficientNormEnergy A := by
  have hE : 0 ≤ rademacherCoefficientNormEnergy A :=
    Finset.sum_nonneg fun e he => sq_nonneg ‖A e‖
  have hrowOne : ‖(1 : Matrix κ κ ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  have hcolOne : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  apply max_le
  · calc
      ‖rademacherRowVariance A‖ =
          ‖rademacherRowSandwich A (1 : Matrix κ κ ℝ)‖ := by rw [rademacherRowSandwich_one]
      _ ≤ rademacherCoefficientNormEnergy A * ‖(1 : Matrix κ κ ℝ)‖ :=
        rademacherRowSandwich_norm_le_energy_mul A _
      _ ≤ rademacherCoefficientNormEnergy A * 1 :=
        mul_le_mul_of_nonneg_left hrowOne hE
      _ = rademacherCoefficientNormEnergy A := mul_one _
  · calc
      ‖rademacherColumnVariance A‖ =
          ‖rademacherColumnSandwich A (1 : Matrix ι ι ℝ)‖ := by rw [rademacherColumnSandwich_one]
      _ ≤ rademacherCoefficientNormEnergy A * ‖(1 : Matrix ι ι ℝ)‖ :=
        rademacherColumnSandwich_norm_le_energy_mul A _
      _ ≤ rademacherCoefficientNormEnergy A * 1 :=
        mul_le_mul_of_nonneg_left hcolOne hE
      _ = rademacherCoefficientNormEnergy A := mul_one _

/- Row-starting open word associated recursively with a Catalan matching. -/
mutual
  def rademacherRowOpenWord
      {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
      [DecidableEq ι] [DecidableEq κ]
      (A : ε → Matrix ι κ ℝ) : {n : ℕ} →
        RademacherNoncrossingMatching n → Matrix ι ι ℝ
    | 0, .empty => 1
    | _, .node inside outside =>
        rademacherRowSandwich A (rademacherColumnOpenWord A inside) *
          rademacherRowOpenWord A outside

  /-- Column-starting open word, obtained by switching row and column types. -/
  def rademacherColumnOpenWord
      {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
      [DecidableEq ι] [DecidableEq κ]
      (A : ε → Matrix ι κ ℝ) : {n : ℕ} →
        RademacherNoncrossingMatching n → Matrix κ κ ℝ
    | 0, .empty => 1
    | _, .node inside outside =>
        rademacherColumnSandwich A (rademacherRowOpenWord A inside) *
          rademacherColumnOpenWord A outside
end

/-- The typed row and column open words are closed under every Catalan node,
with one coefficient-energy factor per matched pair. -/
theorem rademacherOpenWords_norm_le_energy_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    ‖rademacherRowOpenWord A M‖ ≤
        rademacherCoefficientNormEnergy A ^ n ∧
      ‖rademacherColumnOpenWord A M‖ ≤
        rademacherCoefficientNormEnergy A ^ n := by
  induction M with
  | empty =>
      simp only [rademacherRowOpenWord, rademacherColumnOpenWord, pow_zero]
      constructor
      · rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
        exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
      · rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
        exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  | @node a b inside outside ihInside ihOutside =>
      have hE : 0 ≤ rademacherCoefficientNormEnergy A := by
        exact Finset.sum_nonneg fun e he => sq_nonneg ‖A e‖
      constructor
      · calc
          ‖rademacherRowOpenWord A (.node inside outside)‖ ≤
              ‖rademacherRowSandwich A
                  (rademacherColumnOpenWord A inside)‖ *
                ‖rademacherRowOpenWord A outside‖ := by
            simpa [rademacherRowOpenWord] using Matrix.l2_opNorm_mul
              (rademacherRowSandwich A
                (rademacherColumnOpenWord A inside))
              (rademacherRowOpenWord A outside)
          _ ≤ (rademacherCoefficientNormEnergy A *
                  ‖rademacherColumnOpenWord A inside‖) *
                ‖rademacherRowOpenWord A outside‖ := by
            gcongr
            exact rademacherRowSandwich_norm_le_energy_mul A _
          _ ≤ (rademacherCoefficientNormEnergy A *
                  rademacherCoefficientNormEnergy A ^ a) *
                rademacherCoefficientNormEnergy A ^ b := by
            gcongr
            · exact ihInside.2
            · exact ihOutside.1
          _ = rademacherCoefficientNormEnergy A ^ (a + b + 1) := by
            rw [pow_add]
            ring
      · calc
          ‖rademacherColumnOpenWord A (.node inside outside)‖ ≤
              ‖rademacherColumnSandwich A
                  (rademacherRowOpenWord A inside)‖ *
                ‖rademacherColumnOpenWord A outside‖ := by
            simpa [rademacherColumnOpenWord] using Matrix.l2_opNorm_mul
              (rademacherColumnSandwich A
                (rademacherRowOpenWord A inside))
              (rademacherColumnOpenWord A outside)
          _ ≤ (rademacherCoefficientNormEnergy A *
                  ‖rademacherRowOpenWord A inside‖) *
                ‖rademacherColumnOpenWord A outside‖ := by
            gcongr
            exact rademacherColumnSandwich_norm_le_energy_mul A _
          _ ≤ (rademacherCoefficientNormEnergy A *
                  rademacherCoefficientNormEnergy A ^ a) *
                rademacherCoefficientNormEnergy A ^ b := by
            gcongr
            · exact ihInside.1
            · exact ihOutside.2
          _ = rademacherCoefficientNormEnergy A ^ (a + b + 1) := by
            rw [pow_add]
            ring

/-- A diagonal entry is bounded by the Euclidean matrix operator norm. -/
theorem abs_matrix_diag_le_l2_opNorm
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (i : ι) : |B i i| ≤ ‖B‖ := by
  let x : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  let y : EuclideanSpace ℝ ι :=
    (EuclideanSpace.equiv ι ℝ).symm (Matrix.mulVec B x.ofLp)
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ ‖B‖ * ‖x‖ := by
    exact Matrix.l2_opNorm_mulVec B x
  calc
    |B i i| = ‖y.ofLp i‖ := by
      simp [x, y, Real.norm_eq_abs]
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖B‖ * ‖x‖ := hop
    _ = ‖B‖ := by simp [x]

/-- Absolute trace is at most dimension times Euclidean operator norm. -/
theorem abs_matrix_trace_le_card_mul_l2_opNorm
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) :
    |Matrix.trace B| ≤ (Fintype.card ι : ℝ) * ‖B‖ := by
  calc
    |Matrix.trace B| ≤ ∑ i : ι, |B i i| := by
      simpa [Matrix.trace] using
        (Finset.abs_sum_le_sum_abs (fun i : ι => B i i) Finset.univ)
    _ ≤ ∑ _i : ι, ‖B‖ :=
      Finset.sum_le_sum fun i hi => abs_matrix_diag_le_l2_opNorm B i
    _ = (Fintype.card ι : ℝ) * ‖B‖ := by simp

/-- The recursively contracted row-open trace has a fully unconditional
coefficient-energy bound. -/
theorem abs_trace_rademacherRowOpenWord_le_card_mul_energy_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    |Matrix.trace (rademacherRowOpenWord A M)| ≤
      (Fintype.card ι : ℝ) * rademacherCoefficientNormEnergy A ^ n := by
  exact (abs_matrix_trace_le_card_mul_l2_opNorm
    (rademacherRowOpenWord A M)).trans
      (mul_le_mul_of_nonneg_left
        (rademacherOpenWords_norm_le_energy_pow A M).1
        (Nat.cast_nonneg _))

/-- Explicit analytic interface for a common row/column sandwich constant.
The desired sharp instance takes `V = rademacherVarianceNormMax A`. -/
def RademacherSandwichNormBound
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (V : ℝ) : Prop :=
  (∀ X : Matrix κ κ ℝ, ‖rademacherRowSandwich A X‖ ≤ V * ‖X‖) ∧
    (∀ X : Matrix ι ι ℝ, ‖rademacherColumnSandwich A X‖ ≤ V * ‖X‖)

/-- Once a common sandwich constant is available, Catalan recursion loses
exactly one factor `V` per pair. -/
theorem rademacherOpenWords_norm_le_pow_of_sandwichNormBound
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hbound : RademacherSandwichNormBound A V)
    {n : ℕ} (M : RademacherNoncrossingMatching n) :
    ‖rademacherRowOpenWord A M‖ ≤ V ^ n ∧
      ‖rademacherColumnOpenWord A M‖ ≤ V ^ n := by
  induction M with
  | empty =>
      simp only [rademacherRowOpenWord, rademacherColumnOpenWord, pow_zero]
      constructor
      · rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
        exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
      · rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
        exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by simp
  | @node a b inside outside ihInside ihOutside =>
      constructor
      · calc
          ‖rademacherRowOpenWord A (.node inside outside)‖ ≤
              ‖rademacherRowSandwich A
                  (rademacherColumnOpenWord A inside)‖ *
                ‖rademacherRowOpenWord A outside‖ := by
            simpa [rademacherRowOpenWord] using Matrix.l2_opNorm_mul
              (rademacherRowSandwich A
                (rademacherColumnOpenWord A inside))
              (rademacherRowOpenWord A outside)
          _ ≤ (V * ‖rademacherColumnOpenWord A inside‖) *
                ‖rademacherRowOpenWord A outside‖ := by
            gcongr
            exact hbound.1 _
          _ ≤ (V * V ^ a) * V ^ b := by
            gcongr
            · exact ihInside.2
            · exact ihOutside.1
          _ = V ^ (a + b + 1) := by rw [pow_add]; ring
      · calc
          ‖rademacherColumnOpenWord A (.node inside outside)‖ ≤
              ‖rademacherColumnSandwich A
                  (rademacherRowOpenWord A inside)‖ *
                ‖rademacherColumnOpenWord A outside‖ := by
            simpa [rademacherColumnOpenWord] using Matrix.l2_opNorm_mul
              (rademacherColumnSandwich A
                (rademacherRowOpenWord A inside))
              (rademacherColumnOpenWord A outside)
          _ ≤ (V * ‖rademacherRowOpenWord A inside‖) *
                ‖rademacherColumnOpenWord A outside‖ := by
            gcongr
            exact hbound.2 _
          _ ≤ (V * V ^ a) * V ^ b := by
            gcongr
            · exact ihInside.1
            · exact ihOutside.2
          _ = V ^ (a + b + 1) := by rw [pow_add]; ring

/-- Exact sharp endpoint, conditional only on the isolated CP-sandwich norm
lemma.  This premise is deliberately visible and is not an NCK assumption. -/
theorem rademacherOpenWords_norm_le_varianceNormMax_pow_of_sharpSandwich
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ)
    (hsharp : RademacherSandwichNormBound A
      (rademacherVarianceNormMax A))
    {n : ℕ} (M : RademacherNoncrossingMatching n) :
    ‖rademacherRowOpenWord A M‖ ≤ rademacherVarianceNormMax A ^ n ∧
      ‖rademacherColumnOpenWord A M‖ ≤
        rademacherVarianceNormMax A ^ n :=
  rademacherOpenWords_norm_le_pow_of_sandwichNormBound A
    (rademacherVarianceNormMax_nonneg A) hsharp M

#print axioms rademacherRowSandwich_norm_le_energy_mul
#print axioms rademacherColumnSandwich_norm_le_energy_mul
#print axioms rademacherRowSandwich_posSemidef
#print axioms rademacherColumnSandwich_posSemidef
#print axioms rademacherVarianceNormMax_le_coefficientNormEnergy
#print axioms rademacherOpenWords_norm_le_energy_pow
#print axioms abs_trace_rademacherRowOpenWord_le_card_mul_energy_pow
#print axioms rademacherOpenWords_norm_le_pow_of_sandwichNormBound
#print axioms
  rademacherOpenWords_norm_le_varianceNormMax_pow_of_sharpSandwich

end GraphMatrixReplica
