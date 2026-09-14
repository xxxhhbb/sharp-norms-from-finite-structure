import R6.PaperR16HilbertSignFourthMoment

/-! The finite one-group matrix stacking test-vector estimate. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.PaperR16

def lowerMatrixSignSum {ι κ : Type*} (n : ℕ)
    (A : Fin n → Matrix ι κ ℝ) (w : Fin n → Bool) : Matrix ι κ ℝ :=
  fun i j => ∑ e : Fin n, (if w e then (-1 : ℝ) else 1) * A e i j

theorem lowerMatrixSignSum_mulVec
    {ι κ : Type*} [Fintype ι] [Fintype κ] (n : ℕ)
    (A : Fin n → Matrix ι κ ℝ) (w : Fin n → Bool) (x : κ → ℝ) :
    Matrix.mulVec (lowerMatrixSignSum n A w) x =
      euclideanSignSum n (fun e => Matrix.mulVec (A e) x) w := by
  funext i
  simp only [Matrix.mulVec, dotProduct, lowerMatrixSignSum, euclideanSignSum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem euclideanLength_eq_norm {ι : Type*} [Fintype ι]
    (y : ι → ℝ) :
    euclideanLength y = ‖(EuclideanSpace.equiv ι ℝ).symm y‖ := by
  simp [euclideanLength, euclideanSq, EuclideanSpace.norm_eq]

theorem lowerMatrixSignSum_length_le_opNorm_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ)
    (w : Fin n → Bool) (x : EuclideanSpace ℝ κ) :
    euclideanLength
        (euclideanSignSum n (fun e => Matrix.mulVec (A e) x.ofLp) w) ≤
      ‖lowerMatrixSignSum n A w‖ * ‖x‖ := by
  rw [← lowerMatrixSignSum_mulVec]
  rw [euclideanLength_eq_norm]
  exact Matrix.l2_opNorm_mulVec _ x

/-- A one-group lower stacking estimate for every fixed input vector,
without normalizing it or assuming a fourth-moment bound: the needed
Rademacher 2/4-moment computation is imported from the Hilbert module. -/
theorem lowerMatrixSignSum_testVector_variance_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ)
    (x : EuclideanSpace ℝ κ) :
    (∑ e : Fin n, euclideanSq (Matrix.mulVec (A e) x.ofLp)) ≤
      3 * (allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖)) ^ 2 *
        ‖x‖ ^ 2 := by
  let N : ℝ := (2 : ℝ) ^ n
  let L : ℝ := allSignsMean n (fun w =>
    euclideanLength (euclideanSignSum n
      (fun e => Matrix.mulVec (A e) x.ofLp) w))
  let M : ℝ := allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖)
  have hN : 0 ≤ N := by positivity
  have hSum :
      (∑ w : Fin n → Bool,
        euclideanLength (euclideanSignSum n
          (fun e => Matrix.mulVec (A e) x.ofLp) w)) ≤
        (∑ w : Fin n → Bool, ‖lowerMatrixSignSum n A w‖) * ‖x‖ := by
    calc
      _ ≤ ∑ w : Fin n → Bool, ‖lowerMatrixSignSum n A w‖ * ‖x‖ := by
        apply Finset.sum_le_sum
        intro w _
        exact lowerMatrixSignSum_length_le_opNorm_mul n A w x
      _ = (∑ w : Fin n → Bool, ‖lowerMatrixSignSum n A w‖) * ‖x‖ := by
        rw [Finset.sum_mul]
  have hMean : L ≤ M * ‖x‖ := by
    change (∑ w : Fin n → Bool,
      euclideanLength (euclideanSignSum n
        (fun e => Matrix.mulVec (A e) x.ofLp) w)) / N ≤
      ((∑ w : Fin n → Bool, ‖lowerMatrixSignSum n A w‖) / N) * ‖x‖
    calc
      _ ≤ ((∑ w : Fin n → Bool, ‖lowerMatrixSignSum n A w‖) * ‖x‖) / N :=
        div_le_div_of_nonneg_right hSum hN
      _ = ((∑ w : Fin n → Bool, ‖lowerMatrixSignSum n A w‖) / N) * ‖x‖ := by
        ring
  have hL : 0 ≤ L := by
    unfold L allSignsMean
    apply div_nonneg
    · exact Finset.sum_nonneg (fun w _ => euclideanLength_nonneg _)
    · positivity
  have hV := euclideanSignSum_first_mean_sq_lower n
    (fun e => Matrix.mulVec (A e) x.ofLp)
  calc
    (∑ e : Fin n, euclideanSq (Matrix.mulVec (A e) x.ofLp)) ≤ 3 * L ^ 2 := hV
    _ ≤ 3 * (M * ‖x‖) ^ 2 := by gcongr
    _ = 3 * M ^ 2 * ‖x‖ ^ 2 := by ring

def lowerVerticallyStackedMatrix {ι κ : Type*} (n : ℕ)
    (A : Fin n → Matrix ι κ ℝ) : Matrix (Fin n × ι) κ ℝ :=
  fun ei j => A ei.1 ei.2 j

theorem lowerVerticallyStackedMatrix_mulVec_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) (x : κ → ℝ) :
    euclideanSq (Matrix.mulVec (lowerVerticallyStackedMatrix n A) x) =
      ∑ e : Fin n, euclideanSq (Matrix.mulVec (A e) x) := by
  classical
  simp [euclideanSq, lowerVerticallyStackedMatrix,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem lowerVerticallyStackedMatrix_norm_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) :
    ‖lowerVerticallyStackedMatrix n A‖ ^ 2 ≤
      3 * (allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖)) ^ 2 := by
  let B := lowerVerticallyStackedMatrix n A
  let M := allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖)
  have hM : 0 ≤ M := by
    unfold M allSignsMean
    apply div_nonneg
    · exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
    · positivity
  have hB : ‖B‖ ≤ Real.sqrt 3 * M := by
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (Real.sqrt_nonneg 3) hM)
    intro x
    change ‖(EuclideanSpace.equiv (Fin n × ι) ℝ).symm
      (Matrix.mulVec B x.ofLp)‖ ≤ Real.sqrt 3 * M * ‖x‖
    have hVar := lowerMatrixSignSum_testVector_variance_le n A x
    rw [← lowerVerticallyStackedMatrix_mulVec_sq] at hVar
    have hSq :
        ‖(EuclideanSpace.equiv (Fin n × ι) ℝ).symm
          (Matrix.mulVec B x.ofLp)‖ ^ 2 ≤
          (Real.sqrt 3 * M * ‖x‖) ^ 2 := by
      calc
        _ = euclideanSq (Matrix.mulVec B x.ofLp) := by
          simp [EuclideanSpace.norm_sq_eq, euclideanSq]
        _ ≤ 3 * M ^ 2 * ‖x‖ ^ 2 := hVar
        _ = (Real.sqrt 3 * M * ‖x‖) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith [hSq, norm_nonneg ((EuclideanSpace.equiv (Fin n × ι) ℝ).symm
      (Matrix.mulVec B x.ofLp)), mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg 3) hM) (norm_nonneg x)]
  have hBnonneg : 0 ≤ ‖B‖ := norm_nonneg _
  have hTargetNonneg : 0 ≤ Real.sqrt 3 * M :=
    mul_nonneg (Real.sqrt_nonneg _) hM
  have hPow := pow_le_pow_left₀ hBnonneg hB 2
  calc
    ‖B‖ ^ 2 ≤ (Real.sqrt 3 * M) ^ 2 := hPow
    _ = 3 * M ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem lowerMatrixSignSum_transpose
    {ι κ : Type*} (n : ℕ) (A : Fin n → Matrix ι κ ℝ)
    (w : Fin n → Bool) :
    (lowerMatrixSignSum n A w).transpose =
      lowerMatrixSignSum n (fun e => (A e).transpose) w := by
  ext i j
  rfl

theorem lowerMatrixSignSum_transpose_mean_norm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) :
    allSignsMean n
        (fun w => ‖lowerMatrixSignSum n (fun e => (A e).transpose) w‖) =
      allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖) := by
  unfold allSignsMean
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  change ‖lowerMatrixSignSum n (fun e => (A e).transpose) w‖ =
    ‖lowerMatrixSignSum n A w‖
  rw [← lowerMatrixSignSum_transpose]
  simpa using Matrix.l2_opNorm_conjTranspose (lowerMatrixSignSum n A w)

def lowerHorizontallyStackedMatrix {ι κ : Type*} (n : ℕ)
    (A : Fin n → Matrix ι κ ℝ) : Matrix ι (Fin n × κ) ℝ :=
  (lowerVerticallyStackedMatrix n
    (fun e => (A e).transpose)).transpose

theorem lowerHorizontallyStackedMatrix_norm_sq_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) :
    ‖lowerHorizontallyStackedMatrix n A‖ ^ 2 ≤
      3 * (allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖)) ^ 2 := by
  have h := lowerVerticallyStackedMatrix_norm_sq_le n
    (fun e => (A e).transpose)
  rw [lowerMatrixSignSum_transpose_mean_norm n A] at h
  change ‖(lowerVerticallyStackedMatrix n
    (fun e => (A e).transpose)).transpose‖ ^ 2 ≤
      3 * (allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖)) ^ 2
  have hNorm :
      ‖(lowerVerticallyStackedMatrix n
        (fun e => (A e).transpose)).transpose‖ =
        ‖lowerVerticallyStackedMatrix n
          (fun e => (A e).transpose)‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose
      (lowerVerticallyStackedMatrix n (fun e => (A e).transpose))
  rw [hNorm]
  exact h

theorem lowerMatrixSignSum_testVector_mean_lower
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ)
    (x : EuclideanSpace ℝ κ) (hx : ‖x‖ = 1) :
    Real.sqrt
      ((∑ e : Fin n, euclideanSq (Matrix.mulVec (A e) x.ofLp)) / 3) ≤
      allSignsMean n (fun w => ‖lowerMatrixSignSum n A w‖) := by
  have hVector := euclideanSignSum_first_mean_sqrt_lower n
    (fun e => Matrix.mulVec (A e) x.ofLp)
  apply hVector.trans
  unfold allSignsMean
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro w _
  simpa [hx] using lowerMatrixSignSum_length_le_opNorm_mul n A w x

#print axioms lowerMatrixSignSum_mulVec
#print axioms lowerMatrixSignSum_testVector_variance_le
#print axioms lowerVerticallyStackedMatrix_norm_sq_le
#print axioms lowerHorizontallyStackedMatrix_norm_sq_le
#print axioms lowerMatrixSignSum_testVector_mean_lower

end GraphMatrixReplica.PaperR16
