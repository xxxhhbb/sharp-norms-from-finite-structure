import R6.PaperR16LowerFactorInterfaces

/-!
# The finite Euclidean Rademacher 2/4-moment step of R16 lower stacking

This file uses every sign assignment in `Fin n → Bool`, with uniform
normalization by `2^n`.  A vector is represented by finitely many real
coordinates.  No fourth-moment or independence hypothesis is inserted.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.PaperR16

def euclideanSq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ j : ι, x j ^ 2

def euclideanDot {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : ℝ :=
  ∑ j : ι, x j * y j

theorem euclideanSq_nonneg {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : 0 ≤ euclideanSq x := by
  unfold euclideanSq
  positivity

theorem euclideanDot_sq_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    euclideanDot x y ^ 2 ≤ euclideanSq x * euclideanSq y := by
  simpa only [euclideanDot, euclideanSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y)

theorem euclideanSq_add {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    euclideanSq (fun j => x j + y j) =
      euclideanSq x + 2 * euclideanDot x y + euclideanSq y := by
  unfold euclideanSq euclideanDot
  simp_rw [add_pow_two]
  simp [Finset.sum_add_distrib, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

theorem euclideanSq_sub {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    euclideanSq (fun j => x j - y j) =
      euclideanSq x - 2 * euclideanDot x y + euclideanSq y := by
  unfold euclideanSq euclideanDot
  simp_rw [sub_sq]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Pointwise average of the two choices for one fresh sign. -/
theorem euclideanSq_sign_pair {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    euclideanSq (fun j => x j + y j) +
      euclideanSq (fun j => x j - y j) =
        2 * euclideanSq x + 2 * euclideanSq y := by
  rw [euclideanSq_add, euclideanSq_sub]
  ring

/-- The genuinely Hilbert-space fourth-moment one-step inequality. -/
theorem euclideanSq_sq_sign_pair_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    euclideanSq (fun j => x j + y j) ^ 2 +
      euclideanSq (fun j => x j - y j) ^ 2 ≤
        2 * euclideanSq x ^ 2 +
          12 * euclideanSq x * euclideanSq y +
          2 * euclideanSq y ^ 2 := by
  have hCS := euclideanDot_sq_le x y
  rw [euclideanSq_add, euclideanSq_sub]
  nlinarith [hCS]

/-- Uniformly enumerate a new independent sign and the previous `n`
signs. -/
theorem sum_all_signs_succ (n : ℕ)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    (∑ w : Fin (n + 1) → Bool, f w) =
      ∑ w : Fin n → Bool,
        (f (Fin.cons false w) + f (Fin.cons true w)) := by
  classical
  calc
    (∑ w : Fin (n + 1) → Bool, f w) =
        ∑ z : Bool × (Fin n → Bool), f (Fin.cons z.1 z.2) := by
      symm
      apply Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
      intro z
      rfl
    _ = ∑ w : Fin n → Bool,
          (f (Fin.cons false w) + f (Fin.cons true w)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [add_comm]

def euclideanSignSum {ι : Type*} [Fintype ι] (n : ℕ)
    (v : Fin n → ι → ℝ) (w : Fin n → Bool) : ι → ℝ :=
  fun j => ∑ e : Fin n, (if w e then (-1 : ℝ) else 1) * v e j

theorem euclideanSignSum_cons {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → ι → ℝ)
    (b : Bool) (w : Fin n → Bool) :
    euclideanSignSum (n + 1) v (Fin.cons b w) =
      fun j => (if b then (-1 : ℝ) else 1) * v 0 j +
        euclideanSignSum n (fun e => v e.succ) w j := by
  funext j
  simp [euclideanSignSum, Fin.sum_univ_succ]

theorem euclideanSignSum_cons_false {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → ι → ℝ)
    (w : Fin n → Bool) :
    euclideanSignSum (n + 1) v (Fin.cons false w) =
      fun j => euclideanSignSum n (fun e => v e.succ) w j + v 0 j := by
  rw [euclideanSignSum_cons]
  funext j
  simp
  ring

theorem euclideanSignSum_cons_true {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → ι → ℝ)
    (w : Fin n → Bool) :
    euclideanSignSum (n + 1) v (Fin.cons true w) =
      fun j => euclideanSignSum n (fun e => v e.succ) w j - v 0 j := by
  rw [euclideanSignSum_cons]
  funext j
  simp
  ring

theorem signSample_card (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp [Fintype.card_fun]

theorem euclideanSignSum_sq_pair {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → ι → ℝ)
    (w : Fin n → Bool) :
    euclideanSq (euclideanSignSum (n + 1) v (Fin.cons false w)) +
      euclideanSq (euclideanSignSum (n + 1) v (Fin.cons true w)) =
    2 * euclideanSq (euclideanSignSum n (fun e => v e.succ) w) +
      2 * euclideanSq (v 0) := by
  rw [euclideanSignSum_cons_false, euclideanSignSum_cons_true]
  exact euclideanSq_sign_pair
    (euclideanSignSum n (fun e => v e.succ) w) (v 0)

theorem euclideanSignSum_fourth_pair {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → ι → ℝ)
    (w : Fin n → Bool) :
    euclideanSq (euclideanSignSum (n + 1) v (Fin.cons false w)) ^ 2 +
      euclideanSq (euclideanSignSum (n + 1) v (Fin.cons true w)) ^ 2 ≤
    2 * euclideanSq (euclideanSignSum n (fun e => v e.succ) w) ^ 2 +
      12 * euclideanSq (euclideanSignSum n (fun e => v e.succ) w) *
        euclideanSq (v 0) + 2 * euclideanSq (v 0) ^ 2 := by
  rw [euclideanSignSum_cons_false, euclideanSignSum_cons_true]
  exact euclideanSq_sq_sign_pair_le
    (euclideanSignSum n (fun e => v e.succ) w) (v 0)

/-- Exact second moment over all independent sign assignments. -/
theorem euclideanSignSum_second_raw {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin n → ι → ℝ) :
    (∑ w : Fin n → Bool, euclideanSq (euclideanSignSum n v w)) =
      (2 : ℝ) ^ n * ∑ e : Fin n, euclideanSq (v e) := by
  induction n with
  | zero =>
      simp [euclideanSignSum, euclideanSq]
  | succ n ih =>
      let tail : Fin n → ι → ℝ := fun e => v e.succ
      rw [sum_all_signs_succ]
      calc
        (∑ w : Fin n → Bool,
            (euclideanSq (euclideanSignSum (n + 1) v (Fin.cons false w)) +
              euclideanSq (euclideanSignSum (n + 1) v (Fin.cons true w)))) =
          ∑ w : Fin n → Bool,
            (2 * euclideanSq (euclideanSignSum n tail w) +
              2 * euclideanSq (v 0)) := by
          apply Finset.sum_congr rfl
          intro w _
          exact euclideanSignSum_sq_pair n v w
        _ = 2 * (∑ w : Fin n → Bool,
              euclideanSq (euclideanSignSum n tail w)) +
              2 * (2 : ℝ) ^ n * euclideanSq (v 0) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum,
            signSample_card, mul_assoc, mul_comm, mul_left_comm]
        _ = (2 : ℝ) ^ (n + 1) *
              ∑ e : Fin (n + 1), euclideanSq (v e) := by
          rw [ih tail, Fin.sum_univ_succ, pow_succ]
          ring

/-- Fourth moment over the *actual* uniform product sign space.  The
constant `3` follows from the pointwise Hilbert Cauchy--Schwarz bound and
the exact second-moment induction, not from a named Khintchine assumption. -/
theorem euclideanSignSum_fourth_raw {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin n → ι → ℝ) :
    (∑ w : Fin n → Bool,
      euclideanSq (euclideanSignSum n v w) ^ 2) ≤
        3 * (2 : ℝ) ^ n *
          (∑ e : Fin n, euclideanSq (v e)) ^ 2 := by
  induction n with
  | zero =>
      simp [euclideanSignSum, euclideanSq]
  | succ n ih =>
      let tail : Fin n → ι → ℝ := fun e => v e.succ
      let a : ℝ := euclideanSq (v 0)
      let V : ℝ := ∑ e : Fin n, euclideanSq (tail e)
      let N : ℝ := (2 : ℝ) ^ n
      have hA : 0 ≤ a := euclideanSq_nonneg (v 0)
      have hV : 0 ≤ V := Finset.sum_nonneg
        (fun e _ => euclideanSq_nonneg (tail e))
      have hN : 0 ≤ N := by positivity
      have hSecond :
          (∑ w : Fin n → Bool,
            euclideanSq (euclideanSignSum n tail w)) = N * V :=
        euclideanSignSum_second_raw n tail
      have hFourth :
          (∑ w : Fin n → Bool,
            euclideanSq (euclideanSignSum n tail w) ^ 2) ≤
              3 * N * V ^ 2 := ih tail
      rw [sum_all_signs_succ]
      calc
        (∑ w : Fin n → Bool,
          (euclideanSq (euclideanSignSum (n + 1) v (Fin.cons false w)) ^ 2 +
            euclideanSq (euclideanSignSum (n + 1) v (Fin.cons true w)) ^ 2)) ≤
          ∑ w : Fin n → Bool,
            (2 * euclideanSq (euclideanSignSum n tail w) ^ 2 +
              12 * euclideanSq (euclideanSignSum n tail w) * a +
              2 * a ^ 2) := by
          apply Finset.sum_le_sum
          intro w _
          exact euclideanSignSum_fourth_pair n v w
        _ = 2 * (∑ w : Fin n → Bool,
              euclideanSq (euclideanSignSum n tail w) ^ 2) +
              12 * a * (∑ w : Fin n → Bool,
                euclideanSq (euclideanSignSum n tail w)) +
              2 * N * a ^ 2 := by
          simp [Finset.sum_add_distrib, Finset.mul_sum,
            signSample_card, N, mul_assoc, mul_comm, mul_left_comm]
        _ ≤ 2 * (3 * N * V ^ 2) + 12 * a * (N * V) +
              2 * N * a ^ 2 := by
          have hScaled := mul_le_mul_of_nonneg_left hFourth
            (by norm_num : (0 : ℝ) ≤ 2)
          rw [hSecond]
          nlinarith [hScaled]
        _ ≤ 3 * (2 : ℝ) ^ (n + 1) *
              (∑ e : Fin (n + 1), euclideanSq (v e)) ^ 2 := by
          rw [Fin.sum_univ_succ, pow_succ]
          change 2 * (3 * N * V ^ 2) + 12 * a * (N * V) +
            2 * N * a ^ 2 ≤ 3 * (N * 2) * (a + V) ^ 2
          nlinarith [mul_nonneg hN (sq_nonneg a)]

/-- Uniform mean on the complete product sign sample, normalized by its
exact cardinality `2^n`. -/
def allSignsMean (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ w : Fin n → Bool, f w) / (2 : ℝ) ^ n

theorem allSignsMean_eq_card_mean (n : ℕ)
    (f : (Fin n → Bool) → ℝ) :
    allSignsMean n f =
      (∑ w : Fin n → Bool, f w) /
        (Fintype.card (Fin n → Bool) : ℝ) := by
  simp [allSignsMean, signSample_card]

/-- `E‖Σ εᵢvᵢ‖² = Σ‖vᵢ‖²` in finite Euclidean coordinates. -/
theorem euclideanSignSum_second_mean {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin n → ι → ℝ) :
    allSignsMean n
        (fun w => euclideanSq (euclideanSignSum n v w)) =
      ∑ e : Fin n, euclideanSq (v e) := by
  unfold allSignsMean
  rw [euclideanSignSum_second_raw]
  have hTwo : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- `E‖Σ εᵢvᵢ‖⁴ ≤ 3(Σ‖vᵢ‖²)²`, with the same complete sample
normalization as the second moment. -/
theorem euclideanSignSum_fourth_mean {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin n → ι → ℝ) :
    allSignsMean n
        (fun w => euclideanSq (euclideanSignSum n v w) ^ 2) ≤
      3 * (∑ e : Fin n, euclideanSq (v e)) ^ 2 := by
  unfold allSignsMean
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (euclideanSignSum_fourth_raw n v)

def euclideanLength {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (euclideanSq x)

theorem euclideanLength_nonneg {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : 0 ≤ euclideanLength x :=
  Real.sqrt_nonneg _

theorem euclideanLength_sq {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : euclideanLength x ^ 2 = euclideanSq x := by
  exact Real.sq_sqrt (euclideanSq_nonneg x)

theorem euclideanLength_fourth {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : euclideanLength x ^ 4 = euclideanSq x ^ 2 := by
  calc
    euclideanLength x ^ 4 = (euclideanLength x ^ 2) ^ 2 := by ring
    _ = euclideanSq x ^ 2 := by rw [euclideanLength_sq]

/-- The finite-vector `1/√3` stacking constant, in its exact squared
form `E‖Σ εᵢvᵢ‖² ≤ 3(E‖Σ εᵢvᵢ‖)²`.  The 2/4 moments and the interpolation
are both already proved, so there is no probabilistic hypothesis here. -/
theorem euclideanSignSum_first_mean_sq_lower
    {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin n → ι → ℝ) :
    (∑ e : Fin n, euclideanSq (v e)) ≤
      3 * (allSignsMean n
        (fun w => euclideanLength (euclideanSignSum n v w))) ^ 2 := by
  let z : (Fin n → Bool) → ℝ :=
    fun w => euclideanLength (euclideanSignSum n v w)
  let N : ℝ := (2 : ℝ) ^ n
  let V : ℝ := ∑ e : Fin n, euclideanSq (v e)
  have hNpos : 0 < N := pow_pos (by norm_num) _
  have hCard : (Fintype.card (Fin n → Bool) : ℝ) = N := by
    simp [N, signSample_card]
  have hZ : ∀ w ∈ (Finset.univ : Finset (Fin n → Bool)), 0 ≤ z w :=
    fun w _ => euclideanLength_nonneg _
  have hSecond :
      (∑ w : Fin n → Bool, z w ^ 2) = N * V := by
    simp only [z, euclideanLength_sq]
    exact euclideanSignSum_second_raw n v
  have hFourth :
      (∑ w : Fin n → Bool, z w ^ 4) ≤ 3 * N * V ^ 2 := by
    simp only [z, euclideanLength_fourth]
    exact euclideanSignSum_fourth_raw n v
  have hFourthForInterpolation :
      (Fintype.card (Fin n → Bool) : ℝ) *
        (∑ w : Fin n → Bool, z w ^ 4) ≤
          3 * (∑ w : Fin n → Bool, z w ^ 2) ^ 2 := by
    rw [hCard, hSecond]
    calc
      N * (∑ w : Fin n → Bool, z w ^ 4) ≤
          N * (3 * N * V ^ 2) :=
        mul_le_mul_of_nonneg_left hFourth hNpos.le
      _ = 3 * (N * V) ^ 2 := by ring
  have hFirst := finite_first_moment_lower_of_fourth
    (Finset.univ : Finset (Fin n → Bool)) z hZ
      hFourthForInterpolation
  simp only [Finset.card_univ] at hFirst
  rw [hCard, hSecond] at hFirst
  change V ≤ 3 * ((∑ w : Fin n → Bool, z w) / N) ^ 2
  rw [div_pow]
  calc
    V ≤ (3 * (∑ w : Fin n → Bool, z w) ^ 2) / N ^ 2 := by
      apply (le_div_iff₀ (pow_pos hNpos 2)).2
      nlinarith [hFirst]
    _ = 3 * ((∑ w : Fin n → Bool, z w) ^ 2 / N ^ 2) := by ring

theorem euclideanSignSum_first_mean_sqrt_lower
    {ι : Type*} [Fintype ι]
    (n : ℕ) (v : Fin n → ι → ℝ) :
    Real.sqrt ((∑ e : Fin n, euclideanSq (v e)) / 3) ≤
      allSignsMean n
        (fun w => euclideanLength (euclideanSignSum n v w)) := by
  apply (Real.sqrt_le_iff).2
  constructor
  · unfold allSignsMean
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro w _
      exact euclideanLength_nonneg _
    · positivity
  · have h := euclideanSignSum_first_mean_sq_lower n v
    linarith

#print axioms euclideanSignSum_second_raw
#print axioms euclideanSignSum_fourth_raw
#print axioms euclideanSignSum_second_mean
#print axioms euclideanSignSum_fourth_mean
#print axioms euclideanSignSum_first_mean_sq_lower
#print axioms euclideanSignSum_first_mean_sqrt_lower

end GraphMatrixReplica.PaperR16
