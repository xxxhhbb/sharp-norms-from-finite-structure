import GraphMatrix.Probability.Internal.HilbertPolynomial

/-! # All independent-sign finite Euclidean moments needed by P1

The induction is on the number of actual sign coordinates and simultaneously
on every moment index from zero through sixteen. No number-of-coordinates
factor occurs in the moment constant.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
open GraphMatrixReplica.Model
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

/-- Raw complete-cube Hilbert moment inequality, including q = 0. -/
theorem hilbert_sign_moment_raw {T : Type} [Fintype T]
    (n : ℕ) (v : Fin n → T → ℝ) (q : ℕ) (hq : q ≤ 16) :
    (∑ w : Fin n → Bool, euclideanSq (euclideanSignSum n v w) ^ q) ≤
      (32 : ℝ) ^ q * (2 : ℝ) ^ n *
        (∑ i : Fin n, euclideanSq (v i)) ^ q := by
  induction n generalizing q with
  | zero =>
      cases q <;> simp [euclideanSignSum, euclideanSq]
  | succ n ih =>
      let tail : Fin n → T → ℝ := fun i => v i.succ
      let V : ℝ := ∑ i : Fin n, euclideanSq (tail i)
      let Y : ℝ := euclideanSq (v 0)
      let N : ℝ := (2 : ℝ) ^ n
      let X : (Fin n → Bool) → ℝ := fun w =>
        euclideanSq (euclideanSignSum n tail w)
      have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => euclideanSq_nonneg _
      have hY : 0 ≤ Y := euclideanSq_nonneg _
      have hN : 0 ≤ N := by positivity
      rw [sum_all_signs_succ]
      calc
        (∑ w : Fin n → Bool,
          (euclideanSq (euclideanSignSum (n + 1) v (Fin.cons false w)) ^ q +
            euclideanSq (euclideanSignSum (n + 1) v (Fin.cons true w)) ^ q)) ≤
          ∑ w : Fin n → Bool,
            2 * ∑ r ∈ Finset.range (q + 1),
              (Nat.choose (2 * q) (2 * r) : ℝ) * X w ^ (q - r) * Y ^ r := by
          apply Finset.sum_le_sum
          intro w _
          rw [euclideanSignSum_cons_false, euclideanSignSum_cons_true]
          exact euclidean_pair_moment_le
            (euclideanSignSum n tail w) (v 0) q hq
        _ = 2 * ∑ r ∈ Finset.range (q + 1),
              (Nat.choose (2 * q) (2 * r) : ℝ) * Y ^ r *
                (∑ w : Fin n → Bool, X w ^ (q - r)) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
        _ ≤ 2 * ∑ r ∈ Finset.range (q + 1),
              (Nat.choose (2 * q) (2 * r) : ℝ) * Y ^ r *
                ((32 : ℝ) ^ (q - r) * N * V ^ (q - r)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro r hr
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact ih tail (q - r) (by omega)
        _ ≤ 2 * ∑ r ∈ Finset.range (q + 1),
              ((32 : ℝ) ^ q * (Nat.choose q r : ℝ)) *
                Y ^ r * (N * V ^ (q - r)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro r hr
          have hrq : r ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
          have hc := sign_moment_coefficient_le q r hq hrq
          have hh := mul_le_mul_of_nonneg_right hc
            (show 0 ≤ Y ^ r * (N * V ^ (q - r)) by positivity)
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
        _ = (32 : ℝ) ^ q * (N * 2) *
              (∑ r ∈ Finset.range (q + 1),
                Y ^ r * V ^ (q - r) * (Nat.choose q r : ℝ)) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ = (32 : ℝ) ^ q * (2 : ℝ) ^ (n + 1) *
              (∑ i : Fin (n + 1), euclideanSq (v i)) ^ q := by
          rw [← add_pow, Fin.sum_univ_succ, pow_succ]

/-- Same bound, with the project's exact normalized finite mean. -/
theorem hilbert_sign_moment_fin {T : Type} [Fintype T]
    (n : ℕ) (v : Fin n → T → ℝ) (q : ℕ) (hq : q ≤ 16) :
    paperMean (fun w : Fin n → Bool =>
      euclideanSq (euclideanSignSum n v w) ^ q) ≤
      (32 : ℝ) ^ q * (∑ i : Fin n, euclideanSq (v i)) ^ q := by
  have h := hilbert_sign_moment_raw n v q hq
  have hn : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hc : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
    simp [Fintype.card_fun]
  unfold paperMean
  rw [hc]
  calc
    _ ≤ ((2 : ℝ) ^ n)⁻¹ *
        ((32 : ℝ) ^ q * (2 : ℝ) ^ n *
          (∑ i : Fin n, euclideanSq (v i)) ^ q) := by
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = (32 : ℝ) ^ q * (∑ i : Fin n, euclideanSq (v i)) ^ q := by
      field_simp [hn] <;> ring

/-- Reindex an entire finite function space, not just a selected sample. -/
def functionReindex {A B : Type} (e : A ≃ B) (C : Type) :
    (A → C) ≃ (B → C) where
  toFun f b := f (e.symm b)
  invFun f a := f (e a)
  left_inv f := by funext a; simp
  right_inv f := by funext b; simp

/-- The finite Euclidean independent-sign moment theorem for arbitrary
finite coordinate types and all required moment orders. -/
theorem hilbert_sign_moment {I T : Type} [Fintype I] [Fintype T]
    (v : I → T → ℝ) (q : ℕ) (hq : q ≤ 16) :
    paperMean (fun w : I → Bool =>
      euclideanSq (fun t => ∑ i, sign (w i) * v i t) ^ q) ≤
      (32 : ℝ) ^ q * (∑ i, euclideanSq (v i)) ^ q := by
  classical
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let v' : Fin n → T → ℝ := fun i => v (e i)
  let φ := functionReindex e Bool
  have hv (w : Fin n → Bool) :
      (fun t => ∑ i : I, sign (φ w i) * v i t) =
        euclideanSignSum n v' w := by
    funext t
    symm
    unfold euclideanSignSum
    apply Fintype.sum_equiv e
    intro i
    simp [φ, functionReindex, v', sign_eq_if]
  have hE : (∑ i : Fin n, euclideanSq (v' i)) =
      ∑ i : I, euclideanSq (v i) := by
    exact Equiv.sum_comp e (fun i => euclideanSq (v i))
  calc
    _ = paperMean (fun w : Fin n → Bool =>
        euclideanSq (fun t => ∑ i : I, sign (φ w i) * v i t) ^ q) :=
      (paperMean_equiv φ _).symm
    _ = paperMean (fun w : Fin n → Bool =>
        euclideanSq (euclideanSignSum n v' w) ^ q) := by
      simp only [hv]
    _ ≤ (32 : ℝ) ^ q * (∑ i : Fin n, euclideanSq (v' i)) ^ q :=
      hilbert_sign_moment_fin n v' q hq
    _ = (32 : ℝ) ^ q * (∑ i : I, euclideanSq (v i)) ^ q := by rw [hE]

end GraphMatrixReplica.P1AD
