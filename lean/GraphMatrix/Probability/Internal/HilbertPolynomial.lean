import GraphMatrix.Probability.Internal.FiniteMean

/-! # Finite Hilbert sign-pair inequalities through order 32

-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
open GraphMatrixReplica.Model
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

/-- The binomial coefficient comparison needed in the sign induction. -/
theorem sign_moment_coefficient_le (q r : ℕ) (hq : q ≤ 16) (hr : r ≤ q) :
    (Nat.choose (2 * q) (2 * r) : ℝ) * (32 : ℝ) ^ (q - r) ≤
      (32 : ℝ) ^ q * (Nat.choose q r : ℝ) := by
  interval_cases q <;> interval_cases r <;> norm_num [Nat.choose]

/-- Pointwise Hilbert sign-pair bound, retaining every binomial cross term. -/
theorem euclidean_pair_moment_le {T : Type} [Fintype T]
    (x y : T → ℝ) (q : ℕ) (hq : q ≤ 16) :
    euclideanSq (fun t => x t + y t) ^ q +
      euclideanSq (fun t => x t - y t) ^ q ≤
      2 * ∑ r ∈ Finset.range (q + 1),
        (Nat.choose (2 * q) (2 * r) : ℝ) *
          euclideanSq x ^ (q - r) * euclideanSq y ^ r := by
  have hX := euclideanSq_nonneg x
  have hY := euclideanSq_nonneg y
  have hCS := euclideanDot_sq_le x y
  rw [euclideanSq_add, euclideanSq_sub]
  let X := euclideanSq x
  let Y := euclideanSq y
  let Z := euclideanDot x y
  change (X + 2 * Z + Y) ^ q + (X - 2 * Z + Y) ^ q ≤
    2 * ∑ r ∈ Finset.range (q + 1),
      (Nat.choose (2 * q) (2 * r) : ℝ) * X ^ (q - r) * Y ^ r
  have hX' : 0 ≤ X := hX
  have hY' : 0 ≤ Y := hY
  have hCS' : Z ^ 2 ≤ X * Y := hCS
  interval_cases q
  · calc
      (X + 2 * Z + Y) ^ 0 + (X - 2 * Z + Y) ^ 0 =
          (2 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 0 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 0 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (0 + 1),
          (Nat.choose (2 * 0) (2 * r) : ℝ) * X ^ (0 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 1 + (X - 2 * Z + Y) ^ 1 =
          (2 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 0 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 0 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (1 + 1),
          (Nat.choose (2 * 1) (2 * r) : ℝ) * X ^ (1 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 2 + (X - 2 * Z + Y) ^ 2 =
          (2 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 0 +
          (8 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 1 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 0 +
          (8 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 1 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (2 + 1),
          (Nat.choose (2 * 2) (2 * r) : ℝ) * X ^ (2 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 3 + (X - 2 * Z + Y) ^ 3 =
          (2 : ℝ) * (X + Y) ^ 3 * (Z ^ 2) ^ 0 +
          (24 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 1 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 3 * (X * Y) ^ 0 +
          (24 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 1 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (3 + 1),
          (Nat.choose (2 * 3) (2 * r) : ℝ) * X ^ (3 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 4 + (X - 2 * Z + Y) ^ 4 =
          (2 : ℝ) * (X + Y) ^ 4 * (Z ^ 2) ^ 0 +
          (48 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 1 +
          (32 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 2 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 4 * (X * Y) ^ 0 +
          (48 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 1 +
          (32 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 2 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (4 + 1),
          (Nat.choose (2 * 4) (2 * r) : ℝ) * X ^ (4 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 5 + (X - 2 * Z + Y) ^ 5 =
          (2 : ℝ) * (X + Y) ^ 5 * (Z ^ 2) ^ 0 +
          (80 : ℝ) * (X + Y) ^ 3 * (Z ^ 2) ^ 1 +
          (160 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 2 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 5 * (X * Y) ^ 0 +
          (80 : ℝ) * (X + Y) ^ 3 * (X * Y) ^ 1 +
          (160 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 2 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (5 + 1),
          (Nat.choose (2 * 5) (2 * r) : ℝ) * X ^ (5 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 6 + (X - 2 * Z + Y) ^ 6 =
          (2 : ℝ) * (X + Y) ^ 6 * (Z ^ 2) ^ 0 +
          (120 : ℝ) * (X + Y) ^ 4 * (Z ^ 2) ^ 1 +
          (480 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 2 +
          (128 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 3 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 6 * (X * Y) ^ 0 +
          (120 : ℝ) * (X + Y) ^ 4 * (X * Y) ^ 1 +
          (480 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 2 +
          (128 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 3 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (6 + 1),
          (Nat.choose (2 * 6) (2 * r) : ℝ) * X ^ (6 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 7 + (X - 2 * Z + Y) ^ 7 =
          (2 : ℝ) * (X + Y) ^ 7 * (Z ^ 2) ^ 0 +
          (168 : ℝ) * (X + Y) ^ 5 * (Z ^ 2) ^ 1 +
          (1120 : ℝ) * (X + Y) ^ 3 * (Z ^ 2) ^ 2 +
          (896 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 3 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 7 * (X * Y) ^ 0 +
          (168 : ℝ) * (X + Y) ^ 5 * (X * Y) ^ 1 +
          (1120 : ℝ) * (X + Y) ^ 3 * (X * Y) ^ 2 +
          (896 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 3 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (7 + 1),
          (Nat.choose (2 * 7) (2 * r) : ℝ) * X ^ (7 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 8 + (X - 2 * Z + Y) ^ 8 =
          (2 : ℝ) * (X + Y) ^ 8 * (Z ^ 2) ^ 0 +
          (224 : ℝ) * (X + Y) ^ 6 * (Z ^ 2) ^ 1 +
          (2240 : ℝ) * (X + Y) ^ 4 * (Z ^ 2) ^ 2 +
          (3584 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 3 +
          (512 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 4 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 8 * (X * Y) ^ 0 +
          (224 : ℝ) * (X + Y) ^ 6 * (X * Y) ^ 1 +
          (2240 : ℝ) * (X + Y) ^ 4 * (X * Y) ^ 2 +
          (3584 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 3 +
          (512 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 4 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (8 + 1),
          (Nat.choose (2 * 8) (2 * r) : ℝ) * X ^ (8 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 9 + (X - 2 * Z + Y) ^ 9 =
          (2 : ℝ) * (X + Y) ^ 9 * (Z ^ 2) ^ 0 +
          (288 : ℝ) * (X + Y) ^ 7 * (Z ^ 2) ^ 1 +
          (4032 : ℝ) * (X + Y) ^ 5 * (Z ^ 2) ^ 2 +
          (10752 : ℝ) * (X + Y) ^ 3 * (Z ^ 2) ^ 3 +
          (4608 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 4 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 9 * (X * Y) ^ 0 +
          (288 : ℝ) * (X + Y) ^ 7 * (X * Y) ^ 1 +
          (4032 : ℝ) * (X + Y) ^ 5 * (X * Y) ^ 2 +
          (10752 : ℝ) * (X + Y) ^ 3 * (X * Y) ^ 3 +
          (4608 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 4 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (9 + 1),
          (Nat.choose (2 * 9) (2 * r) : ℝ) * X ^ (9 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 10 + (X - 2 * Z + Y) ^ 10 =
          (2 : ℝ) * (X + Y) ^ 10 * (Z ^ 2) ^ 0 +
          (360 : ℝ) * (X + Y) ^ 8 * (Z ^ 2) ^ 1 +
          (6720 : ℝ) * (X + Y) ^ 6 * (Z ^ 2) ^ 2 +
          (26880 : ℝ) * (X + Y) ^ 4 * (Z ^ 2) ^ 3 +
          (23040 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 4 +
          (2048 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 5 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 10 * (X * Y) ^ 0 +
          (360 : ℝ) * (X + Y) ^ 8 * (X * Y) ^ 1 +
          (6720 : ℝ) * (X + Y) ^ 6 * (X * Y) ^ 2 +
          (26880 : ℝ) * (X + Y) ^ 4 * (X * Y) ^ 3 +
          (23040 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 4 +
          (2048 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 5 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (10 + 1),
          (Nat.choose (2 * 10) (2 * r) : ℝ) * X ^ (10 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 11 + (X - 2 * Z + Y) ^ 11 =
          (2 : ℝ) * (X + Y) ^ 11 * (Z ^ 2) ^ 0 +
          (440 : ℝ) * (X + Y) ^ 9 * (Z ^ 2) ^ 1 +
          (10560 : ℝ) * (X + Y) ^ 7 * (Z ^ 2) ^ 2 +
          (59136 : ℝ) * (X + Y) ^ 5 * (Z ^ 2) ^ 3 +
          (84480 : ℝ) * (X + Y) ^ 3 * (Z ^ 2) ^ 4 +
          (22528 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 5 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 11 * (X * Y) ^ 0 +
          (440 : ℝ) * (X + Y) ^ 9 * (X * Y) ^ 1 +
          (10560 : ℝ) * (X + Y) ^ 7 * (X * Y) ^ 2 +
          (59136 : ℝ) * (X + Y) ^ 5 * (X * Y) ^ 3 +
          (84480 : ℝ) * (X + Y) ^ 3 * (X * Y) ^ 4 +
          (22528 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 5 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (11 + 1),
          (Nat.choose (2 * 11) (2 * r) : ℝ) * X ^ (11 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 12 + (X - 2 * Z + Y) ^ 12 =
          (2 : ℝ) * (X + Y) ^ 12 * (Z ^ 2) ^ 0 +
          (528 : ℝ) * (X + Y) ^ 10 * (Z ^ 2) ^ 1 +
          (15840 : ℝ) * (X + Y) ^ 8 * (Z ^ 2) ^ 2 +
          (118272 : ℝ) * (X + Y) ^ 6 * (Z ^ 2) ^ 3 +
          (253440 : ℝ) * (X + Y) ^ 4 * (Z ^ 2) ^ 4 +
          (135168 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 5 +
          (8192 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 6 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 12 * (X * Y) ^ 0 +
          (528 : ℝ) * (X + Y) ^ 10 * (X * Y) ^ 1 +
          (15840 : ℝ) * (X + Y) ^ 8 * (X * Y) ^ 2 +
          (118272 : ℝ) * (X + Y) ^ 6 * (X * Y) ^ 3 +
          (253440 : ℝ) * (X + Y) ^ 4 * (X * Y) ^ 4 +
          (135168 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 5 +
          (8192 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 6 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (12 + 1),
          (Nat.choose (2 * 12) (2 * r) : ℝ) * X ^ (12 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 13 + (X - 2 * Z + Y) ^ 13 =
          (2 : ℝ) * (X + Y) ^ 13 * (Z ^ 2) ^ 0 +
          (624 : ℝ) * (X + Y) ^ 11 * (Z ^ 2) ^ 1 +
          (22880 : ℝ) * (X + Y) ^ 9 * (Z ^ 2) ^ 2 +
          (219648 : ℝ) * (X + Y) ^ 7 * (Z ^ 2) ^ 3 +
          (658944 : ℝ) * (X + Y) ^ 5 * (Z ^ 2) ^ 4 +
          (585728 : ℝ) * (X + Y) ^ 3 * (Z ^ 2) ^ 5 +
          (106496 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 6 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 13 * (X * Y) ^ 0 +
          (624 : ℝ) * (X + Y) ^ 11 * (X * Y) ^ 1 +
          (22880 : ℝ) * (X + Y) ^ 9 * (X * Y) ^ 2 +
          (219648 : ℝ) * (X + Y) ^ 7 * (X * Y) ^ 3 +
          (658944 : ℝ) * (X + Y) ^ 5 * (X * Y) ^ 4 +
          (585728 : ℝ) * (X + Y) ^ 3 * (X * Y) ^ 5 +
          (106496 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 6 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (13 + 1),
          (Nat.choose (2 * 13) (2 * r) : ℝ) * X ^ (13 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 14 + (X - 2 * Z + Y) ^ 14 =
          (2 : ℝ) * (X + Y) ^ 14 * (Z ^ 2) ^ 0 +
          (728 : ℝ) * (X + Y) ^ 12 * (Z ^ 2) ^ 1 +
          (32032 : ℝ) * (X + Y) ^ 10 * (Z ^ 2) ^ 2 +
          (384384 : ℝ) * (X + Y) ^ 8 * (Z ^ 2) ^ 3 +
          (1537536 : ℝ) * (X + Y) ^ 6 * (Z ^ 2) ^ 4 +
          (2050048 : ℝ) * (X + Y) ^ 4 * (Z ^ 2) ^ 5 +
          (745472 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 6 +
          (32768 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 7 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 14 * (X * Y) ^ 0 +
          (728 : ℝ) * (X + Y) ^ 12 * (X * Y) ^ 1 +
          (32032 : ℝ) * (X + Y) ^ 10 * (X * Y) ^ 2 +
          (384384 : ℝ) * (X + Y) ^ 8 * (X * Y) ^ 3 +
          (1537536 : ℝ) * (X + Y) ^ 6 * (X * Y) ^ 4 +
          (2050048 : ℝ) * (X + Y) ^ 4 * (X * Y) ^ 5 +
          (745472 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 6 +
          (32768 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 7 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (14 + 1),
          (Nat.choose (2 * 14) (2 * r) : ℝ) * X ^ (14 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 15 + (X - 2 * Z + Y) ^ 15 =
          (2 : ℝ) * (X + Y) ^ 15 * (Z ^ 2) ^ 0 +
          (840 : ℝ) * (X + Y) ^ 13 * (Z ^ 2) ^ 1 +
          (43680 : ℝ) * (X + Y) ^ 11 * (Z ^ 2) ^ 2 +
          (640640 : ℝ) * (X + Y) ^ 9 * (Z ^ 2) ^ 3 +
          (3294720 : ℝ) * (X + Y) ^ 7 * (Z ^ 2) ^ 4 +
          (6150144 : ℝ) * (X + Y) ^ 5 * (Z ^ 2) ^ 5 +
          (3727360 : ℝ) * (X + Y) ^ 3 * (Z ^ 2) ^ 6 +
          (491520 : ℝ) * (X + Y) ^ 1 * (Z ^ 2) ^ 7 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 15 * (X * Y) ^ 0 +
          (840 : ℝ) * (X + Y) ^ 13 * (X * Y) ^ 1 +
          (43680 : ℝ) * (X + Y) ^ 11 * (X * Y) ^ 2 +
          (640640 : ℝ) * (X + Y) ^ 9 * (X * Y) ^ 3 +
          (3294720 : ℝ) * (X + Y) ^ 7 * (X * Y) ^ 4 +
          (6150144 : ℝ) * (X + Y) ^ 5 * (X * Y) ^ 5 +
          (3727360 : ℝ) * (X + Y) ^ 3 * (X * Y) ^ 6 +
          (491520 : ℝ) * (X + Y) ^ 1 * (X * Y) ^ 7 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (15 + 1),
          (Nat.choose (2 * 15) (2 * r) : ℝ) * X ^ (15 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring
  · calc
      (X + 2 * Z + Y) ^ 16 + (X - 2 * Z + Y) ^ 16 =
          (2 : ℝ) * (X + Y) ^ 16 * (Z ^ 2) ^ 0 +
          (960 : ℝ) * (X + Y) ^ 14 * (Z ^ 2) ^ 1 +
          (58240 : ℝ) * (X + Y) ^ 12 * (Z ^ 2) ^ 2 +
          (1025024 : ℝ) * (X + Y) ^ 10 * (Z ^ 2) ^ 3 +
          (6589440 : ℝ) * (X + Y) ^ 8 * (Z ^ 2) ^ 4 +
          (16400384 : ℝ) * (X + Y) ^ 6 * (Z ^ 2) ^ 5 +
          (14909440 : ℝ) * (X + Y) ^ 4 * (Z ^ 2) ^ 6 +
          (3932160 : ℝ) * (X + Y) ^ 2 * (Z ^ 2) ^ 7 +
          (131072 : ℝ) * (X + Y) ^ 0 * (Z ^ 2) ^ 8 := by ring
      _ ≤ (2 : ℝ) * (X + Y) ^ 16 * (X * Y) ^ 0 +
          (960 : ℝ) * (X + Y) ^ 14 * (X * Y) ^ 1 +
          (58240 : ℝ) * (X + Y) ^ 12 * (X * Y) ^ 2 +
          (1025024 : ℝ) * (X + Y) ^ 10 * (X * Y) ^ 3 +
          (6589440 : ℝ) * (X + Y) ^ 8 * (X * Y) ^ 4 +
          (16400384 : ℝ) * (X + Y) ^ 6 * (X * Y) ^ 5 +
          (14909440 : ℝ) * (X + Y) ^ 4 * (X * Y) ^ 6 +
          (3932160 : ℝ) * (X + Y) ^ 2 * (X * Y) ^ 7 +
          (131072 : ℝ) * (X + Y) ^ 0 * (X * Y) ^ 8 := by
        gcongr <;> first | exact hCS' | positivity
      _ = 2 * ∑ r ∈ Finset.range (16 + 1),
          (Nat.choose (2 * 16) (2 * r) : ℝ) * X ^ (16 - r) * Y ^ r := by
        norm_num [Finset.sum_range_succ, Nat.choose] <;> ring

end GraphMatrixReplica.P1AD
