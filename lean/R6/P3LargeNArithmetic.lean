import R6.P3UniformTail
import R6.P1ADAcceptance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section
open Filter Asymptotics
namespace GraphMatrixReplica

theorem p3_eventually_scalar_bounds
    (A a eps : ℝ) (ha : 0 < a) (heps : 0 < eps) :
    ∀ᶠ x : ℝ in atTop,
      A ≤ eps ^ 2 * Real.log x ∧
        8 * eps * Real.sqrt (Real.log x) ≤ a * x ^ (1 / 4 : ℝ) := by
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hthreshold : ∀ᶠ x : ℝ in atTop, A ≤ eps ^ 2 * Real.log x :=
    (Real.tendsto_log_atTop.const_mul_atTop heps2).eventually_ge_atTop A
  have hsmall0 := isLittleO_iff.1
    (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ) (by norm_num : 0 < (1 / 4 : ℝ)))
    (show 0 < a / (8 * eps) by positivity)
  filter_upwards [hthreshold, hsmall0, eventually_ge_atTop (1 : ℝ)] with x hxA hxsmall hx1
  refine ⟨hxA, ?_⟩
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] at hxsmall
  rw [Real.sqrt_eq_rpow]
  have h8eps : 0 < 8 * eps := mul_pos (by norm_num) heps
  have hm := mul_le_mul_of_nonneg_left hxsmall h8eps.le
  field_simp [h8eps.ne'] at hm
  nlinarith

theorem p3_exists_nat_cutoff_scalar_bounds
    (A a eps : ℝ) (ha : 0 < a) (heps : 0 < eps) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      A ≤ eps ^ 2 * Real.log (n : ℝ) ∧
        8 * eps * Real.sqrt (Real.log (n : ℝ)) ≤
          a * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hreal := p3_eventually_scalar_bounds A a eps ha heps
  have hnat : ∀ᶠ n : ℕ in atTop,
      A ≤ eps ^ 2 * Real.log (n : ℝ) ∧
        8 * eps * Real.sqrt (Real.log (n : ℝ)) ≤
          a * (n : ℝ) ^ (1 / 4 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  exact eventually_atTop.1 hnat

theorem p3_threshold_square_identity
    (eps : ℝ) (n k : ℕ) (hn : 1 ≤ n) :
    (eps * (n : ℝ) ^ ((k : ℝ) / 2) * Real.sqrt (Real.log (n : ℝ))) ^ 2 =
      eps ^ 2 * (n : ℝ) ^ k * Real.log (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn)
  have hsqrt : (Real.sqrt (Real.log (n : ℝ))) ^ 2 = Real.log (n : ℝ) :=
    Real.sq_sqrt hlog0
  have hrpow : ((n : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (n : ℝ) ^ k := by
    rw [P1AD.rpow_nat_power hnR, ← Real.rpow_natCast]
    congr 1
    ring
  calc
    _ = eps ^ 2 * ((n : ℝ) ^ ((k : ℝ) / 2)) ^ 2 *
        (Real.sqrt (Real.log (n : ℝ))) ^ 2 := by ring
    _ = _ := by rw [hrpow, hsqrt]

theorem p3_small_scale_identity
    (a eps : ℝ) (n k : ℕ) (hn : 1 ≤ n)
    (hscalar : 8 * eps * Real.sqrt (Real.log (n : ℝ)) ≤
      a * (n : ℝ) ^ (1 / 4 : ℝ)) :
    8 * (eps * (n : ℝ) ^ ((k : ℝ) / 2) * Real.sqrt (Real.log (n : ℝ))) *
        (n : ℝ) ^ ((k : ℝ) / 2 - 1 / 4) ≤
      a * (n : ℝ) ^ k := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hleft :
      (n : ℝ) ^ ((k : ℝ) / 2) * (n : ℝ) ^ ((k : ℝ) / 2 - 1 / 4) =
        (n : ℝ) ^ ((k : ℝ) - 1 / 4) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hright :
      (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ ((k : ℝ) - 1 / 4) =
        (n : ℝ) ^ k := by
    rw [← Real.rpow_add hnR, ← Real.rpow_natCast]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hscalar
    (Real.rpow_nonneg hnR.le ((k : ℝ) - 1 / 4))
  calc
    _ = (8 * eps * Real.sqrt (Real.log (n : ℝ))) *
        ((n : ℝ) ^ ((k : ℝ) / 2) * (n : ℝ) ^ ((k : ℝ) / 2 - 1 / 4)) := by ring
    _ = (8 * eps * Real.sqrt (Real.log (n : ℝ))) *
        (n : ℝ) ^ ((k : ℝ) - 1 / 4) := by rw [hleft]
    _ ≤ (a * (n : ℝ) ^ (1 / 4 : ℝ)) *
        (n : ℝ) ^ ((k : ℝ) - 1 / 4) := hm
    _ = _ := by rw [mul_assoc, hright]

/-- One graph-dependent cutoff discharges both scalar hypotheses left open by
`p3_component_tail_after_second_good`.  The coefficient envelope is exactly
the P1 output `n^(k/2-1/4)`. -/
theorem p3_exists_large_n_tilt_inputs
    (A a eps : ℝ) (ha : 0 < a) (heps : 0 < eps) :
    ∃ n0 : ℕ, ∀ (n k : ℕ), n0 ≤ n →
      let t := eps * (n : ℝ) ^ ((k : ℝ) / 2) * Real.sqrt (Real.log (n : ℝ))
      1 ≤ n ∧
        A * (n : ℝ) ^ k ≤ t ^ 2 ∧
        8 * t * (n : ℝ) ^ ((k : ℝ) / 2 - 1 / 4) ≤ a * (n : ℝ) ^ k ∧
        t ^ 2 = eps ^ 2 * (n : ℝ) ^ k * Real.log (n : ℝ) := by
  obtain ⟨N, hN⟩ := p3_exists_nat_cutoff_scalar_bounds A a eps ha heps
  refine ⟨max N 1, ?_⟩
  intro n k hn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hscalar := hN n hnN
  have hsq := p3_threshold_square_identity eps n k hn1
  dsimp
  refine ⟨hn1, ?_, p3_small_scale_identity a eps n k hn1 hscalar.2, hsq⟩
  exact p3_threshold_square_from_log
    (eps * (n : ℝ) ^ ((k : ℝ) / 2) * Real.sqrt (Real.log (n : ℝ)))
    A ((n : ℝ) ^ k) eps (Real.log (n : ℝ))
    (by positivity) hscalar.1 hsq

#print axioms p3_exists_large_n_tilt_inputs

end GraphMatrixReplica

