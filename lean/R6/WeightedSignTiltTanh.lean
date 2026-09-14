import Mathlib

noncomputable section
namespace WeightedSignTilt

theorem tanh_exp_two (x : ℝ) :
    Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq, Real.exp_neg, show 2 * x = x + x by ring, Real.exp_add]
  have hp := Real.exp_pos x
  field_simp

theorem half_le_tanh_on_unit {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.tanh x := by
  rw [tanh_exp_two]
  apply (le_div_iff₀ (by positivity : 0 < Real.exp (2 * x) + 1)).mpr
  have he := Real.add_one_le_exp (2 * x)
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 - x by linarith)
  have hprod := mul_nonneg hx (show 0 ≤ 1 - x by linarith)
  nlinarith

theorem tanh_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hd (y : ℝ) :
      HasDerivAt (fun u : ℝ => u * Real.cosh u - Real.sinh u)
        (y * Real.sinh y) y := by
    simpa only [id_eq, one_mul, add_sub_cancel_left] using!
      ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub (Real.hasDerivAt_sinh y)
  have hm : Monotone (fun u : ℝ => u * Real.cosh u - Real.sinh u) := by
    apply monotone_of_hasDerivAt_nonneg hd
    intro y
    rcases le_total 0 y with hy | hy
    · exact mul_nonneg hy (Real.sinh_nonneg_iff.mpr hy)
    · apply mul_nonneg_of_nonpos_of_nonpos hy
      simpa using (Real.sinh_le_sinh.mpr hy)
  have h := hm hx
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h
  rw [Real.tanh_eq_sinh_div_cosh]
  exact (div_le_iff₀ (Real.cosh_pos x)).mpr (by linarith)

theorem tilted_coordinate_mean_bounds (a lam : ℝ) (hlam : 0 ≤ lam)
    (hsmall : |lam * a| ≤ 1) :
    lam * a ^ 2 / 2 ≤ a * Real.tanh (lam * a) ∧
      a * Real.tanh (lam * a) ≤ lam * a ^ 2 := by
  have hpos (b : ℝ) (hb : 0 ≤ b) (hs : lam * b ≤ 1) :
      lam * b ^ 2 / 2 ≤ b * Real.tanh (lam * b) ∧
        b * Real.tanh (lam * b) ≤ lam * b ^ 2 := by
    have hlo := mul_le_mul_of_nonneg_left
      (half_le_tanh_on_unit (mul_nonneg hlam hb) hs) hb
    have hhi := mul_le_mul_of_nonneg_left
      (tanh_le_self_nonneg (mul_nonneg hlam hb)) hb
    constructor <;> nlinarith
  rcases le_total 0 a with ha | ha
  · exact hpos a ha ((le_abs_self _).trans hsmall)
  · have hs : lam * (-a) ≤ 1 := by
      have h := (neg_le_abs (lam * a)).trans hsmall
      nlinarith
    have h := hpos (-a) (neg_nonneg.mpr ha) hs
    simpa [mul_neg, Real.tanh_neg] using h

#print axioms half_le_tanh_on_unit
#print axioms tanh_le_self_nonneg
#print axioms tilted_coordinate_mean_bounds
end WeightedSignTilt
