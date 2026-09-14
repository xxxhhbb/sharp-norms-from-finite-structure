import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import R6.PaperR16EventuallyTypedCoreLp

noncomputable section

namespace GraphMatrixReplica

/-- The finite trace scale, with actual trace order `k`, core exponent `b`,
and separator correction `s`. No counting theorem is assumed here. -/
def rootTraceScale (C n : ℝ) (k a b s : ℕ) : ℝ :=
  (2 * C ^ (2 * k) * (k : ℝ) ^ (a * k) * n ^ (k * b + s)) ^
    ((2 * (k : ℝ))⁻¹)

theorem rootTraceScale_eq_factors (C n : ℝ) (k a b s : ℕ)
    (hC : 0 < C) (hn : 0 < n) (hk : 0 < k) :
    rootTraceScale C n k a b s =
      (2 : ℝ) ^ ((2 * (k : ℝ))⁻¹) * C *
        (k : ℝ) ^ ((a : ℝ) / 2) * n ^ ((b : ℝ) / 2) *
          n ^ ((s : ℝ) / (2 * (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkNe : (k : ℝ) ≠ 0 := ne_of_gt hkR
  unfold rootTraceScale
  rw [Real.rpow_def_of_pos (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hkR, Real.rpow_def_of_pos hn,
    Real.rpow_def_of_pos hn]
  conv_rhs => rw [← Real.exp_log hC]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The separator correction stays bounded when the trace order covers log n. -/
theorem root_separator_rpow_le_exp (n k s : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hs : 0 ≤ s)
    (hlog : Real.log n ≤ k) :
    n ^ (s / (2 * k)) ≤ Real.exp (s / 2) := by
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  have hmul : Real.log n * s ≤ k * s := mul_le_mul_of_nonneg_right hlog hs
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have hdiv : Real.log n * s / k ≤ s :=
    (div_le_iff₀ hk).2 (by simpa only [mul_comm] using hmul)
  calc
    Real.log n * (s / (2 * k)) * 2 = Real.log n * s / k := by field_simp
    _ ≤ s := hdiv

/-- Explicit sharp scale after choosing a logarithmic trace order. -/
theorem rootTraceScale_le_log_scale (C n D : ℝ) (k a b s : ℕ)
    (hC : 0 < C) (hn : 2 ≤ n) (hk : 1 ≤ k) (hD : 0 ≤ D)
    (hcover : Real.log n ≤ (k : ℝ))
    (hwindow : (k : ℝ) ≤ D * Real.log (2 * n)) :
    rootTraceScale C n k a b s ≤
      2 * C * (D * Real.log (2 * n)) ^ ((a : ℝ) / 2) *
        n ^ ((b : ℝ) / 2) * Real.exp ((s : ℝ) / 2) := by
  have hnPos : 0 < n := by linarith
  have hlog0 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hkPos : 0 < k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htwo : (2 : ℝ) ^ ((2 * (k : ℝ))⁻¹) ≤ 2 := by
    calc
      (2 : ℝ) ^ ((2 * (k : ℝ))⁻¹) ≤ (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact (inv_le_one₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ))).2 (by linarith)
      _ = 2 := Real.rpow_one _
  have horder : (k : ℝ) ^ ((a : ℝ) / 2) ≤
      (D * Real.log (2 * n)) ^ ((a : ℝ) / 2) := by
    exact Real.rpow_le_rpow (by positivity) hwindow (by positivity)
  have hsep := root_separator_rpow_le_exp n k s hnPos (by positivity) (by positivity) hcover
  rw [rootTraceScale_eq_factors C n k a b s hC hnPos hkPos]
  gcongr

theorem root_paper_finiteScale_eq_traceScale
    (G : PartiteShape) (p s a n : ℕ) :
    paperR16TypedCoreFiniteLpScale G p s a n =
      rootTraceScale (c079C G.roles) n (p + 1) a (G.roles - s) s := by
  unfold paperR16TypedCoreFiniteLpScale rootTraceScale c079BlockTarget
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- Apply the arithmetic to the project's actual selected replica parameter.
This proves a bound on the explicit scale, not the missing defect count. -/
theorem root_paper_finiteScale_le_log_scale
    (G : PartiteShape) (s a n : ℕ) (q C₀ : ℝ)
    (hn : 2 ≤ n) (hC₀ : 0 ≤ C₀) (hq : 0 ≤ q)
    (hqWindow : q ≤ C₀ * Real.log (2 * (n : ℝ))) :
    paperR16TypedCoreFiniteLpScale G (paperR16ReplicaParameter n q) s a n ≤
      2 * (c079C G.roles : ℝ) *
        ((2 + C₀) * Real.log (2 * (n : ℝ))) ^ ((a : ℝ) / 2) *
        (n : ℝ) ^ ((G.roles - s : ℕ) / (2 : ℝ)) *
          Real.exp ((s : ℝ) / 2) := by
  have hC : (0 : ℝ) < c079C G.roles := by
    by_cases hr : G.roles = 0
    · simp [c079C, hr]
    · have hrPos : 0 < G.roles := Nat.pos_of_ne_zero hr
      unfold c079C
      positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [root_paper_finiteScale_eq_traceScale,
    paperR16ReplicaParameter_add_one]
  apply rootTraceScale_le_log_scale _ _ _ _ _ _ _ hC hnR
    (by have h := paperR16RealTraceOrder_ge_two n q; omega) (by linarith)
  · exact hlog.trans (paperR16RealTraceOrder_covers_log n q)
  · exact paperR16RealTraceOrder_le_log_window n q C₀ hn hC₀ hq hqWindow

/-- The actual finite scale in the original `log n` convention, with an
explicit constant independent of `n` and `q` within the fixed window. -/
theorem root_paper_finiteScale_le_original_log_scale
    (G : PartiteShape) (s a n : ℕ) (q C₀ : ℝ)
    (hs : s ≤ G.roles) (hn : 2 ≤ n) (hC₀ : 0 ≤ C₀) (hq : 0 ≤ q)
    (hqWindow : q ≤ C₀ * Real.log (2 * (n : ℝ))) :
    paperR16TypedCoreFiniteLpScale G (paperR16ReplicaParameter n q) s a n ≤
      (2 * (c079C G.roles : ℝ) * Real.exp ((s : ℝ) / 2) *
        (2 * (2 + C₀)) ^ ((a : ℝ) / 2)) *
      (n : ℝ) ^ (((G.roles : ℝ) - (s : ℝ)) / 2) *
        Real.log (n : ℝ) ^ ((a : ℝ) / 2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlog20 : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hnPos)]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
    linarith
  have hbase : (2 + C₀) * Real.log (2 * (n : ℝ)) ≤
      (2 * (2 + C₀)) * Real.log (n : ℝ) := by
    calc
      (2 + C₀) * Real.log (2 * (n : ℝ)) ≤
          (2 + C₀) * (2 * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2 (by linarith)
      _ = _ := by ring
  calc
    paperR16TypedCoreFiniteLpScale G (paperR16ReplicaParameter n q) s a n ≤
        2 * (c079C G.roles : ℝ) *
          ((2 + C₀) * Real.log (2 * (n : ℝ))) ^ ((a : ℝ) / 2) *
          (n : ℝ) ^ ((G.roles - s : ℕ) / (2 : ℝ)) *
          Real.exp ((s : ℝ) / 2) :=
      root_paper_finiteScale_le_log_scale G s a n q C₀ hn hC₀ hq hqWindow
    _ ≤ 2 * (c079C G.roles : ℝ) *
          ((2 * (2 + C₀)) * Real.log (n : ℝ)) ^ ((a : ℝ) / 2) *
          (n : ℝ) ^ ((G.roles - s : ℕ) / (2 : ℝ)) *
          Real.exp ((s : ℝ) / 2) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (by linarith : 0 ≤ 2 * (2 + C₀)) hlog0,
        Nat.cast_sub hs]
      ring

#print axioms rootTraceScale_eq_factors
#print axioms root_separator_rpow_le_exp
#print axioms rootTraceScale_le_log_scale
#print axioms root_paper_finiteScale_eq_traceScale
#print axioms root_paper_finiteScale_le_log_scale
#print axioms root_paper_finiteScale_le_original_log_scale

end GraphMatrixReplica
