import GraphMatrix.Counting.IidSphereNet
import GraphMatrix.Counting.IidSignMatrixHighMoment
import GraphMatrix.Counting.PathNoiseProductLaw
import GraphMatrix.HighMomentTailMarkov
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

local instance c079IidBilinearTail_propDecidable {P : Prop} : Decidable P :=
  Classical.propDecidable P

private theorem c079_paperMean_exp_sign (z : ℝ) :
    paperMean (fun b : Bool => Real.exp (z * paperSign b)) = Real.cosh z := by
  rw [Real.cosh_eq]
  simp [paperMean, paperSign]
  ring

/-- The exact iid-sign moment generating function is bounded by a Gaussian MGF. -/
theorem c079_paperMean_exp_weightedSigns_le
    {I : Type} [Fintype I] [DecidableEq I] (a : I → ℝ) (t : ℝ) :
    paperMean (fun w : I → Bool =>
      Real.exp (t * ∑ i : I, a i * paperSign (w i))) ≤
      Real.exp (t ^ 2 / 2 * ∑ i : I, (a i) ^ 2) := by
  have hpoint (w : I → Bool) :
      Real.exp (t * ∑ i : I, a i * paperSign (w i)) =
        ∏ i : I, Real.exp ((t * a i) * paperSign (w i)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpoint]
  rw [paperMean_coordinateProduct (fun i b => Real.exp ((t * a i) * paperSign b))]
  simp_rw [c079_paperMean_exp_sign]
  calc
    (∏ i : I, Real.cosh (t * a i)) ≤
        ∏ i : I, Real.exp ((t * a i) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact (Real.cosh_pos _).le
      · intro i _
        exact Real.cosh_le_exp_half_sq _
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Exponential Markov inequality for a finite uniform sample space. -/
theorem c079_finiteUniformProbability_ge_le_exp_mgf
    {Ω : Type} [Fintype Ω] (X : Ω → ℝ) (s t : ℝ) (ht : 0 ≤ t) :
    finiteUniformProbability (fun ω => s ≤ X ω) ≤
      Real.exp (-t * s) * paperMean (fun ω => Real.exp (t * X ω)) := by
  classical
  calc
    finiteUniformProbability (fun ω => s ≤ X ω) ≤
        paperMean (fun ω => Real.exp (-t * s) * Real.exp (t * X ω)) := by
      apply paperMean_mono
      intro ω
      by_cases h : s ≤ X ω
      · simp only [h, if_pos]
        rw [← Real.exp_add]
        have hnonneg : 0 ≤ -t * s + t * X ω := by
          nlinarith [mul_nonneg ht (sub_nonneg.mpr h)]
        simpa using (Real.exp_le_exp.mpr hnonneg : Real.exp 0 ≤ Real.exp (-t * s + t * X ω))
      · simp only [h]
        positivity
    _ = _ := by
      unfold paperMean
      rw [← Finset.mul_sum]
      ring

/-- One-sided Hoeffding bound for any finite iid sign family whose squared
coefficients sum to at most one. -/
theorem c079_finiteUniformProbability_weightedSigns_ge_le
    {I : Type} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (hvar : ∑ i : I, (a i) ^ 2 ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    finiteUniformProbability
      (fun w : I → Bool => s ≤ ∑ i : I, a i * paperSign (w i)) ≤
        Real.exp (-s ^ 2 / 2) := by
  let X : (I → Bool) → ℝ := fun w => ∑ i : I, a i * paperSign (w i)
  calc
    finiteUniformProbability (fun w => s ≤ X w) ≤
        Real.exp (-s * s) * paperMean (fun w => Real.exp (s * X w)) :=
      c079_finiteUniformProbability_ge_le_exp_mgf X s s hs
    _ ≤ Real.exp (-s * s) *
        Real.exp (s ^ 2 / 2 * ∑ i : I, (a i) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (c079_paperMean_exp_weightedSigns_le a s)
        (Real.exp_nonneg _)
    _ ≤ Real.exp (-s ^ 2 / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (div_nonneg (sq_nonneg s) (by norm_num : (0 : ℝ) ≤ 2))
        (sub_nonneg.mpr hvar)]

/-- Two-sided Hoeffding bound for the weighted iid sign sum. -/
theorem c079_finiteUniformProbability_abs_weightedSigns_ge_le
    {I : Type} [Fintype I] [DecidableEq I]
    (a : I → ℝ) (hvar : ∑ i : I, (a i) ^ 2 ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    finiteUniformProbability
      (fun w : I → Bool => s ≤ |∑ i : I, a i * paperSign (w i)|) ≤
        2 * Real.exp (-s ^ 2 / 2) := by
  let X : (I → Bool) → ℝ := fun w => ∑ i : I, a i * paperSign (w i)
  have hsplit : ∀ w, s ≤ |X w| → s ≤ X w ∨ s ≤ -X w := by
    intro w hw
    rcases le_total 0 (X w) with hp | hn
    · left
      simpa only [abs_of_nonneg hp] using hw
    · right
      simpa only [abs_of_nonpos hn] using hw
  have hneg : finiteUniformProbability (fun w => s ≤ -X w) ≤
      Real.exp (-s ^ 2 / 2) := by
    have hvarNeg : ∑ i : I, (-a i) ^ 2 ≤ 1 := by simpa using hvar
    simpa only [X, neg_mul, ← Finset.sum_neg_distrib] using
      (c079_finiteUniformProbability_weightedSigns_ge_le (fun i => -a i) hvarNeg s hs)
  calc
    finiteUniformProbability (fun w => s ≤ |X w|) ≤
        finiteUniformProbability (fun w => s ≤ X w ∨ s ≤ -X w) :=
      finiteUniformProbability_mono hsplit
    _ ≤ finiteUniformProbability (fun w => s ≤ X w) +
          finiteUniformProbability (fun w => s ≤ -X w) :=
      finiteUniformProbability_or_le _ _
    _ ≤ 2 * Real.exp (-s ^ 2 / 2) := by
      have hpos := c079_finiteUniformProbability_weightedSigns_ge_le a hvar s hs
      dsimp [X] at hpos ⊢
      linarith

/-- Product structure gives variance one for a bilinear form of two unit vectors. -/
theorem c079_bilinear_coeff_sq_sum (m : ℕ)
    (u v : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∑ e : Fin m × Fin m, (u e.1 * v e.2) ^ 2) = 1 := by
  calc
    (∑ e : Fin m × Fin m, (u e.1 * v e.2) ^ 2) =
        ∑ i : Fin m, (u i) ^ 2 * ∑ j : Fin m, (v j) ^ 2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i : Fin m, (u i) ^ 2) * (∑ j : Fin m, (v j) ^ 2) := by
      rw [Finset.sum_mul]
    _ = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq, hu, hv]
      norm_num

/-- Fixed unit-vector bilinear Hoeffding bound for the iid sign array. -/
def c079_bilinearSignSum (m : ℕ) (u v : EuclideanSpace ℝ (Fin m))
    (w : Fin m × Fin m → Bool) : ℝ :=
  ∑ e : Fin m × Fin m, (u e.1 * v e.2) * paperSign (w e)

/-- The weighted iid-sign sum is the matrix bilinear form. -/
theorem c079_inner_iidSignMatrix_eq_bilinearSignSum
    (m : ℕ) (w : Fin m × Fin m → Bool)
    (u v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ u (Matrix.toEuclideanLin (c079IidSignMatrix m w) v) =
      c079_bilinearSignSum m u v w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toEuclideanLin_apply, dotProduct, Matrix.mulVec,
    c079IidSignMatrix, c079_bilinearSignSum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

theorem c079_finiteUniformProbability_fixedBilinear_ge_le
    (m : ℕ) (u v : EuclideanSpace ℝ (Fin m))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (s : ℝ) (hs : 0 ≤ s) :
    finiteUniformProbability
      (fun w : Fin m × Fin m → Bool =>
        s ≤ |c079_bilinearSignSum m u v w|) ≤
      2 * Real.exp (-s ^ 2 / 2) := by
  have hvar : (∑ e : Fin m × Fin m, (u e.1 * v e.2) ^ 2) ≤ 1 :=
    le_of_eq (c079_bilinear_coeff_sq_sum m u v hu hv)
  simpa only [c079_bilinearSignSum] using
    (c079_finiteUniformProbability_abs_weightedSigns_ge_le
      (I := Fin m × Fin m) (fun e => u e.1 * v e.2) hvar s hs)

/-- Finite union bound in the exact uniform probability model. -/
theorem c079_finiteUniformProbability_exists_finset_le_sum
    {Ω I : Type} [Fintype Ω] (S : Finset I) (P : I → Ω → Prop) :
    finiteUniformProbability (fun ω => ∃ i ∈ S, P i ω) ≤
      ∑ i ∈ S, finiteUniformProbability (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finiteUniformProbability, paperMean]
  | @insert i S hi ih =>
    calc
      finiteUniformProbability (fun ω => ∃ j ∈ insert i S, P j ω) =
          finiteUniformProbability (fun ω => P i ω ∨ ∃ j ∈ S, P j ω) := by
        congr 1
        funext ω
        simp
      _ ≤ finiteUniformProbability (P i) +
            finiteUniformProbability (fun ω => ∃ j ∈ S, P j ω) :=
        finiteUniformProbability_or_le _ _
      _ ≤ finiteUniformProbability (P i) +
            ∑ j ∈ S, finiteUniformProbability (P j) := by linarith
      _ = ∑ j ∈ insert i S, finiteUniformProbability (P j) := by
        rw [Finset.sum_insert hi]

/-- Union of the fixed-vector Hoeffding bounds over a finite sphere set. -/
theorem c079_finiteUniformProbability_netBilinear_ge_le
    (m : ℕ) (S : Finset (EuclideanSpace ℝ (Fin m)))
    (hunit : ∀ u ∈ S, ‖u‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    finiteUniformProbability (fun w : Fin m × Fin m → Bool =>
      ∃ p ∈ S.product S, r ≤ |c079_bilinearSignSum m p.1 p.2 w|) ≤
        (S.card : ℝ) ^ 2 * (2 * Real.exp (-r ^ 2 / 2)) := by
  let P : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) →
      (Fin m × Fin m → Bool) → Prop :=
    fun p w => r ≤ |c079_bilinearSignSum m p.1 p.2 w|
  calc
    finiteUniformProbability (fun w => ∃ p ∈ S.product S, P p w) ≤
        ∑ p ∈ S.product S, finiteUniformProbability (P p) :=
      c079_finiteUniformProbability_exists_finset_le_sum (S.product S) P
    _ ≤ ∑ p ∈ S.product S, (2 * Real.exp (-r ^ 2 / 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
      exact c079_finiteUniformProbability_fixedBilinear_ge_le m p.1 p.2
        (hunit p.1 hu) (hunit p.2 hv) r hr
    _ = (S.card : ℝ) ^ 2 * (2 * Real.exp (-r ^ 2 / 2)) := by
      simp [Finset.card_product, pow_two]

/-- The volumetric `17^m` net costs at most `289^m` pairs in the union bound. -/
theorem c079_finiteUniformProbability_netBilinear_ge_le_289
    (m : ℕ) (S : Finset (EuclideanSpace ℝ (Fin m)))
    (hunit : ∀ u ∈ S, ‖u‖ = 1) (hcard : S.card ≤ 17 ^ m)
    (r : ℝ) (hr : 0 ≤ r) :
    finiteUniformProbability (fun w : Fin m × Fin m → Bool =>
      ∃ p ∈ S.product S, r ≤ |c079_bilinearSignSum m p.1 p.2 w|) ≤
        2 * (289 : ℝ) ^ m * Real.exp (-r ^ 2 / 2) := by
  have hcardR : (S.card : ℝ) ≤ (17 : ℝ) ^ m := by exact_mod_cast hcard
  have hpowEq : ((17 : ℝ) ^ m) ^ 2 = (289 : ℝ) ^ m := by
    calc
      _ = (17 : ℝ) ^ (m * 2) := by rw [pow_mul]
      _ = (17 : ℝ) ^ (2 * m) := by rw [mul_comm]
      _ = ((17 : ℝ) ^ 2) ^ m := by rw [pow_mul]
      _ = (289 : ℝ) ^ m := by norm_num
  calc
    finiteUniformProbability (fun w : Fin m × Fin m → Bool =>
        ∃ p ∈ S.product S, r ≤ |c079_bilinearSignSum m p.1 p.2 w|) ≤
        (S.card : ℝ) ^ 2 * (2 * Real.exp (-r ^ 2 / 2)) :=
      c079_finiteUniformProbability_netBilinear_ge_le m S hunit r hr
    _ ≤ ((17 : ℝ) ^ m) ^ 2 * (2 * Real.exp (-r ^ 2 / 2)) := by
      gcongr
    _ = 2 * (289 : ℝ) ^ m * Real.exp (-r ^ 2 / 2) := by
      rw [hpowEq]
      ring

/-- A single deterministic eighth-net works for every iid-sign sample and
obeys the union-bound tail estimate. -/
theorem c079_exists_unitSphere_net_with_bilinear_tail (m : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ u ∈ S, ‖u‖ = 1) ∧
      (∀ x, ‖x‖ = 1 → ∃ u ∈ S, ‖x - u‖ ≤ (1 / 8 : ℝ)) ∧
      S.card ≤ 17 ^ m ∧
      (∀ r : ℝ, 0 ≤ r →
        finiteUniformProbability (fun w : Fin m × Fin m → Bool =>
          ∃ p ∈ S.product S, r ≤ |c079_bilinearSignSum m p.1 p.2 w|) ≤
          2 * (289 : ℝ) ^ m * Real.exp (-r ^ 2 / 2)) := by
  obtain ⟨S, hfin, hcard, hunit, hnet⟩ := c079_exists_quantitative_unitSphere_net m
  let F := hfin.toFinset
  have hcardNat : F.card ≤ 17 ^ m := by
    have hcardE : (F.card : ℕ∞) ≤ (17 : ℕ∞) ^ m := by
      simpa only [F, hfin.encard_eq_coe_toFinset_card] using hcard
    exact_mod_cast hcardE
  refine ⟨F, ?_, ?_, hcardNat, ?_⟩
  · intro u hu
    exact hunit u (by simpa [F] using hu)
  · intro x hx
    obtain ⟨u, hu, hdist⟩ := hnet x hx
    exact ⟨u, by simpa [F] using hu, hdist⟩
  · intro r hr
    apply c079_finiteUniformProbability_netBilinear_ge_le_289 m F ?_ hcardNat r hr
    intro u hu
    exact hunit u (by simpa [F] using hu)

private theorem c079_exp_eight_gt_578 : (578 : ℝ) < Real.exp 8 := by
  have h1 : (5 / 2 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (5 : ℝ) < Real.exp 2 := by
    have heq : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      ring
    rw [heq]
    nlinarith [Real.exp_pos 1]
  have heq8 : Real.exp 8 = (Real.exp 2) ^ 4 := by
    rw [show (8 : ℝ) = 2 + 2 + 2 + 2 by norm_num,
      Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  have hp : (5 : ℝ) ^ 4 < (Real.exp 2) ^ 4 := by gcongr
  rw [heq8]
  nlinarith

/-- The `17^m` two-sided union factor is absorbed by the `4√m` shift. -/
theorem c079_union_prefactor_shift_le (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 ≤ t) :
    2 * (289 : ℝ) ^ m *
        Real.exp (-(4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2) ≤
      Real.exp (-t ^ 2 / 2) := by
  have h2pow : (2 : ℝ) ≤ 2 ^ m := by
    cases m with
    | zero => omega
    | succ k =>
      rw [pow_succ]
      have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
  have hcoef : 2 * (289 : ℝ) ^ m ≤ Real.exp (8 * (m : ℝ)) := by
    calc
      2 * (289 : ℝ) ^ m ≤ (2 : ℝ) ^ m * (289 : ℝ) ^ m := by
        exact mul_le_mul_of_nonneg_right h2pow (by positivity)
      _ = (578 : ℝ) ^ m := by rw [← mul_pow]; norm_num
      _ ≤ (Real.exp 8) ^ m := by gcongr; exact c079_exp_eight_gt_578.le
      _ = Real.exp (8 * (m : ℝ)) := by rw [← Real.exp_nat_mul, mul_comm]
  have hshift : 8 * (m : ℝ) -
      (4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2 ≤ -t ^ 2 / 2 := by
    have hsqrt : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m : ℝ)) ht]
  calc
    2 * (289 : ℝ) ^ m * Real.exp (-(4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2) ≤
        Real.exp (8 * (m : ℝ)) *
          Real.exp (-(4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = Real.exp (8 * (m : ℝ) - (4 * Real.sqrt (m : ℝ) + t) ^ 2 / 2) := by
      rw [← Real.exp_add]
      ring
    _ ≤ Real.exp (-t ^ 2 / 2) := Real.exp_le_exp.mpr hshift

/-- The deterministic net also has a shifted Gaussian tail for its maximal
bilinear sign sum. This is a statement about the net maximum, not yet the
matrix operator norm. -/
theorem c079_exists_unitSphere_net_with_shifted_bilinear_tail
    (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin m)),
      (∀ u ∈ S, ‖u‖ = 1) ∧
      (∀ x, ‖x‖ = 1 → ∃ u ∈ S, ‖x - u‖ ≤ (1 / 8 : ℝ)) ∧
      S.card ≤ 17 ^ m ∧
      (∀ t : ℝ, 0 ≤ t →
        finiteUniformProbability (fun w : Fin m × Fin m → Bool =>
          ∃ p ∈ S.product S,
            4 * Real.sqrt (m : ℝ) + t ≤
              |c079_bilinearSignSum m p.1 p.2 w|) ≤
          Real.exp (-t ^ 2 / 2)) := by
  obtain ⟨S, hunit, hnet, hcard, htail⟩ :=
    c079_exists_unitSphere_net_with_bilinear_tail m
  refine ⟨S, hunit, hnet, hcard, ?_⟩
  intro t ht
  exact (htail _ (by positivity)).trans (c079_union_prefactor_shift_le m hm t ht)

/-- Pointwise matrix operator norm control by all bilinear values on an
eighth-net. The norm on the matrix is the project's L2 operator norm. -/
theorem c079_iidSignMatrix_norm_le_fourThirds_netBound
    (m : ℕ) (S : Finset (EuclideanSpace ℝ (Fin m)))
    (hunit : ∀ u ∈ S, ‖u‖ = 1)
    (hnet : ∀ x, ‖x‖ = 1 → ∃ u ∈ S, ‖x - u‖ ≤ (1 / 8 : ℝ))
    (w : Fin m × Fin m → Bool) (B : ℝ) (hBnonneg : 0 ≤ B)
    (hB : ∀ u ∈ S, ∀ v ∈ S,
      |c079_bilinearSignSum m u v w| ≤ B) :
    ‖c079IidSignMatrix m w‖ ≤ (4 / 3 : ℝ) * B := by
  let T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin m)).trans
      LinearMap.toContinuousLinearMap) (c079IidSignMatrix m w)
  have hnetSet : ∀ x : EuclideanSpace ℝ (Fin m), ‖x‖ = 1 →
      ∃ u ∈ (S : Set (EuclideanSpace ℝ (Fin m))), ‖x - u‖ ≤ (1 / 8 : ℝ) := by
    intro x hx
    obtain ⟨u, hu, hdist⟩ := hnet x hx
    exact ⟨u, by simpa using hu, hdist⟩
  have hunitSet : ∀ u : EuclideanSpace ℝ (Fin m),
      u ∈ (S : Set (EuclideanSpace ℝ (Fin m))) → ‖u‖ = 1 := by
    intro u hu
    exact hunit u (by simpa using hu)
  have hBSet : ∀ u ∈ (S : Set _), ∀ v ∈ (S : Set _),
      |inner ℝ u (T v)| ≤ B := by
    intro u hu v hv
    have h := hB u (by simpa using hu) v (by simpa using hv)
    change |inner ℝ u (Matrix.toEuclideanLin (c079IidSignMatrix m w) v)| ≤ B
    rw [c079_inner_iidSignMatrix_eq_bilinearSignSum]
    exact h
  have hT : ‖T‖ ≤ (4 / 3 : ℝ) * B := by
    exact c079_clm_norm_le_fourThirds_netBound m T (S : Set _)
      hnetSet hunitSet B hBnonneg hBSet
  simpa only [T, Matrix.l2_opNorm_def] using hT

/-- Strict operator-norm tail after the necessary `4/3` net amplification.
The threshold is `(4/3)(4√m+t)`, not `4√m+t`. -/
theorem c079_iidSignMatrix_opNorm_tail
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    finiteUniformProbability (fun w : Fin m × Fin m → Bool =>
      (4 / 3 : ℝ) * (4 * Real.sqrt (m : ℝ) + t) <
        ‖c079IidSignMatrix m w‖) ≤
      Real.exp (-t ^ 2 / 2) := by
  obtain ⟨S, hunit, hnet, _, htail⟩ :=
    c079_exists_unitSphere_net_with_shifted_bilinear_tail m hm
  let B : ℝ := 4 * Real.sqrt (m : ℝ) + t
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hsub : ∀ w : Fin m × Fin m → Bool,
      (4 / 3 : ℝ) * B < ‖c079IidSignMatrix m w‖ →
        ∃ p ∈ S.product S, B ≤ |c079_bilinearSignSum m p.1 p.2 w| := by
    intro w hw
    by_contra hn
    have hall : ∀ u ∈ S, ∀ v ∈ S, |c079_bilinearSignSum m u v w| ≤ B := by
      intro u hu v hv
      have hnot : ¬ B ≤ |c079_bilinearSignSum m u v w| := by
        intro hbad
        exact hn ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, hbad⟩
      exact le_of_lt (lt_of_not_ge hnot)
    have hnorm := c079_iidSignMatrix_norm_le_fourThirds_netBound
      m S hunit hnet w B hBnonneg hall
    exact (not_lt_of_ge hnorm) hw
  exact (finiteUniformProbability_mono hsub).trans (htail t ht)


end GraphMatrixReplica
