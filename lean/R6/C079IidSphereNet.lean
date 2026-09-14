import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.MetricSpace.CoveringNumbers

noncomputable section
open Metric Set Module MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal Function

namespace GraphMatrixReplica

private theorem c079_abs_inner_le_norm_mul {m : ℕ}
    (x y : EuclideanSpace ℝ (Fin m)) :
    |inner ℝ x y| ≤ ‖x‖ * ‖y‖ := by
  simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) x y)

/-- Compactness supplies a finite eighth-net on the Euclidean unit sphere.
This does not give the quantitative `17^m` cardinal bound. -/
theorem c079_exists_finite_unitSphere_net (m : ℕ) :
    ∃ S : Set (EuclideanSpace ℝ (Fin m)), S.Finite ∧
      (∀ s ∈ S, ‖s‖ = 1) ∧
      (∀ x, ‖x‖ = 1 → ∃ s ∈ S, ‖x - s‖ ≤ (1 / 8 : ℝ)) := by
  obtain ⟨S, hsub, hfin, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (ε := (1 / 8 : NNReal)) (s := Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)
      (by norm_num) (isCompact_sphere _ _)
  refine ⟨S, hfin, ?_, ?_⟩
  · intro s hs
    have h := hsub hs
    simpa only [Metric.mem_sphere, dist_zero_right] using h
  · intro x hx
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    obtain ⟨s, hs, hdist⟩ := hcover hx'
    refine ⟨s, hs, ?_⟩
    simpa only [dist_eq_norm] using (by exact_mod_cast hdist : dist x s ≤ (1 / 8 : ℝ))

private theorem c079_card_le_of_eighth_separated {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1 / 8 : ℝ) ≤ ‖c - d‖) :
    s.card ≤ 17 ^ Module.finrank ℝ E := by
  borelize E
  let μ : MeasureTheory.Measure E := MeasureTheory.Measure.addHaar
  let δ : ℝ := (1 : ℝ) / 16
  let ρ : ℝ := (17 : ℝ) / 16
  have ρpos : 0 < ρ := by norm_num
  set A := ⋃ c ∈ s, Metric.ball (c : E) δ with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => Metric.ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have hδ : δ + δ = (1 / 8 : ℝ) := by norm_num [δ]
    simpa only [hδ] using (hsep c hc d hd hcd)
  have A_subset : A ⊆ Metric.ball (0 : E) ρ := by
    refine Set.iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (hs x hx)
      _ = ρ := by norm_num
  have I :
    (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) ≤
      ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) = μ A := by
        rw [hA, MeasureTheory.measure_biUnion_finset D fun c _ => measurableSet_ball]
        have hδ : 0 < δ := by norm_num
        simp only [μ.addHaar_ball_of_pos _ hδ]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball (0 : E) ρ) := MeasureTheory.measure_mono A_subset
      _ = ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) ≤ (17 : ℝ) ^ Module.finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using this
  exact mod_cast K

/-- Volumetric packing bound for the Euclidean unit sphere. -/
theorem c079_packingNumber_unitSphere_le (m : ℕ) :
    Metric.packingNumber (1 / 8 : NNReal)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) ≤ (17 : ℕ∞) ^ m := by
  let A : Set (EuclideanSpace ℝ (Fin m)) := Metric.sphere 0 1
  obtain ⟨S₀, _, hS₀fin, hS₀cover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (ε := (1 / 16 : NNReal)) (s := A) (by norm_num) (isCompact_sphere _ _)
  have hpack_le : Metric.packingNumber (1 / 8 : NNReal) A ≤ S₀.encard := by
    calc
      _ = Metric.packingNumber (2 * (1 / 16 : NNReal)) A := by norm_num
      _ ≤ Metric.externalCoveringNumber (1 / 16 : NNReal) A :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ S₀.encard := hS₀cover.externalCoveringNumber_le_encard
  have hpack_ne : Metric.packingNumber (1 / 8 : NNReal) A ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hpack_le (Set.encard_ne_top_iff.mpr hS₀fin).lt_top)
  let S := Metric.maximalSeparatedSet (1 / 8 : NNReal) A
  have hSfin : S.Finite := by
    apply Set.encard_ne_top_iff.mp
    simpa only [S] using (Metric.encard_maximalSeparatedSet hpack_ne ▸ hpack_ne)
  have hSnorm : ∀ c ∈ hSfin.toFinset, ‖c‖ ≤ 1 := by
    intro c hc
    have hcS : c ∈ S := by simpa using hc
    have hcA : c ∈ A := Metric.maximalSeparatedSet_subset hcS
    have hcUnit : ‖c‖ = 1 := by
      simpa only [A, Metric.mem_sphere, dist_zero_right] using hcA
    exact hcUnit.le
  have hSsep : ∀ c ∈ hSfin.toFinset, ∀ d ∈ hSfin.toFinset,
      c ≠ d → (1 / 8 : ℝ) ≤ ‖c - d‖ := by
    intro c hc d hd hcd
    have hcS : c ∈ S := by simpa using hc
    have hdS : d ∈ S := by simpa using hd
    have hed := (Metric.isSeparated_maximalSeparatedSet
      (ε := (1 / 8 : NNReal)) (A := A)) hcS hdS hcd
    have hr : (1 / 8 : ℝ) < dist c d := by
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp
      simpa [edist_dist] using hed
    exact le_of_lt (by simpa only [dist_eq_norm] using hr)
  have hcard := c079_card_le_of_eighth_separated hSfin.toFinset hSnorm hSsep
  rw [finrank_euclideanSpace_fin] at hcard
  have hcard' : S.encard ≤ (17 : ℕ∞) ^ m := by
    rw [hSfin.encard_eq_coe_toFinset_card]
    exact_mod_cast hcard
  simpa only [A, ← Metric.encard_maximalSeparatedSet hpack_ne] using hcard'

/-- A packing-number estimate supplies a quantitative finite net. -/
theorem c079_exists_quantitative_net_of_packing_bound (m : ℕ)
    (hpack : Metric.packingNumber (1 / 8 : NNReal)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) ≤ (17 : ℕ∞) ^ m) :
    ∃ S : Set (EuclideanSpace ℝ (Fin m)), S.Finite ∧
      S.encard ≤ (17 : ℕ∞) ^ m ∧
      (∀ s ∈ S, ‖s‖ = 1) ∧
      (∀ x, ‖x‖ = 1 → ∃ s ∈ S, ‖x - s‖ ≤ (1 / 8 : ℝ)) := by
  let A : Set (EuclideanSpace ℝ (Fin m)) := Metric.sphere 0 1
  have hrhs : (17 : ℕ∞) ^ m < ⊤ := WithTop.pow_lt_top (WithTop.natCast_lt_top 17)
  have hpack' : Metric.packingNumber (1 / 8 : NNReal) A ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hpack hrhs
  let S := Metric.maximalSeparatedSet (1 / 8 : NNReal) A
  have hcard : S.encard ≤ (17 : ℕ∞) ^ m := by
    simpa only [S, A] using
      ((Metric.encard_maximalSeparatedSet hpack').le.trans hpack)
  have hfin : S.Finite := Set.encard_ne_top_iff.mp (ne_of_lt (lt_of_le_of_lt hcard hrhs))
  have hsub : S ⊆ A := Metric.maximalSeparatedSet_subset
  have hcover : Metric.IsCover (1 / 8 : NNReal) A S :=
    Metric.isCover_maximalSeparatedSet hpack'
  refine ⟨S, hfin, hcard, ?_, ?_⟩
  · intro s hs
    have h := hsub hs
    simpa only [A, Metric.mem_sphere, dist_zero_right] using h
  · intro x hx
    have hx' : x ∈ A := by
      simpa only [A, Metric.mem_sphere, dist_zero_right] using hx
    obtain ⟨s, hs, hdist⟩ := hcover hx'
    refine ⟨s, hs, ?_⟩
    simpa only [dist_eq_norm] using (by exact_mod_cast hdist : dist x s ≤ (1 / 8 : ℝ))

/-- A finite eighth-net of the Euclidean unit sphere with at most `17^m` points. -/
theorem c079_exists_quantitative_unitSphere_net (m : ℕ) :
    ∃ S : Set (EuclideanSpace ℝ (Fin m)), S.Finite ∧
      S.encard ≤ (17 : ℕ∞) ^ m ∧
      (∀ s ∈ S, ‖s‖ = 1) ∧
      (∀ x, ‖x‖ = 1 → ∃ s ∈ S, ‖x - s‖ ≤ (1 / 8 : ℝ)) :=
  c079_exists_quantitative_net_of_packing_bound m (c079_packingNumber_unitSphere_le m)

/-- Deterministic approximation of a unit bilinear form by two sphere-net
points. The net existence and its cardinality are separate statements. -/
theorem c079_unitBilinear_le_netBound
    (m : ℕ) (T : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m))
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hnet : ∀ x, ‖x‖ = 1 → ∃ s ∈ S, ‖x - s‖ ≤ (1 / 8 : ℝ))
    (hunit : ∀ s ∈ S, ‖s‖ = 1)
    (B : ℝ)
    (hB : ∀ u ∈ S, ∀ v ∈ S, |inner ℝ u (T v)| ≤ B)
    (x y : EuclideanSpace ℝ (Fin m))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |inner ℝ y (T x)| ≤ B + (1 / 8 : ℝ) * ‖T x‖ +
      (1 / 8 : ℝ) * ‖T‖ := by
  obtain ⟨u, huS, huy⟩ := hnet y hy
  obtain ⟨v, hvS, hvx⟩ := hnet x hx
  have h1 : |inner ℝ y (T x)| ≤
      |inner ℝ u (T x)| + ‖y - u‖ * ‖T x‖ := by
    have hdecomp : inner ℝ y (T x) =
        inner ℝ u (T x) + inner ℝ (y - u) (T x) := by
      rw [inner_sub_left]
      ring
    rw [hdecomp]
    exact (abs_add_le _ _).trans
      (add_le_add_right (c079_abs_inner_le_norm_mul (y - u) (T x)) _)
  have h2 : |inner ℝ u (T x)| ≤
      |inner ℝ u (T v)| + ‖u‖ * ‖T (x - v)‖ := by
    have hdecomp : inner ℝ u (T x) =
        inner ℝ u (T v) + inner ℝ u (T (x - v)) := by
      rw [map_sub, inner_sub_right]
      ring
    rw [hdecomp]
    exact (abs_add_le _ _).trans
      (add_le_add_right (c079_abs_inner_le_norm_mul u (T (x - v))) _)
  have hTv : ‖T (x - v)‖ ≤ ‖T‖ * ‖x - v‖ := T.le_opNorm _
  have hu : ‖u‖ = 1 := hunit u huS
  have hmain := (h1.trans (add_le_add_left h2 _))
  have hbilin := hB u huS v hvS
  have hsmall1 : ‖y - u‖ * ‖T x‖ ≤ (1 / 8 : ℝ) * ‖T x‖ :=
    mul_le_mul_of_nonneg_right huy (norm_nonneg _)
  have hsmall2 : ‖T (x - v)‖ ≤ (1 / 8 : ℝ) * ‖T‖ := by
    calc
      ‖T (x - v)‖ ≤ ‖T‖ * ‖x - v‖ := hTv
      _ ≤ ‖T‖ * (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hvx (norm_nonneg _)
      _ = (1 / 8 : ℝ) * ‖T‖ := by ring
  rw [hu, one_mul] at hmain
  linarith

/-- An eighth-net controls the operator norm with the convenient bookkeeping
factor `4/3`. The assertion is conditional on a genuine covering property;
no quantitative net existence is claimed here. -/
theorem c079_clm_norm_le_fourThirds_netBound
    (m : ℕ) (T : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m))
    (S : Set (EuclideanSpace ℝ (Fin m)))
    (hnet : ∀ x, ‖x‖ = 1 → ∃ s ∈ S, ‖x - s‖ ≤ (1 / 8 : ℝ))
    (hunit : ∀ s ∈ S, ‖s‖ = 1)
    (B : ℝ) (hBnonneg : 0 ≤ B)
    (hB : ∀ u ∈ S, ∀ v ∈ S, |inner ℝ u (T v)| ≤ B) :
    ‖T‖ ≤ (4 / 3 : ℝ) * B := by
  have hunitBound : ∀ x : EuclideanSpace ℝ (Fin m), ‖x‖ = 1 →
      ‖T x‖ ≤ (8 / 7 : ℝ) * B + (1 / 7 : ℝ) * ‖T‖ := by
    intro x hx
    by_cases hz : T x = 0
    · simp [hz]
      positivity
    let y : EuclideanSpace ℝ (Fin m) := (‖T x‖)⁻¹ • T x
    have hnz : ‖T x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hy : ‖y‖ = 1 := by
      simp [y, norm_smul, hnz]
    have hinner : inner ℝ y (T x) = ‖T x‖ := by
      dsimp [y]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [hnz]
    have h := c079_unitBilinear_le_netBound m T S hnet hunit B hB x y hx hy
    rw [hinner, abs_of_nonneg (norm_nonneg _)] at h
    linarith
  have hC : 0 ≤ (8 / 7 : ℝ) * B + (1 / 7 : ℝ) * ‖T‖ := by
    positivity
  have hT : ‖T‖ ≤ (8 / 7 : ℝ) * B + (1 / 7 : ℝ) * ‖T‖ :=
    T.opNorm_le_of_unit_norm hC hunitBound
  linarith

#print axioms c079_exists_finite_unitSphere_net
#print axioms c079_packingNumber_unitSphere_le
#print axioms c079_exists_quantitative_net_of_packing_bound
#print axioms c079_exists_quantitative_unitSphere_net
#print axioms c079_unitBilinear_le_netBound
#print axioms c079_clm_norm_le_fourThirds_netBound

end GraphMatrixReplica
