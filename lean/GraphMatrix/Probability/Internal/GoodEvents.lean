import GraphMatrix.Probability.Internal.ScaleBounds

/-!
# D: two actual good events and a uniform bound for every good full realization

The public second event uses absolute N-based variance cutoffs. Consequently
its deterministic conclusions do not need an unstated InternalGood premise.
Only its probability proof uses the fixed full realization being internally good.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

def InternalGood
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (n : ℕ) (eps : P1InternalSample P dimension cut c) : Prop :=
  (componentCount P dimension cut c : ℝ) / 2 ≤ p1Q P dimension cut c eps ∧
  p1Q P dimension cut c eps ≤
    16 * internalFourthConstant P cut c * (componentCount P dimension cut c : ℝ) ∧
  ∀ j : Fin (dimension z0),
    p1R P dimension cut c z0 hz0 eps j ≤ internalThreshold n (roleCount P cut c)

def SecondGood
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (n : ℕ) (eps : P1InternalSample P dimension cut c)
    (eta : P1SecondSample P dimension cut c z0) : Prop :=
  (componentCount P dimension cut c : ℝ) / 4 ≤ p1SigmaSq P dimension cut c z0 hz0 eps eta ∧
  p1SigmaSq P dimension cut c z0 hz0 eps eta ≤
    (16 * secondFourthConstant P cut c z0) * (16 * internalFourthConstant P cut c) *
      (componentCount P dimension cut c : ℝ) ∧
  ∀ j : Fin (dimension z0),
    |p1Z P dimension cut c z0 hz0 eps eta j| ≤ secondThreshold n (roleCount P cut c)

theorem finiteUniformProbability_decidable_irrel_explicit
    {Omega : Type} [Fintype Omega] (A : Omega → Prop)
    (d₁ d₂ : DecidablePred A) :
    @finiteUniformProbability Omega inferInstance A d₁ =
      @finiteUniformProbability Omega inferInstance A d₂ := by
  unfold finiteUniformProbability
  congr 1
  funext omega
  by_cases h : A omega <;> simp [h]

theorem finiteUniformProbability_mono_explicit
    {Omega : Type} [Fintype Omega] {A B : Omega → Prop}
    (dA : DecidablePred A) (dB : DecidablePred B)
    (hAB : ∀ omega, A omega → B omega) :
    @finiteUniformProbability Omega inferInstance A dA ≤
      @finiteUniformProbability Omega inferInstance B dB := by
  unfold finiteUniformProbability
  apply paperMean_mono
  intro omega
  by_cases hA : A omega
  · have hB : B omega := hAB omega hA
    simp [hA, hB]
  · simp only [hA, if_false]
    split <;> norm_num

/-- Paley--Zygmund, upper Markov truncation, and a complete coordinate union.
This is only a finite-probability helper: every input moment is discharged
from the actual A/B/C theorems in the public result below. -/
theorem good_probability_from_moments {Ω J : Type}
    [Fintype Ω] [Nonempty Ω] [Fintype J]
    (X : Ω → ℝ) (Y : J → Ω → ℝ) (N C threshold : ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hN : 0 < N) (hC : 0 < C)
    (hMean : paperMean X = N)
    (hSecond : paperMean (fun ω => X ω ^ 2) ≤ C * N ^ 2)
    (hTail : (∑ j, finiteUniformProbability (fun ω => threshold < Y j ω)) ≤
      1 / (16 * C)) :
    1 / (8 * C) ≤ finiteUniformProbability (fun ω =>
      N / 2 ≤ X ω ∧ X ω ≤ 16 * C * N ∧ ∀ j, Y j ω ≤ threshold) := by
  have hμ : 0 < paperMean X := by rw [hMean]; exact hN
  have hM : paperMean (fun ω => X ω ^ 2) ≤ C * paperMean X ^ 2 := by
    rw [hMean]
    exact hSecond
  have hPZ := paley_zygmund_half X C hX hμ hC hM
  rw [hMean] at hPZ
  have hUpper : finiteUniformProbability (fun ω => 16 * C * N < X ω) ≤
      1 / (16 * C) := by
    calc
      _ ≤ N / (16 * C * N) ^ 1 :=
        finiteUniformProbability_le_budget_div_pow X (16 * C * N) N 1 hX
          (by positivity) (by simpa only [pow_one, hMean] using (le_refl N))
      _ = 1 / (16 * C) := by
        field_simp [hC.ne', hN.ne'] <;> ring
  have hTrim := probability_trim
    (fun ω => N / 2 ≤ X ω) (fun ω => 16 * C * N < X ω)
    (fun j ω => threshold < Y j ω)
  have hTrim' :
      finiteUniformProbability (fun ω => N / 2 ≤ X ω) -
        finiteUniformProbability (fun ω => 16 * C * N < X ω) -
          (∑ j, finiteUniformProbability (fun ω => threshold < Y j ω)) ≤
        finiteUniformProbability (fun ω =>
          N / 2 ≤ X ω ∧ X ω ≤ 16 * C * N ∧ ∀ j, Y j ω ≤ threshold) := by
    simpa only [not_lt] using hTrim
  have hnum : 1 / (4 * C) - 1 / (16 * C) - 1 / (16 * C) = 1 / (8 * C) := by
    field_simp [hC.ne'] <;> ring
  linarith

/-- First-layer per-coordinate failure, with the exact n^(-4) power. -/
theorem R_coordinate_tail
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (z0 : Fin P.roles)
    (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 1 ≤ n)
    (hsize : Balanced P dimension cut c a b n) (j : Fin (dimension z0)) :
    finiteUniformProbability (fun eps : P1InternalSample P dimension cut c =>
      internalThreshold n (roleCount P cut c) < p1R P dimension cut c z0 hz0 eps j) ≤
      internalTailCoefficient P cut c b / (n : ℝ) ^ 4 := by
  have hr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hC : 0 < internalHighConstant P cut c := (moment_constants_pos P cut c z0).2.1
  have hCount := puncturedCount_upper P dimension cut c z0 hz0 a b ha n hsize
  have hpow := pow_le_pow_left₀
    (show 0 ≤ (puncturedCount P dimension cut c z0 : ℝ) by positivity) hCount 16
  have hm := R_moment P dimension cut c hActive z0 hz0 j 16 (by norm_num)
  have hm' : paperMean
      (fun eps => p1R P dimension cut c z0 hz0 eps j ^ 16) ≤
      internalHighConstant P cut c *
        (b ^ (roleCount P cut c - 1) * (n : ℝ) ^ (roleCount P cut c - 1)) ^ 16 :=
    hm.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  calc
    _ ≤ (internalHighConstant P cut c *
        (b ^ (roleCount P cut c - 1) * (n : ℝ) ^ (roleCount P cut c - 1)) ^ 16) /
        internalThreshold n (roleCount P cut c) ^ 16 :=
      finiteUniformProbability_le_budget_div_pow
        (fun eps => p1R P dimension cut c z0 hz0 eps j)
        (internalThreshold n (roleCount P cut c)) _ 16
        (fun eps => p1R_nonneg P dimension cut c z0 hz0 eps j)
        (internalThreshold_pos n _ hn) hm'
    _ = internalTailCoefficient P cut c b / (n : ℝ) ^ 4 := by
      rw [internalThreshold_power n _ hn (roleCount_pos P cut c), mul_pow]
      unfold internalTailCoefficient
      field_simp [hr.ne'] <;> ring

/-- Second-layer per-coordinate failure, for one fixed complete eps. -/
theorem Z_coordinate_tail
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (n : ℕ) (hn : 1 ≤ n) (eps : P1InternalSample P dimension cut c)
    (j : Fin (dimension z0))
    (hR : p1R P dimension cut c z0 hz0 eps j ≤ internalThreshold n (roleCount P cut c)) :
    finiteUniformProbability (fun eta : P1SecondSample P dimension cut c z0 =>
      secondThreshold n (roleCount P cut c) < |p1Z P dimension cut c z0 hz0 eps eta j|) ≤
      secondHighConstant P cut c z0 / (n : ℝ) ^ 4 := by
  have hr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hC : 0 < secondHighConstant P cut c z0 := (moment_constants_pos P cut c z0).2.2.2
  have hT : 0 < internalThreshold n (roleCount P cut c) := internalThreshold_pos n _ hn
  have hpow := pow_le_pow_left₀ (p1R_nonneg P dimension cut c z0 hz0 eps j) hR 16
  have hm : paperMean (fun eta => |p1Z P dimension cut c z0 hz0 eps eta j| ^ 32) ≤
      secondHighConstant P cut c z0 * p1R P dimension cut c z0 hz0 eps j ^ 16 := by
    simpa only [p1SecondMean, secondHighConstant, show 2 * 16 = 32 by norm_num] using
      Z_even_moment P dimension cut c z0 hz0 eps j 16 (by norm_num)
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  calc
    _ ≤ (secondHighConstant P cut c z0 * internalThreshold n (roleCount P cut c) ^ 16) /
        secondThreshold n (roleCount P cut c) ^ 32 :=
      finiteUniformProbability_le_budget_div_pow
        (fun eta => |p1Z P dimension cut c z0 hz0 eps eta j|)
        (secondThreshold n (roleCount P cut c)) _ 32
        (fun eta => abs_nonneg _) (secondThreshold_pos n _ hn) hm'
    _ = secondHighConstant P cut c z0 / (n : ℝ) ^ 4 := by
      rw [secondThreshold_power n _ hn]
      field_simp [hr.ne', hT.ne'] <;> ring

/-- First-layer probability after a graph-only numerical size condition. -/
theorem InternalGood_probability
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (z0 : Fin P.roles)
    (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n)
    (hsize : Balanced P dimension cut c a b n)
    (hcut : (b * internalTailCoefficient P cut c b) / (n : ℝ) ^ 3 ≤
      1 / (16 * internalFourthConstant P cut c)) :
    1 / (8 * internalFourthConstant P cut c) ≤
      finiteUniformProbability (InternalGood P dimension cut c z0 hz0 n) := by
  classical
  letI : Nonempty (P1InternalSample P dimension cut c) := ⟨fun _ _ => false⟩
  have hCs := moment_constants_pos P cut c z0
  have hCIpos : 0 < internalFourthConstant P cut c := hCs.1
  have hCEpos : 0 < secondFourthConstant P cut c z0 := hCs.2.2.1
  have hN := componentCount_pos P dimension cut c a b ha n hn hsize
  have hD : 0 ≤ internalTailCoefficient P cut c b := by
    unfold internalTailCoefficient
    exact mul_nonneg hCs.2.1.le (by positivity)
  have hzK := p1BoundaryRoles_subset_component P cut c hz0
  have hUnion := coordinate_union_budget (dimension z0) n b
    (internalTailCoefficient P cut c b) hn hD (hsize z0 hzK).2
    (fun j eps => internalThreshold n (roleCount P cut c) < p1R P dimension cut c z0 hz0 eps j)
    (fun j => R_coordinate_tail P dimension cut c hActive z0 hz0 a b ha.le n hn hsize j)
  have hRaw := good_probability_from_moments
    (p1Q P dimension cut c) (fun j eps => p1R P dimension cut c z0 hz0 eps j)
    (componentCount P dimension cut c : ℝ) (internalFourthConstant P cut c)
    (internalThreshold n (roleCount P cut c))
    (p1Q_nonneg P dimension cut c) hN hCs.1
    (Q_mean P dimension cut c hActive)
    (Q_moment P dimension cut c hActive 2 (by norm_num)) (hUnion.trans hcut)
  convert hRaw using 1
  exact finiteUniformProbability_decidable_irrel_explicit _ _ _

/-- Uniformity is pointwise: eps is chosen and completely fixed before this
probability is considered. No conditional average over InternalGood appears. -/
theorem SecondGood_probability
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n)
    (hsize : Balanced P dimension cut c a b n)
    (hcut : (b * secondHighConstant P cut c z0) / (n : ℝ) ^ 3 ≤
      1 / (16 * secondFourthConstant P cut c z0))
    (eps : P1InternalSample P dimension cut c)
    (hgood : InternalGood P dimension cut c z0 hz0 n eps) :
    1 / (8 * secondFourthConstant P cut c z0) ≤
      finiteUniformProbability (SecondGood P dimension cut c z0 hz0 n eps) := by
  classical
  letI : Nonempty (P1SecondSample P dimension cut c z0) := ⟨fun _ _ => false⟩
  have hCs := moment_constants_pos P cut c z0
  have hCIpos : 0 < internalFourthConstant P cut c := hCs.1
  have hCEpos : 0 < secondFourthConstant P cut c z0 := hCs.2.2.1
  have hN := componentCount_pos P dimension cut c a b ha n hn hsize
  have hQ : 0 < p1Q P dimension cut c eps := by
    have h := hgood.1
    linarith
  have hzK := p1BoundaryRoles_subset_component P cut c hz0
  have hUnion := coordinate_union_budget (dimension z0) n b
    (secondHighConstant P cut c z0) hn hCs.2.2.2.le (hsize z0 hzK).2
    (fun j eta => secondThreshold n (roleCount P cut c) <
      |p1Z P dimension cut c z0 hz0 eps eta j|)
    (fun j => Z_coordinate_tail P dimension cut c z0 hz0 n hn eps j (hgood.2.2 j))
  have hRelative := good_probability_from_moments
    (p1SigmaSq P dimension cut c z0 hz0 eps)
    (fun j eta => |p1Z P dimension cut c z0 hz0 eps eta j|)
    (p1Q P dimension cut c eps) (secondFourthConstant P cut c z0)
    (secondThreshold n (roleCount P cut c))
    (p1SigmaSq_nonneg P dimension cut c z0 hz0 eps) hQ hCs.2.2.1
    (sigmaSq_mean P dimension cut c z0 hz0 eps)
    (sigmaSq_moment P dimension cut c z0 hz0 eps 2 (by norm_num)) (hUnion.trans hcut)
  apply hRelative.trans
  apply finiteUniformProbability_mono_explicit
  intro eta hrel
  refine ⟨?_, ?_, hrel.2.2⟩
  · have hG := hgood.1
    have hE := hrel.1
    linarith
  · have hG := mul_le_mul_of_nonneg_left hgood.2.1
      (show 0 ≤ 16 * secondFourthConstant P cut c z0 by positivity)
    exact hrel.2.1.trans (by simpa only [mul_assoc] using hG)

/-- Deterministic first-layer conclusions in the requested n^k/rpow scale. -/
theorem InternalGood_bounds
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (hsize : Balanced P dimension cut c a b n)
    (eps : P1InternalSample P dimension cut c)
    (hgood : InternalGood P dimension cut c z0 hz0 n eps) :
    (a ^ roleCount P cut c / 2) * (n : ℝ) ^ roleCount P cut c ≤ p1Q P dimension cut c eps ∧
    p1Q P dimension cut c eps ≤
      (16 * internalFourthConstant P cut c * b ^ roleCount P cut c) *
        (n : ℝ) ^ roleCount P cut c ∧
    ∀ j : Fin (dimension z0), p1R P dimension cut c z0 hz0 eps j ≤
      (n : ℝ) ^ ((roleCount P cut c : ℝ) - (3 : ℝ) / 4) := by
  have hN := componentCount_bounds P dimension cut c a b ha n hsize
  have hC := (moment_constants_pos P cut c z0).1
  refine ⟨?_, ?_, hgood.2.2⟩
  · have h := hgood.1
    nlinarith [hN.1]
  · have h := mul_le_mul_of_nonneg_left hN.2
      (show 0 ≤ 16 * internalFourthConstant P cut c by positivity)
    exact hgood.2.1.trans (by simpa only [mul_assoc] using h)

/-- This implication needs SecondGood alone, not a concealed InternalGood premise. -/
theorem SecondGood_bounds
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (hsize : Balanced P dimension cut c a b n)
    (eps : P1InternalSample P dimension cut c)
    (eta : P1SecondSample P dimension cut c z0)
    (hgood : SecondGood P dimension cut c z0 hz0 n eps eta) :
    (a ^ roleCount P cut c / 4) * (n : ℝ) ^ roleCount P cut c ≤
      p1SigmaSq P dimension cut c z0 hz0 eps eta ∧
    p1SigmaSq P dimension cut c z0 hz0 eps eta ≤
      ((16 * secondFourthConstant P cut c z0) * (16 * internalFourthConstant P cut c) *
        b ^ roleCount P cut c) * (n : ℝ) ^ roleCount P cut c ∧
    ∀ j : Fin (dimension z0), |p1Z P dimension cut c z0 hz0 eps eta j| ≤
      (n : ℝ) ^ ((roleCount P cut c : ℝ) / 2 - (1 : ℝ) / 4) := by
  have hN := componentCount_bounds P dimension cut c a b ha n hsize
  have hCs := moment_constants_pos P cut c z0
  have hCIpos : 0 < internalFourthConstant P cut c := hCs.1
  have hCEpos : 0 < secondFourthConstant P cut c z0 := hCs.2.2.1
  refine ⟨?_, ?_, hgood.2.2⟩
  · have h := hgood.1
    nlinarith [hN.1]
  · have h := mul_le_mul_of_nonneg_left hN.2
      (show 0 ≤ (16 * secondFourthConstant P cut c z0) *
        (16 * internalFourthConstant P cut c) by positivity)
    exact hgood.2.1.trans (by simpa only [mul_assoc] using h)

/-- D, with the full quantifier order. Constants and n0 are selected before
all heterogeneous dimension functions, n, internal samples, and second samples.
There is no moment, support-injection, or probability hypothesis. -/
theorem exists_two_layer_good_events
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (hActive : c.IsActive)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ p_int p_ext cQ CQ cS CS : ℝ, ∃ n0 : ℕ,
      0 < p_int ∧ 0 < p_ext ∧ 0 < cQ ∧ 0 < CQ ∧ 0 < cS ∧ 0 < CS ∧ 1 ≤ n0 ∧
      ∀ (dimension : Fin P.roles → ℕ) (n : ℕ), n0 ≤ n →
        Balanced P dimension cut c a b n →
        (p_int ≤ finiteUniformProbability (InternalGood P dimension cut c z0 hz0 n)) ∧
        (∀ eps : P1InternalSample P dimension cut c,
          InternalGood P dimension cut c z0 hz0 n eps →
            cQ * (n : ℝ) ^ roleCount P cut c ≤ p1Q P dimension cut c eps ∧
            p1Q P dimension cut c eps ≤ CQ * (n : ℝ) ^ roleCount P cut c ∧
            ∀ j : Fin (dimension z0), p1R P dimension cut c z0 hz0 eps j ≤
              (n : ℝ) ^ ((roleCount P cut c : ℝ) - (3 : ℝ) / 4)) ∧
        (∀ eps : P1InternalSample P dimension cut c,
          InternalGood P dimension cut c z0 hz0 n eps →
            p_ext ≤ finiteUniformProbability (SecondGood P dimension cut c z0 hz0 n eps)) ∧
        (∀ (eps : P1InternalSample P dimension cut c) (eta : P1SecondSample P dimension cut c z0),
          SecondGood P dimension cut c z0 hz0 n eps eta →
            cS * (n : ℝ) ^ roleCount P cut c ≤ p1SigmaSq P dimension cut c z0 hz0 eps eta ∧
            p1SigmaSq P dimension cut c z0 hz0 eps eta ≤ CS * (n : ℝ) ^ roleCount P cut c ∧
            ∀ j : Fin (dimension z0), |p1Z P dimension cut c z0 hz0 eps eta j| ≤
              (n : ℝ) ^ ((roleCount P cut c : ℝ) / 2 - (1 : ℝ) / 4)) := by
  classical
  let CI := internalFourthConstant P cut c
  let CE := secondFourthConstant P cut c z0
  let DI := b * internalTailCoefficient P cut c b
  let DE := b * secondHighConstant P cut c z0
  let k := roleCount P cut c
  have hCs := moment_constants_pos P cut c z0
  have hCIpos : 0 < internalFourthConstant P cut c := hCs.1
  have hCEpos : 0 < secondFourthConstant P cut c z0 := hCs.2.2.1
  have hCI : 0 < CI := hCs.1
  have hCE : 0 < CE := hCs.2.2.1
  have hb : 0 < b := ha.trans_le hab
  have hpI : 0 < 1 / (4 * CI) := by positivity
  have hpE : 0 < 1 / (4 * CE) := by positivity
  obtain ⟨n0, hn01, hcut⟩ := exists_common_cutoff DI DE
    (1 / (4 * CI)) (1 / (4 * CE)) hpI hpE
  refine ⟨1 / (8 * CI), 1 / (8 * CE), a ^ k / 2, 16 * CI * b ^ k,
    a ^ k / 4, (16 * CE) * (16 * CI) * b ^ k, n0,
    by positivity, by positivity, by positivity, by positivity,
    by positivity, by positivity, hn01, ?_⟩
  intro dimension n hn hsize
  have hn1 : 1 ≤ n := hn01.trans hn
  have hqI : (1 / (4 * CI)) / 4 = 1 / (16 * CI) := by
    field_simp [hCI.ne'] <;> ring
  have hqE : (1 / (4 * CE)) / 4 = 1 / (16 * CE) := by
    field_simp [hCE.ne'] <;> ring
  have hcutI : DI / (n : ℝ) ^ 3 ≤ 1 / (16 * CI) := by
    simpa only [hqI] using (hcut n hn).1
  have hcutE : DE / (n : ℝ) ^ 3 ≤ 1 / (16 * CE) := by
    simpa only [hqE] using (hcut n hn).2
  refine ⟨InternalGood_probability P dimension cut c hActive z0 hz0 a b ha n hn1 hsize hcutI,
    ?_, ?_, ?_⟩
  · intro eps hgood
    exact InternalGood_bounds P dimension cut c z0 hz0 a b ha.le n hsize eps hgood
  · intro eps hgood
    exact SecondGood_probability P dimension cut c z0 hz0 a b ha n hn1 hsize hcutE eps hgood
  · intro eps eta hgood
    exact SecondGood_bounds P dimension cut c z0 hz0 a b ha.le n hsize eps eta hgood

end GraphMatrixReplica.P1AD
