import R6.P1ADSecondLayerMoments

/-! # Balanced heterogeneous dimensions and exact fractional-power budgets -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000

def roleCount (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) : ℕ :=
  (p1ComponentRoles P cut c).card

def Balanced (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (a b : ℝ) (n : ℕ) : Prop :=
  ∀ v ∈ p1ComponentRoles P cut c,
    a * (n : ℝ) ≤ (dimension v : ℝ) ∧ (dimension v : ℝ) ≤ b * (n : ℝ)

/-- Every fractional exponent in the statement is a real exponent. -/
def internalThreshold (n k : ℕ) : ℝ := (n : ℝ) ^ ((k : ℝ) - (3 : ℝ) / 4)
def secondThreshold (n k : ℕ) : ℝ := (n : ℝ) ^ ((k : ℝ) / 2 - (1 : ℝ) / 4)

def internalFourthConstant (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) : ℝ :=
  (32 : ℝ) ^ (2 * internalDegree P cut c)
def internalHighConstant (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) : ℝ :=
  (32 : ℝ) ^ (16 * internalDegree P cut c)
def secondFourthConstant (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (z0 : Fin P.roles) : ℝ :=
  (32 : ℝ) ^ (2 * secondDegree P cut c z0)
def secondHighConstant (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (z0 : Fin P.roles) : ℝ :=
  (32 : ℝ) ^ (16 * secondDegree P cut c z0)

def internalTailCoefficient (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (b : ℝ) : ℝ :=
  internalHighConstant P cut c * (b ^ (roleCount P cut c - 1)) ^ 16

theorem moment_constants_pos
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (z0 : Fin P.roles) :
    0 < internalFourthConstant P cut c ∧
    0 < internalHighConstant P cut c ∧
    0 < secondFourthConstant P cut c z0 ∧
    0 < secondHighConstant P cut c z0 := by
  unfold internalFourthConstant internalHighConstant secondFourthConstant secondHighConstant
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem roleCount_pos
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) : 1 ≤ roleCount P cut c := by
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr
    (P.toPartiteShape.c079ComponentRoles_nonempty cut c))

theorem dimensionProduct_bounds
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (A : Finset (Fin P.roles)) (a b r : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hsize : ∀ v ∈ A, a * r ≤ (dimension v : ℝ) ∧ (dimension v : ℝ) ≤ b * r) :
    a ^ A.card * r ^ A.card ≤ (p1DimensionProduct P dimension A : ℝ) ∧
    (p1DimensionProduct P dimension A : ℝ) ≤ b ^ A.card * r ^ A.card := by
  have hL : (∏ v ∈ A, a * r) ≤ ∏ v ∈ A, (dimension v : ℝ) :=
    Finset.prod_le_prod (fun _ _ => mul_nonneg ha hr) (fun v hv => (hsize v hv).1)
  have hU : (∏ v ∈ A, (dimension v : ℝ)) ≤ ∏ v ∈ A, b * r :=
    Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun v hv => (hsize v hv).2)
  constructor
  · simpa [p1DimensionProduct, mul_pow] using hL
  · simpa [p1DimensionProduct, mul_pow] using hU

theorem componentCount_bounds
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (a b : ℝ) (ha : 0 ≤ a) (n : ℕ) (hsize : Balanced P dimension cut c a b n) :
    a ^ roleCount P cut c * (n : ℝ) ^ roleCount P cut c ≤
        (componentCount P dimension cut c : ℝ) ∧
    (componentCount P dimension cut c : ℝ) ≤
        b ^ roleCount P cut c * (n : ℝ) ^ roleCount P cut c :=
  dimensionProduct_bounds P dimension (p1ComponentRoles P cut c) a b n ha
    (Nat.cast_nonneg n) hsize

theorem componentCount_pos
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (a b : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n)
    (hsize : Balanced P dimension cut c a b n) :
    0 < (componentCount P dimension cut c : ℝ) := by
  have hr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h := (componentCount_bounds P dimension cut c a b ha.le n hsize).1
  exact lt_of_lt_of_le (mul_pos (pow_pos ha _) (pow_pos hr _)) h

theorem puncturedCount_upper
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 ≤ a) (n : ℕ) (hsize : Balanced P dimension cut c a b n) :
    (puncturedCount P dimension cut c z0 : ℝ) ≤
      b ^ (roleCount P cut c - 1) * (n : ℝ) ^ (roleCount P cut c - 1) := by
  classical
  let K := p1ComponentRoles P cut c
  have hzK : z0 ∈ K := p1BoundaryRoles_subset_component P cut c hz0
  have hset : K \ {z0} = K.erase z0 := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase]
    tauto
  have hcard : (K \ {z0}).card = roleCount P cut c - 1 := by
    rw [hset, Finset.card_erase_of_mem hzK]
    rfl
  have h := (dimensionProduct_bounds P dimension (K \ {z0}) a b n ha
    (Nat.cast_nonneg n) (fun v hv => hsize v (Finset.mem_sdiff.mp hv).1)).2
  simpa only [puncturedCount, hcard] using h

theorem rpow_nat_power {r : ℝ} (hr : 0 < r) (x : ℝ) (m : ℕ) :
    (r ^ x) ^ m = r ^ (x * (m : ℝ)) := by
  rw [Real.rpow_mul hr.le, Real.rpow_natCast]

theorem internalThreshold_pos (n k : ℕ) (hn : 1 ≤ n) :
    0 < internalThreshold n k := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (show 0 < n by omega)

theorem secondThreshold_pos (n k : ℕ) (hn : 1 ≤ n) :
    0 < secondThreshold n k := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (show 0 < n by omega)

/-- Exact exponent identity behind the first n^(-4) coordinate bound. -/
theorem internalThreshold_power (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    internalThreshold n k ^ 16 = ((n : ℝ) ^ (k - 1)) ^ 16 * (n : ℝ) ^ 4 := by
  have hr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold internalThreshold
  calc
    _ = (n : ℝ) ^ (((k : ℝ) - (3 : ℝ) / 4) * (16 : ℝ)) := rpow_nat_power hr _ 16
    _ = (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) * (16 : ℝ) + (4 : ℝ)) := by
      congr 1
      rw [Nat.cast_sub hk]
      norm_num <;> ring
    _ = (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) * (16 : ℝ)) * (n : ℝ) ^ (4 : ℝ) :=
      Real.rpow_add hr _ _
    _ = _ := by
      rw [Real.rpow_mul hr.le]
      norm_num only [Real.rpow_natCast, Real.rpow_ofNat]

/-- Exact exponent identity behind the second n^(-4) coordinate bound. -/
theorem secondThreshold_power (n k : ℕ) (hn : 1 ≤ n) :
    secondThreshold n k ^ 32 = internalThreshold n k ^ 16 * (n : ℝ) ^ 4 := by
  have hr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  unfold secondThreshold internalThreshold
  rw [rpow_nat_power hr _ 32, rpow_nat_power hr _ 16]
  calc
    _ = (n : ℝ) ^ ((((k : ℝ) - (3 : ℝ) / 4) * (16 : ℝ)) + (4 : ℝ)) := by
      congr 1
      ring
    _ = _ := by
      rw [Real.rpow_add hr]
      norm_num only [Real.rpow_ofNat]

/-- Union over the real heterogeneous label type Fin m; no independence is
needed for this inequality. -/
theorem coordinate_union_budget {Ω : Type} [Fintype Ω]
    (m n : ℕ) (b D : ℝ) (hn : 1 ≤ n) (hD : 0 ≤ D)
    (hcard : (m : ℝ) ≤ b * (n : ℝ))
    (E : Fin m → Ω → Prop)
    (hEach : ∀ j, finiteUniformProbability (E j) ≤ D / (n : ℝ) ^ 4) :
    (∑ j, finiteUniformProbability (E j)) ≤ (b * D) / (n : ℝ) ^ 3 := by
  have hr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ∑ _ : Fin m, D / (n : ℝ) ^ 4 := Finset.sum_le_sum fun j _ => hEach j
    _ = (m : ℝ) * (D / (n : ℝ) ^ 4) := by simp
    _ ≤ (b * (n : ℝ)) * (D / (n : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hD (pow_nonneg hr.le _))
    _ = (b * D) / (n : ℝ) ^ 3 := by
      field_simp [hr.ne'] <;> ring

/-- A simple sufficient size condition. It intentionally avoids taking an
unformalized cube root when selecting a common integer cutoff. -/
theorem budget_le_quarter {D p r : ℝ} (hp : 0 < p) (hr : 1 ≤ r)
    (hcut : 4 * D / p ≤ r) : D / r ^ 3 ≤ p / 4 := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hrp : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have h1 := mul_nonneg (sub_nonneg.mpr hr) hr0
  have h2 := mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg r)
  have hcube : r ≤ r ^ 3 := by nlinarith [h1, h2]
  have hcut' : 4 * D ≤ r * p := (div_le_iff₀ hp).mp hcut
  have hscale := mul_le_mul_of_nonneg_right hcube hp.le
  apply (div_le_iff₀ (pow_pos hrp 3)).mpr
  nlinarith [hcut', hscale]

/-- One cutoff works for the two budgets, before n, dimensions, or eps are chosen. -/
theorem exists_common_cutoff (DI DE pI pE : ℝ) (hpI : 0 < pI) (hpE : 0 < pE) :
    ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      DI / (n : ℝ) ^ 3 ≤ pI / 4 ∧ DE / (n : ℝ) ^ 3 ≤ pE / 4 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (4 * DI / pI) (4 * DE / pE))
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  have hr : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hNn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  constructor
  · apply budget_le_quarter hpI hr
    exact (le_max_left _ _).trans (hN.le.trans hNn')
  · apply budget_le_quarter hpE hr
    exact (le_max_right _ _).trans (hN.le.trans hNn')

#print axioms componentCount_bounds
#print axioms puncturedCount_upper
#print axioms internalThreshold_power
#print axioms secondThreshold_power
#print axioms exists_common_cutoff
end GraphMatrixReplica.P1AD
