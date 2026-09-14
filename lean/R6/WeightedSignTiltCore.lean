import Mathlib

/-!
Finite exponential tilting bridge for the weighted-sign lower tail.
The sample space and statistic are arbitrary here.  The two inputs that still
need to be instantiated for weighted Rademacher sums are the centered sample
sum and the tilted band-mass bound (obtained from mean/variance/Chebyshev).
-/

noncomputable section
open scoped BigOperators

namespace WeightedSignTilt

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def partition (Y : Ω → ℝ) (lam : ℝ) : ℝ :=
  ∑ ω : Ω, Real.exp (lam * Y ω)

def bandMass (Y : Ω → ℝ) (lam : ℝ) (P : Ω → Prop) [DecidablePred P] : ℝ :=
  ∑ ω ∈ Finset.univ.filter P, Real.exp (lam * Y ω)

def uniformProbability (P : Ω → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ)

def tiltedProbability (Y : Ω → ℝ) (lam : ℝ)
    (P : Ω → Prop) [DecidablePred P] : ℝ :=
  bandMass Y lam P / partition Y lam

def tiltedAtom (Y : Ω → ℝ) (lam : ℝ) (ω : Ω) : ℝ :=
  Real.exp (lam * Y ω) / partition Y lam

def inverseLikelihood (Y : Ω → ℝ) (lam : ℝ) (ω : Ω) : ℝ :=
  partition Y lam / (Fintype.card Ω : ℝ) * Real.exp (-(lam * Y ω))

theorem partition_pos (Y : Ω → ℝ) (lam : ℝ) :
    0 < partition Y lam := by
  unfold partition
  exact Finset.sum_pos (fun ω _ => Real.exp_pos _) Finset.univ_nonempty

theorem tiltedProbability_univ (Y : Ω → ℝ) (lam : ℝ) :
    tiltedProbability Y lam (fun _ => True) = 1 := by
  have hZ : partition Y lam ≠ 0 := ne_of_gt (partition_pos Y lam)
  simp [tiltedProbability, bandMass, partition] at hZ ⊢
  exact hZ

theorem tiltedAtom_mul_inverseLikelihood
    (Y : Ω → ℝ) (lam : ℝ) (ω : Ω) :
    tiltedAtom Y lam ω * inverseLikelihood Y lam ω =
      1 / (Fintype.card Ω : ℝ) := by
  have hZ : partition Y lam ≠ 0 := ne_of_gt (partition_pos Y lam)
  have hC : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold tiltedAtom inverseLikelihood
  rw [Real.exp_neg]
  field_simp [hZ, hC, Real.exp_ne_zero]

theorem partition_ge_card_of_centered (Y : Ω → ℝ) (lam : ℝ)
    (hcenter : (∑ ω : Ω, Y ω) = 0) :
    (Fintype.card Ω : ℝ) ≤ partition Y lam := by
  have hlinear :
      (∑ ω : Ω, (1 + lam * Y ω)) = (Fintype.card Ω : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hcenter]
  calc
    (Fintype.card Ω : ℝ) = ∑ ω : Ω, (1 + lam * Y ω) := hlinear.symm
    _ ≤ ∑ ω : Ω, Real.exp (lam * Y ω) := by
      apply Finset.sum_le_sum
      intro ω _
      simpa [add_comm] using Real.add_one_le_exp (lam * Y ω)
    _ = partition Y lam := rfl

theorem bandMass_le_exp_mul_card (Y : Ω → ℝ) (lam b : ℝ)
    (P : Ω → Prop) [DecidablePred P]
    (hupper : ∀ ω, P ω → lam * Y ω ≤ lam * b) :
    bandMass Y lam P ≤
      Real.exp (lam * b) * ((Finset.univ.filter P).card : ℝ) := by
  unfold bandMass
  calc
    (∑ ω ∈ Finset.univ.filter P, Real.exp (lam * Y ω)) ≤
        ∑ ω ∈ Finset.univ.filter P, Real.exp (lam * b) := by
          apply Finset.sum_le_sum
          intro ω hω
          exact Real.exp_le_exp.mpr (hupper ω ((Finset.mem_filter.mp hω).2))
    _ = Real.exp (lam * b) * ((Finset.univ.filter P).card : ℝ) := by
      simp [mul_comm]

/-- The exact finite likelihood bridge.  The band-mass premise is the only
probabilistic input; the result already has the paper's inverse likelihood
factor and no unproved normalization assumption. -/
theorem uniformProbability_ge_half_exp_of_centered_band
    (Y : Ω → ℝ) (lam b : ℝ) (P : Ω → Prop) [DecidablePred P]
    (hcenter : (∑ ω : Ω, Y ω) = 0)
    (hupper : ∀ ω, P ω → lam * Y ω ≤ lam * b)
    (hhalf : (1 / 2 : ℝ) ≤ tiltedProbability Y lam P) :
    (1 / 2 : ℝ) * Real.exp (-(lam * b)) ≤ uniformProbability P := by
  let C : ℝ := Fintype.card Ω
  let E : ℝ := Real.exp (lam * b)
  let N : ℝ := (Finset.univ.filter P).card
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast Fintype.card_pos
  have hZ : C ≤ partition Y lam := partition_ge_card_of_centered Y lam hcenter
  have hZpos : 0 < partition Y lam := partition_pos Y lam
  have hmass : partition Y lam / 2 ≤ bandMass Y lam P := by
    unfold tiltedProbability at hhalf
    apply (le_div_iff₀ hZpos).mp at hhalf
    nlinarith
  have hband : bandMass Y lam P ≤ E * N :=
    bandMass_le_exp_mul_card Y lam b P hupper
  have hCE : C / 2 ≤ E * N := by linarith
  have hE : 0 < E := Real.exp_pos _
  have hEinverse : E * Real.exp (-(lam * b)) = 1 := by
    dsimp [E]
    rw [Real.exp_neg]
    exact mul_inv_cancel₀ (Real.exp_ne_zero _)
  have hcount : (1 / 2 : ℝ) * Real.exp (-(lam * b)) * C ≤ N := by
    calc
      (1 / 2 : ℝ) * Real.exp (-(lam * b)) * C =
          (C / 2) * Real.exp (-(lam * b)) := by ring
      _ ≤ (E * N) * Real.exp (-(lam * b)) :=
        mul_le_mul_of_nonneg_right hCE (le_of_lt (Real.exp_pos _))
      _ = N := by
        calc
          (E * N) * Real.exp (-(lam * b)) =
              (E * Real.exp (-(lam * b))) * N := by ring
          _ = N := by rw [hEinverse]; ring
  unfold uniformProbability
  exact (le_div_iff₀ hC).mpr (by simpa [C, N] using hcount)

/-! The concrete finite Rademacher sample.  A global sign flip proves exact
centering, so the likelihood bridge above applies without a centering axiom. -/

variable {J : Type*} [Fintype J] [DecidableEq J]

def sign (b : Bool) : ℝ := if b then 1 else -1

def flip (ε : J → Bool) : J → Bool := fun j => !(ε j)

def weightedSum (z : J → ℝ) (ε : J → Bool) : ℝ :=
  ∑ j : J, z j * sign (ε j)

theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

theorem flip_flip (ε : J → Bool) : flip (flip ε) = ε := by
  funext j
  simp [flip]

def flipEquiv : (J → Bool) ≃ (J → Bool) where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

theorem weightedSum_flip (z : J → ℝ) (ε : J → Bool) :
    weightedSum z (flip ε) = -weightedSum z ε := by
  simp [weightedSum, flip, sign_not, Finset.sum_neg_distrib]

theorem weightedSum_centered (z : J → ℝ) :
    (∑ ε : J → Bool, weightedSum z ε) = 0 := by
  let S : ℝ := ∑ ε : J → Bool, weightedSum z ε
  have hflip : S = ∑ ε : J → Bool, weightedSum z (flip ε) := by
    dsimp [S]
    apply Fintype.sum_equiv (flipEquiv (J := J))
    intro ε
    simp [flipEquiv, flip_flip]
  have hneg : S = -S := by
    calc
      S = ∑ ε : J → Bool, weightedSum z (flip ε) := hflip
      _ = ∑ ε : J → Bool, -weightedSum z ε := by simp only [weightedSum_flip]
      _ = -S := by simp [S, Finset.sum_neg_distrib]
  dsimp [S] at *
  linarith

theorem weightedSum_partition_ge_card (z : J → ℝ) (lam : ℝ) :
    (Fintype.card (J → Bool) : ℝ) ≤ partition (weightedSum z) lam :=
  partition_ge_card_of_centered (weightedSum z) lam (weightedSum_centered z)

def coordinateWeight (z : J → ℝ) (lam : ℝ) (j : J) (b : Bool) : ℝ :=
  Real.exp (lam * z j * sign b)

def coordinatePartition (z : J → ℝ) (lam : ℝ) (j : J) : ℝ :=
  ∑ b : Bool, coordinateWeight z lam j b

theorem coordinatePartition_pos (z : J → ℝ) (lam : ℝ) (j : J) :
    0 < coordinatePartition z lam j := by
  unfold coordinatePartition coordinateWeight
  exact Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty

theorem exp_weightedSum_eq_prod (z : J → ℝ) (lam : ℝ) (ε : J → Bool) :
    Real.exp (lam * weightedSum z ε) =
      ∏ j : J, coordinateWeight z lam j (ε j) := by
  have hsum : lam * weightedSum z ε =
      ∑ j : J, lam * z j * sign (ε j) := by
    simp [weightedSum, Finset.mul_sum]
    congr 1
    funext j
    ring
  rw [hsum, Real.exp_sum]
  rfl

/-- The partition is exactly the product of the Bernoulli normalizers.
This is the finite tensor factorization underlying independence after tilt. -/
theorem weightedSum_partition_eq_prod (z : J → ℝ) (lam : ℝ) :
    partition (weightedSum z) lam =
      ∏ j : J, coordinatePartition z lam j := by
  unfold partition
  simp_rw [exp_weightedSum_eq_prod]
  unfold coordinatePartition
  simpa only [Fintype.piFinset_univ] using
    (Finset.sum_prod_piFinset (s := Finset.univ)
      (g := fun j b => coordinateWeight z lam j b))

theorem weightedSum_tiltedAtom_eq_prod (z : J → ℝ) (lam : ℝ)
    (ε : J → Bool) :
    tiltedAtom (weightedSum z) lam ε =
      ∏ j : J, coordinateWeight z lam j (ε j) /
        coordinatePartition z lam j := by
  unfold tiltedAtom
  rw [exp_weightedSum_eq_prod, weightedSum_partition_eq_prod]
  rw [Finset.prod_div_distrib]


theorem weightedSum_uniformProbability_ge_half_exp_of_band
    (z : J → ℝ) (lam b : ℝ) (P : (J → Bool) → Prop) [DecidablePred P]
    (hupper : ∀ ε, P ε → lam * weightedSum z ε ≤ lam * b)
    (hhalf : (1 / 2 : ℝ) ≤ tiltedProbability (weightedSum z) lam P) :
    (1 / 2 : ℝ) * Real.exp (-(lam * b)) ≤ uniformProbability P :=
  uniformProbability_ge_half_exp_of_centered_band
    (weightedSum z) lam b P (weightedSum_centered z) hupper hhalf

theorem paper_chebyshev_band_constant :
    (1 / 2 : ℝ) ≤ 1 - 1 / 9 - 1 / 16 := by norm_num

theorem paper_tilt_exponent_constant (t sigmaSq : ℝ) (hσ : sigmaSq ≠ 0) :
    (8 * t / sigmaSq) * (12 * t) = 96 * t ^ 2 / sigmaSq := by
  field_simp
  ring

/-- Exact paper constant, conditional only on the tilted band-mass estimate.
The missing mean/variance/Chebyshev calculation must establish `hband`. -/
theorem paper_weighted_tail_of_tilted_band
    (z : J → ℝ) (t sigmaSq : ℝ) (hσ : 0 < sigmaSq) (ht : 0 ≤ t)
    (hband : (1 / 2 : ℝ) ≤ tiltedProbability (weightedSum z)
      (8 * t / sigmaSq)
      (fun ε => t ≤ weightedSum z ε ∧ weightedSum z ε ≤ 12 * t)) :
    (1 / 2 : ℝ) * Real.exp (-(96 * t ^ 2 / sigmaSq)) ≤
      uniformProbability (fun ε => t ≤ weightedSum z ε) := by
  let lam : ℝ := 8 * t / sigmaSq
  let band : (J → Bool) → Prop :=
    fun ε => t ≤ weightedSum z ε ∧ weightedSum z ε ≤ 12 * t
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    positivity
  have hupper : ∀ ε, band ε → lam * weightedSum z ε ≤ lam * (12 * t) := by
    intro ε hε
    exact mul_le_mul_of_nonneg_left hε.2 hlam
  have hhalf : (1 / 2 : ℝ) * Real.exp (-(lam * (12 * t))) ≤
      uniformProbability band :=
    weightedSum_uniformProbability_ge_half_exp_of_band
      z lam (12 * t) band hupper hband
  have hsubset : Finset.univ.filter band ⊆
      Finset.univ.filter (fun ε => t ≤ weightedSum z ε) := by
    intro ε hε
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ ε,
      (Finset.mem_filter.mp hε).2.1⟩
  have hmono : uniformProbability band ≤
      uniformProbability (fun ε => t ≤ weightedSum z ε) := by
    unfold uniformProbability
    have hcard : ((Finset.univ.filter band).card : ℝ) ≤
        ((Finset.univ.filter (fun ε => t ≤ weightedSum z ε)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hC : (0 : ℝ) < Fintype.card (J → Bool) := by
      exact_mod_cast Fintype.card_pos
    exact (div_le_div_iff₀ hC hC).mpr (by nlinarith)
  calc
    (1 / 2 : ℝ) * Real.exp (-(96 * t ^ 2 / sigmaSq)) =
        (1 / 2 : ℝ) * Real.exp (-(lam * (12 * t))) := by
          rw [paper_tilt_exponent_constant t sigmaSq (ne_of_gt hσ)]
    _ ≤ uniformProbability band := hhalf
    _ ≤ uniformProbability (fun ε => t ≤ weightedSum z ε) := hmono

#print axioms partition_pos
#print axioms tiltedProbability_univ
#print axioms tiltedAtom_mul_inverseLikelihood
#print axioms partition_ge_card_of_centered
#print axioms bandMass_le_exp_mul_card
#print axioms uniformProbability_ge_half_exp_of_centered_band
#print axioms weightedSum_centered
#print axioms weightedSum_partition_ge_card
#print axioms coordinatePartition_pos
#print axioms exp_weightedSum_eq_prod
#print axioms weightedSum_partition_eq_prod
#print axioms weightedSum_tiltedAtom_eq_prod
#print axioms weightedSum_uniformProbability_ge_half_exp_of_band
#print axioms paper_chebyshev_band_constant
#print axioms paper_tilt_exponent_constant
#print axioms paper_weighted_tail_of_tilted_band

end WeightedSignTilt
