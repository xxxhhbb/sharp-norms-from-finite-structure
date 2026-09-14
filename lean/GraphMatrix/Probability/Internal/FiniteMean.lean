import GraphMatrix.Probability.ComponentEvents
import GraphMatrix.HighMomentTailMarkov
import GraphMatrix.Probability.Conditional.ConditionalProductLaw
import GraphMatrix.RademacherMatrixSecondMoment
import GraphMatrix.Model.HilbertSignFourthMoment
import Mathlib

/-!
# Finite averages and the probability assembly used by P1-AD

All averages below are the existing `GraphMatrixReplica.paperMean`.
In particular, no independence or moment estimate is a field of a model.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000

@[simp] theorem mean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (r : ℝ) :
    paperMean (fun _ : Ω => r) = r := by
  have h : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [paperMean, h]

theorem mean_nonneg {Ω : Type} [Fintype Ω] {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ paperMean f := by
  unfold paperMean
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun ω _ => hf ω)

theorem mean_add {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    paperMean (fun ω => f ω + g ω) = paperMean f + paperMean g := by
  simp only [paperMean, Finset.sum_add_distrib, mul_add]

theorem mean_sub {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    paperMean (fun ω => f ω - g ω) = paperMean f - paperMean g := by
  simp only [paperMean, Finset.sum_sub_distrib, mul_sub]

theorem mean_mul_left {Ω : Type} [Fintype Ω] (r : ℝ) (f : Ω → ℝ) :
    paperMean (fun ω => r * f ω) = r * paperMean f := by
  simp only [paperMean, ← Finset.mul_sum]
  ring

theorem mean_mul_right {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (r : ℝ) :
    paperMean (fun ω => f ω * r) = paperMean f * r := by
  simp only [paperMean, ← Finset.sum_mul]
  ring

theorem mean_prod {Ω Ψ : Type} [Fintype Ω] [Fintype Ψ]
    (f : Ω → Ψ → ℝ) :
    paperMean (fun z : Ω × Ψ => f z.1 z.2) =
      paperMean (fun ω => paperMean (f ω)) := by
  exact P2a.paperMean_prod f

theorem mean_prod_swap {Ω Ψ : Type} [Fintype Ω] [Fintype Ψ]
    (f : Ω → Ψ → ℝ) :
    paperMean (fun z : Ω × Ψ => f z.1 z.2) =
      paperMean (fun ψ => paperMean (fun ω => f ω ψ)) := by
  rw [← paperMean_equiv (Equiv.prodComm Ψ Ω)]
  exact mean_prod (fun ψ ω => f ω ψ)

theorem mean_pi_product {G : Type} [Fintype G] {I : G → Type}
    [∀ g, Fintype (I g)] (f : ∀ g, I g → ℝ) :
    paperMean (fun x : ∀ g, I g => ∏ g, f g (x g)) =
      ∏ g, paperMean (f g) := by
  classical
  exact P2a.paperMean_piProduct f

theorem mean_cs {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    paperMean (fun ω => f ω * g ω) ^ 2 ≤
      paperMean (fun ω => f ω ^ 2) * paperMean (fun ω => g ω ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hs := mul_le_mul_of_nonneg_left h
    (sq_nonneg ((Fintype.card Ω : ℝ)⁻¹))
  unfold paperMean
  calc
    ((Fintype.card Ω : ℝ)⁻¹ * ∑ x, f x * g x) ^ 2 =
        ((Fintype.card Ω : ℝ)⁻¹) ^ 2 * (∑ x, f x * g x) ^ 2 := by ring
    _ ≤ ((Fintype.card Ω : ℝ)⁻¹) ^ 2 *
        ((∑ x, f x ^ 2) * ∑ x, g x ^ 2) := hs
    _ = ((Fintype.card Ω : ℝ)⁻¹ * ∑ x, f x ^ 2) *
        ((Fintype.card Ω : ℝ)⁻¹ * ∑ x, g x ^ 2) := by ring

@[simp] theorem probability_nonneg {Ω : Type} [Fintype Ω]
    (A : Ω → Prop) : 0 ≤ finiteUniformProbability A := by
  apply mean_nonneg
  intro ω
  split_ifs <;> norm_num

theorem probability_le_one {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) : finiteUniformProbability A ≤ 1 := by
  calc
    finiteUniformProbability A ≤ paperMean (fun _ : Ω => (1 : ℝ)) := by
      apply paperMean_mono
      intro ω
      split_ifs <;> norm_num
    _ = 1 := mean_const 1

theorem probability_exists_le_sum {Ω J : Type} [Fintype Ω] [Fintype J]
    (A : J → Ω → Prop) :
    finiteUniformProbability (fun ω => ∃ j, A j ω) ≤
      ∑ j, finiteUniformProbability (A j) := by
  calc
    finiteUniformProbability (fun ω => ∃ j, A j ω) ≤
        paperMean (fun ω => ∑ j : J, if A j ω then (1 : ℝ) else 0) := by
      apply paperMean_mono
      intro ω
      by_cases h : ∃ j, A j ω
      · obtain ⟨j, hj⟩ := h
        rw [if_pos ⟨j, hj⟩]
        have hterm := Finset.single_le_sum
          (s := (Finset.univ : Finset J))
          (f := fun j => if A j ω then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
        simpa only [if_pos hj] using hterm
      · rw [if_neg h]
        exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
    _ = ∑ j, finiteUniformProbability (A j) := by
      rw [paperMean_sum]
      rfl

/-- Finite-uniform Paley--Zygmund at one half of the mean. -/
theorem paley_zygmund_half {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (C : ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hμ : 0 < paperMean X) (hC : 0 < C)
    (hM : paperMean (fun ω => X ω ^ 2) ≤ C * paperMean X ^ 2) :
    1 / (4 * C) ≤
      finiteUniformProbability (fun ω => paperMean X / 2 ≤ X ω) := by
  let μ := paperMean X
  let A : Ω → Prop := fun ω => μ / 2 ≤ X ω
  let I : Ω → ℝ := fun ω => if A ω then 1 else 0
  let T := paperMean (fun ω => X ω * I ω)
  let p := finiteUniformProbability A
  have hμ' : 0 < μ := hμ
  have hp : 0 ≤ p := probability_nonneg A
  have hT : μ / 2 ≤ T := by
    have hpoint : ∀ ω, X ω ≤ μ / 2 + X ω * I ω := by
      intro ω
      by_cases h : A ω
      · simp only [I, if_pos h, mul_one]
        linarith
      · have hn : X ω < μ / 2 := lt_of_not_ge h
        simp only [I, if_neg h, mul_zero, add_zero]
        exact hn.le
    have h := paperMean_mono hpoint
    rw [mean_add, mean_const] at h
    change μ ≤ μ / 2 + T at h
    linarith
  have hI : paperMean (fun ω => I ω ^ 2) = p := by
    change paperMean (fun ω => (if A ω then (1 : ℝ) else 0) ^ 2) =
      paperMean (fun ω => if A ω then (1 : ℝ) else 0)
    congr 1
    funext ω
    split_ifs <;> norm_num
  have hCS : T ^ 2 ≤ paperMean (fun ω => X ω ^ 2) * p := by
    have h := mean_cs X I
    rw [hI] at h
    exact h
  have hBound : T ^ 2 ≤ (C * μ ^ 2) * p :=
    hCS.trans (mul_le_mul_of_nonneg_right hM hp)
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ μ / 2) hT 2
  have hμsq : 0 < μ ^ 2 := sq_pos_of_pos hμ'
  have hcancel : μ ^ 2 * 1 ≤ μ ^ 2 * (4 * C * p) := by
    nlinarith [hs, hBound]
  have hone : 1 ≤ 4 * C * p := by
    nlinarith [hcancel]
  change 1 / (4 * C) ≤ p
  apply (div_le_iff₀ (by positivity : 0 < 4 * C)).2
  nlinarith

/-- The subtraction step uses actual event inclusion, not conditioning on A. -/
theorem probability_trim {Ω J : Type} [Fintype Ω] [Fintype J]
    (A B : Ω → Prop) (E : J → Ω → Prop) :
    finiteUniformProbability A - finiteUniformProbability B -
        ∑ j, finiteUniformProbability (E j) ≤
      finiteUniformProbability (fun ω => A ω ∧ ¬ B ω ∧ ∀ j, ¬ E j ω) := by
  let H : Ω → Prop := fun ω => A ω ∧ ¬ B ω ∧ ∀ j, ¬ E j ω
  have hIncl : ∀ ω, A ω → H ω ∨ (B ω ∨ ∃ j, E j ω) := by
    intro ω hA
    by_cases hB : B ω
    · exact Or.inr (Or.inl hB)
    · by_cases hE : ∃ j, E j ω
      · exact Or.inr (Or.inr hE)
      · exact Or.inl ⟨hA, hB, fun j hj => hE ⟨j, hj⟩⟩
  have h1 := finiteUniformProbability_mono hIncl
  have h2 := finiteUniformProbability_or_le H (fun ω => B ω ∨ ∃ j, E j ω)
  have h3 := finiteUniformProbability_or_le B (fun ω => ∃ j, E j ω)
  have h4 := probability_exists_le_sum E
  dsimp only [H] at h1 h2
  linarith

theorem probability_trim_quarters {Ω J : Type} [Fintype Ω] [Fintype J]
    (A B : Ω → Prop) (E : J → Ω → Prop) (p : ℝ)
    (hA : p ≤ finiteUniformProbability A)
    (hB : finiteUniformProbability B ≤ p / 4)
    (hE : (∑ j, finiteUniformProbability (E j)) ≤ p / 4) :
    p / 2 ≤ finiteUniformProbability
      (fun ω => A ω ∧ ¬ B ω ∧ ∀ j, ¬ E j ω) := by
  have h := probability_trim A B E
  linarith

/-- One sign with the convention of the actual primitive coordinates. -/
def sign (b : Bool) : ℝ := (rademacherSign b : ℝ)

@[simp] theorem sign_false : sign false = 1 := by
  norm_num [sign, rademacherSign]
@[simp] theorem sign_true : sign true = -1 := by
  norm_num [sign, rademacherSign]
@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign, rademacherSign]

theorem sign_eq_if (b : Bool) : sign b = if b then -1 else 1 := by
  cases b <;> norm_num [sign, rademacherSign]

theorem sign_eq_neg_paperSign (b : Bool) : sign b = -paperSign b := by
  cases b <;> norm_num [sign, rademacherSign, paperSign]

theorem mean_sign_pair {I : Type} [Fintype I] (i j : I) :
    paperMean (fun w : I → Bool => sign (w i) * sign (w j)) =
      if i = j then 1 else 0 := by
  classical
  simp_rw [sign_eq_neg_paperSign, neg_mul_neg]
  exact paperMean_paperSign_mul_paperSign i j

/-- One coordinate is read from each group; neither groups nor coordinates
are collapsed when their numeric labels coincide. -/
def character {G : Type} [Fintype G] {I : G → Type}
    (x : ∀ g, I g) (w : ∀ g, I g → Bool) : ℝ :=
  ∏ g, sign (w g (x g))

@[simp] theorem character_sq {G : Type} [Fintype G] {I : G → Type}
    (x : ∀ g, I g) (w : ∀ g, I g → Bool) : character x w ^ 2 = 1 := by
  unfold character
  rw [pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro g _
  simpa only [pow_two] using sign_sq (w g (x g))

theorem character_orthogonal {G : Type} [Fintype G]
    {I : G → Type} [∀ g, Fintype (I g)] (x y : ∀ g, I g) :
    paperMean (fun w : ∀ g, I g → Bool => character x w * character y w) =
      if x = y then 1 else 0 := by
  classical
  calc
    _ = paperMean (fun w : ∀ g, I g → Bool =>
        ∏ g, sign (w g (x g)) * sign (w g (y g))) := by
      simp only [character, Finset.prod_mul_distrib]
    _ = ∏ g, paperMean (fun w : I g → Bool =>
        sign (w (x g)) * sign (w (y g))) := by
      simpa using
        (mean_pi_product (G := G) (I := fun g => I g → Bool)
          (fun g w => sign (w (x g)) * sign (w (y g))))
    _ = ∏ g, if x g = y g then (1 : ℝ) else 0 := by
      simp_rw [mean_sign_pair]
    _ = if x = y then 1 else 0 := by
      by_cases h : x = y
      · subst y
        simp
      · rw [if_neg h]
        have hex : ∃ g, x g ≠ y g := by
          by_contra hn
          apply h
          funext g
          by_contra hg
          exact hn ⟨g, hg⟩
        obtain ⟨g, hg⟩ := hex
        exact Finset.prod_eq_zero (Finset.mem_univ g) (if_neg hg)

/-- Exact second moment of any injectively indexed family of grouped
characters. Injectivity is proved from the graph before this is instantiated. -/
theorem sparse_second {G U : Type} [Fintype G] [Fintype U]
    {I : G → Type} [∀ g, Fintype (I g)]
    (key : U → ∀ g, I g) (hkey : Function.Injective key) (a : U → ℝ) :
    paperMean (fun w : ∀ g, I g → Bool =>
      (∑ u, a u * character (key u) w) ^ 2) = ∑ u, a u ^ 2 := by
  classical
  have hexpand : ∀ w : ∀ g, I g → Bool,
      (∑ u, a u * character (key u) w) ^ 2 =
        ∑ u, ∑ v, (a u * a v) * (character (key u) w * character (key v) w) := by
    intro w
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  simp_rw [hexpand]
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [paperMean_sum]
  simp_rw [mean_mul_left, character_orthogonal]
  have heq : ∀ v, key u = key v ↔ u = v := fun v => hkey.eq_iff
  simp only [heq]
  simp [pow_two]

end GraphMatrixReplica.P1AD
