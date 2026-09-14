import R6.P1ADHilbertMoments

/-!
# Finite grouped-sign moments, with all mixed square terms retained

A group is a complete independent array. Coordinates are read from that
array by their actual typed address. The induction enlarges the deterministic
Euclidean target when it integrates a group; it never replaces repeated reads
of one address by independent variables.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
open GraphMatrixReplica.PaperR16
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

/-- A finite, vector-valued, fully multilinear grouped-sign polynomial. -/
def chaos {G T : Type} [Fintype G] {I : G → Type}
    [∀ g, Fintype (I g)] (a : T → (∀ g, I g) → ℝ)
    (w : ∀ g, I g → Bool) (t : T) : ℝ :=
  ∑ x : ∀ g, I g, a t x * character x w

/-- Deterministic squared coefficient energy, before taking any moments. -/
def energy {T X : Type} [Fintype T] [Fintype X]
    (a : T → X → ℝ) : ℝ := ∑ t, ∑ x, a t x ^ 2

theorem energy_nonneg {T X : Type} [Fintype T] [Fintype X]
    (a : T → X → ℝ) : 0 ≤ energy a := by
  exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun x _ => sq_nonneg _

theorem sum_pi_fin_succ {n : ℕ} (I : Fin (n + 1) → Type)
    [∀ g, Fintype (I g)] (f : (∀ g, I g) → ℝ) :
    (∑ x : ∀ g, I g, f x) =
      ∑ i : I 0, ∑ x : ∀ g : Fin n, I g.succ, f (Fin.cons i x) := by
  calc
    _ = ∑ z : I 0 × (∀ g : Fin n, I g.succ),
        f ((Fin.consEquiv I) z) := (Equiv.sum_comp (Fin.consEquiv I) f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

theorem character_cons {n : ℕ} {I : Fin (n + 1) → Type}
    (i : I 0) (x : ∀ g : Fin n, I g.succ)
    (w0 : I 0 → Bool) (w : ∀ g : Fin n, I g.succ → Bool) :
    character (Fin.cons i x) (Fin.cons w0 w) =
      sign (w0 i) * character x w := by
  simp only [character, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem chaos_cons {n : ℕ} {T : Type}
    {I : Fin (n + 1) → Type} [∀ g, Fintype (I g)]
    (a : T → (∀ g, I g) → ℝ)
    (w0 : I 0 → Bool) (w : ∀ g : Fin n, I g.succ → Bool) (t : T) :
    chaos a (Fin.cons w0 w) t =
      ∑ i : I 0, sign (w0 i) *
        chaos (fun it : I 0 × T => fun x => a it.2 (Fin.cons it.1 x)) w (i, t) := by
  letI : DecidableEq (Fin (n + 1)) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  unfold chaos
  calc
    _ = ∑ z : I 0 × (∀ g : Fin n, I g.succ),
        a t ((Fin.consEquiv I) z) *
          character ((Fin.consEquiv I) z) (Fin.cons w0 w) :=
      (Equiv.sum_comp (Fin.consEquiv I)
        (fun x => a t x * character x (Fin.cons w0 w))).symm
    _ = ∑ i : I 0, ∑ x : ∀ g : Fin n, I g.succ,
        a t (Fin.cons i x) * character (Fin.cons i x) (Fin.cons w0 w) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [character_cons]
      ring

/-- Tensorization on the actual complete product sample. Each eliminated
array adds its label coordinate to the Euclidean target. -/
theorem grouped_moment_fin (n : ℕ) (I : Fin n → Type)
    [∀ g, Fintype (I g)] {T : Type} [Fintype T]
    (a : T → (∀ g, I g) → ℝ) (q : ℕ) (hq : q ≤ 16) :
    paperMean (fun w : ∀ g, I g → Bool => euclideanSq (chaos a w) ^ q) ≤
      (32 : ℝ) ^ (q * n) * energy a ^ q := by
  induction n generalizing T q with
  | zero =>
      letI : Unique (∀ g : Fin 0, I g) :=
        { default := fun g => Fin.elim0 g
          uniq := fun x => funext fun g => Fin.elim0 g }
      letI : Unique (∀ g : Fin 0, I g → Bool) :=
        { default := fun g => Fin.elim0 g
          uniq := fun w => funext fun g => Fin.elim0 g }
      simp [chaos, character, energy, euclideanSq]
  | succ n ih =>
      let J : Fin n → Type := fun g => I g.succ
      let a' : (I 0 × T) → (∀ g, J g) → ℝ :=
        fun it x => a it.2 (Fin.cons it.1 x)
      let F : (∀ g, J g → Bool) → I 0 → T → ℝ :=
        fun w i t => chaos a' w (i, t)
      have hSplit (w0 : I 0 → Bool) (w : ∀ g, J g → Bool) :
          chaos a (Fin.cons w0 w) = fun t => ∑ i, sign (w0 i) * F w i t := by
        funext t
        exact chaos_cons a w0 w t
      have hSq (w : ∀ g, J g → Bool) :
          (∑ i : I 0, euclideanSq (F w i)) = euclideanSq (chaos a' w) := by
        simp only [euclideanSq, Fintype.sum_prod_type, F]
      have hEnergy : energy a' = energy a := by
        unfold energy
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        exact (sum_pi_fin_succ I (fun x => a t x ^ 2)).symm
      calc
        _ = paperMean (fun z : (I 0 → Bool) × (∀ g, J g → Bool) =>
            euclideanSq (chaos a (Fin.cons z.1 z.2)) ^ q) := by
          exact (paperMean_equiv (Fin.consEquiv (fun g => I g → Bool)) _).symm
        _ = paperMean (fun w : ∀ g, J g → Bool =>
            paperMean (fun w0 : I 0 → Bool =>
              euclideanSq (fun t => ∑ i, sign (w0 i) * F w i t) ^ q)) := by
          rw [mean_prod_swap (fun w0 w =>
            euclideanSq (chaos a (Fin.cons w0 w)) ^ q)]
          simp only [hSplit]
          rfl
        _ ≤ paperMean (fun w : ∀ g, J g → Bool =>
            (32 : ℝ) ^ q * euclideanSq (chaos a' w) ^ q) := by
          apply paperMean_mono
          intro w
          simpa only [hSq] using hilbert_sign_moment (F w) q hq
        _ = (32 : ℝ) ^ q * paperMean (fun w : ∀ g, J g → Bool =>
            euclideanSq (chaos a' w) ^ q) := mean_mul_left _ _
        _ ≤ (32 : ℝ) ^ q * ((32 : ℝ) ^ (q * n) * energy a' ^ q) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact ih J a' q hq
        _ = (32 : ℝ) ^ (q * (n + 1)) * energy a ^ q := by
          rw [hEnergy, Nat.mul_succ, pow_add]
          ring

/-- No ordering, equal-dimension convention, or nonemptiness assumption on
an individual label set is introduced by enumerating the finite group set. -/
theorem grouped_moment {G T : Type} [Fintype G] [Fintype T]
    {I : G → Type} [∀ g, Fintype (I g)]
    (a : T → (∀ g, I g) → ℝ) (q : ℕ) (hq : q ≤ 16) :
    paperMean (fun w : ∀ g, I g → Bool => euclideanSq (chaos a w) ^ q) ≤
      (32 : ℝ) ^ (q * Fintype.card G) * energy a ^ q := by
  classical
  let n := Fintype.card G
  let e : Fin n ≃ G := (Fintype.equivFin G).symm
  let J : Fin n → Type := fun i => I (e i)
  let π : (∀ i, J i) ≃ (∀ g, I g) := Equiv.piCongrLeft I e
  let φ : (∀ i, J i → Bool) ≃ (∀ g, I g → Bool) :=
    Equiv.piCongrLeft (fun g => I g → Bool) e
  let a' : T → (∀ i, J i) → ℝ := fun t x => a t (π x)
  have hChar (x : ∀ g, I g) (w : ∀ g, I g → Bool) :
      character (π.symm x) (φ.symm w) = character x w := by
    change (∏ i : Fin n, sign (w (e i) (x (e i)))) =
      ∏ g : G, sign (w g (x g))
    exact Equiv.prod_comp e (fun g => sign (w g (x g)))
  have hChaos (w : ∀ g, I g → Bool) :
      chaos a' (φ.symm w) = chaos a w := by
    letI : DecidableEq (Fin n) := Classical.decEq _
    funext t
    unfold chaos
    calc
      _ = ∑ x, a t (π x) * character (π x) w := by
        apply Finset.sum_congr rfl
        intro x _
        have hh := hChar (π x) w
        simpa only [a', Equiv.symm_apply_apply] using
          congrArg (fun r : ℝ => a t (π x) * r) hh
      _ = _ := Equiv.sum_comp π (fun x => a t x * character x w)
  have hEnergy : energy a' = energy a := by
    unfold energy
    apply Finset.sum_congr rfl
    intro t _
    exact Equiv.sum_comp π (fun x => a t x ^ 2)
  have hMean :
      paperMean (fun w : ∀ g, I g → Bool => euclideanSq (chaos a w) ^ q) =
        paperMean (fun w : ∀ i, J i → Bool => euclideanSq (chaos a' w) ^ q) := by
    simpa only [hChaos] using
      paperMean_equiv φ.symm (fun w => euclideanSq (chaos a' w) ^ q)
  rw [hMean]
  have h := grouped_moment_fin n J a' q hq
  simpa only [hEnergy] using h

/-- Push a sparse coefficient family into the full tensor address type.
Equal addresses are explicitly summed rather than silently separated. -/
def pushCoefficient {U X : Type} [Fintype U]
    (key : U → X) (a : U → ℝ) (x : X) : ℝ :=
  ∑ u, if key u = x then a u else 0

theorem pushCoefficient_at_key {U X : Type} [Fintype U]
    (key : U → X) (hk : Function.Injective key) (a : U → ℝ) (u : U) :
    pushCoefficient key a (key u) = a u := by
  classical
  simp [pushCoefficient, hk.eq_iff]

theorem pushCoefficient_sq {U X : Type} [Fintype U]
    (key : U → X) (hk : Function.Injective key) (a : U → ℝ) (x : X) :
    pushCoefficient key a x ^ 2 =
      ∑ u, if key u = x then a u ^ 2 else 0 := by
  classical
  by_cases hx : ∃ u, key u = x
  · obtain ⟨u, rfl⟩ := hx
    simp [pushCoefficient, hk.eq_iff]
  · have hne : ∀ u, key u ≠ x := fun u h => hx ⟨u, h⟩
    simp [pushCoefficient, hne]

theorem pushCoefficient_energy {U X : Type} [Fintype U] [Fintype X]
    (key : U → X) (hk : Function.Injective key) (a : U → ℝ) :
    (∑ x, pushCoefficient key a x ^ 2) = ∑ u, a u ^ 2 := by
  classical
  simp_rw [pushCoefficient_sq key hk]
  rw [Finset.sum_comm]
  simp

theorem pushCoefficient_sum {U X : Type} [Fintype U] [Fintype X]
    (key : U → X) (a : U → ℝ) (f : X → ℝ) :
    (∑ x, pushCoefficient key a x * f x) = ∑ u, a u * f (key u) := by
  classical
  calc
    _ = ∑ x, ∑ u, if key u = x then a u * f x else 0 := by
      simp only [pushCoefficient, Finset.sum_mul, ite_mul, zero_mul]
    _ = ∑ u, ∑ x, if key u = x then a u * f x else 0 := Finset.sum_comm
    _ = _ := by simp

/-- Sparse vector moment inequality. Injectivity is only within each fixed
Euclidean output index; no orthogonality between different outputs is used. -/
theorem sparse_vector_moment {G T U : Type}
    [Fintype G] [Fintype T] [Fintype U]
    {I : G → Type} [∀ g, Fintype (I g)]
    (key : T → U → ∀ g, I g)
    (hk : ∀ t, Function.Injective (key t))
    (a : T → U → ℝ) (q : ℕ) (hq : q ≤ 16) :
    paperMean (fun w : ∀ g, I g → Bool =>
      (∑ t, (∑ u, a t u * character (key t u) w) ^ 2) ^ q) ≤
      (32 : ℝ) ^ (q * Fintype.card G) * energy a ^ q := by
  classical
  let b : T → (∀ g, I g) → ℝ := fun t => pushCoefficient (key t) (a t)
  have hChaos (w : ∀ g, I g → Bool) :
      chaos b w = fun t => ∑ u, a t u * character (key t u) w := by
    funext t
    exact pushCoefficient_sum (key t) (a t) (fun x => character x w)
  have hEnergy : energy b = energy a := by
    unfold energy
    apply Finset.sum_congr rfl
    intro t _
    exact pushCoefficient_energy (key t) (hk t) (a t)
  have h := grouped_moment b q hq
  simpa only [hChaos, hEnergy, euclideanSq] using h

theorem sparse_scalar_moment {G U : Type} [Fintype G] [Fintype U]
    {I : G → Type} [∀ g, Fintype (I g)]
    (key : U → ∀ g, I g) (hk : Function.Injective key)
    (a : U → ℝ) (q : ℕ) (hq : q ≤ 16) :
    paperMean (fun w : ∀ g, I g → Bool =>
      |∑ u, a u * character (key u) w| ^ (2 * q)) ≤
      (32 : ℝ) ^ (q * Fintype.card G) * (∑ u, a u ^ 2) ^ q := by
  have h := sparse_vector_moment (T := PUnit)
    (fun _ => key) (fun _ => hk) (fun _ => a) q hq
  simpa only [energy, Fintype.sum_unique, pow_mul, sq_abs] using h

#print axioms grouped_moment
#print axioms sparse_vector_moment
#print axioms sparse_scalar_moment
end GraphMatrixReplica.P1AD
