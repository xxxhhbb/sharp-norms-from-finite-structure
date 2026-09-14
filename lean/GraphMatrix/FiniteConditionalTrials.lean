import GraphMatrix.HighMomentTailMarkov
import GraphMatrix.Counting.PathNoiseProductLaw

/-! A finite, explicit product sample for the synchronized-witness step.
The fresh sample `Ξ` already encodes all active components at one separator tuple.
Its one-trial success event must be justified separately from the graph model. -/

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace GraphMatrixReplica

private theorem sync_mean_one {A : Type} [Fintype A] [Nonempty A] :
    paperMean (fun _ : A => (1 : ℝ)) = 1 := by
  unfold paperMean
  simp [Fintype.card_ne_zero]

private theorem sync_prob_compl {A : Type} [Fintype A] [Nonempty A]
    (P : A → Prop) [DecidablePred P] :
    finiteUniformProbability (fun a => ¬ P a) =
      1 - finiteUniformProbability P := by
  classical
  have h : ∀ a : A,
      (if ¬ P a then (1 : ℝ) else 0) = 1 - (if P a then 1 else 0) := by
    intro a
    by_cases ha : P a <;> simp [ha]
  unfold finiteUniformProbability paperMean
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp
  have hc : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hc]

private theorem sync_prob_nonneg {A : Type} [Fintype A]
    (P : A → Prop) [DecidablePred P] :
    0 ≤ finiteUniformProbability P := by
  have h := paperMean_mono (f := fun _ : A => (0 : ℝ))
      (g := fun a => if P a then 1 else 0)
      (by intro a; split <;> norm_num)
  simpa [finiteUniformProbability, paperMean_zero] using h

private theorem sync_prob_le_one {A : Type} [Fintype A] [Nonempty A]
    (P : A → Prop) [DecidablePred P] :
    finiteUniformProbability P ≤ 1 := by
  calc
    finiteUniformProbability P ≤ paperMean (fun _ : A => (1 : ℝ)) := by
      apply paperMean_mono
      intro a
      split <;> norm_num
    _ = 1 := sync_mean_one

/-- Exact failure probability for `N` fresh, independent finite-uniform trials.
The `N=0` case gives probability one, including when success is impossible. -/
theorem sync_all_fail_probability
    {Ξ : Type} [Fintype Ξ] [Nonempty Ξ]
    (N : ℕ) (S : Ξ → Prop) [DecidablePred S] :
    finiteUniformProbability (fun v : Fin N → Ξ => ∀ i, ¬ S (v i)) =
      (1 - finiteUniformProbability S) ^ N := by
  classical
  have hpoint (v : Fin N → Ξ) :
      (if (∀ i, ¬ S (v i)) then (1 : ℝ) else 0) =
        ∏ i : Fin N, (if S (v i) then (0 : ℝ) else 1) := by
    by_cases h : ∀ i, ¬ S (v i)
    · simp [fun i => h i]
    · have hn : ¬ ∀ i, ¬ S (v i) := h
      obtain ⟨i, hi⟩ := not_forall.mp hn
      have hi' : S (v i) := Classical.not_not.mp hi
      rw [if_neg hn]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])).symm
  calc
    finiteUniformProbability (fun v : Fin N → Ξ => ∀ i, ¬ S (v i)) =
        paperMean (fun v : Fin N → Ξ =>
          ∏ i : Fin N, (if S (v i) then (0 : ℝ) else 1)) := by
            unfold finiteUniformProbability
            exact congrArg paperMean (funext hpoint)
    _ = ∏ i : Fin N, paperMean (fun ξ : Ξ => if S ξ then (0 : ℝ) else 1) :=
      paperMean_coordinateProduct
        (fun _i : Fin N => fun ξ : Ξ => if S ξ then (0 : ℝ) else 1)
    _ = (1 - finiteUniformProbability S) ^ N := by
      have hc : paperMean (fun ξ : Ξ => if S ξ then (0 : ℝ) else 1) =
          1 - finiteUniformProbability S := by
        rw [← sync_prob_compl S]
        unfold finiteUniformProbability
        congr 1
        funext ξ
        by_cases hs : S ξ <;> simp [hs]
      simp [hc]


private theorem sync_mean_prod_eq_iterated
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A × B → ℝ) :
    paperMean f =
      paperMean (fun a : A => paperMean (fun b : B => f (a, b))) := by
  unfold paperMean
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  push_cast
  rw [← Finset.mul_sum]
  ring

private theorem sync_some_success_probability
    {Ξ : Type} [Fintype Ξ] [Nonempty Ξ]
    (N : ℕ) (S : Ξ → Prop) [DecidablePred S] :
    finiteUniformProbability (fun v : Fin N → Ξ => ∃ i, S (v i)) =
      1 - (1 - finiteUniformProbability S) ^ N := by
  classical
  calc
    finiteUniformProbability (fun v : Fin N → Ξ => ∃ i, S (v i)) =
        finiteUniformProbability (fun v : Fin N → Ξ => ¬ ∀ i, ¬ S (v i)) := by
      congr 1
      funext v
      simp
    _ = 1 - finiteUniformProbability
        (fun v : Fin N → Ξ => ∀ i, ¬ S (v i)) :=
      sync_prob_compl _
    _ = 1 - (1 - finiteUniformProbability S) ^ N := by
      rw [sync_all_fail_probability]

/-- Averaging over the full internal sample after the fresh product sample.
The input lower bound is for the joint one-trial event, for every good internal
realization; it is not inferred from componentwise marginal bounds. -/
theorem sync_good_and_some_success_probability
    {I Ξ : Type} [Fintype I] [Fintype Ξ] [Nonempty I] [Nonempty Ξ]
    (N : ℕ) (G : I → Prop) (S : I → Ξ → Prop)
    [DecidablePred G] [∀ ω, DecidablePred (S ω)]
    (ρ : ℝ) (_hρ0 : 0 ≤ ρ) (_hρ1 : ρ ≤ 1)
    (hsingle : ∀ ω, G ω → ρ ≤ finiteUniformProbability (S ω)) :
    finiteUniformProbability
        (fun x : I × (Fin N → Ξ) => G x.1 ∧ ∃ i, S x.1 (x.2 i)) ≥
      finiteUniformProbability G * (1 - (1 - ρ) ^ N) := by
  classical
  let p : I → ℝ := fun ω => finiteUniformProbability (S ω)
  have hinner (ω : I) :
      paperMean (fun v : Fin N → Ξ =>
        if G ω ∧ (∃ i, S ω (v i)) then (1 : ℝ) else 0) =
        if G ω then 1 - (1 - p ω) ^ N else 0 := by
    by_cases hg : G ω
    · simp only [hg, true_and, if_true]
      exact sync_some_success_probability N (S ω)
    · simp [hg, paperMean_zero]
  have hpoint (ω : I) :
      (if G ω then 1 - (1 - ρ) ^ N else 0) ≤
        (if G ω then 1 - (1 - p ω) ^ N else 0) := by
    by_cases hg : G ω
    · simp only [hg, if_true]
      have hp1 : p ω ≤ 1 := sync_prob_le_one (S ω)
      have hbase0 : 0 ≤ 1 - p ω := by linarith
      have hbase : 1 - p ω ≤ 1 - ρ := by
        have := hsingle ω hg
        dsimp [p] at *
        linarith
      have hpow := pow_le_pow_left₀ hbase0 hbase N
      linarith
    · simp [hg]
  have hfactor :
      paperMean (fun ω : I => if G ω then 1 - (1 - ρ) ^ N else 0) =
        finiteUniformProbability G * (1 - (1 - ρ) ^ N) := by
    unfold finiteUniformProbability paperMean
    have hh (ω : I) :
        (if G ω then 1 - (1 - ρ) ^ N else 0) =
          (if G ω then (1 : ℝ) else 0) * (1 - (1 - ρ) ^ N) := by
      by_cases hg : G ω <;> simp [hg]
    simp_rw [hh]
    rw [← Finset.sum_mul]
    ring
  calc
    finiteUniformProbability
        (fun x : I × (Fin N → Ξ) => G x.1 ∧ ∃ i, S x.1 (x.2 i)) =
        paperMean (fun ω : I =>
          paperMean (fun v : Fin N → Ξ =>
            if G ω ∧ (∃ i, S ω (v i)) then (1 : ℝ) else 0)) := by
      unfold finiteUniformProbability
      exact sync_mean_prod_eq_iterated _
    _ = paperMean (fun ω : I => if G ω then 1 - (1 - p ω) ^ N else 0) := by
      exact congrArg paperMean (funext hinner)
    _ ≥ paperMean (fun ω : I => if G ω then 1 - (1 - ρ) ^ N else 0) :=
      paperMean_mono hpoint
    _ = finiteUniformProbability G * (1 - (1 - ρ) ^ N) := hfactor


/-- Deterministic threshold-to-expectation transfer.  In the manuscript,
`F` is the maximum of the nonnegative witness values over separator tuples;
the graph-specific proof must show that a successful tuple forces `T ≤ F`. -/
theorem sync_expected_max_lower_of_success
    {I Ξ : Type} [Fintype I] [Fintype Ξ] [Nonempty I] [Nonempty Ξ]
    (N : ℕ) (G : I → Prop) (S : I → Ξ → Prop)
    [DecidablePred G] [∀ ω, DecidablePred (S ω)]
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hsingle : ∀ ω, G ω → ρ ≤ finiteUniformProbability (S ω))
    (F : I × (Fin N → Ξ) → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hF0 : ∀ x, 0 ≤ F x)
    (hFsuccess : ∀ ω v, G ω → (∃ i, S ω (v i)) → T ≤ F (ω, v)) :
    T * (finiteUniformProbability G * (1 - (1 - ρ) ^ N)) ≤
      paperMean F := by
  classical
  let E : I × (Fin N → Ξ) → Prop :=
    fun x => G x.1 ∧ ∃ i, S x.1 (x.2 i)
  have hprob : finiteUniformProbability G * (1 - (1 - ρ) ^ N) ≤
      finiteUniformProbability E :=
    sync_good_and_some_success_probability N G S ρ hρ0 hρ1 hsingle
  have hpoint (x : I × (Fin N → Ξ)) :
      T * (if E x then (1 : ℝ) else 0) ≤ F x := by
    rcases x with ⟨ω, v⟩
    by_cases he : E (ω, v)
    · obtain ⟨hg, hs⟩ := he
      simpa [E, hg, hs] using hFsuccess ω v hg hs
    · simpa [E, he] using hF0 (ω, v)
  have hscale :
      paperMean (fun x : I × (Fin N → Ξ) =>
        T * (if E x then (1 : ℝ) else 0)) =
        T * finiteUniformProbability E := by
    unfold finiteUniformProbability paperMean
    rw [← Finset.mul_sum]
    ring
  calc
    T * (finiteUniformProbability G * (1 - (1 - ρ) ^ N)) ≤
        T * finiteUniformProbability E :=
      mul_le_mul_of_nonneg_left hprob hT
    _ = paperMean (fun x : I × (Fin N → Ξ) =>
          T * (if E x then (1 : ℝ) else 0)) := hscale.symm
    _ ≤ paperMean F := paperMean_mono hpoint


end GraphMatrixReplica
