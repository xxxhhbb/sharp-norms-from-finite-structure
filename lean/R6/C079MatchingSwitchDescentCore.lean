import R6.C079MatchingSwitch
import R6.C079MatchingDistanceFaithful

/-! # A target-guided switch preserves the old intersection

If `a,b` are paired by the target matching and `b,c` by the current
matching, then every function constant on both old matchings has equal values
at `a,c`.  Swapping these two coordinates therefore leaves such a function
constant on the switched current matching.  This is the inclusion half of
the strict-descent argument; strictness requires the two-point-block
indicator witness and is not asserted here.
-/

noncomputable section

namespace GraphMatrixReplica

private theorem function_swap_eq_of_values_eq {α : Type*} [DecidableEq α]
    {β : Type*} (f : α → β) (a c : α) (hac : f a = f c) :
    ∀ x, f ((Equiv.swap a c) x) = f x := by
  intro x
  by_cases hxa : x = a
  · subst x
    simp [hac]
  by_cases hxc : x = c
  · subst x
    simp [hac]
  · simp [Equiv.swap_apply_of_ne_of_ne hxa hxc]

/-- Switching along one target pair and one current pair cannot reduce the
intersection of their constant-vector subspaces. -/
theorem c079_targetGuidedSwitch_intersection_mono {m : ℕ}
    (σ τ : C079MatchingPartition m) (a b c : Replica m)
    (hτ : τ.1.r a b) (hσ : σ.1.r b c) :
    partitionConstantSubspace (K := ℚ) σ.1 ⊓
        partitionConstantSubspace (K := ℚ) τ.1 ≤
      partitionConstantSubspace (K := ℚ) (σ.switchPoints a c).1 ⊓
        partitionConstantSubspace (K := ℚ) τ.1 := by
  intro f hf
  have hac : (f : Replica m → ℚ) a = f c :=
    (hf.2 a b hτ).trans (hf.1 b c hσ)
  have hswap := function_swap_eq_of_values_eq (f : Replica m → ℚ) a c hac
  constructor
  · intro x y hxy
    have hrel := (c079_switchPoints_rel_iff σ a c x y).mp hxy
    calc
      (f : Replica m → ℚ) x = f ((Equiv.swap a c) x) := (hswap x).symm
      _ = f ((Equiv.swap a c) y) := hf.1 _ _ hrel
      _ = f y := hswap y
  · exact hf.2

/-- A matching block containing two distinct specified points contains
exactly those two points. -/
theorem c079_matching_pair_block_iff {m : ℕ}
    (σ : C079MatchingPartition m) (a b x : Replica m)
    (hab : σ.1.r a b) (hne : a ≠ b) :
    σ.1.r a x ↔ x = a ∨ x = b := by
  obtain ⟨ρ, hρ⟩ := σ.2
  rw [← hρ] at hab ⊢
  let e := ρ.pairingEquiv.symm
  have habKey : (e a).1 = (e b).1 := hab
  have hneE : e a ≠ e b := fun he => hne (e.injective he)
  constructor
  · intro hax
    have haxKey : (e a).1 = (e x).1 := hax
    have hor : e x = e a ∨ e x = e b := by
      cases ha : e a with
      | mk ka ba =>
        cases hb : e b with
        | mk kb bb =>
          cases hx : e x with
          | mk kx bx =>
            have hkb : ka = kb := by simpa [ha, hb] using habKey
            have hkx : ka = kx := by simpa [ha, hx] using haxKey
            have hbb : ba ≠ bb := by
              intro he
              apply hneE
              simp [ha, hb, hkb, he]
            subst kb
            subst kx
            cases ba <;> cases bb <;> cases bx <;> simp_all
    rcases hor with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective h)
  · intro hx
    rcases hx with hx | hx
    · rw [hx]
    · rw [hx]
      exact hab

/-- When the target pair `a,b` crosses two current pairs and `c` is the
current partner of `b`, its indicator belongs to the new intersection but
not the old one. -/
theorem c079_targetGuidedSwitch_strictWitness {m : ℕ}
    (σ τ : C079MatchingPartition m) (a b c : Replica m)
    (hτ : τ.1.r a b) (hnot : ¬ σ.1.r a b)
    (hσ : σ.1.r b c) (hbc : b ≠ c) :
    ∃ g : Replica m → ℚ,
      g ∈ partitionConstantSubspace (K := ℚ) (σ.switchPoints a c).1 ⊓
            partitionConstantSubspace (K := ℚ) τ.1 ∧
        g ∉ partitionConstantSubspace (K := ℚ) σ.1 ⊓
            partitionConstantSubspace (K := ℚ) τ.1 := by
  classical
  have hab : a ≠ b := by
    intro he
    subst b
    exact hnot (σ.1.iseqv.refl a)
  have hac : a ≠ c := by
    intro he
    subst c
    exact hnot (σ.1.iseqv.symm hσ)
  have hcb : c ≠ b := Ne.symm hbc
  have hσnew : (σ.switchPoints a c).1.r a b := by
    apply (c079_switchPoints_rel_iff σ a c a b).2
    have hswapB : (Equiv.swap a c) b = b :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbc
    rw [Equiv.swap_apply_left, hswapB]
    exact σ.1.iseqv.symm hσ
  have hblocks : ∀ x : Replica m,
      τ.1.r a x ↔ (σ.switchPoints a c).1.r a x := by
    intro x
    exact (c079_matching_pair_block_iff τ a b x hτ hab).trans
      (c079_matching_pair_block_iff (σ.switchPoints a c) a b x hσnew hab).symm
  let g : Replica m → ℚ := fun x => if τ.1.r a x then 1 else 0
  refine ⟨g, ?_, ?_⟩
  · constructor
    · intro x y hxy
      have hiff : τ.1.r a x ↔ τ.1.r a y := by
        rw [hblocks x, hblocks y]
        constructor
        · intro hx
          exact (σ.switchPoints a c).1.iseqv.trans hx hxy
        · intro hy
          exact (σ.switchPoints a c).1.iseqv.trans hy
            ((σ.switchPoints a c).1.iseqv.symm hxy)
      change (if τ.1.r a x then (1 : ℚ) else 0) =
        (if τ.1.r a y then (1 : ℚ) else 0)
      by_cases hx : τ.1.r a x
      · simp [hx, hiff.mp hx]
      · have hy : ¬ τ.1.r a y := fun hy => hx (hiff.mpr hy)
        simp [hx, hy]
    · intro x y hxy
      have hiff : τ.1.r a x ↔ τ.1.r a y := by
        constructor
        · intro hx
          exact τ.1.iseqv.trans hx hxy
        · intro hy
          exact τ.1.iseqv.trans hy (τ.1.iseqv.symm hxy)
      change (if τ.1.r a x then (1 : ℚ) else 0) =
        (if τ.1.r a y then (1 : ℚ) else 0)
      by_cases hx : τ.1.r a x
      · simp [hx, hiff.mp hx]
      · have hy : ¬ τ.1.r a y := fun hy => hx (hiff.mpr hy)
        simp [hx, hy]
  · intro hold
    have hτb : τ.1.r a b := hτ
    have hτc : ¬ τ.1.r a c := by
      intro hc
      rcases (c079_matching_pair_block_iff τ a b c hτ hab).mp hc with hc | hc
      · exact hac hc.symm
      · exact hbc hc.symm
    have hgbc := hold.1 b c hσ
    simp [g, hτb, hτc] at hgbc

/-- A target-guided switch across a current pair strictly decreases the
intersection distance to the target. -/
theorem c079_targetGuidedSwitch_distance_lt {m : ℕ}
    (σ τ : C079MatchingPartition m) (a b c : Replica m)
    (hτ : τ.1.r a b) (hnot : ¬ σ.1.r a b)
    (hσ : σ.1.r b c) (hbc : b ≠ c) :
    c079MatchingPartitionDistance (σ.switchPoints a c) τ <
      c079MatchingPartitionDistance σ τ := by
  let old : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) σ.1 ⊓
      partitionConstantSubspace (K := ℚ) τ.1
  let new : Submodule ℚ (Replica m → ℚ) :=
    partitionConstantSubspace (K := ℚ) (σ.switchPoints a c).1 ⊓
      partitionConstantSubspace (K := ℚ) τ.1
  have hle : old ≤ new :=
    c079_targetGuidedSwitch_intersection_mono σ τ a b c hτ hσ
  obtain ⟨g, hgnew, hgnotold⟩ :=
    c079_targetGuidedSwitch_strictWitness σ τ a b c hτ hnot hσ hbc
  change g ∈ new at hgnew
  change g ∉ old at hgnotold
  have hne : old ≠ new := by
    intro he
    rw [he] at hgnotold
    exact hgnotold hgnew
  have hlt : old < new := lt_of_le_of_ne hle hne
  have hrank : Module.finrank ℚ old < Module.finrank ℚ new :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have hbound : Module.finrank ℚ new ≤ m := by
    calc
      Module.finrank ℚ new ≤
          Module.finrank ℚ
            (partitionConstantSubspace (K := ℚ) (σ.switchPoints a c).1) :=
              Submodule.finrank_mono inf_le_left
      _ = partitionBlockCount (σ.switchPoints a c).1 :=
        finrank_partitionConstantSubspace_eq_blockCount _
      _ = m := (σ.switchPoints a c).blockCount_eq
  change m - Module.finrank ℚ new < m - Module.finrank ℚ old
  omega

/-- Every point has a different partner in a matching partition. -/
theorem c079_exists_matching_partner {m : ℕ}
    (σ : C079MatchingPartition m) (a : Replica m) :
    ∃ b : Replica m, b ≠ a ∧ σ.1.r a b := by
  obtain ⟨ρ, hρ⟩ := σ.2
  let e := ρ.pairingEquiv.symm
  let b := ρ.pairingEquiv ((e a).1, !(e a).2)
  have heb : e b = ((e a).1, !(e a).2) := by
    simp [e, b]
  refine ⟨b, ?_, ?_⟩
  · intro hba
    have heq : e b = e a := congrArg e hba
    rw [heb] at heq
    cases h : e a with
    | mk k bit =>
      cases bit <;> simp [h] at heq
  · rw [← hρ]
    change (e a).1 = (e b).1
    rw [heb]

/-- Distinct matching partitions have a target pair crossing two current
pairs.  Equal block sizes prevent one matching relation from strictly
containing the other. -/
theorem c079_exists_target_pair_not_current {m : ℕ}
    (σ τ : C079MatchingPartition m) (hne : σ ≠ τ) :
    ∃ a b : Replica m, τ.1.r a b ∧ ¬ σ.1.r a b := by
  classical
  by_contra hnone
  have hle : ∀ a b : Replica m, τ.1.r a b → σ.1.r a b := by
    intro a b hτ
    by_contra hnot
    exact hnone ⟨a, b, hτ, hnot⟩
  apply hne
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  constructor
  · intro hσ
    by_cases hab : a = b
    · subst b
      exact τ.1.iseqv.refl a
    obtain ⟨c, hca, hτ⟩ := c079_exists_matching_partner τ a
    have hσac := hle a c hτ
    rcases (c079_matching_pair_block_iff σ a b c hσ hab).mp hσac with hc | hc
    · exact False.elim (hca hc)
    · rwa [hc] at hτ
  · exact hle a b

/-- Every positive matching distance admits a genuine one-letter descent. -/
theorem c079_exists_switch_distance_lt {m : ℕ}
    (σ τ : C079MatchingPartition m)
    (hpos : 0 < c079MatchingPartitionDistance σ τ) :
    ∃ a c : Replica m,
      c079MatchingPartitionDistance (σ.switchPoints a c) τ <
        c079MatchingPartitionDistance σ τ := by
  have hne : σ ≠ τ := by
    intro he
    have hz := (c079MatchingPartitionDistance_eq_zero_iff_eq σ τ).2 he
    omega
  obtain ⟨a, b, hτ, hnot⟩ := c079_exists_target_pair_not_current σ τ hne
  obtain ⟨c, hcb, hσ⟩ := c079_exists_matching_partner σ b
  exact ⟨a, c, c079_targetGuidedSwitch_distance_lt σ τ a b c
    hτ hnot hσ hcb.symm⟩

/-- Every matching partition within intersection distance `d` is reached by
an actual switch word of length at most `d`.  This is the previously missing
direction needed to put the output count around a metric ball. -/
theorem c079MatchingPartitionDistance_switchReachableWithin {m : ℕ}
    (σ τ : C079MatchingPartition m) :
    C079SwitchReachableWithin σ τ
      (c079MatchingPartitionDistance σ τ) := by
  have H : ∀ d : ℕ, ∀ υ : C079MatchingPartition m,
      c079MatchingPartitionDistance υ τ = d →
        C079SwitchReachableWithin υ τ d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro υ hd
      by_cases hzero : d = 0
      · have heq : υ = τ :=
          (c079MatchingPartitionDistance_eq_zero_iff_eq υ τ).1
            (hd.trans hzero)
        subst υ
        refine ⟨0, by omega, ⟨[], rfl⟩, ?_⟩
        rfl
      · have hpos : 0 < c079MatchingPartitionDistance υ τ := by omega
        obtain ⟨a, c, hstep⟩ := c079_exists_switch_distance_lt υ τ hpos
        let υ' := υ.switchPoints a c
        have hlt : c079MatchingPartitionDistance υ' τ < d := by
          dsimp [υ']
          omega
        obtain ⟨k, hk, word, hword⟩ :=
          ih (c079MatchingPartitionDistance υ' τ) hlt υ' rfl
        refine ⟨k + 1, by omega,
          ⟨(a, c) :: word.toList, by simp⟩, ?_⟩
        change word.toList.foldl c079ApplySwitchLetter
          (υ.switchPoints a c) = τ
        exact hword
  exact H _ σ rfl

/-- The matching partitions in the closed distance ball of radius `t`. -/
def c079MatchingMetricBall {m : ℕ}
    (σ : C079MatchingPartition m) (t : ℕ) :
    Finset (C079MatchingPartition m) := by
  classical
  letI : Fintype (ReplicaPartition m) :=
    Fintype.ofInjective (fun π : ReplicaPartition m => π.r) (by
      intro π ψ h
      apply Setoid.ext
      intro a b
      exact Iff.of_eq (congrFun (congrFun h a) b))
  letI : Fintype (C079MatchingPartition m) := inferInstance
  exact Finset.univ.filter
    (fun τ => c079MatchingPartitionDistance σ τ ≤ t)

/-- A metric ball is contained in the actual fixed-length switch-output set
when a null letter exists. -/
theorem c079MatchingMetricBall_subset_switchOutputs {m t : ℕ}
    (σ : C079MatchingPartition m) (hm : 0 < m) :
    c079MatchingMetricBall σ t ⊆ c079SwitchOutputs σ t := by
  intro τ hτ
  have hdist : c079MatchingPartitionDistance σ τ ≤ t := by
    simpa [c079MatchingMetricBall] using hτ
  let a : Replica m := (⟨0, hm⟩, false)
  obtain ⟨k, hk, word, hword⟩ :=
    c079MatchingPartitionDistance_switchReachableWithin σ τ
  exact c079SwitchReachableWithin_mem_outputs σ τ a
    ⟨k, hk.trans hdist, word, hword⟩

/-- The genuine metric ball has the paper's switch-word cardinality bound,
for positive `m`.  This follows from reachability, not from the cardinality
of the output set alone. -/
theorem c079MatchingMetricBall_card_le {m : ℕ}
    (σ : C079MatchingPartition m) (t : ℕ) (hm : 0 < m) :
    (c079MatchingMetricBall σ t).card ≤ (4 * m ^ 2) ^ t := by
  exact (Finset.card_le_card
    (c079MatchingMetricBall_subset_switchOutputs σ hm)).trans
      (c079SwitchOutputs_card_le σ t)

#print axioms c079_targetGuidedSwitch_intersection_mono
#print axioms c079_matching_pair_block_iff
#print axioms c079_targetGuidedSwitch_strictWitness
#print axioms c079_targetGuidedSwitch_distance_lt
#print axioms c079_exists_matching_partner
#print axioms c079_exists_target_pair_not_current
#print axioms c079_exists_switch_distance_lt
#print axioms c079MatchingPartitionDistance_switchReachableWithin
#print axioms c079MatchingMetricBall_subset_switchOutputs
#print axioms c079MatchingMetricBall_card_le

end GraphMatrixReplica
