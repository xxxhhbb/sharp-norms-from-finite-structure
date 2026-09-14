import R6.C079MatchingPartition
import Mathlib.Data.Fintype.BigOperators

/-! # C079 two-point switches and finite record counts

Swapping two replica points in the output of a pairing equivalence replaces
two cross-pair endpoints (or is a null move when the points coincide or lie
in one pair).  The alphabet is a pair of replica points and has exactly
`(2m)^2 = 4m^2` letters.  Records are counted on the nonredundant matching-
partition subtype, not on enumerated `PerfectMatching` values.

This file does not identify the partition-intersection distance with the
shortest number of such switches.  That equivalence is a separate paper
obligation before the output count can be called a metric-ball bound.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Swap two replica points in the image of a pairing equivalence.  As a
permutation of endpoints this is a two-pair switch whenever the points lie
in different matched pairs. -/
def PerfectMatching.switchPoints {m : ℕ} (ρ : PerfectMatching m)
    (a b : Replica m) : PerfectMatching m :=
  ⟨ρ.pairingEquiv.trans (Equiv.swap a b)⟩

/-- Intrinsic effect of a two-point switch on pair equivalence. -/
theorem PerfectMatching.switchPoints_rel_iff {m : ℕ}
    (ρ : PerfectMatching m) (a b x y : Replica m) :
    (ρ.switchPoints a b).partition.r x y ↔
      ρ.partition.r ((Equiv.swap a b) x) ((Equiv.swap a b) y) := by
  change ((ρ.pairingEquiv.trans (Equiv.swap a b)).symm x).1 =
      ((ρ.pairingEquiv.trans (Equiv.swap a b)).symm y).1 ↔
    (ρ.pairingEquiv.symm ((Equiv.swap a b) x)).1 =
      (ρ.pairingEquiv.symm ((Equiv.swap a b) y)).1
  rfl

/-- A switch on the nonredundant matching-partition space.  A witness of
matchability is chosen only internally; the returned value is a partition. -/
def C079MatchingPartition.switchPoints {m : ℕ}
    (σ : C079MatchingPartition m) (a b : Replica m) :
    C079MatchingPartition m :=
  ((Classical.choose σ.2).switchPoints a b).toC079MatchingPartition

/-- The subtype switch depends only on the matching partition, not on the
internal enumeration chosen to witness matchability. -/
theorem c079_switchPoints_rel_iff {m : ℕ}
    (σ : C079MatchingPartition m) (a b x y : Replica m) :
    (σ.switchPoints a b).1.r x y ↔
      σ.1.r ((Equiv.swap a b) x) ((Equiv.swap a b) y) := by
  have hρ := Classical.choose_spec σ.2
  change ((Classical.choose σ.2).switchPoints a b).partition.r x y ↔
    σ.1.r ((Equiv.swap a b) x) ((Equiv.swap a b) y)
  exact (PerfectMatching.switchPoints_rel_iff
    (Classical.choose σ.2) a b x y).trans (by rw [hρ])

/-- A switch always remains a matching partition, by construction. -/
theorem c079_switchPoints_is_matching {m : ℕ}
    (σ : C079MatchingPartition m) (a b : Replica m) :
    ∃ ρ : PerfectMatching m,
      ρ.partition = (σ.switchPoints a b).1 :=
  (σ.switchPoints a b).2

/-- Swapping a point with itself is a null operation. -/
theorem c079_switchPoints_self {m : ℕ}
    (σ : C079MatchingPartition m) (a : Replica m) :
    σ.switchPoints a a = σ := by
  apply Subtype.ext
  have hρ := Classical.choose_spec σ.2
  change ((Classical.choose σ.2).switchPoints a a).partition = σ.1
  have hsame : ((Classical.choose σ.2).switchPoints a a).partition =
      (Classical.choose σ.2).partition := by
    apply Setoid.ext
    intro x y
    change (((Classical.choose σ.2).pairingEquiv.trans
      (Equiv.swap a a)).symm x).1 =
        (((Classical.choose σ.2).pairingEquiv.trans
          (Equiv.swap a a)).symm y).1 ↔
      ((Classical.choose σ.2).pairingEquiv.symm x).1 =
        ((Classical.choose σ.2).pairingEquiv.symm y).1
    rw [Equiv.swap_self]
    rfl
  exact hsame.trans hρ

/-- An ordered pair of points specifies one switch; the diagonal letters
will be used as null operations for fixed-length padding. -/
abbrev C079SwitchLetter (m : ℕ) := Replica m × Replica m

theorem c079_switchLetter_card (m : ℕ) :
    Fintype.card (C079SwitchLetter m) = 4 * m ^ 2 := by
  simp [C079SwitchLetter, Replica, Fintype.card_prod]
  ring

/-- A record with exactly `t` switch letters. -/
abbrev C079SwitchWord (m t : ℕ) := List.Vector (C079SwitchLetter m) t

/-- Apply one letter of a switch record. -/
def c079ApplySwitchLetter {m : ℕ}
    (σ : C079MatchingPartition m) (letter : C079SwitchLetter m) :
    C079MatchingPartition m :=
  σ.switchPoints letter.1 letter.2

/-- Decode a fixed-length switch record from an initial matching partition. -/
def c079DecodeSwitchWord {m t : ℕ}
    (σ : C079MatchingPartition m) (word : C079SwitchWord m t) :
    C079MatchingPartition m :=
  word.toList.foldl c079ApplySwitchLetter σ

/-- Pad a word on the right by diagonal (null) letters. -/
def c079PadSwitchWord {m t : ℕ}
    (word : C079SwitchWord m t) (extra : ℕ)
    (a : Replica m) : C079SwitchWord m (t + extra) :=
  ⟨word.toList ++ List.replicate extra (a, a), by simp⟩

theorem c079ApplySwitchLetter_diag {m : ℕ}
    (σ : C079MatchingPartition m) (a : Replica m) :
    c079ApplySwitchLetter σ (a, a) = σ :=
  c079_switchPoints_self σ a

theorem c079Foldl_diag_replicate {m : ℕ}
    (σ : C079MatchingPartition m) (a : Replica m) (extra : ℕ) :
    (List.replicate extra (a, a)).foldl c079ApplySwitchLetter σ = σ := by
  induction extra generalizing σ with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [c079ApplySwitchLetter_diag]
      exact ih σ

theorem c079DecodeSwitchWord_pad {m t : ℕ}
    (σ : C079MatchingPartition m) (word : C079SwitchWord m t)
    (extra : ℕ) (a : Replica m) :
    c079DecodeSwitchWord σ (c079PadSwitchWord word extra a) =
      c079DecodeSwitchWord σ word := by
  change (word.toList ++ List.replicate extra (a, a)).foldl
    c079ApplySwitchLetter σ = word.toList.foldl c079ApplySwitchLetter σ
  rw [List.foldl_append]
  exact c079Foldl_diag_replicate _ a extra

/-- Reachability by *at most* `t` switches, distinguished from the original
partition-intersection metric until their equality is proved. -/
def C079SwitchReachableWithin {m : ℕ}
    (σ τ : C079MatchingPartition m) (t : ℕ) : Prop :=
  ∃ k ≤ t, ∃ word : C079SwitchWord m k,
    c079DecodeSwitchWord σ word = τ

/-- A word of length at most `t` is represented by one exact-length `t`
record, provided the replica type is nonempty (as in the paper's `m ≥ 2`
regime). -/
theorem c079SwitchReachableWithin_has_exact_record {m t : ℕ}
    (σ τ : C079MatchingPartition m) (a : Replica m)
    (h : C079SwitchReachableWithin σ τ t) :
    ∃ word : C079SwitchWord m t,
      c079DecodeSwitchWord σ word = τ := by
  obtain ⟨k, hkt, word, hword⟩ := h
  obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hkt
  subst t
  exact ⟨c079PadSwitchWord word extra a,
    (c079DecodeSwitchWord_pad σ word extra a).trans hword⟩

/-- The distinct matching-partition outputs of exactly `t` letters. -/
def c079SwitchOutputs {m : ℕ}
    (σ : C079MatchingPartition m) (t : ℕ) :
    Finset (C079MatchingPartition m) := by
  classical
  exact (Finset.univ : Finset (C079SwitchWord m t)).image
    (fun word => c079DecodeSwitchWord σ word)

theorem mem_c079SwitchOutputs_iff {m t : ℕ}
    (σ τ : C079MatchingPartition m) :
    τ ∈ c079SwitchOutputs σ t ↔
      ∃ word : C079SwitchWord m t,
        c079DecodeSwitchWord σ word = τ := by
  classical
  simp [c079SwitchOutputs]

theorem c079SwitchReachableWithin_mem_outputs {m t : ℕ}
    (σ τ : C079MatchingPartition m) (a : Replica m)
    (h : C079SwitchReachableWithin σ τ t) :
    τ ∈ c079SwitchOutputs σ t :=
  (mem_c079SwitchOutputs_iff σ τ).mpr
    (c079SwitchReachableWithin_has_exact_record σ τ a h)

/-- With a null letter available, the exact-length output set is precisely
the at-most-`t` switch-reachable set. -/
theorem c079SwitchReachableWithin_iff_mem_outputs {m t : ℕ}
    (σ τ : C079MatchingPartition m) (a : Replica m) :
    C079SwitchReachableWithin σ τ t ↔
      τ ∈ c079SwitchOutputs σ t := by
  constructor
  · exact c079SwitchReachableWithin_mem_outputs σ τ a
  · intro h
    obtain ⟨word, hword⟩ := (mem_c079SwitchOutputs_iff σ τ).mp h
    exact ⟨t, le_rfl, word, hword⟩

/-- A fixed choice of one decoding record for each reachable output. -/
def c079SwitchRecord {m t : ℕ}
    (σ : C079MatchingPartition m)
    (τ : {υ : C079MatchingPartition m // υ ∈ c079SwitchOutputs σ t}) :
    C079SwitchWord m t :=
  Classical.choose ((mem_c079SwitchOutputs_iff σ τ.1).mp τ.2)

theorem c079SwitchRecord_decode {m t : ℕ}
    (σ : C079MatchingPartition m)
    (τ : {υ : C079MatchingPartition m // υ ∈ c079SwitchOutputs σ t}) :
    c079DecodeSwitchWord σ (c079SwitchRecord σ τ) = τ.1 :=
  Classical.choose_spec ((mem_c079SwitchOutputs_iff σ τ.1).mp τ.2)

/-- Reachable outputs inject into records by a chosen decoding witness.
This is an injection of *outputs* into words, not an assertion that every
word decodes to a different matching. -/
theorem c079SwitchRecord_injective {m t : ℕ}
    (σ : C079MatchingPartition m) :
    Function.Injective (c079SwitchRecord σ (t := t)) := by
  intro τ υ h
  apply Subtype.ext
  calc
    τ.1 = c079DecodeSwitchWord σ (c079SwitchRecord σ τ) :=
      (c079SwitchRecord_decode σ τ).symm
    _ = c079DecodeSwitchWord σ (c079SwitchRecord σ υ) := by rw [h]
    _ = υ.1 := c079SwitchRecord_decode σ υ

/-- The exact-length reachable output set has at most `(4m²)^t` elements. -/
theorem c079SwitchOutputs_card_le {m : ℕ}
    (σ : C079MatchingPartition m) (t : ℕ) :
    (c079SwitchOutputs σ t).card ≤ (4 * m ^ 2) ^ t := by
  classical
  calc
    (c079SwitchOutputs σ t).card ≤
        (Finset.univ : Finset (C079SwitchWord m t)).card := by
          change ((Finset.univ : Finset (C079SwitchWord m t)).image
            (fun word => c079DecodeSwitchWord σ word)).card ≤ _
          exact Finset.card_image_le
    _ = Fintype.card (C079SwitchLetter m) ^ t := by
      simp [C079SwitchWord]
    _ = (4 * m ^ 2) ^ t := by rw [c079_switchLetter_card]

#print axioms c079_switchPoints_is_matching
#print axioms c079_switchPoints_rel_iff
#print axioms c079_switchPoints_self
#print axioms c079DecodeSwitchWord_pad
#print axioms c079SwitchReachableWithin_iff_mem_outputs
#print axioms c079SwitchRecord_injective
#print axioms c079SwitchOutputs_card_le

end GraphMatrixReplica
