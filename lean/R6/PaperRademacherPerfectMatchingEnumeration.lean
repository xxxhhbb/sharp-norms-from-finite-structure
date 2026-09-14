import R6.PaperRademacherEvenWordPairingDecomposition

/-! # Recursive enumeration of perfect matchings

This file realizes the odd-double-factorial code as an actual perfect
matching.  At a successor step, position `0` is paired with the position
selected by the new `Fin (2 * r + 1)` digit; the two positions are deleted
and the recursive matching is inserted in the complement.
-/

noncomputable section

namespace GraphMatrixReplica

set_option maxHeartbeats 1600000

/-- The selected partner, viewed in the successor output type. -/
def rademacherPairPartnerPosition (r : ℕ) (j : Fin (r * 2 + 1)) :
    Fin ((r + 1) * 2) :=
  ⟨j.val + 1, by omega⟩

/-- Insert a distinguished pair into `2 * r` residual positions. -/
def rademacherPairInsertEquiv (r : ℕ) (j : Fin (r * 2 + 1)) :
    Bool ⊕ Fin (r * 2) ≃ Fin ((r + 1) * 2) := by
  let f : Bool ⊕ Fin (r * 2) → Fin ((r + 1) * 2)
    | Sum.inl false => ⟨0, by omega⟩
    | Sum.inl true => rademacherPairPartnerPosition r j
    | Sum.inr x =>
        ⟨(j.succ.succAbove x.succ).val, by omega⟩
  refine Equiv.ofBijective f ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro a b hab
    rcases a with (a | a) <;> rcases b with (b | b)
    · cases a <;> cases b
      · rfl
      · exfalso
        have hv := congrArg Fin.val hab
        simp [f, rademacherPairPartnerPosition] at hv
      · exfalso
        have hv := congrArg Fin.val hab
        simp [f, rademacherPairPartnerPosition] at hv
      · rfl
    · cases a
      · exfalso
        simpa [f] using congrArg Fin.val hab
      · exfalso
        have hne := j.succ.succAbove_ne b.succ
        apply hne
        apply Fin.ext
        have hv := congrArg Fin.val hab.symm
        simp [f, rademacherPairPartnerPosition] at hv ⊢
        omega
    · cases b
      · exfalso
        simpa [f] using congrArg Fin.val hab
      · exfalso
        have hne := j.succ.succAbove_ne a.succ
        apply hne
        apply Fin.ext
        have hv := congrArg Fin.val hab
        simp [f, rademacherPairPartnerPosition] at hv ⊢
        omega
    · congr
      have hs : j.succ.succAbove a.succ =
          j.succ.succAbove b.succ := by
        apply Fin.ext
        simpa [f] using congrArg Fin.val hab
      have hs' : a.succ = b.succ := Fin.succAbove_right_injective hs
      apply Fin.ext
      simpa using congrArg Fin.val hs'
  · simp only [Fintype.card_sum, Fintype.card_bool, Fintype.card_fin]
    omega

@[simp] theorem rademacherPairInsertEquiv_inl_false
    (r : ℕ) (j : Fin (r * 2 + 1)) :
    rademacherPairInsertEquiv r j (Sum.inl false) = 0 := rfl

@[simp] theorem rademacherPairInsertEquiv_inl_true
    (r : ℕ) (j : Fin (r * 2 + 1)) :
    rademacherPairInsertEquiv r j (Sum.inl true) =
      rademacherPairPartnerPosition r j := rfl

/-- Split pair label `0` from the remaining pair labels. -/
def rademacherPairDomainSplitEquiv (r : ℕ) :
    Fin (r + 1) × Bool ≃ Bool ⊕ (Fin r × Bool) :=
  (Equiv.prodCongr (finSuccEquiv r) (Equiv.refl Bool)).trans
    optionProdEquiv

@[simp] theorem rademacherPairDomainSplitEquiv_zero
    (r : ℕ) (b : Bool) :
    rademacherPairDomainSplitEquiv r (0, b) = Sum.inl b := by
  simp [rademacherPairDomainSplitEquiv]

@[simp] theorem rademacherPairDomainSplitEquiv_succ
    (r : ℕ) (k : Fin r) (b : Bool) :
    rademacherPairDomainSplitEquiv r (k.succ, b) = Sum.inr (k, b) := by
  simp [rademacherPairDomainSplitEquiv]

/-- Decode an odd-double-factorial code into a matching of the ordered
positions. -/
def rademacherPerfectMatchingDecode :
    ∀ r : ℕ, RademacherPerfectMatchingCode r →
      (Fin r × Bool ≃ Fin (r * 2))
  | 0, _ => Fintype.equivOfCardEq (by simp)
  | r + 1, code =>
      (rademacherPairDomainSplitEquiv r).trans
        ((Equiv.sumCongr (Equiv.refl Bool)
          (rademacherPerfectMatchingDecode r code.2)).trans
          (rademacherPairInsertEquiv r (Fin.cast (by omega) code.1)))

@[simp] theorem rademacherPerfectMatchingDecode_zero_false
    (r : ℕ) (code : RademacherPerfectMatchingCode (r + 1)) :
    rademacherPerfectMatchingDecode (r + 1) code (0, false) = 0 := by
  simp [rademacherPerfectMatchingDecode]

@[simp] theorem rademacherPerfectMatchingDecode_zero_true
    (r : ℕ) (code : RademacherPerfectMatchingCode (r + 1)) :
    rademacherPerfectMatchingDecode (r + 1) code (0, true) =
      rademacherPairPartnerPosition r
        (Fin.cast (by omega) code.1) := by
  simp [rademacherPerfectMatchingDecode]

@[simp] theorem rademacherPerfectMatchingDecode_succ
    (r : ℕ) (code : RademacherPerfectMatchingCode (r + 1))
    (k : Fin r) (b : Bool) :
    rademacherPerfectMatchingDecode (r + 1) code (k.succ, b) =
      rademacherPairInsertEquiv r (Fin.cast (by omega) code.1)
        (Sum.inr (rademacherPerfectMatchingDecode r code.2 (k, b))) := by
  simp [rademacherPerfectMatchingDecode]

/-- Every non-distinguished old pair lands in the residual summand after
the distinguished pair has been removed. -/
theorem exists_rademacherResidualPosition
    {epsilon : Type} {r : ℕ} (f : Fin ((r + 1) * 2) → epsilon)
    (P : FiberwisePairing (r + 1) f)
    (k : Fin (r + 1)) (b : Bool) (j : Fin (r * 2 + 1))
    (hzero : P.pairingEquiv (k, b) = 0)
    (hpartner : P.pairingEquiv (k, !b) =
      rademacherPairPartnerPosition r j)
    (l : Fin r) (c : Bool) :
    ∃ x : Fin (r * 2),
      (rademacherPairInsertEquiv r j).symm
          (P.pairingEquiv (k.succAbove l, c)) = Sum.inr x := by
  let y := (rademacherPairInsertEquiv r j).symm
    (P.pairingEquiv (k.succAbove l, c))
  cases hy : y with
  | inr x => exact ⟨x, hy⟩
  | inl d =>
      exfalso
      have hout : P.pairingEquiv (k.succAbove l, c) =
          rademacherPairInsertEquiv r j (Sum.inl d) := by
        calc
          P.pairingEquiv (k.succAbove l, c) =
              rademacherPairInsertEquiv r j y :=
            ((rademacherPairInsertEquiv r j).apply_symm_apply _).symm
          _ = rademacherPairInsertEquiv r j (Sum.inl d) :=
            congrArg (rademacherPairInsertEquiv r j) hy
      cases d
      · rw [rademacherPairInsertEquiv_inl_false, ← hzero] at hout
        have hin := P.pairingEquiv.injective hout
        have hk : k.succAbove l = k := congrArg Prod.fst hin
        exact k.succAbove_ne l hk
      · rw [rademacherPairInsertEquiv_inl_true, ← hpartner] at hout
        have hin := P.pairingEquiv.injective hout
        have hk : k.succAbove l = k := congrArg Prod.fst hin
        exact k.succAbove_ne l hk

/-- The residual pairing after deleting one pair. -/
def rademacherResidualFiberwisePairing
    {epsilon : Type} {r : ℕ} (f : Fin ((r + 1) * 2) → epsilon)
    (P : FiberwisePairing (r + 1) f)
    (k : Fin (r + 1)) (b : Bool) (j : Fin (r * 2 + 1))
    (hzero : P.pairingEquiv (k, b) = 0)
    (hpartner : P.pairingEquiv (k, !b) =
      rademacherPairPartnerPosition r j) :
    FiberwisePairing r
      (fun x => f (rademacherPairInsertEquiv r j (Sum.inr x))) := by
  let g : Fin r × Bool → Fin (r * 2) := fun x =>
    Classical.choose (exists_rademacherResidualPosition f P k b j
      hzero hpartner x.1 x.2)
  have hg (x : Fin r × Bool) :
      (rademacherPairInsertEquiv r j).symm
          (P.pairingEquiv (k.succAbove x.1, x.2)) = Sum.inr (g x) :=
    Classical.choose_spec (exists_rademacherResidualPosition f P k b j
      hzero hpartner x.1 x.2)
  have hginj : Function.Injective g := by
    intro x y hxy
    have hs : (rademacherPairInsertEquiv r j).symm
          (P.pairingEquiv (k.succAbove x.1, x.2)) =
        (rademacherPairInsertEquiv r j).symm
          (P.pairingEquiv (k.succAbove y.1, y.2)) := by
      rw [hg x, hg y, hxy]
    have hp : (k.succAbove x.1, x.2) =
        (k.succAbove y.1, y.2) :=
      P.pairingEquiv.injective
        ((rademacherPairInsertEquiv r j).symm.injective hs)
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    have h₁ : x₁ = y₁ :=
      Fin.succAbove_right_injective (congrArg Prod.fst hp)
    have h₂ : x₂ = y₂ := congrArg Prod.snd hp
    cases h₁
    cases h₂
    rfl
  let e : Fin r × Bool ≃ Fin (r * 2) :=
    Equiv.ofBijective g (by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hginj, by simp⟩)
  refine ⟨e, ?_⟩
  intro l
  have happly (c : Bool) :
      rademacherPairInsertEquiv r j (Sum.inr (e (l, c))) =
        P.pairingEquiv (k.succAbove l, c) := by
    apply (rademacherPairInsertEquiv r j).symm.injective
    simpa [e] using (hg (l, c)).symm
  rw [happly false, happly true]
  exact P.sameFiber (k.succAbove l)

/-- The recursive decoder covers every fiberwise pairing.  Pair labels and
the two orientations inside a pair are deliberately forgotten; only the
induced unordered pairs of positions matter. -/
theorem exists_rademacherPerfectMatchingDecode_compatible_of_pairing
    {epsilon : Type} :
    ∀ (r : ℕ) (f : Fin (r * 2) → epsilon)
      (P : FiberwisePairing r f),
      ∃ code : RademacherPerfectMatchingCode r,
        ∀ k : Fin r,
          f (rademacherPerfectMatchingDecode r code (k, false)) =
            f (rademacherPerfectMatchingDecode r code (k, true))
  | 0, _, _ => ⟨PUnit.unit, fun k => Fin.elim0 k⟩
  | r + 1, f, P => by
      rcases hkb : P.pairingEquiv.symm 0 with ⟨k, b⟩
      have hzero : P.pairingEquiv (k, b) = 0 := by
        rw [← hkb]
        exact P.pairingEquiv.apply_symm_apply 0
      let partner := P.pairingEquiv (k, !b)
      have hpartner_ne : partner ≠ 0 := by
        intro hp
        have heq : (k, !b) = (k, b) :=
          P.pairingEquiv.injective (hp.trans hzero.symm)
        cases b <;> simp at heq
      have hpartner_val : partner.val ≠ 0 := by
        intro hp
        apply hpartner_ne
        apply Fin.ext
        simpa using hp
      let j : Fin (r * 2 + 1) :=
        ⟨partner.val - 1, by
          have := partner.isLt
          omega⟩
      have hpartner : P.pairingEquiv (k, !b) =
          rademacherPairPartnerPosition r j := by
        apply Fin.ext
        change partner.val = partner.val - 1 + 1
        omega
      let residual := rademacherResidualFiberwisePairing f P k b j
        hzero hpartner
      obtain ⟨rest, hrest⟩ :=
        exists_rademacherPerfectMatchingDecode_compatible_of_pairing r
          (fun x => f (rademacherPairInsertEquiv r j (Sum.inr x))) residual
      let digit : Fin (2 * r + 1) := Fin.cast (by omega) j
      let code : RademacherPerfectMatchingCode (r + 1) := (digit, rest)
      refine ⟨code, ?_⟩
      intro q
      refine Fin.cases ?_ (fun l => ?_) q
      · rw [rademacherPerfectMatchingDecode_zero_false,
          rademacherPerfectMatchingDecode_zero_true]
        have hdigit : Fin.cast (by omega) digit = j := by
          apply Fin.ext
          rfl
        rw [hdigit]
        cases b
        · simp only [Bool.not_false] at hpartner
          rw [← hzero, ← hpartner]
          exact P.sameFiber k
        · simp only [Bool.not_true] at hpartner
          rw [← hzero, ← hpartner]
          exact (P.sameFiber k).symm
      · rw [rademacherPerfectMatchingDecode_succ,
          rademacherPerfectMatchingDecode_succ]
        have hdigit : Fin.cast (by omega) digit = j := by
          apply Fin.ext
          rfl
        simpa [code, hdigit] using hrest l

/-- Every even paired edge word is covered by the recursive
odd-double-factorial decoder. -/
theorem exists_rademacherPerfectMatchingDecode_of_even
    {epsilon : Type} [Fintype epsilon] [DecidableEq epsilon]
    {r : ℕ} (choice : Fin r → epsilon × epsilon)
    (hEven : ∀ e, Even ((rademacherPairEdgeWord choice).count e)) :
    ∃ code : RademacherPerfectMatchingCode r,
      RademacherWordMatchingCompatible choice
        (rademacherPerfectMatchingDecode r code) := by
  obtain ⟨P⟩ :=
    exists_rademacherPairEdgeFiberwisePairing_of_even choice hEven
  exact exists_rademacherPerfectMatchingDecode_compatible_of_pairing r
    (rademacherPairEdgeAt choice) P

/-- The promised concrete enumeration used by the canonical pairing-class
decomposition. -/
def canonicalRademacherPerfectMatchingEnumeration (r : ℕ) :
    RademacherPerfectMatchingEnumeration r where
  matching := rademacherPerfectMatchingDecode r
  complete := by
    intro epsilon _ _ choice hEven
    exact exists_rademacherPerfectMatchingDecode_of_even choice hEven

#print axioms rademacherPairInsertEquiv
#print axioms rademacherPerfectMatchingDecode
#print axioms rademacherResidualFiberwisePairing
#print axioms exists_rademacherPerfectMatchingDecode_compatible_of_pairing
#print axioms exists_rademacherPerfectMatchingDecode_of_even
#print axioms canonicalRademacherPerfectMatchingEnumeration

end GraphMatrixReplica
