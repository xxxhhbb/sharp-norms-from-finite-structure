import GraphMatrix.Probability.MomentComparison.ScalarCombinatorics

/-!
# X3a A: exact-pair witness injection

The recursive odd-double-factorial matching code is recovered from the
same-label relation of the generated word.  At a successor step the unique
nonzero position paired with position `0` recovers the first digit; deleting
that distinguished pair with `rademacherPairInsertEquiv` reduces to the tail
code.  Thus this file works with the project's actual recursive decoder and
does not replace it by an abstract perfect-matching quotient.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.ScalarMomentComparison

/-- The pair label of a position under the concrete recursive decoder. -/
def scalarMatchingPairKey {k : ℕ}
    (code : RademacherPerfectMatchingCode k) (pos : Fin (k * 2)) : Fin k :=
  (((rademacherPerfectMatchingDecode k code).symm pos).1)

@[simp] theorem scalarMatchingPairKey_decode {k : ℕ}
    (code : RademacherPerfectMatchingCode k) (i : Fin k) (b : Bool) :
    scalarMatchingPairKey code
        (rademacherPerfectMatchingDecode k code (i, b)) = i := by
  simp [scalarMatchingPairKey]

@[simp] theorem scalarMatchingPairKey_zero {r : ℕ}
    (code : RademacherPerfectMatchingCode (r + 1)) :
    scalarMatchingPairKey code 0 = 0 := by
  have h := scalarMatchingPairKey_decode code (0 : Fin (r + 1)) false
  simpa using h

@[simp] theorem scalarMatchingPairKey_partner {r : ℕ}
    (code : RademacherPerfectMatchingCode (r + 1)) :
    scalarMatchingPairKey code
        (rademacherPairPartnerPosition r (Fin.cast (by omega) code.1)) = 0 := by
  have h := scalarMatchingPairKey_decode code (0 : Fin (r + 1)) true
  simpa using h

/-- The selected partner is never position zero. -/
theorem rademacherPairPartnerPosition_ne_zero
    (r : ℕ) (j : Fin (r * 2 + 1)) :
    rademacherPairPartnerPosition r j ≠ (0 : Fin ((r + 1) * 2)) := by
  intro h
  have hv := congrArg Fin.val h
  simp [rademacherPairPartnerPosition] at hv

/-- In a successor code, the fiber of pair-key `0` consists exactly of the
position `0` and the partner encoded by the first digit. -/
theorem scalarMatchingPairKey_eq_zero_iff {r : ℕ}
    (code : RademacherPerfectMatchingCode (r + 1))
    (pos : Fin ((r + 1) * 2)) :
    scalarMatchingPairKey code pos = 0 ↔
      pos = 0 ∨
        pos = rademacherPairPartnerPosition r
          (Fin.cast (by omega) code.1) := by
  constructor
  · intro h
    rcases hq : (rademacherPerfectMatchingDecode (r + 1) code).symm pos with
      ⟨i, b⟩
    have hpos :=
      (rademacherPerfectMatchingDecode (r + 1) code).apply_symm_apply pos
    rw [hq] at hpos
    have hi : i = 0 := by
      simpa [scalarMatchingPairKey, hq] using h
    subst i
    cases b with
    | false =>
        left
        simpa using hpos.symm
    | true =>
        right
        simpa using hpos.symm
  · intro h
    rcases h with h | h
    · subst pos
      exact scalarMatchingPairKey_zero code
    · subst pos
      exact scalarMatchingPairKey_partner code

/-- Removing the distinguished pair transports the successor pair-key to the
successor of the tail pair-key. -/
theorem scalarMatchingPairKey_residual {r : ℕ}
    (code : RademacherPerfectMatchingCode (r + 1))
    (x : Fin (r * 2)) :
    scalarMatchingPairKey code
        (rademacherPairInsertEquiv r (Fin.cast (by omega) code.1)
          (Sum.inr x)) =
      (scalarMatchingPairKey code.2 x).succ := by
  rcases hq : (rademacherPerfectMatchingDecode r code.2).symm x with ⟨i, b⟩
  have hx := (rademacherPerfectMatchingDecode r code.2).apply_symm_apply x
  rw [hq] at hx
  rw [← hx]
  unfold scalarMatchingPairKey
  have hdecode := congrArg Prod.fst
    ((rademacherPerfectMatchingDecode (r + 1) code).symm_apply_apply
      (i.succ, b))
  simpa [rademacherPerfectMatchingDecode_succ] using hdecode

/-- Equality of the pair-equivalence relations uniquely determines the
project's recursive matching code.  This is the explicit code-recovery step
required by X3a: first recover the partner of zero, hence the first digit,
then recurse on the residual positions. -/
theorem rademacherPerfectMatchingCode_eq_of_pairRelation :
    ∀ {k : ℕ} (code code' : RademacherPerfectMatchingCode k),
      (∀ p q : Fin (k * 2),
        (scalarMatchingPairKey code p = scalarMatchingPairKey code q) ↔
          (scalarMatchingPairKey code' p = scalarMatchingPairKey code' q)) →
      code = code'
  | 0, code, code', _ => by
      cases code
      cases code'
      rfl
  | r + 1, code, code', hrel => by
      let partner : Fin ((r + 1) * 2) :=
        rademacherPairPartnerPosition r (Fin.cast (by omega) code.1)
      let partner' : Fin ((r + 1) * 2) :=
        rademacherPairPartnerPosition r (Fin.cast (by omega) code'.1)
      have hsame : scalarMatchingPairKey code 0 =
          scalarMatchingPairKey code partner := by
        simp [partner]
      have hsame' : scalarMatchingPairKey code' 0 =
          scalarMatchingPairKey code' partner :=
        (hrel 0 partner).mp hsame
      have hpartnerKey : scalarMatchingPairKey code' partner = 0 := by
        simpa using hsame'.symm
      have hor := (scalarMatchingPairKey_eq_zero_iff code' partner).mp
        hpartnerKey
      have hp0 : partner ≠ (0 : Fin ((r + 1) * 2)) := by
        exact rademacherPairPartnerPosition_ne_zero r
          (Fin.cast (by omega) code.1)
      have hp : partner = partner' := by
        rcases hor with h0 | hp'
        · exact False.elim (hp0 h0)
        · exact hp'
      have hdigit : code.1 = code'.1 := by
        apply Fin.ext
        have hv := congrArg Fin.val hp
        dsimp [partner, partner'] at hv
        simp [rademacherPairPartnerPosition] at hv
        omega
      rcases code with ⟨digit, tail⟩
      rcases code' with ⟨digit', tail'⟩
      dsimp at hdigit
      subst digit'
      have htailrel : ∀ x y : Fin (r * 2),
          (scalarMatchingPairKey tail x = scalarMatchingPairKey tail y) ↔
            (scalarMatchingPairKey tail' x = scalarMatchingPairKey tail' y) := by
        intro x y
        let posx : Fin ((r + 1) * 2) :=
          rademacherPairInsertEquiv r (Fin.cast (by omega) digit) (Sum.inr x)
        let posy : Fin ((r + 1) * 2) :=
          rademacherPairInsertEquiv r (Fin.cast (by omega) digit) (Sum.inr y)
        have hfull := hrel posx posy
        have hx : scalarMatchingPairKey (k := r + 1) (digit, tail) posx =
            (scalarMatchingPairKey tail x).succ := by
          simpa [posx] using
            (scalarMatchingPairKey_residual (code := (digit, tail)) x)
        have hy : scalarMatchingPairKey (k := r + 1) (digit, tail) posy =
            (scalarMatchingPairKey tail y).succ := by
          simpa [posy] using
            (scalarMatchingPairKey_residual (code := (digit, tail)) y)
        have hx' : scalarMatchingPairKey (k := r + 1) (digit, tail') posx =
            (scalarMatchingPairKey tail' x).succ := by
          simpa [posx] using
            (scalarMatchingPairKey_residual (code := (digit, tail')) x)
        have hy' : scalarMatchingPairKey (k := r + 1) (digit, tail') posy =
            (scalarMatchingPairKey tail' y).succ := by
          simpa [posy] using
            (scalarMatchingPairKey_residual (code := (digit, tail')) y)
        rw [hx, hy, hx', hy'] at hfull
        simpa using hfull
      have htail : tail = tail' :=
        rademacherPerfectMatchingCode_eq_of_pairRelation tail tail' htailrel
      subst tail'
      rfl

/-- In an exact-pair witness word, equality of labels is exactly equality of
decoded pair keys because the pair-label map is injective. -/
theorem scalarExactPairWitnessWord_eq_iff_pairKey_eq
    {m k : ℕ} (z : ScalarExactPairWitness m k)
    (p q : Fin (k * 2)) :
    scalarExactPairWitnessWord z p = scalarExactPairWitnessWord z q ↔
      scalarMatchingPairKey z.1 p = scalarMatchingPairKey z.1 q := by
  change z.2 (scalarMatchingPairKey z.1 p) =
      z.2 (scalarMatchingPairKey z.1 q) ↔ _
  exact z.2.injective.eq_iff

/-- The actual witness-to-word map is injective.  The proof first reconstructs
the recursive matching code from the equality relation of the word, then
recovers every injected pair label at a canonical decoded position. -/
theorem scalarExactPairWitnessWord_injective {m k : ℕ} :
    Function.Injective
      (scalarExactPairWitnessWord : ScalarExactPairWitness m k → ScalarWord m k) := by
  intro z z' hword
  have hrel : ∀ p q : Fin (k * 2),
      (scalarMatchingPairKey z.1 p = scalarMatchingPairKey z.1 q) ↔
        (scalarMatchingPairKey z'.1 p = scalarMatchingPairKey z'.1 q) := by
    intro p q
    calc
      scalarMatchingPairKey z.1 p = scalarMatchingPairKey z.1 q ↔
          scalarExactPairWitnessWord z p = scalarExactPairWitnessWord z q :=
        (scalarExactPairWitnessWord_eq_iff_pairKey_eq z p q).symm
      _ ↔ scalarExactPairWitnessWord z' p = scalarExactPairWitnessWord z' q := by
        rw [hword]
      _ ↔ scalarMatchingPairKey z'.1 p = scalarMatchingPairKey z'.1 q :=
        scalarExactPairWitnessWord_eq_iff_pairKey_eq z' p q
  have hcode : z.1 = z'.1 :=
    rademacherPerfectMatchingCode_eq_of_pairRelation z.1 z'.1 hrel
  rcases z with ⟨code, labels⟩
  rcases z' with ⟨code', labels'⟩
  dsimp at hcode
  subst code'
  have hlabels : labels = labels' := by
    apply DFunLike.ext _ _
    intro i
    have h := congrFun hword
      (rademacherPerfectMatchingDecode k code (i, false))
    simpa [scalarExactPairWitnessWord] using h
  subst labels'
  rfl

/-- The positions carrying one used injected label are canonically equivalent
to the two orientations of its decoded pair. -/
noncomputable def scalarExactPairFiberEquiv
    {m k : ℕ} (z : ScalarExactPairWitness m k) (i : Fin k) :
    {p : Fin (k * 2) // scalarExactPairWitnessWord z p = z.2 i} ≃ Bool where
  toFun p := ((rademacherPerfectMatchingDecode k z.1).symm p.1).2
  invFun b :=
    ⟨rademacherPerfectMatchingDecode k z.1 (i, b), by
      simp [scalarExactPairWitnessWord]⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rcases hq : (rademacherPerfectMatchingDecode k z.1).symm p.1 with ⟨j, b⟩
    have hp := (rademacherPerfectMatchingDecode k z.1).apply_symm_apply p.1
    rw [hq] at hp
    have hlabel : z.2 j = z.2 i := by
      simpa [scalarExactPairWitnessWord, hq] using p.2
    have hij : j = i := z.2.injective hlabel
    subst j
    simpa [hq] using hp
  right_inv := by
    intro b
    simp

/-- A used injected label occurs exactly twice. -/
theorem scalarExactPairWitness_usedMultiplicity
    {m k : ℕ} (z : ScalarExactPairWitness m k) (i : Fin k) :
    scalarMultiplicity (scalarExactPairWitnessWord z) (z.2 i) = 2 := by
  classical
  unfold scalarMultiplicity occurrenceMultiplicity
  rw [← Fintype.card_subtype (fun p : Fin (k * 2) =>
    scalarExactPairWitnessWord z p = z.2 i)]
  exact Fintype.card_congr (scalarExactPairFiberEquiv z i)

/-- A label outside the injected range does not occur. -/
theorem scalarExactPairWitness_unusedMultiplicity
    {m k : ℕ} (z : ScalarExactPairWitness m k) (a : Fin m)
    (ha : ∀ i : Fin k, z.2 i ≠ a) :
    scalarMultiplicity (scalarExactPairWitnessWord z) a = 0 := by
  classical
  unfold scalarMultiplicity occurrenceMultiplicity
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ hp
  have hi := ha (scalarMatchingPairKey z.1 p)
  exact hi (by
    simpa [scalarExactPairWitnessWord, scalarMatchingPairKey] using hp)

/-- Every label in an exact-pair word has multiplicity exactly `0` or `2`. -/
theorem scalarExactPairWitness_multiplicity_zero_or_two
    {m k : ℕ} (z : ScalarExactPairWitness m k) (a : Fin m) :
    scalarMultiplicity (scalarExactPairWitnessWord z) a = 0 ∨
      scalarMultiplicity (scalarExactPairWitnessWord z) a = 2 := by
  classical
  by_cases h : ∃ i : Fin k, z.2 i = a
  · rcases h with ⟨i, rfl⟩
    exact Or.inr (scalarExactPairWitness_usedMultiplicity z i)
  · push_neg at h
    exact Or.inl (scalarExactPairWitness_unusedMultiplicity z a h)

/-- Hence every exact-pair witness word belongs to the even-word subtype. -/
theorem scalarExactPairWitnessWord_even
    {m k : ℕ} (z : ScalarExactPairWitness m k) :
    ∀ a : Fin m, Even (scalarMultiplicity (scalarExactPairWitnessWord z) a) := by
  intro a
  rcases scalarExactPairWitness_multiplicity_zero_or_two z a with h | h
  · rw [h]
    exact ⟨0, by omega⟩
  · rw [h]
    exact ⟨1, by omega⟩

/-- The witness map as an embedding into the actual `ScalarEvenWord`. -/
noncomputable def scalarExactPairWitnessEmbedding (m k : ℕ) :
    ScalarExactPairWitness m k ↪ ScalarEvenWord m k where
  toFun z := ⟨scalarExactPairWitnessWord z, scalarExactPairWitnessWord_even z⟩
  inj' := by
    intro z z' h
    apply scalarExactPairWitnessWord_injective
    exact congrArg Subtype.val h

/-- X3a scalar lower-count inequality.  The statement includes `k = 0`; when
`k > m` the descending factorial is zero because the embedding type is empty. -/
theorem card_scalarEvenWord_lower (m k : ℕ) :
    rademacherPerfectMatchingCount k * m.descFactorial k ≤
      Fintype.card (ScalarEvenWord m k) := by
  classical
  rw [← card_scalarExactPairWitness]
  exact Fintype.card_le_of_injective
    (scalarExactPairWitnessEmbedding m k)
    (scalarExactPairWitnessEmbedding m k).injective

end GraphMatrixReplica.ScalarMomentComparison
