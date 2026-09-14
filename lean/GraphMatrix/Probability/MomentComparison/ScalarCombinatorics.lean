import GraphMatrix.RademacherPerfectMatchingEnumeration
import GraphMatrix.RademacherCharacterSum
import GraphMatrix.EqualityPatternLabelCount

/-!
# X3a: finite Rademacher scalar combinatorics

This file isolates the finite combinatorics behind the scalar part of X3a.
It does not introduce a Gaussian probability space.  In particular, it proves
that every even word is covered by an odd-double-factorial matching code and
that the set of words compatible with one fixed code has exactly `m^k`
elements.  Multiple compatible codes for the same even word are deliberately
allowed: the resulting count is an upper bound by covering, not a partition.

The exact-pair witness type is also counted.  Turning that witness count into
the scalar lower moment bound additionally needs the injectivity of the
witness-to-word map (equivalently, uniqueness of the induced unlabeled
matching for an exact-pair word).  That lemma is not present in the supplied
source slice and is intentionally not postulated here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.ScalarMomentComparison

/-- A length `2k` word of primitive labels from `Fin m`. -/
abbrev ScalarWord (m k : ℕ) := Fin (k * 2) → Fin m

/-- Multiplicity of one primitive label in a scalar word. -/
def scalarMultiplicity {m k : ℕ} (w : ScalarWord m k) (a : Fin m) : ℕ :=
  occurrenceMultiplicity w a

/-- Words for which every primitive label occurs an even number of times. -/
def ScalarEvenWord (m k : ℕ) :=
  {w : ScalarWord m k // ∀ a : Fin m, Even (scalarMultiplicity w a)}

noncomputable instance instFintypeScalarEvenWord (m k : ℕ) :
    Fintype (ScalarEvenWord m k) := by
  classical
  unfold ScalarEvenWord
  infer_instance

/-- Compatibility with the concrete recursive matching decoder. -/
def ScalarWordMatchingCompatible {m k : ℕ}
    (w : ScalarWord m k) (code : RademacherPerfectMatchingCode k) : Prop :=
  ∀ i : Fin k,
    w (rademacherPerfectMatchingDecode k code (i, false)) =
      w (rademacherPerfectMatchingDecode k code (i, true))

/-- The finite fiber of words compatible with a fixed matching code. -/
def ScalarCompatibleWord (m k : ℕ)
    (code : RademacherPerfectMatchingCode k) :=
  {w : ScalarWord m k // ScalarWordMatchingCompatible w code}

noncomputable instance instFintypeScalarCompatibleWord
    (m k : ℕ) (code : RademacherPerfectMatchingCode k) :
    Fintype (ScalarCompatibleWord m k code) := by
  classical
  unfold ScalarCompatibleWord
  infer_instance

/-- Every even word is covered by at least one recursive matching code.
This is the exact covering direction required for the scalar upper bound. -/
theorem exists_scalarWordMatchingCompatible_of_even
    {m k : ℕ} (w : ScalarWord m k)
    (hEven : ∀ a : Fin m, Even (scalarMultiplicity w a)) :
    ∃ code : RademacherPerfectMatchingCode k,
      ScalarWordMatchingCompatible w code := by
  classical
  obtain ⟨P⟩ := exists_fiberwisePairing_of_even_fibers k w (by simp) (by
    intro a
    simpa [scalarMultiplicity, occurrenceMultiplicity] using hEven a)
  exact exists_rademacherPerfectMatchingDecode_compatible_of_pairing k w P

/-- An even word, viewed as a subtype, therefore has a compatible code. -/
theorem exists_scalarEvenWord_matchingCode
    {m k : ℕ} (w : ScalarEvenWord m k) :
    ∃ code : RademacherPerfectMatchingCode k,
      ScalarWordMatchingCompatible w.1 code :=
  exists_scalarWordMatchingCompatible_of_even w.1 w.2

/-- For one fixed matching code, a compatible word is equivalent to freely
choosing one label for each of the `k` decoded pairs. -/
noncomputable def scalarCompatibleWordEquivPairLabels
    (m k : ℕ) (code : RademacherPerfectMatchingCode k) :
    ScalarCompatibleWord m k code ≃ (Fin k → Fin m) where
  toFun w := fun i =>
    w.1 (rademacherPerfectMatchingDecode k code (i, false))
  invFun labels :=
    ⟨fun pos =>
        labels (((rademacherPerfectMatchingDecode k code).symm pos).1), by
      intro i
      simp⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext pos
    rcases hq : (rademacherPerfectMatchingDecode k code).symm pos with ⟨i, b⟩
    have hpos : rademacherPerfectMatchingDecode k code (i, b) = pos := by
      have h := (rademacherPerfectMatchingDecode k code).apply_symm_apply pos
      rw [hq] at h
      exact h
    simp only [hq]
    cases b with
    | false =>
        exact congrArg w.1 hpos
    | true =>
        exact (w.2 i).trans (congrArg w.1 hpos)
  right_inv := by
    intro labels
    funext i
    simp

/-- Hence a fixed matching code covers exactly `m^k` words. -/
theorem card_scalarCompatibleWord
    (m k : ℕ) (code : RademacherPerfectMatchingCode k) :
    Fintype.card (ScalarCompatibleWord m k code) = m ^ k := by
  classical
  calc
    Fintype.card (ScalarCompatibleWord m k code) =
        Fintype.card (Fin k → Fin m) :=
      Fintype.card_congr (scalarCompatibleWordEquivPairLabels m k code)
    _ = m ^ k := by simp

/-- Sigma of all matching-code fibers is just code × free pair labels. -/
noncomputable def scalarCompatibleSigmaEquiv
    (m k : ℕ) :
    (Σ code : RademacherPerfectMatchingCode k,
      ScalarCompatibleWord m k code) ≃
      RademacherPerfectMatchingCode k × (Fin k → Fin m) where
  toFun z :=
    ⟨z.1, scalarCompatibleWordEquivPairLabels m k z.1 z.2⟩
  invFun z :=
    ⟨z.1, (scalarCompatibleWordEquivPairLabels m k z.1).symm z.2⟩
  left_inv := by
    intro z
    rcases z with ⟨code, w⟩
    simp
  right_inv := by
    intro z
    rcases z with ⟨code, labels⟩
    simp

/-- Cardinality of the full covering family. -/
theorem card_scalarCompatibleSigma (m k : ℕ) :
    Fintype.card
        (Σ code : RademacherPerfectMatchingCode k,
          ScalarCompatibleWord m k code) =
      rademacherPerfectMatchingCount k * m ^ k := by
  classical
  calc
    Fintype.card
        (Σ code : RademacherPerfectMatchingCode k,
          ScalarCompatibleWord m k code) =
        Fintype.card
          (RademacherPerfectMatchingCode k × (Fin k → Fin m)) :=
      Fintype.card_congr (scalarCompatibleSigmaEquiv m k)
    _ = rademacherPerfectMatchingCount k * m ^ k := by
      simp [card_rademacherPerfectMatchingCode]

/-- Choose one covering matching code for each even word. -/
noncomputable def scalarEvenWordCoverCode
    {m k : ℕ} (w : ScalarEvenWord m k) :
    RademacherPerfectMatchingCode k :=
  Classical.choose (exists_scalarEvenWord_matchingCode w)

/-- The chosen code really is compatible. -/
theorem scalarEvenWordCoverCode_spec
    {m k : ℕ} (w : ScalarEvenWord m k) :
    ScalarWordMatchingCompatible w.1 (scalarEvenWordCoverCode w) :=
  Classical.choose_spec (exists_scalarEvenWord_matchingCode w)

/-- Inject every even word into the disjoint union of matching-code fibers.
The word itself is retained in the second component, so no uniqueness of the
covering code is required. -/
noncomputable def scalarEvenWordCoverEmbedding (m k : ℕ) :
    ScalarEvenWord m k ↪
      (Σ code : RademacherPerfectMatchingCode k,
        ScalarCompatibleWord m k code) where
  toFun w :=
    ⟨scalarEvenWordCoverCode w,
      ⟨w.1, scalarEvenWordCoverCode_spec w⟩⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z => z.2.1) h

/-- Counting consequence of the covering argument:
`# even words ≤ (2k-1)!! * m^k`.
The recursive count is the project representation of `(2k-1)!!`. -/
theorem card_scalarEvenWord_le (m k : ℕ) :
    Fintype.card (ScalarEvenWord m k) ≤
      rademacherPerfectMatchingCount k * m ^ k := by
  classical
  calc
    Fintype.card (ScalarEvenWord m k) ≤
        Fintype.card
          (Σ code : RademacherPerfectMatchingCode k,
            ScalarCompatibleWord m k code) :=
      Fintype.card_le_of_injective
        (scalarEvenWordCoverEmbedding m k)
        (scalarEvenWordCoverEmbedding m k).injective
    _ = rademacherPerfectMatchingCount k * m ^ k :=
      card_scalarCompatibleSigma m k

/-- Exact-pair witnesses: an unlabeled matching code together with an
injective choice of `k` distinct labels. -/
abbrev ScalarExactPairWitness (m k : ℕ) :=
  RademacherPerfectMatchingCode k × (Fin k ↪ Fin m)

/-- The witness family has the exact expected cardinality
`(2k-1)!! * (m)_k`. -/
theorem card_scalarExactPairWitness (m k : ℕ) :
    Fintype.card (ScalarExactPairWitness m k) =
      rademacherPerfectMatchingCount k * m.descFactorial k := by
  classical
  have hEmb : Fintype.card (Fin k ↪ Fin m) = m.descFactorial k := by
    simpa using
      (Fintype.card_embedding_eq (alpha := Fin k) (beta := Fin m))
  simp [ScalarExactPairWitness, card_rademacherPerfectMatchingCode, hEmb]

/-- The concrete exact-pair word generated by a matching code and distinct
pair labels.  This definition preserves the original decoded pair positions. -/
def scalarExactPairWitnessWord {m k : ℕ}
    (z : ScalarExactPairWitness m k) : ScalarWord m k :=
  fun pos => z.2 (((rademacherPerfectMatchingDecode k z.1).symm pos).1)

/-- Each decoded pair receives one and the same label in the generated word. -/
theorem scalarExactPairWitnessWord_compatible
    {m k : ℕ} (z : ScalarExactPairWitness m k) :
    ScalarWordMatchingCompatible (scalarExactPairWitnessWord z) z.1 := by
  intro i
  simp [scalarExactPairWitnessWord]

/-- Generic fiber-multiplicity bookkeeping: the sum of all fiber sizes is
exactly the size of the domain.  This is reused by the trace module. -/
theorem sum_occurrenceMultiplicity
    {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    (key : A → K) :
    (∑ k : K, occurrenceMultiplicity key k) = Fintype.card A := by
  classical
  unfold occurrenceMultiplicity
  calc
    (∑ k : K, (Finset.univ.filter fun a : A => key a = k).card) =
        ∑ k : K, ∑ a : A, if key a = k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ a : A, ∑ k : K, if key a = k then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _a : A, 1 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = Fintype.card A := by simp

end GraphMatrixReplica.ScalarMomentComparison
