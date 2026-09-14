import GraphMatrix.Counting.FreeSeedCountNumerical
import GraphMatrix.RademacherPerfectMatchingEnumeration

/-!
# cardinality of actual, unlabelled compatible matching seeds

The proof uses the existing compatibility enumeration with the *original
matching's pair-index labels*, not with theta-block labels.  The separate
`pair_relation_exact` lemma upgrades that compatibility to exact recovery.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica
namespace C079U1

attribute [local instance] Classical.propDecidable

/-- The actual subtype of occurrences in one quotient block. -/
abbrev Block {p : ℕ} (θ : ReplicaPartition p) (b : Quotient θ) :=
  {a : Replica p // (Quotient.mk'' a : Quotient θ) = b}

/-- Public bridge to the half-size defined by the input numerical module.
The private finite-set definition in that module is unfolded only by rfl. -/
theorem block_card {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (b : Quotient θ) :
    Fintype.card (Block θ b) = c079_thetaHalfSize θ b * 2 := by
  classical
  have hn : Fintype.card (Block θ b) =
      ((Finset.univ : Finset (Replica p)).filter
        (fun a => (Quotient.mk'' a : Quotient θ) = b)).card := by
    simp only [Block, Fintype.card_subtype]
  have hhalf : c079_thetaHalfSize θ b =
      Fintype.card (Block θ b) / 2 := by
    rw [hn]
    rfl
  have heven : Even (Fintype.card (Block θ b)) := by
    rw [hn]
    refine Quotient.inductionOn b ?_
    intro a
    rw [quotientFiber_eq_partitionBlock]
    exact hEven a
  obtain ⟨k, hk⟩ := heven
  rw [hhalf]
  omega

/-- A fixed coordinate chart for a theta block.  It depends on theta and b,
not on the matching seed.  Ordered charts are used in the mathematical
bijection; any fixed chart suffices for the injection below. -/
def chart {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (b : Quotient θ) :
    Fin (c079_thetaHalfSize θ b * 2) ≃ Block θ b :=
  (Fintype.equivFinOfCardEq (block_card θ hEven b)).symm

/-- Pair indices of a witness matching whose two occurrences lie in b.
This type is used solely to construct a local existence witness; it is
never counted as an extra choice. -/
abbrev PairIndex {p : ℕ} (θ : ReplicaPartition p)
    (ρ : PerfectMatching p) (b : Quotient θ) :=
  {k : Fin p //
    (Quotient.mk'' (ρ.pairingEquiv (k, false)) : Quotient θ) = b}

/-- Restriction of an actual matching witness to one theta block. -/
def blockPairEquiv {p : ℕ} (θ : ReplicaPartition p)
    (ρ : PerfectMatching p)
    (hcoarse : PartitionCoarsens θ ρ.partition) (b : Quotient θ) :
    PairIndex θ ρ b × Bool ≃ Block θ b := by
  classical
  let f : PairIndex θ ρ b × Bool → Block θ b := fun x =>
    ⟨ρ.pairingEquiv (x.1.val, x.2), by
      have hrel : ρ.partition.r
          (ρ.pairingEquiv (x.1.val, x.2))
          (ρ.pairingEquiv (x.1.val, false)) := by
        change (ρ.pairingEquiv.symm
            (ρ.pairingEquiv (x.1.val, x.2))).1 =
          (ρ.pairingEquiv.symm
            (ρ.pairingEquiv (x.1.val, false))).1
        simp
      exact (Quotient.sound (hcoarse _ _ hrel)).trans x.1.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hval : ρ.pairingEquiv (x.1.val, x.2) =
        ρ.pairingEquiv (y.1.val, y.2) :=
      congrArg Subtype.val hxy
    have hpair := ρ.pairingEquiv.injective hval
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpair)
    · exact congrArg (fun z : Fin p × Bool => z.2) hpair
  · intro a
    let k : Fin p := (ρ.pairingEquiv.symm a.val).1
    have hk :
        (Quotient.mk'' (ρ.pairingEquiv (k, false)) : Quotient θ) = b := by
      have hrel : ρ.partition.r (ρ.pairingEquiv (k, false)) a.val := by
        change (ρ.pairingEquiv.symm
          (ρ.pairingEquiv (k, false))).1 = (ρ.pairingEquiv.symm a.val).1
        simp [k]
      exact (Quotient.sound (hcoarse _ _ hrel)).trans a.property
    refine ⟨(⟨k, hk⟩, (ρ.pairingEquiv.symm a.val).2), ?_⟩
    apply Subtype.ext
    change ρ.pairingEquiv
      ((ρ.pairingEquiv.symm a.val).1,
        (ρ.pairingEquiv.symm a.val).2) = a.val
    exact ρ.pairingEquiv.apply_symm_apply a.val

/-- The number of restricted pair indices is the *existing* block half-size. -/
theorem pairIndex_card {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (ρ : PerfectMatching p)
    (hcoarse : PartitionCoarsens θ ρ.partition) (b : Quotient θ) :
    Fintype.card (PairIndex θ ρ b) = c079_thetaHalfSize θ b := by
  classical
  have hc := Fintype.card_congr (blockPairEquiv θ ρ hcoarse b)
  simp only [Fintype.card_prod, Fintype.card_bool] at hc
  have hb := block_card θ hEven b
  omega

def indexEquiv {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (ρ : PerfectMatching p)
    (hcoarse : PartitionCoarsens θ ρ.partition) (b : Quotient θ) :
    Fin (c079_thetaHalfSize θ b) ≃ PairIndex θ ρ b :=
  (Fintype.equivFinOfCardEq
    (pairIndex_card θ hEven ρ hcoarse b)).symm

/-- Local labelled witness, used only to invoke the existing recursive
coverage theorem.  The output we count later is a canonical code, not this
redundantly labelled equivalence. -/
def localPairingEquiv {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (ρ : PerfectMatching p)
    (hcoarse : PartitionCoarsens θ ρ.partition) (b : Quotient θ) :
    Fin (c079_thetaHalfSize θ b) × Bool ≃
      Fin (c079_thetaHalfSize θ b * 2) :=
  ((Equiv.prodCongr (indexEquiv θ hEven ρ hcoarse b)
      (Equiv.refl Bool)).trans (blockPairEquiv θ ρ hcoarse b)).trans
    (chart θ hEven b).symm

theorem localPairingEquiv_key {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (ρ : PerfectMatching p)
    (hcoarse : PartitionCoarsens θ ρ.partition) (b : Quotient θ)
    (k : Fin (c079_thetaHalfSize θ b)) (bit : Bool) :
    (ρ.pairingEquiv.symm
      ((chart θ hEven b)
        (localPairingEquiv θ hEven ρ hcoarse b (k, bit))).val).1 =
      (indexEquiv θ hEven ρ hcoarse b k).val := by
  simp only [localPairingEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply]
  change (ρ.pairingEquiv.symm
    (ρ.pairingEquiv ((indexEquiv θ hEven ρ hcoarse b k).val, bit))).1 = _
  simp only [Equiv.symm_apply_apply]

/-- Every decoded pair belongs to the *original matching* partition. -/
def BlockFits {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (s : C079CompatibleMatchingSeed θ)
    (b : Quotient θ)
    (c : RademacherPerfectMatchingCode (c079_thetaHalfSize θ b)) : Prop :=
  ∀ k : Fin (c079_thetaHalfSize θ b),
    s.1.1.r
      ((chart θ hEven b)
        (rademacherPerfectMatchingDecode _ c (k, false))).val
      ((chart θ hEven b)
        (rademacherPerfectMatchingDecode _ c (k, true))).val

/-- Compatibility is obtained, not postulated.  Its labels are the pair
indices of the original matching witness. -/
theorem exists_block_code {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (s : C079CompatibleMatchingSeed θ)
    (b : Quotient θ) :
    ∃ c : RademacherPerfectMatchingCode (c079_thetaHalfSize θ b),
      BlockFits θ hEven s b c := by
  classical
  obtain ⟨ρ, hρ⟩ := s.1.property
  have hcoarse : PartitionCoarsens θ ρ.partition := by
    simpa only [hρ] using s.property
  let f : Fin (c079_thetaHalfSize θ b * 2) → Fin p := fun a =>
    (ρ.pairingEquiv.symm ((chart θ hEven b) a).val).1
  let P : FiberwisePairing (c079_thetaHalfSize θ b) f := {
    pairingEquiv := localPairingEquiv θ hEven ρ hcoarse b
    sameFiber := by
      intro k
      change (ρ.pairingEquiv.symm
        ((chart θ hEven b)
          (localPairingEquiv θ hEven ρ hcoarse b (k, false))).val).1 =
        (ρ.pairingEquiv.symm
          ((chart θ hEven b)
            (localPairingEquiv θ hEven ρ hcoarse b (k, true))).val).1
      rw [localPairingEquiv_key, localPairingEquiv_key]
  }
  obtain ⟨c, hc⟩ :=
    exists_rademacherPerfectMatchingDecode_compatible_of_pairing
      (c079_thetaHalfSize θ b) f P
  refine ⟨c, ?_⟩
  intro k
  rw [← hρ]
  exact hc k

/-- A pair-preserving injection into two-point fibres induces an injection
on pair keys.  This is the no-loss step missing from mere compatibility. -/
theorem pair_key_injective {ι κ : Type*}
    (f : ι × Bool → κ × Bool) (hf : Function.Injective f)
    (hpair : ∀ k, (f (k, false)).1 = (f (k, true)).1) :
    Function.Injective (fun k => (f (k, false)).1) := by
  intro k l hkl
  have hne : (f (k, false)).2 ≠ (f (k, true)).2 := by
    intro heq
    have hprod := hf (Prod.ext (hpair k) heq)
    have hbool : (false : Bool) = true := congrArg Prod.snd hprod
    cases hbool
  have hhit : ∃ bit : Bool, (f (k, bit)).2 = (f (l, false)).2 := by
    by_cases heq : (f (k, false)).2 = (f (l, false)).2
    · exact ⟨false, heq⟩
    · refine ⟨true, ?_⟩
      cases h0 : (f (k, false)).2 <;>
        cases h1 : (f (k, true)).2 <;>
        cases h2 : (f (l, false)).2 <;> simp_all
  obtain ⟨bit, hbit⟩ := hhit
  have hfirst : (f (k, bit)).1 = (f (l, false)).1 := by
    cases bit
    · exact hkl
    · exact (hpair k).symm.trans hkl
  have hprod := hf (Prod.ext hfirst hbit)
  exact congrArg Prod.fst hprod

/-- Exact equivalence of pair relations; not just the forward implication. -/
theorem pair_relation_exact {ι κ : Type*}
    (f : ι × Bool → κ × Bool) (hf : Function.Injective f)
    (hpair : ∀ k, (f (k, false)).1 = (f (k, true)).1)
    (x y : ι × Bool) :
    (f x).1 = (f y).1 ↔ x.1 = y.1 := by
  have hnorm (z : ι × Bool) : (f z).1 = (f (z.1, false)).1 := by
    rcases z with ⟨k, bit⟩
    cases bit
    · rfl
    · exact (hpair k).symm
  rw [hnorm x, hnorm y]
  constructor
  · intro hxy
    exact pair_key_injective f hf hpair hxy
  · intro hxy
    rw [hxy]

/-- Exact recovery of the original matching relation on a theta block. -/
theorem block_relation_iff {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (s : C079CompatibleMatchingSeed θ)
    (b : Quotient θ)
    (c : RademacherPerfectMatchingCode (c079_thetaHalfSize θ b))
    (hc : BlockFits θ hEven s b c) (u v : Block θ b) :
    s.1.1.r u.val v.val ↔
      ((rademacherPerfectMatchingDecode _ c).symm
        ((chart θ hEven b).symm u)).1 =
      ((rademacherPerfectMatchingDecode _ c).symm
        ((chart θ hEven b).symm v)).1 := by
  classical
  obtain ⟨ρ, hρ⟩ := s.1.property
  let d := rademacherPerfectMatchingDecode (c079_thetaHalfSize θ b) c
  let e := chart θ hEven b
  let f : Fin (c079_thetaHalfSize θ b) × Bool → Replica p := fun z =>
    ρ.pairingEquiv.symm (e (d z)).val
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hval : (e (d x)).val = (e (d y)).val :=
      ρ.pairingEquiv.symm.injective hxy
    exact d.injective (e.injective (Subtype.ext hval))
  have hpair : ∀ k, (f (k, false)).1 = (f (k, true)).1 := by
    intro k
    have h := hc k
    rw [← hρ] at h
    exact h
  have h := pair_relation_exact f hfinj hpair
    (d.symm (e.symm u)) (d.symm (e.symm v))
  rw [← hρ]
  change (ρ.pairingEquiv.symm u.val).1 = (ρ.pairingEquiv.symm v.val).1 ↔
    (d.symm (e.symm u)).1 = (d.symm (e.symm v)).1
  simpa [f] using h

/-- A function on actual unlabelled seeds; the choice witnesses are Props. -/
def encode {p : ℕ} (θ : ReplicaPartition p) (hEven : IsEvenPartition θ)
    (s : C079CompatibleMatchingSeed θ) :
    (b : Quotient θ) →
      RademacherPerfectMatchingCode (c079_thetaHalfSize θ b) :=
  fun b => Classical.choose (exists_block_code θ hEven s b)

theorem encode_fits {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) (s : C079CompatibleMatchingSeed θ)
    (b : Quotient θ) :
    BlockFits θ hEven s b (encode θ hEven s b) :=
  Classical.choose_spec (exists_block_code θ hEven s b)

/-- Equality of all block codes forces equality of the full setoids, and
then equality of both proof-irrelevant subtype wrappers. -/
theorem encode_injective {p : ℕ} (θ : ReplicaPartition p)
    (hEven : IsEvenPartition θ) :
    Function.Injective (encode θ hEven) := by
  classical
  intro s t hcode
  have hlocal : ∀ (b : Quotient θ) (u v : Block θ b),
      s.1.1.r u.val v.val ↔ t.1.1.r u.val v.val := by
    intro b u v
    rw [block_relation_iff θ hEven s b (encode θ hEven s b)
        (encode_fits θ hEven s b) u v,
      block_relation_iff θ hEven t b (encode θ hEven t b)
        (encode_fits θ hEven t b) u v]
    rw [congrFun hcode b]
  apply Subtype.ext
  apply Subtype.ext
  apply Setoid.ext
  intro a a'
  constructor
  · intro haa'
    let b : Quotient θ := Quotient.mk'' a
    let u : Block θ b := ⟨a, rfl⟩
    let v : Block θ b :=
      ⟨a', (Quotient.sound (s.property a a' haa')).symm⟩
    exact (hlocal b u v).mp haa'
  · intro haa'
    let b : Quotient θ := Quotient.mk'' a
    let u : Block θ b := ⟨a, rfl⟩
    let v : Block θ b :=
      ⟨a', (Quotient.sound (t.property a a' haa')).symm⟩
    exact (hlocal b u v).mpr haa'

end C079U1

/-- The former hEncoding premise is now a theorem about the actual seed type. -/
theorem c079_compatibleSeed_card_le_product {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ) :
    Nat.card (C079CompatibleMatchingSeed θ) ≤
      ∏ b : Quotient θ,
        rademacherPerfectMatchingCount (c079_thetaHalfSize θ b) := by
  classical
  let : Fintype (C079CompatibleMatchingSeed θ) :=
    Fintype.ofInjective (C079U1.encode θ hEven)
      (C079U1.encode_injective θ hEven)
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (C079CompatibleMatchingSeed θ) ≤
        Fintype.card ((b : Quotient θ) →
          RademacherPerfectMatchingCode (c079_thetaHalfSize θ b)) :=
      Fintype.card_le_of_injective (C079U1.encode θ hEven)
        (C079U1.encode_injective θ hEven)
    _ = ∏ b : Quotient θ,
        rademacherPerfectMatchingCount (c079_thetaHalfSize θ b) := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro b _
      exact card_rademacherPerfectMatchingCode _

/-- U1, with no encoding/cardinality premise and with p = 0 included. -/
theorem c079_compatibleSeed_card_le {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ) :
    Nat.card (C079CompatibleMatchingSeed θ) ≤
      (2 * p) ^ (p - partitionBlockCount θ) := by
  exact c079_compatibleSeed_card_le_of_product_encoding θ hEven
    (c079_compatibleSeed_card_le_product θ hEven)


end GraphMatrixReplica
end
