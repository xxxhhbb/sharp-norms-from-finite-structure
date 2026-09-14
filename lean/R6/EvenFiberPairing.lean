import R6.PerfectMatchingDistance
import Mathlib.Data.Fintype.EquivFin

/-! # Pairing a finite type fiberwise

If every fiber of a map from a `2q`-element type has even cardinality, the
domain admits a perfect pairing whose two points stay in the same fiber.
This is the finite combinatorial construction needed to choose an edge
matching inside every even meet cell.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A pairing of `α` into `q` pairs, with both points in each pair having the
same image under `f`. -/
structure FiberwisePairing {α β : Type*} [Fintype α]
    (q : ℕ) (f : α → β) where
  pairingEquiv : Fin q × Bool ≃ α
  sameFiber : ∀ k : Fin q,
    f (pairingEquiv (k, false)) = f (pairingEquiv (k, true))

/-- Even fibers of a map out of a `2q`-element finite type can be paired
without crossing fibers. -/
theorem exists_fiberwisePairing_of_even_fibers
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (q : ℕ) (f : α → β)
    (hcard : Fintype.card α = q * 2)
    (hEven : ∀ b : β,
      Even ((Finset.univ.filter fun x : α => f x = b).card)) :
    Nonempty (FiberwisePairing q f) := by
  classical
  have hEvenSubtype : ∀ b : β,
      Even (Fintype.card {x : α // f x = b}) := by
    intro b
    rw [Fintype.card_subtype]
    exact hEven b
  choose half hHalf using hEvenSubtype
  let PairIndex := Σ b : β, Fin (half b)
  let fiberEquiv : ∀ b : β, {x : α // f x = b} ≃ Fin (half b) × Bool :=
    fun b => Fintype.equivOfCardEq (by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
        hHalf b]
      omega)
  let split : α ≃ PairIndex × Bool :=
    (Equiv.sigmaFiberEquiv f).symm |>.trans
      ((Equiv.sigmaCongrRight fiberEquiv).trans
        (Equiv.sigmaProdDistrib (fun b : β => Fin (half b)) Bool).symm)
  have hPairIndex : Fintype.card PairIndex = q := by
    have h := Fintype.card_congr split
    simp only [Fintype.card_prod, Fintype.card_bool] at h
    omega
  let baseEquiv : Fin q ≃ PairIndex :=
    (Fintype.equivFinOfCardEq hPairIndex).symm
  let pairing : Fin q × Bool ≃ α :=
    (Equiv.prodCongr baseEquiv (Equiv.refl Bool)).trans split.symm
  refine ⟨⟨pairing, ?_⟩⟩
  intro k
  change f (split.symm (baseEquiv k, false)) =
    f (split.symm (baseEquiv k, true))
  rcases hk : baseEquiv k with ⟨b, i⟩
  change f ↑((fiberEquiv b).symm (i, false)) =
    f ↑((fiberEquiv b).symm (i, true))
  exact ((fiberEquiv b).symm (i, false)).property.trans
    ((fiberEquiv b).symm (i, true)).property.symm

/-- Regard a fiberwise pairing of the replica set as a perfect matching. -/
def FiberwisePairing.toPerfectMatching
    {q : ℕ} {β : Type*} {f : Replica q → β}
    (P : FiberwisePairing q f) : PerfectMatching q :=
  ⟨P.pairingEquiv⟩

/-- The equality partition induced by `f` coarsens the pair partition of a
fiberwise pairing. -/
theorem FiberwisePairing.mapPartitionCoarsens
    {q : ℕ} {β : Type*} {f : Replica q → β}
    (P : FiberwisePairing q f) :
    PartitionCoarsens (equalityPartition f) P.toPerfectMatching.partition := by
  intro a b hab
  change f a = f b
  change (P.pairingEquiv.symm a).1 =
    (P.pairingEquiv.symm b).1 at hab
  rcases ha : P.pairingEquiv.symm a with ⟨ka, ba⟩
  rcases hb : P.pairingEquiv.symm b with ⟨kb, bb⟩
  simp only [ha, hb] at hab
  subst kb
  have ha' : a = P.pairingEquiv (ka, ba) := by
    rw [← ha]
    exact (P.pairingEquiv.apply_symm_apply a).symm
  have hb' : b = P.pairingEquiv (ka, bb) := by
    rw [← hb]
    exact (P.pairingEquiv.apply_symm_apply b).symm
  rw [ha', hb']
  cases ba <;> cases bb
  · rfl
  · exact P.sameFiber ka
  · exact (P.sameFiber ka).symm
  · rfl

#print axioms exists_fiberwisePairing_of_even_fibers
#print axioms FiberwisePairing.mapPartitionCoarsens

end GraphMatrixReplica
