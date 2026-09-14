import GraphMatrix.RademacherMatrixDyadicMoment
import GraphMatrix.EvenFiberPairing

/-! # Pairing even Rademacher edge words

An edge word surviving Rademacher averaging has even multiplicity in every
edge label.  This file turns that parity statement into a perfect pairing of
the `2r` word positions, with paired positions carrying the same label.

It also records the elementary nonnegative covering bound obtained by summing
over all perfect-matching encodings.  Matchings may cover a word more than
once; this harmless overcount is exactly what later Khintchine arguments use.
No noncommutative Khintchine estimate is claimed here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The paired edge word, packaged as a vector of its exact length `2r`. -/
def rademacherPairEdgeVector
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) :
    List.Vector ε (r * 2) :=
  ⟨rademacherPairEdgeWord choice, by
    simp [rademacherPairEdgeWord, List.length_flatMap, List.sum_ofFn]
  ⟩

/-- The edge label at a position of the paired word. -/
def rademacherPairEdgeAt
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) :
    Fin (r * 2) → ε :=
  (rademacherPairEdgeVector choice).get

/-- Even edge multiplicities produce a perfect pairing of word positions in
which every pair has the same edge label. -/
theorem exists_rademacherPairEdgeFiberwisePairing_of_even
    {ε : Type} [Fintype ε] [DecidableEq ε] {r : ℕ}
    (choice : Fin r → ε × ε)
    (hEven : ∀ e, Even ((rademacherPairEdgeWord choice).count e)) :
    Nonempty (FiberwisePairing r (rademacherPairEdgeAt choice)) := by
  classical
  apply exists_fiberwisePairing_of_even_fibers r
  · simp
  · intro e
    change Even ((Finset.univ.filter fun i =>
      (rademacherPairEdgeVector choice).get i = e).card)
    rw [Fin.card_filter_univ_eq_vector_get_eq_count e
      (rademacherPairEdgeVector choice)]
    exact hEven e

/-- A matching encoding of the `2r` positions respects a word when the two
positions in each of its pairs carry the same edge label. -/
def RademacherWordMatchingCompatible
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε)
    (matching : Fin r × Bool ≃ Fin (r * 2)) : Prop :=
  ∀ k : Fin r,
    rademacherPairEdgeAt choice (matching (k, false)) =
      rademacherPairEdgeAt choice (matching (k, true))

instance instDecidableRademacherWordMatchingCompatible
    {ε : Type} [DecidableEq ε] {r : ℕ}
    (choice : Fin r → ε × ε)
    (matching : Fin r × Bool ≃ Fin (r * 2)) :
    Decidable (RademacherWordMatchingCompatible choice matching) := by
  unfold RademacherWordMatchingCompatible
  infer_instance

/-- Every even word is covered by at least one compatible perfect-matching
encoding. -/
theorem exists_compatibleMatching_of_even_rademacherPairEdgeWord
    {ε : Type} [Fintype ε] [DecidableEq ε] {r : ℕ}
    (choice : Fin r → ε × ε)
    (hEven : ∀ e, Even ((rademacherPairEdgeWord choice).count e)) :
    ∃ matching : Fin r × Bool ≃ Fin (r * 2),
      RademacherWordMatchingCompatible choice matching := by
  obtain ⟨P⟩ :=
    exists_rademacherPairEdgeFiberwisePairing_of_even choice hEven
  exact ⟨P.pairingEquiv, P.sameFiber⟩

/-- A nonnegative weight of one even word is bounded by the sum of that
weight over all compatible perfect-matching encodings.  The right side can
count the word repeatedly. -/
theorem rademacherEvenWord_weight_le_sum_compatibleMatchings
    {ε : Type} [Fintype ε] [DecidableEq ε] {r : ℕ}
    (weight : (Fin r → ε × ε) → ℝ)
    (hweight : ∀ choice, 0 ≤ weight choice)
    (choice : Fin r → ε × ε)
    (hEven : ∀ e, Even ((rademacherPairEdgeWord choice).count e)) :
    weight choice ≤
      ∑ matching : Fin r × Bool ≃ Fin (r * 2),
        if RademacherWordMatchingCompatible choice matching then
          weight choice else 0 := by
  classical
  obtain ⟨matching, hmatching⟩ :=
    exists_compatibleMatching_of_even_rademacherPairEdgeWord choice hEven
  calc
    weight choice =
        if RademacherWordMatchingCompatible choice matching then
          weight choice else 0 := by simp [hmatching]
    _ ≤ ∑ matching' : Fin r × Bool ≃ Fin (r * 2),
          if RademacherWordMatchingCompatible choice matching' then
            weight choice else 0 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun matching' : Fin r × Bool ≃ Fin (r * 2) =>
          if RademacherWordMatchingCompatible choice matching' then
            weight choice else 0)
        (by
          intro matching' _
          split_ifs
          · exact hweight choice
          · exact le_rfl)
        (Finset.mem_univ matching)

/-- The sum of arbitrary nonnegative weights over even paired edge words is
bounded by the covering sum over all perfect-matching encodings and all words
compatible with the encoding.  Duplicate covers are intentionally retained.
-/
theorem sum_even_rademacherPairEdgeWords_le_matchingCover
    {ε : Type} [Fintype ε] [DecidableEq ε] (r : ℕ)
    (weight : (Fin r → ε × ε) → ℝ)
    (hweight : ∀ choice, 0 ≤ weight choice) :
    (∑ choice : Fin r → ε × ε,
        if ∀ e, Even ((rademacherPairEdgeWord choice).count e) then
          weight choice else 0) ≤
      ∑ matching : Fin r × Bool ≃ Fin (r * 2),
        ∑ choice : Fin r → ε × ε,
          if RademacherWordMatchingCompatible choice matching then
            weight choice else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro choice _
  by_cases hEven : ∀ e, Even ((rademacherPairEdgeWord choice).count e)
  · simp only [if_pos hEven]
    exact rademacherEvenWord_weight_le_sum_compatibleMatchings
      weight hweight choice hEven
  · simp only [if_neg hEven]
    apply Finset.sum_nonneg
    intro matching _
    split_ifs
    · exact hweight choice
    · exact le_rfl


end GraphMatrixReplica
