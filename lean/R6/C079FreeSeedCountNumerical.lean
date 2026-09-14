import R6.C079MatchingPartition
import R6.PaperRademacherPerfectMatchingCount

/-! Numerical factor in R16 Appendix D's free-seed estimate. -/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

theorem c079_pairingCount_le_seedBudget (p : ℕ) :
    ∀ t : ℕ, 0 < t → t ≤ p →
      rademacherPerfectMatchingCount t ≤ (2 * p) ^ (t - 1) := by
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
      intro ht htp
      by_cases ht0 : t = 0
      · subst t
        simp [rademacherPerfectMatchingCount]
      · have hprev := ih (by omega) (by omega)
        have hfactor : 2 * t + 1 ≤ 2 * p := by omega
        calc
          rademacherPerfectMatchingCount (t + 1) =
              (2 * t + 1) * rademacherPerfectMatchingCount t := rfl
          _ ≤ (2 * t + 1) * (2 * p) ^ (t - 1) :=
            Nat.mul_le_mul_left _ hprev
          _ ≤ (2 * p) * (2 * p) ^ (t - 1) :=
            Nat.mul_le_mul_right _ hfactor
          _ = (2 * p) ^ ((t + 1) - 1) := by
            have h : (t + 1) - 1 = (t - 1) + 1 := by omega
            rw [h, pow_succ]
            exact Nat.mul_comm _ _

theorem c079_freeSeed_product_numerical
    {J : Type} [Fintype J] (p : ℕ) (halfSize : J → ℕ)
    (hpos : ∀ j, 0 < halfSize j)
    (hsum : ∑ j, halfSize j = p) :
    (∏ j, rademacherPerfectMatchingCount (halfSize j)) ≤
      (2 * p) ^ (p - Fintype.card J) := by
  classical
  have hle : ∀ j, halfSize j ≤ p := by
    intro j
    calc
      halfSize j ≤ ∑ k, halfSize k :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
      _ = p := hsum
  have hterm : ∀ j, rademacherPerfectMatchingCount (halfSize j) ≤
      (2 * p) ^ (halfSize j - 1) := by
    intro j
    exact c079_pairingCount_le_seedBudget p (halfSize j) (hpos j) (hle j)
  have hexp : (∑ j, (halfSize j - 1)) = p - Fintype.card J := by
    have hsum' : (∑ j, (halfSize j - 1)) + Fintype.card J = p := by
      calc
        _ = ∑ j, ((halfSize j - 1) + 1) := by
          rw [Finset.sum_add_distrib]
          simp
        _ = ∑ j, halfSize j := by
          exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hpos j))
        _ = p := hsum
    omega
  calc
    (∏ j, rademacherPerfectMatchingCount (halfSize j)) ≤
        ∏ j, (2 * p) ^ (halfSize j - 1) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Nat.zero_le _
      · intro j _
        exact hterm j
    _ = (2 * p) ^ (∑ j, (halfSize j - 1)) := by
      simpa using Finset.prod_pow_eq_pow_sum
        (Finset.univ : Finset J) (fun j => halfSize j - 1) (2 * p)
    _ = (2 * p) ^ (p - Fintype.card J) := by rw [hexp]

private noncomputable instance c079_quotientFintype {p : ℕ}
    (θ : ReplicaPartition p) : Fintype (Quotient θ) := by
  classical
  exact Quotient.fintype θ

private def c079_thetaFiber {p : ℕ}
    (θ : ReplicaPartition p) (b : Quotient θ) : Finset (Replica p) := by
  classical
  exact (Finset.univ : Finset (Replica p)).filter
    (fun a => Quotient.mk'' a = b)

/-- Half the size of a quotient block of a replica partition. -/
def c079_thetaHalfSize {p : ℕ} (θ : ReplicaPartition p)
    (b : Quotient θ) : ℕ :=
  (c079_thetaFiber θ b).card / 2

private theorem c079_thetaFiber_even {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ)
    (b : Quotient θ) :
    Even (c079_thetaFiber θ b).card := by
  refine Quotient.inductionOn b ?_
  intro a
  unfold c079_thetaFiber
  rw [quotientFiber_eq_partitionBlock]
  exact hEven a

private theorem c079_thetaHalfSize_double {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ)
    (b : Quotient θ) :
    2 * c079_thetaHalfSize θ b =
      (c079_thetaFiber θ b).card := by
  obtain ⟨k, hk⟩ := c079_thetaFiber_even θ hEven b
  unfold c079_thetaHalfSize
  omega

private theorem c079_thetaHalfSize_pos {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ)
    (b : Quotient θ) : 0 < c079_thetaHalfSize θ b := by
  have hcard : 2 ≤ (c079_thetaFiber θ b).card := by
    refine Quotient.inductionOn b ?_
    intro a
    unfold c079_thetaFiber
    rw [quotientFiber_eq_partitionBlock]
    exact two_le_card_partitionBlock_of_even θ hEven a
  have hdouble := c079_thetaHalfSize_double θ hEven b
  omega

private theorem c079_thetaHalfSize_sum {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ) :
    ∑ b : Quotient θ, c079_thetaHalfSize θ b = p := by
  classical
  have hsumCard :
      (Finset.univ : Finset (Replica p)).card =
        ∑ b : Quotient θ,
          (c079_thetaFiber θ b).card := by
    simpa [c079_thetaFiber] using Finset.card_eq_sum_card_fiberwise
      (f := fun a : Replica p => Quotient.mk'' a)
      (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
  have hdoubleSum :
      2 * (∑ b : Quotient θ, c079_thetaHalfSize θ b) =
        (Finset.univ : Finset (Replica p)).card := by
    calc
      _ = ∑ b : Quotient θ, 2 * c079_thetaHalfSize θ b := by
        rw [Finset.mul_sum]
      _ = ∑ b : Quotient θ,
          (c079_thetaFiber θ b).card := by
        apply Finset.sum_congr rfl
        intro b _
        exact c079_thetaHalfSize_double θ hEven b
      _ = _ := hsumCard.symm
  have hReplicaCard :
      (Finset.univ : Finset (Replica p)).card = 2 * p := by
    simp [Replica, Nat.mul_comm]
  omega

theorem c079_evenPartition_seedProduct_numerical {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ) :
    (∏ b : Quotient θ,
      rademacherPerfectMatchingCount (c079_thetaHalfSize θ b)) ≤
      (2 * p) ^ (p - partitionBlockCount θ) := by
  have h := c079_freeSeed_product_numerical p
    (c079_thetaHalfSize θ)
    (c079_thetaHalfSize_pos θ hEven)
    (c079_thetaHalfSize_sum θ hEven)
  have hcard : Fintype.card (Quotient θ) = partitionBlockCount θ := by
    unfold partitionBlockCount
    exact Fintype.card_congr (Equiv.refl _)
  rw [hcard] at h
  exact h

/-- The actual paper seed object: one unlabeled matching partition refining θ. -/
abbrev C079CompatibleMatchingSeed {p : ℕ} (θ : ReplicaPartition p) :=
  {σ : C079MatchingPartition p // PartitionCoarsens θ σ.1}

/-- The precise outstanding combinatorial injection/equivalence needed to
turn the proved blockwise numerical estimate into a count of actual seeds. -/
theorem c079_compatibleSeed_card_le_of_product_encoding {p : ℕ}
    (θ : ReplicaPartition p) (hEven : IsEvenPartition θ)
    (hEncoding : Nat.card (C079CompatibleMatchingSeed θ) ≤
      ∏ b : Quotient θ,
        rademacherPerfectMatchingCount (c079_thetaHalfSize θ b)) :
    Nat.card (C079CompatibleMatchingSeed θ) ≤
      (2 * p) ^ (p - partitionBlockCount θ) :=
  hEncoding.trans (c079_evenPartition_seedProduct_numerical θ hEven)

#print axioms c079_pairingCount_le_seedBudget
#print axioms c079_freeSeed_product_numerical
#print axioms c079_evenPartition_seedProduct_numerical
#print axioms c079_compatibleSeed_card_le_of_product_encoding

end GraphMatrixReplica
end
