import R6.C079DefectStratification

/-! # C079 all-defect count to state-polynomial endpoint

This module connects an explicitly supplied C079 bound on every exact defect
fiber to the existing fully-partite admissible-state polynomial.  It stops at
the polynomial endpoint and deliberately does not import or prove any
operator-norm, Markov-tail, or moment-order selection result.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Rolewise falling-factorial weights are bounded by the ambient power whose
degree is the state's total number of blocks. -/
theorem c079_labelingWeight_le_uniform_pow_totalBlockCount
    {G : PartiteShape} {p n : ℕ} (T : AdmissiblePartitionState G p)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n) :
    T.toReplicaState.labelingWeight dimension ≤
      n ^ T.toReplicaState.totalBlockCount := by
  classical
  unfold ReplicaState.labelingWeight ReplicaState.totalBlockCount
  calc
    (∏ v : Fin G.roles,
        (dimension v).descFactorial
          (partitionBlockCount (T.toReplicaState.partition v))) ≤
        ∏ v : Fin G.roles,
          (dimension v) ^ partitionBlockCount
            (T.toReplicaState.partition v) := by
      exact Finset.prod_le_prod' fun v _ => Nat.descFactorial_le_pow _ _
    _ ≤ ∏ v : Fin G.roles,
          n ^ partitionBlockCount (T.toReplicaState.partition v) := by
      exact Finset.prod_le_prod' fun v _ =>
        Nat.pow_le_pow_left (hDimension v) _
    _ = n ^ ∑ v : Fin G.roles,
          partitionBlockCount (T.toReplicaState.partition v) := by
      simpa using Finset.prod_pow_eq_pow_sum
        (Finset.univ : Finset (Fin G.roles))
        (fun v => partitionBlockCount (T.toReplicaState.partition v)) n

/-- Total labeling weight of one exact defect fiber. -/
def c079DefectWeightSum
    (G : PartiteShape) (p s : ℕ)
    (dimension : Fin G.roles → ℕ)
    (delta : Fin (c079BlockTarget G p s + 1)) : ℕ :=
  ∑ U : C079DefectStratum G p s delta.1,
    U.1.toReplicaState.labelingWeight dimension

/-- The admissible-state polynomial is exactly the sum of its exact-defect
fiber polynomials. -/
theorem c079_statePolynomial_eq_sum_defectWeightSum
    (G : PartiteShape) (p s : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s) :
    (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) =
      ∑ delta : Fin (c079BlockTarget G p s + 1),
        c079DefectWeightSum G p s dimension delta := by
  let E := c079DefectStratificationEquiv G p s hBlocks
  calc
    (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) =
        ∑ z : (Σ delta : Fin (c079BlockTarget G p s + 1),
          C079DefectStratum G p s delta.1),
          z.2.1.toReplicaState.labelingWeight dimension := by
      apply Fintype.sum_equiv E
      intro T
      rfl
    _ = ∑ delta : Fin (c079BlockTarget G p s + 1),
          c079DefectWeightSum G p s dimension delta := by
      simpa [c079DefectWeightSum] using
        (Fintype.sum_sigma'
          (fun delta : Fin (c079BlockTarget G p s + 1) =>
            fun U : C079DefectStratum G p s delta.1 =>
              U.1.toReplicaState.labelingWeight dimension))

/-- Inside one exact defect fiber, every state has degree exactly
`target - delta`; hence its total weight is bounded by the fiber cardinality
times that ambient power. -/
theorem c079_defectWeightSum_le_coefficient_mul_degreePower
    (G : PartiteShape) (p s n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (delta : Fin (c079BlockTarget G p s + 1)) :
    c079DefectWeightSum G p s dimension delta ≤
      c079DefectCoefficient G p s delta *
        n ^ (c079BlockTarget G p s - delta.1) := by
  unfold c079DefectWeightSum c079DefectCoefficient
  calc
    (∑ U : C079DefectStratum G p s delta.1,
        U.1.toReplicaState.labelingWeight dimension) ≤
        ∑ _U : C079DefectStratum G p s delta.1,
          n ^ (c079BlockTarget G p s - delta.1) := by
      exact Finset.sum_le_sum fun U _ => by
        have hDegree :
            U.1.toReplicaState.totalBlockCount =
              c079BlockTarget G p s - delta.1 := by
          have hDelta := U.2
          omega
        simpa [hDegree] using
          c079_labelingWeight_le_uniform_pow_totalBlockCount
            U.1 dimension hDimension
    _ = Fintype.card (C079DefectStratum G p s delta.1) *
          n ^ (c079BlockTarget G p s - delta.1) := by
      simp

/-- Formal C079 polynomial endpoint.  The only unproved mathematical input is
the displayed all-defect coefficient hypothesis, with constants uniform in
the trace order and defect. -/
theorem c079_statePolynomial_le_of_uniform_allDefect_count
    (G : PartiteShape) (p s a K C n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s)
    (hscale : (p + 1) ^ K ≤ n)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        C ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1) + K * delta.1)) :
    (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) ≤
      (c079BlockTarget G p s + 1) *
        (C ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s) := by
  rw [c079_statePolynomial_eq_sum_defectWeightSum
    G p s dimension hBlocks]
  calc
    (∑ delta : Fin (c079BlockTarget G p s + 1),
        c079DefectWeightSum G p s dimension delta) ≤
        ∑ delta : Fin (c079BlockTarget G p s + 1),
          c079DefectCoefficient G p s delta *
            n ^ (c079BlockTarget G p s - delta.1) := by
      exact Finset.sum_le_sum fun delta _ =>
        c079_defectWeightSum_le_coefficient_mul_degreePower
          G p s n dimension hDimension delta
    _ ≤ (c079BlockTarget G p s + 1) *
          (C ^ (2 * (p + 1)) *
            (p + 1) ^ (a * (p + 1)) *
              n ^ c079BlockTarget G p s) := by
      exact c079_all_defect_weighted_sum_le
        (p + 1) a K C n (c079BlockTarget G p s)
        (c079DefectCoefficient G p s) hscale hCount

#print axioms c079_labelingWeight_le_uniform_pow_totalBlockCount
#print axioms c079_statePolynomial_eq_sum_defectWeightSum
#print axioms c079_defectWeightSum_le_coefficient_mul_degreePower
#print axioms c079_statePolynomial_le_of_uniform_allDefect_count

end GraphMatrixReplica
