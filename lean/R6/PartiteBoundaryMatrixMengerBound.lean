import R6.PartiteBoundaryMatrixTrace
import R6.IsolatedMiddleCorrection
import R6.FiniteMengerResidualPathProjection

/-! # Menger exponent bound for the concrete fully-partite boundary matrix

This file turns the exact boundary-matrix/state-polynomial identity into a
matrix-facing upper bound.  The dimensions may vary from role to role, but
are uniformly bounded by one ambient parameter `n`.  The exponent is supplied
by the unconditional finite vertex-Menger certificate, with the exact
isolated-middle correction already proved in R6.

The result remains scoped to the fully-partite surrogate and makes no
identification with the paper's globally-injective shared-noise matrix.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A product of rolewise falling factorials is bounded by the uniform
ambient dimension raised to the state's total number of equality blocks. -/
theorem ReplicaState.labelingWeight_le_uniform_pow_totalBlockCount
    {G : PartiteShape} {p n : ℕ} (S : ReplicaState G p)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n) :
    S.labelingWeight dimension ≤ n ^ S.totalBlockCount := by
  classical
  unfold ReplicaState.labelingWeight ReplicaState.totalBlockCount
  calc
    (∏ v : Fin G.roles,
        (dimension v).descFactorial
          (partitionBlockCount (S.partition v))) ≤
        ∏ v : Fin G.roles,
          (dimension v) ^ partitionBlockCount (S.partition v) := by
            exact Finset.prod_le_prod' fun v _ =>
              Nat.descFactorial_le_pow _ _
    _ ≤ ∏ v : Fin G.roles,
          n ^ partitionBlockCount (S.partition v) := by
            exact Finset.prod_le_prod' fun v _ =>
              Nat.pow_le_pow_left (hDimension v) _
    _ = n ^ ∑ v : Fin G.roles,
          partitionBlockCount (S.partition v) := by
            simpa using Finset.prod_pow_eq_pow_sum
              (Finset.univ : Finset (Fin G.roles))
              (fun v => partitionBlockCount (S.partition v)) n

/-- A uniform cap on admissible-state block counts bounds the natural-valued
fully-partite state polynomial by the number of states times one power. -/
theorem partiteStatePolynomial_nat_le_card_mul_pow
    (G : PartiteShape) (p n B : ℕ)
    (dimension : Fin G.roles → ℕ) (hn : 1 ≤ n)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ B) :
    (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) ≤
      Fintype.card (AdmissiblePartitionState G p) * n ^ B := by
  calc
    (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) ≤
        ∑ _T : AdmissiblePartitionState G p, n ^ B := by
      exact Finset.sum_le_sum fun T _ =>
        (T.toReplicaState.labelingWeight_le_uniform_pow_totalBlockCount
          dimension hDimension).trans
        (Nat.pow_le_pow_right hn (hBlocks T))
    _ = Fintype.card (AdmissiblePartitionState G p) * n ^ B := by
      simp

/-- Rational-cast form matching the boundary trace identity. -/
theorem partiteStatePolynomial_rat_le_card_mul_pow
    (G : PartiteShape) (p n B : ℕ)
    (dimension : Fin G.roles → ℕ) (hn : 1 ≤ n)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ B) :
    (∑ T : AdmissiblePartitionState G p,
        (T.toReplicaState.labelingWeight dimension : ℚ)) ≤
      (Fintype.card (AdmissiblePartitionState G p) : ℚ) * (n : ℚ) ^ B := by
  exact_mod_cast partiteStatePolynomial_nat_le_card_mul_pow
    G p n B dimension hn hDimension hBlocks

/-- Matrix-facing bound under any supplied finite Menger certificate. -/
theorem partiteBoundaryMatrixGramTracePowAverage_le_of_mengerCertificate
    {G : PartiteShape} {p n : ℕ}
    (dimension : Fin G.roles → ℕ) (hn : 1 ≤ n)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (certificate : G.RightLeftMengerCertificate) :
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) ≤
      (Fintype.card (AdmissiblePartitionState G p) : ℚ) *
        (n : ℚ) ^ ((p + 1) *
          (G.roles - certificate.cut.card + G.isolatedMiddleCount) +
            certificate.cut.card) := by
  rw [partiteBoundaryMatrixGramTracePowAverage_eq_statePolynomial]
  exact partiteStatePolynomial_rat_le_card_mul_pow G p n _ dimension hn
    hDimension fun T =>
      T.toReplicaState.totalBlockCount_le_minSeparator_with_isolatedMiddle
        certificate

/-- Fully unconditional finite-Menger specialization.  The certificate is
the one constructed internally by the residual-flow/path-decomposition chain. -/
theorem partiteBoundaryMatrixGramTracePowAverage_le_unconditionalMenger
    (G : PartiteShape) {p n : ℕ}
    (dimension : Fin G.roles → ℕ) (hn : 1 ≤ n)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n) :
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) ≤
      (Fintype.card (AdmissiblePartitionState G p) : ℚ) *
        (n : ℚ) ^ ((p + 1) *
          (G.roles - G.rightLeftMengerCertificate.cut.card +
            G.isolatedMiddleCount) +
          G.rightLeftMengerCertificate.cut.card) := by
  exact partiteBoundaryMatrixGramTracePowAverage_le_of_mengerCertificate
    dimension hn hDimension G.rightLeftMengerCertificate

/-- Separator-number presentation of the unconditional exponent. -/
theorem partiteBoundaryMatrixGramTracePowAverage_le_separatorNumber
    (G : PartiteShape) {p n : ℕ}
    (dimension : Fin G.roles → ℕ) (hn : 1 ≤ n)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n) :
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) ≤
      (Fintype.card (AdmissiblePartitionState G p) : ℚ) *
        (n : ℚ) ^ ((p + 1) *
          (G.roles - G.rightLeftSeparatorNumber + G.isolatedMiddleCount) +
          G.rightLeftSeparatorNumber) := by
  have hCut : G.rightLeftMengerCertificate.cut.card =
      G.rightLeftSeparatorNumber := by
    unfold PartiteShape.rightLeftSeparatorNumber
    apply Nat.le_antisymm
    · exact G.rightLeftMengerCertificate.cut_minimum.2
        G.minimumRightLeftSeparator
        G.minimumRightLeftSeparator_isMinimum.1
    · exact G.minimumRightLeftSeparator_isMinimum.2
        G.rightLeftMengerCertificate.cut
        G.rightLeftMengerCertificate.cut_minimum.1
  have h := partiteBoundaryMatrixGramTracePowAverage_le_unconditionalMenger
    (p := p) G dimension hn hDimension
  rw [hCut] at h
  exact h

/-- A finite replica partition is determined injectively by its complete
Boolean relation table. -/
noncomputable def replicaPartitionRelationCode (q : ℕ) :
    ReplicaPartition q → (Replica q → Replica q → Bool) := by
  classical
  exact fun pi a b => decide (pi.r a b)

theorem replicaPartitionRelationCode_injective (q : ℕ) :
    Function.Injective (replicaPartitionRelationCode q) := by
  classical
  intro pi sigma h
  apply Setoid.ext
  intro a b
  have hab := congrFun (congrFun h a) b
  change decide (pi.r a b) = decide (sigma.r a b) at hab
  exact decide_eq_decide.mp hab

/-- Crude but completely explicit bound on the number of equality
partitions: at most the number of Boolean binary-relation tables. -/
theorem card_replicaPartition_le_boolRelationTable (q : ℕ) :
    Fintype.card (ReplicaPartition q) ≤
      2 ^ (Fintype.card (Replica q) * Fintype.card (Replica q)) := by
  have h := Fintype.card_le_of_injective
    (replicaPartitionRelationCode q)
    (replicaPartitionRelationCode_injective q)
  simpa [Fintype.card_fun, pow_mul] using h

/-- Admissible states form a subtype of all independent rolewise partition
assignments. -/
theorem card_admissiblePartitionState_le_partitionAssignments
    (G : PartiteShape) (p : ℕ) :
    Fintype.card (AdmissiblePartitionState G p) ≤
      Fintype.card (ReplicaPartition (p + 1)) ^ G.roles := by
  calc
    Fintype.card (AdmissiblePartitionState G p) ≤
        Fintype.card (PartitionAssignment G p) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Fintype.card (ReplicaPartition (p + 1)) ^ G.roles := by
      simp [PartitionAssignment]

/-- Fully explicit admissible-state count obtained by composing the two
finite injections. -/
theorem card_admissiblePartitionState_le_boolRelationTables
    (G : PartiteShape) (p : ℕ) :
    Fintype.card (AdmissiblePartitionState G p) ≤
      (2 ^ (Fintype.card (Replica (p + 1)) *
        Fintype.card (Replica (p + 1)))) ^ G.roles := by
  exact (card_admissiblePartitionState_le_partitionAssignments G p).trans
    (Nat.pow_le_pow_left
      (card_replicaPartition_le_boolRelationTable (p + 1)) G.roles)

/-- Explicit-state-count version of the unconditional separator-number
matrix bound. -/
theorem partiteBoundaryMatrixGramTracePowAverage_le_explicitStateCount
    (G : PartiteShape) {p n : ℕ}
    (dimension : Fin G.roles → ℕ) (hn : 1 ≤ n)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n) :
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) ≤
      ((2 ^ (Fintype.card (Replica (p + 1)) *
        Fintype.card (Replica (p + 1)))) ^ G.roles : ℚ) *
        (n : ℚ) ^ ((p + 1) *
          (G.roles - G.rightLeftSeparatorNumber + G.isolatedMiddleCount) +
          G.rightLeftSeparatorNumber) := by
  refine (partiteBoundaryMatrixGramTracePowAverage_le_separatorNumber
    G dimension hn hDimension).trans ?_
  have hCard :
      (Fintype.card (AdmissiblePartitionState G p) : ℚ) ≤
        ((2 ^ (Fintype.card (Replica (p + 1)) *
          Fintype.card (Replica (p + 1)))) ^ G.roles : ℚ) := by
    exact_mod_cast card_admissiblePartitionState_le_boolRelationTables G p
  gcongr

#print axioms ReplicaState.labelingWeight_le_uniform_pow_totalBlockCount
#print axioms partiteStatePolynomial_nat_le_card_mul_pow
#print axioms partiteBoundaryMatrixGramTracePowAverage_le_of_mengerCertificate
#print axioms partiteBoundaryMatrixGramTracePowAverage_le_unconditionalMenger
#print axioms partiteBoundaryMatrixGramTracePowAverage_le_separatorNumber
#print axioms card_replicaPartition_le_boolRelationTable
#print axioms card_admissiblePartitionState_le_boolRelationTables
#print axioms partiteBoundaryMatrixGramTracePowAverage_le_explicitStateCount

end GraphMatrixReplica
