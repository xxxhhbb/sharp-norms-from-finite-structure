import GraphMatrix.EdgeExpectationProduct

/-! # Joint finite expectation over all independent edge arrays

The factorized edge expectation is realized as one uniform finite average
over a sample carrying every independent Rademacher array.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- One coordinate of the sign array attached to an edge role. -/
abbrev EdgeSignCoordinate {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) (e : Fin G.edges) : Type :=
  Fin (dimension (G.source e)) × Fin (dimension (G.target e))

/-- A joint sample of all independent Rademacher edge arrays. -/
abbrev JointEdgeSignSample {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) : Type :=
  ∀ e : Fin G.edges, EdgeSignCoordinate dimension e → Bool

/-- Character contributed by one edge in one joint sample. -/
def jointEdgeCharacter
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension)
    (epsilon : JointEdgeSignSample dimension) (e : Fin G.edges) : ℤ :=
  rademacherCharacter
    (fun a : Replica (p + 1) =>
      (x (G.source e) a, x (G.target e) a))
    (epsilon e)

/-- Product of all edge characters in a joint sample. -/
def jointEdgeCharacterProduct
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension)
    (epsilon : JointEdgeSignSample dimension) : ℤ :=
  ∏ e : Fin G.edges, jointEdgeCharacter x epsilon e

/-- Unnormalized joint expectation numerator. -/
def jointEdgeCharacterSum
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) : ℤ :=
  ∑ epsilon : JointEdgeSignSample dimension,
    jointEdgeCharacterProduct x epsilon

/-- Joint summation factors exactly into independent one-edge sums. -/
theorem jointEdgeCharacterSum_factorized
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) :
    jointEdgeCharacterSum x =
      ∏ e : Fin G.edges, rademacherCharacterSum
        (fun a : Replica (p + 1) =>
          (x (G.source e) a, x (G.target e) a)) := by
  classical
  unfold jointEdgeCharacterSum jointEdgeCharacterProduct jointEdgeCharacter
  exact (Fintype.prod_sum fun e epsilon =>
    rademacherCharacter
      (fun a : Replica (p + 1) =>
        (x (G.source e) a, x (G.target e) a)) epsilon).symm

/-- Cardinality of the joint independent sample space. -/
theorem card_jointEdgeSignSample
    {G : PartiteShape} (dimension : Fin G.roles → ℕ) :
    Fintype.card (JointEdgeSignSample dimension) =
      ∏ e : Fin G.edges,
        2 ^ Fintype.card (EdgeSignCoordinate dimension e) := by
  classical
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro e _
  simp [EdgeSignCoordinate]

/-- Uniform average over the full joint sign sample. -/
def jointEdgeCharacterAverage
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) : ℚ :=
  (jointEdgeCharacterSum x : ℚ) /
    Fintype.card (JointEdgeSignSample dimension)

/-- Exact finite independence/Fubini identity. -/
theorem jointEdgeCharacterAverage_eq_product
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) :
    jointEdgeCharacterAverage x = edgeRademacherExpectationProduct x := by
  classical
  unfold jointEdgeCharacterAverage
  rw [jointEdgeCharacterSum_factorized, card_jointEdgeSignSample]
  push_cast
  rw [← Finset.prod_div_distrib]
  rfl

def jointReplicaMomentAverage
    {G : PartiteShape} (p : ℕ) (dimension : Fin G.roles → ℕ) : ℚ :=
  (∑ epsilon : JointEdgeSignSample dimension,
      ∑ x : RoleLabeling G p dimension,
        traceGlueIndicator x * (jointEdgeCharacterProduct x epsilon : ℚ)) /
    Fintype.card (JointEdgeSignSample dimension)

theorem jointReplicaMomentAverage_eq_replicaMomentSum
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    jointReplicaMomentAverage p dimension =
      ∑ x : RoleLabeling G p dimension, replicaMomentIntegrand x := by
  classical
  unfold jointReplicaMomentAverage
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, mul_div_assoc]
  have hCast :
      (∑ i, (jointEdgeCharacterProduct x i : ℚ)) =
        (jointEdgeCharacterSum x : ℚ) := by
    unfold jointEdgeCharacterSum
    push_cast
    rfl
  rw [hCast]
  change traceGlueIndicator x * jointEdgeCharacterAverage x =
    replicaMomentIntegrand x
  rw [jointEdgeCharacterAverage_eq_product]
  rfl
theorem jointReplicaMomentAverage_eq_statePolynomial
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    jointReplicaMomentAverage p dimension =
      ∑ T : AdmissiblePartitionState G p,
        (T.toReplicaState.labelingWeight dimension : ℚ) := by
  rw [jointReplicaMomentAverage_eq_replicaMomentSum]
  exact replicaMomentSum_eq_statePolynomial dimension

end GraphMatrixReplica
