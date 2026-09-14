import R6.RademacherCharacterSum
import R6.AdmissibleStatePolynomial

/-! # Product of independent Rademacher edge expectations

For a fixed concrete role labeling, every graph edge uses its own independent
rectangular array of signs.  The product of the normalized edge character
averages is exactly the indicator that every edge meet cell has even size.
Together with the deterministic trace gluings, this is the expectation-to-
admissibility bridge used by the exact state polynomial.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Simultaneous parity condition for the concrete labels on all graph edges. -/
def EdgeParityForLabeling
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) : Prop :=
  ∀ e : Fin G.edges,
    EdgeParityCompatible
      (equalityPartition (x (G.source e)))
      (equalityPartition (x (G.target e)))

/-- Deterministic left and right trace constraints on a concrete labeling. -/
def TraceGlueForLabeling
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) : Prop :=
  (∀ v : Fin G.roles, v ∈ G.leftBoundary →
    LeftTraceCoarsens (equalityPartition (x v))) ∧
  (∀ v : Fin G.roles, v ∈ G.rightBoundary →
    RightTraceCoarsens (equalityPartition (x v)))

theorem concreteLabelingAdmissible_iff_edgeParity_and_traceGlue
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) :
    ConcreteLabelingAdmissible dimension x ↔
      EdgeParityForLabeling x ∧ TraceGlueForLabeling x := by
  rfl

/-- Product of the independent, normalized Rademacher character averages. -/
def edgeRademacherExpectationProduct
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) : ℚ :=
  ∏ e : Fin G.edges,
    rademacherCharacterAverage
      (fun a : Replica (p + 1) =>
        (x (G.source e) a, x (G.target e) a))

/-- Exact factorized expectation: all edges survive iff all concrete edge
multiplicities are even. -/
theorem edgeRademacherExpectationProduct_eq_indicator
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension)
    [Decidable (EdgeParityForLabeling x)] :
    edgeRademacherExpectationProduct x =
      if EdgeParityForLabeling x then 1 else 0 := by
  classical
  unfold edgeRademacherExpectationProduct
  simp_rw [replicaEdgeCharacterAverage_eq_indicator]
  by_cases h : EdgeParityForLabeling x
  · rw [if_pos h]
    have he : ∀ e : Fin G.edges, EdgeParityCompatible
        (equalityPartition (x (G.source e)))
        (equalityPartition (x (G.target e))) := h
    simp [he]
  · rw [if_neg h]
    have hn : ¬ ∀ e : Fin G.edges, EdgeParityCompatible
        (equalityPartition (x (G.source e)))
        (equalityPartition (x (G.target e))) := h
    push Not at hn
    obtain ⟨e, he⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)

/-- Under the deterministic trace constraints, the edge expectation product
is exactly the full concrete-state admissibility indicator. -/
theorem edgeRademacherExpectationProduct_eq_admissibleIndicator
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) (hTrace : TraceGlueForLabeling x)
    [Decidable (ConcreteLabelingAdmissible dimension x)] :
    edgeRademacherExpectationProduct x =
      if ConcreteLabelingAdmissible dimension x then 1 else 0 := by
  classical
  rw [edgeRademacherExpectationProduct_eq_indicator]
  by_cases hEdge : EdgeParityForLabeling x
  · have hAdmissible : ConcreteLabelingAdmissible dimension x :=
      (concreteLabelingAdmissible_iff_edgeParity_and_traceGlue x).2
        ⟨hEdge, hTrace⟩
    rw [if_pos hEdge, if_pos hAdmissible]
  · have hAdmissible : ¬ ConcreteLabelingAdmissible dimension x := by
      intro h
      exact hEdge
        ((concreteLabelingAdmissible_iff_edgeParity_and_traceGlue x).1 h).1
    rw [if_neg hEdge, if_neg hAdmissible]

/-- Indicator imposing the deterministic trace contractions. -/
def traceGlueIndicator
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) : ℚ := by
  classical
  exact if TraceGlueForLabeling x then 1 else 0

/-- Fixed-label contribution after averaging every independent edge and
imposing both trace contractions. -/
def replicaMomentIntegrand
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension) : ℚ :=
  traceGlueIndicator x * edgeRademacherExpectationProduct x

theorem replicaMomentIntegrand_eq_admissibleIndicator
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (x : RoleLabeling G p dimension)
    [Decidable (ConcreteLabelingAdmissible dimension x)] :
    replicaMomentIntegrand x =
      if ConcreteLabelingAdmissible dimension x then 1 else 0 := by
  classical
  unfold replicaMomentIntegrand
  rw [edgeRademacherExpectationProduct_eq_indicator]
  by_cases ht : TraceGlueForLabeling x
  · have htraceIndicator : traceGlueIndicator x = 1 := by
      simp [traceGlueIndicator, ht]
    rw [htraceIndicator]
    by_cases he : EdgeParityForLabeling x
    · have ha : ConcreteLabelingAdmissible dimension x :=
        (concreteLabelingAdmissible_iff_edgeParity_and_traceGlue x).2 ⟨he, ht⟩
      rw [if_pos he, if_pos ha]
      norm_num
    · have ha : ¬ ConcreteLabelingAdmissible dimension x := by
        intro ha
        exact he
          ((concreteLabelingAdmissible_iff_edgeParity_and_traceGlue x).1 ha).1
      rw [if_neg he, if_neg ha]
      norm_num
  · have htraceIndicator : traceGlueIndicator x = 0 := by
      simp [traceGlueIndicator, ht]
    rw [htraceIndicator]
    have ha : ¬ ConcreteLabelingAdmissible dimension x := by
      intro ha
      exact ht
        ((concreteLabelingAdmissible_iff_edgeParity_and_traceGlue x).1 ha).2
    rw [if_neg ha]
    norm_num

/-- Summing the averaged fixed-label contributions counts exactly the
admissible concrete labelings. -/
theorem replicaMomentSum_eq_admissibleLabelingCount
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    (∑ x : RoleLabeling G p dimension, replicaMomentIntegrand x) =
      (Nat.card {x : RoleLabeling G p dimension //
        ConcreteLabelingAdmissible dimension x} : ℚ) := by
  classical
  simp_rw [replicaMomentIntegrand_eq_admissibleIndicator]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp

/-- Exact moment/state expansion: after the finite independent Rademacher
averages and trace contractions, the label sum is the admissible-state
falling-factorial polynomial. -/
theorem replicaMomentSum_eq_statePolynomial
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    (∑ x : RoleLabeling G p dimension, replicaMomentIntegrand x) =
      ∑ T : AdmissiblePartitionState G p,
        (T.toReplicaState.labelingWeight dimension : ℚ) := by
  rw [replicaMomentSum_eq_admissibleLabelingCount]
  rw [admissibleLabelingCount_eq_statePolynomial]
  simp

#print axioms edgeRademacherExpectationProduct_eq_indicator
#print axioms edgeRademacherExpectationProduct_eq_admissibleIndicator
#print axioms replicaMomentIntegrand_eq_admissibleIndicator
#print axioms replicaMomentSum_eq_admissibleLabelingCount
#print axioms replicaMomentSum_eq_statePolynomial

end GraphMatrixReplica
