import R6.P1ContractionReadout
import R6.M1ConditionalWitnessEndpoint

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open PaperR16 PaperR16.C2Actual
attribute [local instance] Classical.propDecidable

/-- The literal weighted-sum trial event, expressed without depending on the
probability proof module. It uses the same actual P3 sample decoder. -/
def rootWeightedTrialSuccess (P : PaperShape) (cut : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (eps : ℝ) (n : ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) : Prop :=
  ∃ i : Fin N, ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
    eps * (n : ℝ) ^ ((P1AD.roleCount P cut K.1 : ℝ) / 2) *
      Real.sqrt (Real.log (n : ℝ)) ≤
      |WeightedSignTilt.weightedSum
        (fun j => p1Z P dimension cut K.1
          (p3DistinguishedBoundaryRole P cut K).1
          (p3DistinguishedBoundaryRole P cut K).2
          (rootP1InternalSample P cut dimension I K)
          (p3ComponentSampleFromRest P dimension cut N hN i K R).1 j)
        (p3ComponentSampleFromRest P dimension cut N hN i K R).2|

/-- One common successful trial supplies one legal separator tuple for all
actual contractions. The exact absolute-value readout handles the opposite
Boolean sign conventions without changing the sample distribution. -/
theorem root_weightedTrialSuccess_implies_actual
    (P : PaperShape) (cut : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ)
    (N : ℕ) (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (eps : ℝ) (n : ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension)
    (h : rootWeightedTrialSuccess P cut dimension N hN eps n I R) :
    rootSimultaneousComponentEvent P cut dimension eps n I R := by
  obtain ⟨i, hi⟩ := h
  refine ⟨P2a.separatorTrial (G := P.toPartiteShape) (cut := cut) dimension N hN i, ?_⟩
  intro K
  rw [componentContractionAt_eq_p2a, p2a_componentContraction_abs_eq_weightedSum]
  have hK := hi K
  have hRoles := root_P1_componentRoleCount_eq P cut K
  simpa only [hRoles] using hK

/-- Probability of the actual simultaneous contraction event is at least the
probability already proved for the weighted-sum trial event. -/
theorem root_weightedTrial_probability_le_actual
    (P : PaperShape) (cut : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ)
    (N : ℕ) (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (eps : ℝ) (n : ℕ)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension) :
    finiteUniformProbability (rootWeightedTrialSuccess P cut dimension N hN eps n I) ≤
      finiteUniformProbability (rootSimultaneousComponentEvent P cut dimension eps n I) := by
  apply finiteUniformProbability_mono
  intro R hR
  exact root_weightedTrialSuccess_implies_actual P cut dimension N hN eps n I R hR

#print axioms root_weightedTrialSuccess_implies_actual
#print axioms root_weightedTrial_probability_le_actual
end GraphMatrixReplica
