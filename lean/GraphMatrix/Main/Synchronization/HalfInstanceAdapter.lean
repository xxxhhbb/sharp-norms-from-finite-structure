import GraphMatrix.Probability.Synchronization.ComponentJointLaw
import GraphMatrix.Main.FiniteProbabilityInstanceTransport

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

/-- Normalize finite instances while the events remain abstract functions. -/
theorem main_p3_some_trial_half_canonical
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut, N ≤ dimension u.1)
    (E : ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      P3ComponentPairSample P dimension cut K → Prop)
    (rho : ℝ) (hrho0 : 0 ≤ rho)
    (hrho : rho ≤ ∏ K : P2a.ActiveComponent P.toPartiteShape cut,
      finiteUniformProbability (E K))
    (hfail : (1 - rho) ^ N ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ finiteUniformProbability
      (fun R : P2a.RestCube (G := P.toPartiteShape) cut dimension =>
        ∃ i : Fin N, ∀ K,
          E K (p3ComponentSampleFromRest P dimension cut N hN i K R)) := by
  classical
  have h := p3_actual_some_trial_all_component_event_half P dimension cut N hN E
    rho hrho0 (by
      convert hrho using 1) hfail
  convert h using 1

end GraphMatrixReplica
