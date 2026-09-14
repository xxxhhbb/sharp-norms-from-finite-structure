import R6.P3ActualP1ComponentLaw

set_option autoImplicit false
noncomputable section

namespace GraphMatrixReplica

/-- The equivalence-based P3 sample decoder is the same pair as the direct
coordinate decoder used by the component-contraction calculation. -/
theorem p3ComponentSampleFromRest_eq_trialComponentSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (N : ℕ)
    (hN : ∀ u : P2a.SeparatorRole P.toPartiteShape cut,
      N ≤ dimension u.1)
    (i : Fin N) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) :
    p3ComponentSampleFromRest P dimension cut N hN i K R =
      p3TrialComponentSample P dimension cut N hN i K R := by
  apply Prod.ext
  · funext v j
    rfl
  · funext j
    rfl

#print axioms p3ComponentSampleFromRest_eq_trialComponentSample

end GraphMatrixReplica
