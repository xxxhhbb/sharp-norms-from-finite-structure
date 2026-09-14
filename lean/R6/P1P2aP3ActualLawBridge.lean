import R6.P2aComponentContraction
import R6.P1CrossingArrays
import R6.P3ActualAddressBridge

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- P1's internal edge arrays are exactly the P2a component primitive block. -/
def p1InternalBlockEquiv (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P1InternalSample P dimension cut K.1 ≃
      ({a : P2a.PrimitiveAddress (G := P.toPartiteShape) dimension //
        a ∈ P2a.componentInternalSupport (G := P.toPartiteShape) cut dimension K} → Bool) where
  toFun eps a := eps ⟨a.1.1, by
    exact (Finset.mem_filter.mp a.2).2⟩ a.1.2
  invFun w e ij := w ⟨⟨e.1, ij⟩, by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩⟩
  left_inv eps := by
    funext e ij
    rfl
  right_inv w := by
    funext a
    rfl

theorem p1InternalBlockEquiv_restrict (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (eps : P1TypedSample P dimension) :
    p1InternalBlockEquiv P dimension cut K (p1RestrictInternalSample P dimension cut K.1 eps) =
      fun a => P2a.jointSampleEquivPrimitive (G := P.toPartiteShape) dimension eps a.1 := rfl

/-- Restriction of a complete internal realization to the existing P1 arrays. -/
def p1InternalFromComplete (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension) :
    P1InternalSample P dimension cut K.1 :=
  fun e ij => I ⟨⟨e.1, ij⟩, ⟨K, e.2⟩⟩

/-- For every remainder, reconstructing the actual full sample leaves P1's
internal arrays fixed at the chosen complete realization. -/
theorem p1_restrict_internalRest_reconstruct (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (K : P2a.ActiveComponent P.toPartiteShape cut)
    (I : P2a.InternalCube (G := P.toPartiteShape) cut dimension)
    (R : P2a.RestCube (G := P.toPartiteShape) cut dimension) :
    p1RestrictInternalSample P dimension cut K.1
      ((P2a.internalRestEquiv (G := P.toPartiteShape) cut dimension).symm (I, R)) =
      p1InternalFromComplete P dimension cut K I := by
  funext e ij
  change (if h : P2a.IsInternalAddress (G := P.toPartiteShape) cut dimension ⟨e.1, ij⟩ then _ else _) = _
  rw [dif_pos (show P2a.IsInternalAddress (G := P.toPartiteShape) cut dimension ⟨e.1, ij⟩ from ⟨K, e.2⟩)]
  rfl

/-- Componentwise P1 observables factor under the original full edge-array law.
The actual disjoint component geometry discharges independence. -/
theorem p1_actual_internal_component_product (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (F : ∀ K : P2a.ActiveComponent P.toPartiteShape cut,
      P1InternalSample P dimension cut K.1 → ℝ) :
    paperMean (fun eps : P1TypedSample P dimension =>
      ∏ K, F K (p1RestrictInternalSample P dimension cut K.1 eps)) =
      ∏ K, paperMean (F K) := by
  classical
  let H := fun K w => F K ((p1InternalBlockEquiv P dimension cut K).symm w)
  have h := P2a.internalComponentFunction_product_law (G := P.toPartiteShape) cut dimension H
  simp only [H, ← p1InternalBlockEquiv_restrict, Equiv.symm_apply_apply,
    P2a.paperMean_equiv] at h
  exact h

/-- P2a and P3 use the same occurrence-preserving primitive address. -/
def p2aP3AddressEquiv {G : PartiteShape} (dimension : Fin G.roles → ℕ) :
    P2a.PrimitiveAddress dimension ≃ P3EdgeRawAddress dimension := Equiv.refl _

/-- Exact complete-internal conditioning for P3 events in the actual model. -/
theorem p3_actual_internal_probability {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) (cut : Finset (Fin G.roles))
    (A : JointEdgeSignSample dimension → Prop) [DecidablePred A] :
    finiteUniformProbability A =
      paperMean (fun I : P2a.InternalCube cut dimension =>
        finiteUniformProbability (fun R : P2a.RestCube cut dimension =>
          A ((P2a.internalRestEquiv cut dimension).symm (I, R)))) := by
  exact P2a.paperMean_eq_internal_then_rest cut dimension (fun eps => if A eps then 1 else 0)

#print axioms p1InternalBlockEquiv
#print axioms p1_restrict_internalRest_reconstruct
#print axioms p1_actual_internal_component_product
#print axioms p2aP3AddressEquiv
#print axioms p3_actual_internal_probability
end GraphMatrixReplica
