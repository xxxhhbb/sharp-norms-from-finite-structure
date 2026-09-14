import R6.P3FiniteProductLaw
import R6.DistinctCoordinateTrials

/-!
# P3 actual typed raw-address bridge

This file uses the existing R6 `PartiteShape`, `EdgeSignCoordinate`, and
`JointEdgeSignSample` definitions.  It records the exact facts used in the P3
address-disjointness argument:

* edge ID is part of an address;
* source/target positions are not interchangeable;
* fixing one endpoint and changing the other changes the raw address;
* coordinatewise-injective separator labels make the same directed crossing
  edge use disjoint raw coordinates in different trials;
* different crossing edge IDs are automatically disjoint.

What is NOT encoded here is the graph-theoretic map assigning each crossing
edge to its connected component of `G-S`; that project-specific connector is
the remaining local formalization step.

Execution status in this handoff: NOT EXECUTED.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Constructor spelling out the actual `(edge, source-label, target-label)`
raw address. -/
def p3EdgeRawAddressMk
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    (e : Fin G.edges)
    (u : Fin (dimension (G.source e)))
    (v : Fin (dimension (G.target e))) :
    P3EdgeRawAddress dimension :=
  ⟨e, (u, v)⟩

/-- For a fixed directed edge and fixed target label, source labels inject into
raw addresses. -/
theorem p3EdgeRawAddressMk_source_injective
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    (e : Fin G.edges) (v : Fin (dimension (G.target e))) :
    Function.Injective
      (fun u : Fin (dimension (G.source e)) =>
        p3EdgeRawAddressMk e u v) := by
  intro u u' h
  have hc := p3_rawAddress_fixed_edge_injective (dimension := dimension) e h
  exact congrArg Prod.fst hc

/-- For a fixed directed edge and fixed source label, target labels inject into
raw addresses. -/
theorem p3EdgeRawAddressMk_target_injective
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    (e : Fin G.edges) (u : Fin (dimension (G.source e))) :
    Function.Injective
      (fun v : Fin (dimension (G.target e)) =>
        p3EdgeRawAddressMk e u v) := by
  intro v v' h
  have hc := p3_rawAddress_fixed_edge_injective (dimension := dimension) e h
  exact congrArg Prod.snd hc

/-- Support of one trial when the separator endpoint is the TARGET of the
actual directed edge.  Every source label is retained; the target label is the
trial's separator label. -/
def p3TargetSeparatorTrialSupport
    {G : PartiteShape} (dimension : Fin G.roles → ℕ)
    {N : ℕ} (e : Fin G.edges)
    (sepLabel : Fin N → Fin (dimension (G.target e)))
    (r : Fin N) : Finset (P3EdgeRawAddress dimension) :=
  Finset.univ.image
    (fun u : Fin (dimension (G.source e)) =>
      p3EdgeRawAddressMk e u (sepLabel r))

/-- Same construction when the separator endpoint is the SOURCE of the actual
directed edge. -/
def p3SourceSeparatorTrialSupport
    {G : PartiteShape} (dimension : Fin G.roles → ℕ)
    {N : ℕ} (e : Fin G.edges)
    (sepLabel : Fin N → Fin (dimension (G.source e)))
    (r : Fin N) : Finset (P3EdgeRawAddress dimension) :=
  Finset.univ.image
    (fun v : Fin (dimension (G.target e)) =>
      p3EdgeRawAddressMk e (sepLabel r) v)

/-- On one crossing edge with separator endpoint at target, distinct trials
with distinct separator labels use disjoint raw coordinates. -/
theorem p3TargetSeparatorTrialSupport_disjoint
    {G : PartiteShape} (dimension : Fin G.roles → ℕ)
    {N : ℕ} (e : Fin G.edges)
    (sepLabel : Fin N → Fin (dimension (G.target e)))
    (hsep : Function.Injective sepLabel)
    {r r' : Fin N} (hrr : r ≠ r') :
    Disjoint
      (p3TargetSeparatorTrialSupport dimension e sepLabel r)
      (p3TargetSeparatorTrialSupport dimension e sepLabel r') := by
  classical
  rw [Finset.disjoint_left]
  intro a ha ha'
  rcases Finset.mem_image.mp ha with ⟨u, _hu, rfl⟩
  rcases Finset.mem_image.mp ha' with ⟨u', _hu', hEq⟩
  have hc := p3_rawAddress_fixed_edge_injective (dimension := dimension) e hEq
  have hlabel' : sepLabel r' = sepLabel r := congrArg Prod.snd hc
  exact hrr (hsep hlabel'.symm)

/-- Source-endpoint analogue of the previous theorem. -/
theorem p3SourceSeparatorTrialSupport_disjoint
    {G : PartiteShape} (dimension : Fin G.roles → ℕ)
    {N : ℕ} (e : Fin G.edges)
    (sepLabel : Fin N → Fin (dimension (G.source e)))
    (hsep : Function.Injective sepLabel)
    {r r' : Fin N} (hrr : r ≠ r') :
    Disjoint
      (p3SourceSeparatorTrialSupport dimension e sepLabel r)
      (p3SourceSeparatorTrialSupport dimension e sepLabel r') := by
  classical
  rw [Finset.disjoint_left]
  intro a ha ha'
  rcases Finset.mem_image.mp ha with ⟨v, _hv, rfl⟩
  rcases Finset.mem_image.mp ha' with ⟨v', _hv', hEq⟩
  have hc := p3_rawAddress_fixed_edge_injective (dimension := dimension) e hEq
  have hlabel' : sepLabel r' = sepLabel r := congrArg Prod.fst hc
  exact hrr (hsep hlabel'.symm)

/-- Any raw-address support living on edge `e` is disjoint from any support
living on a different edge `e'`. -/
theorem p3_edgeSupports_disjoint_of_edge_ne
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    {e e' : Fin G.edges} (hee : e ≠ e')
    (A : Finset (EdgeSignCoordinate dimension e))
    (B : Finset (EdgeSignCoordinate dimension e')) :
    Disjoint
      (A.image (fun c => (⟨e, c⟩ : P3EdgeRawAddress dimension)))
      (B.image (fun c => (⟨e', c⟩ : P3EdgeRawAddress dimension))) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha ha'
  rcases Finset.mem_image.mp ha with ⟨c, _hc, rfl⟩
  rcases Finset.mem_image.mp ha' with ⟨c', _hc', hEq⟩
  exact hee (congrArg Sigma.fst hEq.symm)

#print axioms p3EdgeRawAddressMk_source_injective
#print axioms p3EdgeRawAddressMk_target_injective
#print axioms p3TargetSeparatorTrialSupport_disjoint
#print axioms p3SourceSeparatorTrialSupport_disjoint
#print axioms p3_edgeSupports_disjoint_of_edge_ne

end GraphMatrixReplica
