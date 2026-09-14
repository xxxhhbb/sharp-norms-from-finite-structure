import GraphMatrix.DisjointPathDegreeBound
import GraphMatrix.Counting.SeparatorLayerCertificate

/-! # C079 layer size from vertex-disjoint paths

Every certified horizontal layer hits every right-to-left path.  For a
vertex-disjoint path family, choosing one hit occurrence on each path gives an
injection into that layer.  This proves the separator-size lower bound needed
by the exact interval excess identity.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A path hit has an explicitly indexed witnessing occurrence. -/
theorem PartiteShape.EdgePathToLeft.exists_hitOccurrence
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (A : Finset (Fin G.roles))
    (h : path.Hits A) :
    ∃ o : Fin path.vertexCount, path.vertexAt o ∈ A := by
  induction path with
  | finish v hLeft =>
      exact ⟨⟨0, by simp [PartiteShape.EdgePathToLeft.vertexCount]⟩, h⟩
  | @step v e w hAtStart hAtEnd tail ih =>
      cases h with
      | inl hHead =>
          refine ⟨⟨0, by simp [PartiteShape.EdgePathToLeft.vertexCount]⟩, ?_⟩
          change v ∈ A
          exact hHead
      | inr hTail =>
          rcases ih hTail with ⟨o, ho⟩
          exact ⟨Fin.succ o, ho⟩

/-- Choose one witnessing occurrence.  The choice is made only after the
propositional existence theorem above. -/
noncomputable def PartiteShape.EdgePathToLeft.hitOccurrence
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (A : Finset (Fin G.roles))
    (h : path.Hits A) : Fin path.vertexCount :=
  Classical.choose (path.exists_hitOccurrence A h)

/-- The chosen occurrence really lies in the hit set. -/
theorem PartiteShape.EdgePathToLeft.vertexAt_hitOccurrence_mem
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (A : Finset (Fin G.roles))
    (h : path.Hits A) :
    path.vertexAt (path.hitOccurrence A h) ∈ A := by
  exact Classical.choose_spec (path.exists_hitOccurrence A h)

/-- A horizontal layer has at least as many roles as any vertex-disjoint
right-to-left path family. -/
theorem C079IntervalCertificate.pathCount_le_layer_card
    {G : PartiteShape} {q s k : ℕ} (C : C079IntervalCertificate G q)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hk : k ∈ Finset.Icc 1 q) :
    s ≤ (c079IntervalLayer C.ell C.upper k).card := by
  let A := c079IntervalLayer C.ell C.upper k
  let hHits : ∀ i : Fin s, (family.path i).Hits A := fun i =>
    C.rightToLeftPath_hits_layer hk (family.start i)
      (family.startRight i) (family.path i)
  let occurrence : ∀ i : Fin s, Fin (family.path i).vertexCount :=
    fun i => (family.path i).hitOccurrence A (hHits i)
  let hitRole : Fin s → {v : Fin G.roles // v ∈ A} := fun i =>
    ⟨(family.path i).vertexAt (occurrence i),
      (family.path i).vertexAt_hitOccurrence_mem A (hHits i)⟩
  have hInjective : Function.Injective hitRole := by
    intro i j hij
    have hRole :
        (family.path i).vertexAt (occurrence i) =
          (family.path j).vertexAt (occurrence j) :=
      congrArg Subtype.val hij
    have hSigma :
        (⟨i, occurrence i⟩ :
          Σ t : Fin s, Fin (family.path t).vertexCount) =
        ⟨j, occurrence j⟩ :=
      family.vertexAt_injective hRole
    exact congrArg Sigma.fst hSigma
  simpa [A] using Fintype.card_le_of_injective hitRole hInjective

/-- Complete interval-certificate form of C079 equation (6): the path packing
forces the layer lower bounds, and double counting gives the exact total
excess. -/
theorem C079IntervalCertificate.sum_layer_excess_eq_of_disjointPaths
    {G : PartiteShape} {q s : ℕ} (C : C079IntervalCertificate G q)
    (family : G.VertexDisjointRightToLeftPaths s) :
    (∑ k ∈ Finset.Icc 1 q,
      ((c079IntervalLayer C.ell C.upper k).card - s)) =
      (∑ v : Fin G.roles, (C.upper v - C.ell v)) - s * q := by
  exact c079_sum_intervalLayer_excess_eq C.ell C.upper q s C.upper_le
    (fun k hk => C.pathCount_le_layer_card family hk)


end GraphMatrixReplica
