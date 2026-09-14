import GraphMatrix.SeparatorPathCertificate

/-!
Exact path witness supplied by a minimum separator. This is the
graph-theoretic input used in lower separator flattening; it does not yet
assign primitive edge coordinates to the two sides.
-/

noncomputable section

namespace GraphMatrixReplica.Model.Separator

theorem minimumSeparator_erase_not_separator
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (hMin : G.IsMinimumRightLeftSeparator cut)
    {z : Fin G.roles} (hz : z ∈ cut) :
    ¬ G.IsRightLeftSeparator (cut.erase z) := by
  intro hErase
  have hCard := hMin.2 (cut.erase z) hErase
  have hStrict := Finset.card_erase_lt_of_mem hz
  omega

/-- Every vertex of a minimum separator is essential: there is a path from
the right boundary to the left boundary whose *only* separator role is `z`.
The path may visit `z` more than once; the claim is about roles, not a unique
occurrence. -/
theorem minimumSeparator_vertex_has_sole_hit_path
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (hMin : G.IsMinimumRightLeftSeparator cut)
    {z : Fin G.roles} (hz : z ∈ cut) :
    ∃ (v : Fin G.roles) (_hv : v ∈ G.rightBoundary)
      (path : G.EdgePathToLeft v),
      (∃ o : Fin path.vertexCount, path.vertexAt o = z) ∧
      (∀ o : Fin path.vertexCount,
        path.vertexAt o ∈ cut → path.vertexAt o = z) := by
  have hNot := minimumSeparator_erase_not_separator hMin hz
  dsimp [PartiteShape.IsRightLeftSeparator] at hNot
  push Not at hNot
  obtain ⟨v, hv, path, hAvoid⟩ := hNot
  refine ⟨v, hv, path, ?_, ?_⟩
  · obtain ⟨o, ho⟩ := hMin.1 v hv path
    refine ⟨o, ?_⟩
    by_contra hNe
    exact hAvoid o (Finset.mem_erase.mpr ⟨hNe, ho⟩)
  · intro o ho
    by_contra hNe
    exact hAvoid o (Finset.mem_erase.mpr ⟨hNe, ho⟩)


end GraphMatrixReplica.Model.Separator
