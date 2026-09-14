import R6.PaperToPartiteBridge

/-! # Combinatorial exponent bound for paper final flattenings

This file formalizes the two finite-graph inequalities used in BLNvH v2,
lines (27): row/column overlap is a boundary separator, while a role omitted
from both sides is an isolated middle role.  Consequently the exponent of
every final flattening is bounded by
`|V| - |S_min| + |W_iso|`.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The role-side data induced by a final flattening.  Assigning an edge
coordinate to a side places both of its endpoint roles on that side. -/
structure PaperFinalFlattening (G : PaperShape) where
  rowRoles : Finset (Fin G.roles)
  colRoles : Finset (Fin G.roles)
  left_mem_row : G.leftBoundaryFinset ⊆ rowRoles
  right_mem_col : G.rightBoundaryFinset ⊆ colRoles
  edge_side : ∀ e : Fin G.edges,
    (G.source e ∈ rowRoles ∧ G.target e ∈ rowRoles) ∨
      (G.source e ∈ colRoles ∧ G.target e ∈ colRoles)

/-- Roles visible on both sides of the flattening. -/
def PaperFinalFlattening.separatorRoles {G : PaperShape}
    (F : PaperFinalFlattening G) : Finset (Fin G.roles) :=
  F.rowRoles ∩ F.colRoles

/-- Roles invisible on either side of the flattening. -/
def PaperFinalFlattening.omittedRoles {G : PaperShape}
    (F : PaperFinalFlattening G) : Finset (Fin G.roles) :=
  Finset.univ \ (F.rowRoles ∪ F.colRoles)

/-- The isolated middle roles of the paper shape. -/
def PaperShape.isolatedMiddleRoles (G : PaperShape) :
    Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter G.IsolatedMiddleRole

@[simp] theorem PaperShape.mem_isolatedMiddleRoles_iff
    (G : PaperShape) (v : Fin G.roles) :
    v ∈ G.isolatedMiddleRoles ↔ G.IsolatedMiddleRole v := by
  classical
  simp [PaperShape.isolatedMiddleRoles]

/-- Across one path step, a column-side vertex that is not on the row side
forces the next vertex to remain on the column side. -/
theorem PaperFinalFlattening.step_end_mem_col
    {G : PaperShape} (F : PaperFinalFlattening G)
    {v w : Fin G.roles} (e : Fin G.edges)
    (hAtStart : G.toPartiteShape.EdgeIncident e v)
    (hAtEnd : G.toPartiteShape.EdgeIncident e w)
    (hvCol : v ∈ F.colRoles) (hvNotRow : v ∉ F.rowRoles) :
    w ∈ F.colRoles := by
  rcases F.edge_side e with hRow | hCol
  · exfalso
    apply hvNotRow
    rcases hAtStart with hSource | hTarget
    · simpa only using hSource ▸ hRow.1
    · simpa only using hTarget ▸ hRow.2
  · rcases hAtEnd with hSource | hTarget
    · simpa only using hSource ▸ hCol.1
    · simpa only using hTarget ▸ hCol.2

/-- A certified occurrence at which a column-starting path meets the role
intersection.  The explicit vertex-count measure avoids relying on the
generated size of this indexed path type. -/
def PaperFinalFlattening.separatorHit
    {G : PaperShape} (F : PaperFinalFlattening G)
    {v : Fin G.roles} (path : G.toPartiteShape.EdgePathToLeft v)
    (hvCol : v ∈ F.colRoles) :
    {o : Fin path.vertexCount // path.vertexAt o ∈ F.separatorRoles} := by
  classical
  exact match path with
  | .finish v hLeft =>
      ⟨PartiteShape.EdgePathToLeft.headOccurrence _, by
        have hvRow : v ∈ F.rowRoles := F.left_mem_row hLeft
        exact Finset.mem_inter.2 ⟨hvRow, hvCol⟩⟩
  | .step (v := v) e w hAtStart hAtEnd tail =>
      if hvRow : v ∈ F.rowRoles then
        ⟨PartiteShape.EdgePathToLeft.headOccurrence _, by
          exact Finset.mem_inter.2 ⟨hvRow, hvCol⟩⟩
      else
        have hwCol : w ∈ F.colRoles :=
          F.step_end_mem_col e hAtStart hAtEnd hvCol hvRow
        let hit := F.separatorHit tail hwCol
        ⟨Fin.succ hit.1, by
          change tail.vertexAt hit.1 ∈ F.separatorRoles
          exact hit.2⟩
termination_by path.vertexCount
decreasing_by simp [PartiteShape.EdgePathToLeft.vertexCount]

/-- If a path starts on the column side, it must encounter a role carried by
both sides before ending at the left boundary. -/
theorem PaperFinalFlattening.path_hits_separatorRoles
    {G : PaperShape} (F : PaperFinalFlattening G)
    {v : Fin G.roles} (path : G.toPartiteShape.EdgePathToLeft v)
    (hvCol : v ∈ F.colRoles) :
    ∃ o : Fin path.vertexCount, path.vertexAt o ∈ F.separatorRoles :=
  ⟨(F.separatorHit path hvCol).1, (F.separatorHit path hvCol).2⟩

/-- The row/column intersection of every final flattening is a genuine
right-to-left vertex separator, including singleton paths from `U ∩ V`. -/
theorem PaperFinalFlattening.separatorRoles_isRightLeftSeparator
    {G : PaperShape} (F : PaperFinalFlattening G) :
    G.toPartiteShape.IsRightLeftSeparator F.separatorRoles := by
  intro v hRight path
  exact F.path_hits_separatorRoles path (F.right_mem_col hRight)

/-- A role omitted from both sides has no boundary occurrence and no incident
edge, hence is an isolated middle role. -/
theorem PaperFinalFlattening.omittedRoles_subset_isolatedMiddleRoles
    {G : PaperShape} (F : PaperFinalFlattening G) :
    F.omittedRoles ⊆ G.isolatedMiddleRoles := by
  classical
  intro v hv
  have hvBoth : v ∉ F.rowRoles ∧ v ∉ F.colRoles := by
    simpa [PaperFinalFlattening.omittedRoles] using hv
  have hvRow : v ∉ F.rowRoles := by
    exact hvBoth.1
  have hvCol : v ∉ F.colRoles := by
    exact hvBoth.2
  apply (G.mem_isolatedMiddleRoles_iff v).2
  refine ⟨?_, ?_, ?_⟩
  · intro hvLeft
    exact hvRow (F.left_mem_row hvLeft)
  · intro hvRight
    exact hvCol (F.right_mem_col hvRight)
  · intro e
    constructor
    · intro hSource
      rcases F.edge_side e with hRow | hCol
      · exact hvRow (by simpa only [hSource] using hRow.1)
      · exact hvCol (by simpa only [hSource] using hCol.1)
    · intro hTarget
      rcases F.edge_side e with hRow | hCol
      · exact hvRow (by simpa only [hTarget] using hRow.2)
      · exact hvCol (by simpa only [hTarget] using hCol.2)

/-- The first cardinal inequality in the paper: a minimum separator cannot
be larger than the row/column overlap of a final flattening. -/
theorem PaperFinalFlattening.minimumCut_card_le_separatorRoles_card
    {G : PaperShape} (F : PaperFinalFlattening G)
    (cut : Finset (Fin G.roles))
    (hCut : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    cut.card ≤ F.separatorRoles.card :=
  hCut.2 F.separatorRoles F.separatorRoles_isRightLeftSeparator

/-- The second cardinal inequality in the paper: roles omitted from both
sides are bounded by the number of isolated middle roles. -/
theorem PaperFinalFlattening.omittedRoles_card_le_isolatedMiddleRoles_card
    {G : PaperShape} (F : PaperFinalFlattening G) :
    F.omittedRoles.card ≤ G.isolatedMiddleRoles.card :=
  Finset.card_le_card F.omittedRoles_subset_isolatedMiddleRoles

/-- Exact natural-number form of the polynomial exponent comparison in
BLNvH v2, equation (27). -/
theorem PaperFinalFlattening.exponentNumerator_le
    {G : PaperShape} (F : PaperFinalFlattening G)
    (cut : Finset (Fin G.roles))
    (hCut : G.toPartiteShape.IsMinimumRightLeftSeparator cut) :
    G.roles - F.separatorRoles.card + F.omittedRoles.card ≤
      G.roles - cut.card + G.isolatedMiddleRoles.card := by
  exact Nat.add_le_add
    (Nat.sub_le_sub_left (F.minimumCut_card_le_separatorRoles_card cut hCut)
      G.roles)
    F.omittedRoles_card_le_isolatedMiddleRoles_card

#print axioms PaperFinalFlattening.separatorRoles_isRightLeftSeparator
#print axioms PaperFinalFlattening.omittedRoles_subset_isolatedMiddleRoles
#print axioms PaperFinalFlattening.exponentNumerator_le

end GraphMatrixReplica
