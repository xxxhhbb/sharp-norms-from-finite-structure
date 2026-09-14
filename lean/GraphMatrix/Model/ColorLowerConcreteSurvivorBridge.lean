import GraphMatrix.Model.ColorLowerConcreteTag
import GraphMatrix.Model.ColorLowerRoleReconstruction

/-! # Concrete fixed-class Walsh survivor to a shape automorphism

This is the graph-theoretic survivor classification for an actual globally
injective paper realization and a fixed disjoint role coloring. The only
remaining color hypothesis is that the compressed boundary labels lie in
their prescribed boundary-role classes. A later matrix-entry bridge must
derive that hypothesis from row/column compression and sum all survivors.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A realization compatible with a compressed colored boundary row has
the prescribed color at every left boundary role. -/
theorem PaperRoleColoring.leftBoundaryColor_of_paperEntryCompatible
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension)
    (hCompatible : paperEntryCompatible G phi (C.paperRow row) (C.paperCol col)) :
    ∀ v ∈ G.leftBoundaryFinset, C.roleOfLabel? (phi v) = some v := by
  intro v hv
  obtain ⟨i, hi⟩ := (G.mem_leftBoundaryFinset_iff v).mp hv
  subst v
  rw [hCompatible.1 i]
  exact C.roleOfLabel?_embedding _ _

/-- The corresponding right boundary condition follows from column
compression, including roles shared with the left boundary. -/
theorem PaperRoleColoring.rightBoundaryColor_of_paperEntryCompatible
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension)
    (hCompatible : paperEntryCompatible G phi (C.paperRow row) (C.paperCol col)) :
    ∀ v ∈ G.rightBoundaryFinset, C.roleOfLabel? (phi v) = some v := by
  intro v hv
  obtain ⟨i, hi⟩ := (G.mem_rightBoundaryFinset_iff v).mp hv
  subst v
  rw [hCompatible.2 i]
  exact C.roleOfLabel?_embedding _ _

/-- A globally injective realization whose concrete edge-color Walsh word
survives is a boundary-fixing shape automorphism, provided its boundary
labels carry the prescribed role colors. The role map, edge-color map, and
their bijectivity are all constructed, rather than supplied. -/
def PaperRoleColoring.survivingRealization_toAutomorphism
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount C.targetEdgeTag
        (List.ofFn fun e : Fin G.edges =>
          (phi (G.source e), phi (G.target e))) k))
    (hLeft : ∀ v ∈ G.leftBoundaryFinset,
      C.roleOfLabel? (phi v) = some v)
    (hRight : ∀ v ∈ G.rightBoundaryFinset,
      C.roleOfLabel? (phi v) = some v)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    G.R16BoundaryFixingAutomorphism := by
  let word : Fin G.edges → Fin n × Fin n :=
    fun e => (phi (G.source e), phi (G.target e))
  let vertexColor : Fin G.roles → Option (Fin G.roles) :=
    fun v => C.roleOfLabel? (phi v)
  have hEndpoints : ∀ (e k : Fin G.edges),
      C.targetEdgeTag (paperUnorderedPair (word e).1 (word e).2) =
        some k →
        (vertexColor (G.source e) = some (G.source k) ∧
          vertexColor (G.target e) = some (G.target k)) ∨
        (vertexColor (G.source e) = some (G.target k) ∧
          vertexColor (G.target e) = some (G.source k)) := by
    intro e k hTag
    let i : Fin n := phi (G.source e)
    let j : Fin n := phi (G.target e)
    change C.targetEdgeTag (paperUnorderedPair i j) = some k at hTag
    rcases le_total i j with hij | hji
    · have hOrdered : C.targetEdgeTag (i, j) = some k := by
        simpa [paperUnorderedPair, min_eq_left hij, max_eq_right hij]
          using hTag
      exact C.targetEdgeTag_endpoint_roles i j k hOrdered
    · have hOrdered : C.targetEdgeTag (j, i) = some k := by
        simpa [paperUnorderedPair, min_eq_right hji, max_eq_left hji]
          using hTag
      rcases C.targetEdgeTag_endpoint_roles j i k hOrdered with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
  exact paperR16SurvivingWord_toAutomorphism
    C.targetEdgeTag word vertexColor hOdd hEndpoints hLeft hRight
    hNoIsolated

/-- The fully concrete survivor classification from actual colored
boundary compression: no edge-color, role-map, tag, or boundary-color
certificate is separately assumed. -/
def PaperRoleColoring.survivingCompressedRealization_toAutomorphism
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension)
    (hCompatible : paperEntryCompatible G phi (C.paperRow row) (C.paperCol col))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount C.targetEdgeTag
        (List.ofFn fun e : Fin G.edges =>
          (phi (G.source e), phi (G.target e))) k))
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    G.R16BoundaryFixingAutomorphism :=
  C.survivingRealization_toAutomorphism phi hOdd
    (C.leftBoundaryColor_of_paperEntryCompatible phi row col hCompatible)
    (C.rightBoundaryColor_of_paperEntryCompatible phi row col hCompatible)
    hNoIsolated


end GraphMatrixReplica
