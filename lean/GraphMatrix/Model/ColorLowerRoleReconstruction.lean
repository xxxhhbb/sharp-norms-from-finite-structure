import GraphMatrix.Model.ColorLowerTagSaturation

/-! # Reconstructing the role-color map from a surviving edge word

The data here is exactly what a concrete fixed-class tag must provide:
whenever a realized source edge has target tag `k`, the option-valued
colors of its two endpoint roles match those of `k` (possibly swapped).
Boundary compression fixes boundary-role colors. Walsh survival itself
then forces every source edge tagged; no isolated middle role remains
uncolored. The resulting role and edge maps form a boundary-fixing
automorphism. The concrete tag/ambient-realization adapter is separate.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Odd Walsh survival colors every role, using tagged incident edges for
middle roles and compression-fixed colors for boundary roles. -/
theorem paperR16SurvivingWord_allRolesColored
    {G : PaperShape} {n : ℕ}
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (word : Fin G.edges → Fin n × Fin n)
    (vertexColor : Fin G.roles → Option (Fin G.roles))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount tag (List.ofFn word) k))
    (hTagEndpoints : ∀ (e : Fin G.edges) (k : Fin G.edges),
      tag (paperUnorderedPair (word e).1 (word e).2) = some k →
        (vertexColor (G.source e) = some (G.source k) ∧
          vertexColor (G.target e) = some (G.target k)) ∨
        (vertexColor (G.source e) = some (G.target k) ∧
          vertexColor (G.target e) = some (G.source k)))
    (hLeft : ∀ v ∈ G.leftBoundaryFinset, vertexColor v = some v)
    (hRight : ∀ v ∈ G.rightBoundaryFinset, vertexColor v = some v)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    ∀ v : Fin G.roles, ∃ c : Fin G.roles, vertexColor v = some c := by
  let edgeColor : Fin G.edges → Fin G.edges :=
    (paperR16TaggedWord_hasEdgeColorMap tag word hOdd).choose
  have hTag : ∀ e : Fin G.edges,
      tag (paperUnorderedPair (word e).1 (word e).2) =
        some (edgeColor e) :=
    (paperR16TaggedWord_hasEdgeColorMap tag word hOdd).choose_spec
  intro v
  have hCovered :=
    (G.hasNoIsolatedMiddleRoles_iff_all_roleCovered).mp hNoIsolated v
  rcases hCovered with ⟨e, he⟩ | hL | hR
  · rcases hTagEndpoints e (edgeColor e) (hTag e) with h | h
    · rcases he with he | he
      · subst v
        exact ⟨G.source (edgeColor e), h.1⟩
      · subst v
        exact ⟨G.target (edgeColor e), h.2⟩
    · rcases he with he | he
      · subst v
        exact ⟨G.target (edgeColor e), h.1⟩
      · subst v
        exact ⟨G.source (edgeColor e), h.2⟩
  · exact ⟨v, hLeft v hL⟩
  · exact ⟨v, hRight v hR⟩

/-- A surviving edge word reconstructs both maps and produces the exact
boundary-fixing automorphism. Only the concrete tag endpoint law and
boundary-color law are input; `hTag` and the role map are derived. -/
def paperR16SurvivingWord_toAutomorphism
    {G : PaperShape} {n : ℕ}
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (word : Fin G.edges → Fin n × Fin n)
    (vertexColor : Fin G.roles → Option (Fin G.roles))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount tag (List.ofFn word) k))
    (hTagEndpoints : ∀ (e : Fin G.edges) (k : Fin G.edges),
      tag (paperUnorderedPair (word e).1 (word e).2) = some k →
        (vertexColor (G.source e) = some (G.source k) ∧
          vertexColor (G.target e) = some (G.target k)) ∨
        (vertexColor (G.source e) = some (G.target k) ∧
          vertexColor (G.target e) = some (G.source k)))
    (hLeft : ∀ v ∈ G.leftBoundaryFinset, vertexColor v = some v)
    (hRight : ∀ v ∈ G.rightBoundaryFinset, vertexColor v = some v)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    G.R16BoundaryFixingAutomorphism := by
  classical
  let edgeColor : Fin G.edges → Fin G.edges :=
    (paperR16TaggedWord_hasEdgeColorMap tag word hOdd).choose
  have hTag : ∀ e : Fin G.edges,
      tag (paperUnorderedPair (word e).1 (word e).2) =
        some (edgeColor e) :=
    (paperR16TaggedWord_hasEdgeColorMap tag word hOdd).choose_spec
  have hEvery := paperR16SurvivingWord_allRolesColored
    tag word vertexColor hOdd hTagEndpoints hLeft hRight hNoIsolated
  let role : Fin G.roles → Fin G.roles := fun v => (hEvery v).choose
  have hRole : ∀ v : Fin G.roles, vertexColor v = some (role v) := by
    intro v
    exact (hEvery v).choose_spec
  have hEndpoints : ∀ e : Fin G.edges,
      (role (G.source e) = G.source (edgeColor e) ∧
        role (G.target e) = G.target (edgeColor e)) ∨
      (role (G.source e) = G.target (edgeColor e) ∧
        role (G.target e) = G.source (edgeColor e)) := by
    intro e
    rcases hTagEndpoints e (edgeColor e) (hTag e) with h | h
    · left
      exact ⟨Option.some.inj ((hRole _).symm.trans h.1),
        Option.some.inj ((hRole _).symm.trans h.2)⟩
    · right
      exact ⟨Option.some.inj ((hRole _).symm.trans h.1),
        Option.some.inj ((hRole _).symm.trans h.2)⟩
  have hLeftRole : ∀ v ∈ G.leftBoundaryFinset, role v = v := by
    intro v hv
    exact Option.some.inj ((hRole v).symm.trans (hLeft v hv))
  have hRightRole : ∀ v ∈ G.rightBoundaryFinset, role v = v := by
    intro v hv
    exact Option.some.inj ((hRole v).symm.trans (hRight v hv))
  exact paperR16TaggedWord_toAutomorphism tag word role edgeColor
    hTag hOdd hEndpoints hLeftRole hRightRole hNoIsolated


end GraphMatrixReplica
