import R6.PaperR16ColorLowerFourier
import R6.PaperRoleColoredNoiseExtension

/-!
# Concrete partial role and edge-color tags for the R16 lower projection

The disjoint role embeddings need not cover all ambient labels.  Accordingly
both the role of one label and the target edge of one ambient edge are
optional.  They are defined from the existing embeddings, with no balanced
partition or noise assumptions.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The role color of an ambient label, when it lies in one of the selected
disjoint role classes.  Remaining ambient labels receive `none`. -/
def PaperRoleColoring.roleOfLabel?
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) (i : Fin n) :
    Option (Fin G.roles) := by
  classical
  exact if h : ∃ z : Σ v : Fin G.roles, Fin (dimension v),
      C.embedding z.1 z.2 = i then some h.choose.1 else none

/-- Disjointness makes the role of every embedded label exact. -/
theorem PaperRoleColoring.roleOfLabel?_embedding
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (v : Fin G.roles) (a : Fin (dimension v)) :
    C.roleOfLabel? (C.embedding v a) = some v := by
  classical
  unfold roleOfLabel?
  split
  next h =>
    have hv : h.choose.1 = v := by
      by_contra hne
      exact C.disjoint hne h.choose.2 a h.choose_spec
    simp [hv]
  next h => exact (h ⟨⟨v, a⟩, rfl⟩).elim

/-- If a label has a role tag, it belongs to that role's selected class. -/
theorem PaperRoleColoring.roleOfLabel?_eq_some_iff
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (i : Fin n) (v : Fin G.roles) :
    C.roleOfLabel? i = some v ↔
      ∃ a : Fin (dimension v), C.embedding v a = i := by
  classical
  constructor
  · intro htag
    unfold roleOfLabel? at htag
    split at htag
    next h =>
      have hv : h.choose.1 = v := Option.some.inj htag
      subst v
      exact ⟨h.choose.2, h.choose_spec⟩
    next h => cases htag
  · rintro ⟨a, rfl⟩
    exact C.roleOfLabel?_embedding v a

/-- The tag of an ambient ordered pair is the unique shape edge whose
colored coordinate maps to that pair; pairs outside the selected edge colors
are untagged.  It is used at canonical unordered pairs in the Fourier module. -/
def PaperRoleColoring.targetEdgeTag
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (pair : Fin n × Fin n) : Option (Fin G.edges) := by
  classical
  exact if h : ∃ z : PaperColoredEdgeCoordinate G dimension,
      C.ambientEdge z = pair then some h.choose.1 else none

/-- Every selected colored edge coordinate has its defining target tag. -/
theorem PaperRoleColoring.targetEdgeTag_ambientEdge
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (z : PaperColoredEdgeCoordinate G dimension) :
    C.targetEdgeTag (C.ambientEdge z) = some z.1 := by
  classical
  unfold targetEdgeTag
  split
  next h =>
    have hz : h.choose = z := C.ambientEdge_injective h.choose_spec
    simp [hz]
  next h => exact (h ⟨z, rfl⟩).elim

/-- A nonempty edge tag has a concrete pair of labels in the two endpoint
role classes. -/
theorem PaperRoleColoring.targetEdgeTag_eq_some_iff
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (pair : Fin n × Fin n) (e : Fin G.edges) :
    C.targetEdgeTag pair = some e ↔
      ∃ (a : Fin (dimension (G.source e)))
        (b : Fin (dimension (G.target e))),
          C.ambientEdge ⟨e, (a, b)⟩ = pair := by
  classical
  constructor
  · intro htag
    unfold targetEdgeTag at htag
    split at htag
    next h =>
      have he : h.choose.1 = e := Option.some.inj htag
      subst e
      exact ⟨h.choose.2.1, h.choose.2.2, h.choose_spec⟩
    next h => cases htag
  · rintro ⟨a, b, hpair⟩
    rw [← hpair]
    exact C.targetEdgeTag_ambientEdge ⟨e, (a, b)⟩

/-- A canonical unordered pair is either its original ordered endpoints or
their reversal. -/
theorem paperUnorderedPair_eq_iff_orientation {n : ℕ}
    (x y i j : Fin n)
    (h : paperUnorderedPair x y = (i, j)) :
    (i = x ∧ j = y) ∨ (i = y ∧ j = x) := by
  rcases le_total x y with hxy | hyx
  · have hmin : min x y = x := min_eq_left hxy
    have hmax : max x y = y := max_eq_right hxy
    left
    simpa [paperUnorderedPair, hmin, hmax] using h.symm
  · have hmin : min x y = y := min_eq_right hyx
    have hmax : max x y = x := max_eq_left hyx
    right
    simpa [paperUnorderedPair, hmin, hmax] using h.symm

/-- A tagged ambient edge has exactly the target edge's endpoint role colors,
with the two orientations allowed because paper noise is unordered. -/
theorem PaperRoleColoring.targetEdgeTag_endpoint_roles
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (i j : Fin n) (e : Fin G.edges)
    (htag : C.targetEdgeTag (i, j) = some e) :
    (C.roleOfLabel? i = some (G.source e) ∧
      C.roleOfLabel? j = some (G.target e)) ∨
    (C.roleOfLabel? i = some (G.target e) ∧
      C.roleOfLabel? j = some (G.source e)) := by
  obtain ⟨a, b, hpair⟩ := (C.targetEdgeTag_eq_some_iff (i, j) e).1 htag
  have horient := paperUnorderedPair_eq_iff_orientation
    (C.embedding (G.source e) a)
    (C.embedding (G.target e) b) i j (by simpa [PaperRoleColoring.ambientEdge] using hpair)
  rcases horient with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · left
    rw [hi, hj]
    exact ⟨C.roleOfLabel?_embedding _ _, C.roleOfLabel?_embedding _ _⟩
  · right
    rw [hi, hj]
    exact ⟨C.roleOfLabel?_embedding _ _, C.roleOfLabel?_embedding _ _⟩

/-- Conversely, a pair whose endpoint labels lie in the source and target
role classes carries that shape edge's target color tag. -/
theorem PaperRoleColoring.targetEdgeTag_of_endpoint_roles
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (i j : Fin n) (e : Fin G.edges)
    (hi : C.roleOfLabel? i = some (G.source e))
    (hj : C.roleOfLabel? j = some (G.target e)) :
    C.targetEdgeTag (paperUnorderedPair i j) = some e := by
  obtain ⟨a, ha⟩ := (C.roleOfLabel?_eq_some_iff i (G.source e)).1 hi
  obtain ⟨b, hb⟩ := (C.roleOfLabel?_eq_some_iff j (G.target e)).1 hj
  subst i
  subst j
  simpa [PaperRoleColoring.ambientEdge] using
    C.targetEdgeTag_ambientEdge ⟨e, (a, b)⟩

/-- The same conclusion holds if the two ambient endpoints are presented in
the opposite order. -/
theorem PaperRoleColoring.targetEdgeTag_of_endpoint_roles_swapped
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (i j : Fin n) (e : Fin G.edges)
    (hi : C.roleOfLabel? i = some (G.target e))
    (hj : C.roleOfLabel? j = some (G.source e)) :
    C.targetEdgeTag (paperUnorderedPair i j) = some e := by
  have h := C.targetEdgeTag_of_endpoint_roles j i e hj hi
  simpa [paperUnorderedPair, min_comm, max_comm] using h

#print axioms PaperRoleColoring.roleOfLabel?_embedding
#print axioms PaperRoleColoring.roleOfLabel?_eq_some_iff
#print axioms PaperRoleColoring.targetEdgeTag_ambientEdge
#print axioms PaperRoleColoring.targetEdgeTag_eq_some_iff
#print axioms paperUnorderedPair_eq_iff_orientation
#print axioms PaperRoleColoring.targetEdgeTag_endpoint_roles
#print axioms PaperRoleColoring.targetEdgeTag_of_endpoint_roles
#print axioms PaperRoleColoring.targetEdgeTag_of_endpoint_roles_swapped

end GraphMatrixReplica
