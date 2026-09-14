import GraphMatrix.Probability.Internal.GroupedMoments

/-!
# Actual graph addresses and heterogeneous label cardinalities

The only model is the supplied `PaperShape` and its genuine cut component.
The fixed-boundary internal address injection is proved here from connectedness
and attachment. It is not a field or a hypothesis of the moment theorems.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000

/-- Every interior role of an active component has an actual internal edge.
The neighbor is obtained in the induced cut graph, not the ambient noise graph. -/
theorem interior_incident_internal
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (hActive : c.IsActive)
    (v : P1InteriorRole P cut c) :
    ∃ e : P1InternalEdge P cut c, P.source e.1 = v.1 ∨ P.target e.1 = v.1 := by
  classical
  obtain ⟨b, hbB⟩ := p1BoundaryRoles_nonempty P cut c hActive
  have hbK := p1BoundaryRoles_subset_component P cut c hbB
  have hvb : v.1 ≠ b := by
    intro h
    exact v.2.2 (h.symm ▸ hbB)
  obtain ⟨hvCut, hvComp⟩ :=
    (P.toPartiteShape.mem_c079ComponentRoles_iff cut c v.1).mp v.2.1
  obtain ⟨hbCut, hbComp⟩ :=
    (P.toPartiteShape.mem_c079ComponentRoles_iff cut c b).mp hbK
  have hReach : (P.toPartiteShape.c079CutGraph cut).Reachable
      ⟨v.1, hvCut⟩ ⟨b, hbCut⟩ :=
    SimpleGraph.ConnectedComponent.exact (hvComp.trans hbComp.symm)
  have hne : (⟨v.1, hvCut⟩ : {x : Fin P.roles // x ∉ cut}) ≠ ⟨b, hbCut⟩ :=
    fun h => hvb (congrArg Subtype.val h)
  obtain ⟨w, hw⟩ := SimpleGraph.Reachable.nonempty_neighborSet_left hne hReach
  change (P.toPartiteShape.c079RoleGraph).Adj v.1 w.1 at hw
  obtain ⟨hvw, e, hve, hwe⟩ := hw
  have hwK := P.toPartiteShape.c079ComponentRoles_edge_closed_outside_cut
    cut c v.2.1 e hve hwe w.2
  change w.1 ∈ p1ComponentRoles P cut c at hwK
  change P.source e = v.1 ∨ P.target e = v.1 at hve
  change P.source e = w.1 ∨ P.target e = w.1 at hwe
  have hsK : P.source e ∈ p1ComponentRoles P cut c := by
    rcases hve with hs | ht
    · simpa only [hs] using v.2.1
    · rcases hwe with hs | ht'
      · simpa only [hs] using hwK
      · exact (hvw (ht.symm.trans ht')).elim
  have htK : P.target e ∈ p1ComponentRoles P cut c := by
    rcases hve with hs | ht
    · rcases hwe with hs' | ht
      · exact (hvw (hs.symm.trans hs')).elim
      · simpa only [ht] using hwK
    · simpa only [ht] using v.2.1
  exact ⟨⟨e, hsK, htK⟩, hve⟩

/-- One address per actual internal edge occurrence, with its ordered,
role-typed endpoints. -/
def internalKey
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (b : P1BoundaryLabel P dimension cut c)
    (u : P1InteriorLabel P dimension cut c)
    (e : P1InternalEdge P cut c) : P1InternalCoordinate P dimension cut c e :=
  (p1Glue P dimension cut c b u ⟨P.source e.1, e.2.1⟩,
   p1Glue P dimension cut c b u ⟨P.target e.1, e.2.2⟩)

/-- The needed injection keeps the boundary assignment fixed. In particular,
it does not assert a false full-assignment injection for singleton components. -/
theorem internalKey_injective
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (b : P1BoundaryLabel P dimension cut c) :
    Function.Injective (internalKey P dimension cut c b) := by
  classical
  intro u u' h
  funext v
  apply Fin.ext
  obtain ⟨e, he⟩ := interior_incident_internal P cut c hActive v
  rcases he with hs | ht
  · have hsNB : P.source e.1 ∉ p1BoundaryRoles P cut c := by
      simpa only [hs] using v.2.2
    have hp := congrArg
      (fun z : P1InternalCoordinate P dimension cut c e => z.1.val)
      (congrFun h e)
    have hp' :
        (u ⟨P.source e.1, ⟨e.2.1, hsNB⟩⟩).val =
          (u' ⟨P.source e.1, ⟨e.2.1, hsNB⟩⟩).val := by
      simpa [internalKey, p1Glue, hsNB] using hp
    have hev :
        (⟨P.source e.1, ⟨e.2.1, hsNB⟩⟩ : P1InteriorRole P cut c) = v := by
      exact Subtype.ext hs
    cases hev
    exact hp'
  · have htNB : P.target e.1 ∉ p1BoundaryRoles P cut c := by
      simpa only [ht] using v.2.2
    have hp := congrArg
      (fun z : P1InternalCoordinate P dimension cut c e => z.2.val)
      (congrFun h e)
    have hp' :
        (u ⟨P.target e.1, ⟨e.2.2, htNB⟩⟩).val =
          (u' ⟨P.target e.1, ⟨e.2.2, htNB⟩⟩).val := by
      simpa [internalKey, p1Glue, htNB] using hp
    have hev :
        (⟨P.target e.1, ⟨e.2.2, htNB⟩⟩ : P1InteriorRole P cut c) = v := by
      exact Subtype.ext ht
    cases hev
    exact hp'

/-- Exact expansion of the existing integer-cast coefficient, not a newly
postulated surrogate polynomial. -/
theorem gamma_eq_character_sum
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (b : P1BoundaryLabel P dimension cut c)
    (eps : P1InternalSample P dimension cut c) :
    p1Gamma P dimension cut c b eps =
      ∑ u : P1InteriorLabel P dimension cut c,
        character (internalKey P dimension cut c b u) eps := by
  simp [p1Gamma, p1GammaZ, p1InternalMonomialZ, internalKey, character, sign]

def interiorCount (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut) : ℕ :=
  p1DimensionProduct P dimension (p1ComponentRoles P cut c \ p1BoundaryRoles P cut c)

def componentCount (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut) : ℕ :=
  p1DimensionProduct P dimension (p1ComponentRoles P cut c)

def puncturedCount (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) : ℕ :=
  p1DimensionProduct P dimension (p1ComponentRoles P cut c \ {z0})

def internalDegree (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) : ℕ :=
  Fintype.card (P1InternalEdge P cut c)

def secondDegree (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (z0 : Fin P.roles) : ℕ :=
  Fintype.card (P1BoundaryRestRole P cut c z0)

/-- Counting genuinely heterogeneous dependent functions. -/
theorem card_labels_subtype {V : Type} [Fintype V]
    (dimension : V → ℕ) (p : V → Prop) [DecidablePred p]
    (A : Finset V) (hA : ∀ v, v ∈ A ↔ p v) :
    Fintype.card ((v : {v : V // p v}) → Fin (dimension v.1)) =
      ∏ v ∈ A, dimension v := by
  classical
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact (Finset.prod_subtype A hA dimension).symm

theorem card_interiorLabel (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut) :
    Fintype.card (P1InteriorLabel P dimension cut c) =
      interiorCount P dimension cut c := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, interiorCount, p1DimensionProduct]
  exact (Finset.prod_subtype
    (p1ComponentRoles P cut c \ p1BoundaryRoles P cut c)
    (fun v => Finset.mem_sdiff) dimension).symm

theorem card_boundaryLabel (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut) :
    Fintype.card (P1BoundaryLabel P dimension cut c) =
      p1DimensionProduct P dimension (p1BoundaryRoles P cut c) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, p1DimensionProduct]
  exact (Finset.prod_subtype (p1BoundaryRoles P cut c)
    (fun _ => Iff.rfl) dimension).symm

theorem card_boundaryRestLabel (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) :
    Fintype.card (P1BoundaryRestLabel P dimension cut c z0) =
      p1DimensionProduct P dimension (p1BoundaryRoles P cut c \ {z0}) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, p1DimensionProduct]
  exact (Finset.prod_subtype (p1BoundaryRoles P cut c \ {z0})
    (fun v => by simp only [Finset.mem_sdiff, Finset.mem_singleton]) dimension).symm

theorem dimensionProduct_disjoint_union
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (A B C : Finset (Fin P.roles)) (hdis : Disjoint A B) (hcover : A ∪ B = C) :
    p1DimensionProduct P dimension A * p1DimensionProduct P dimension B =
      p1DimensionProduct P dimension C := by
  unfold p1DimensionProduct
  rw [← Finset.prod_union hdis, hcover]

theorem boundary_interior_count
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut) :
    Fintype.card (P1BoundaryLabel P dimension cut c) *
        Fintype.card (P1InteriorLabel P dimension cut c) =
      componentCount P dimension cut c := by
  classical
  rw [card_boundaryLabel, card_interiorLabel]
  apply dimensionProduct_disjoint_union
  · apply Finset.disjoint_left.mpr
    intro v hvB hvI
    exact (Finset.mem_sdiff.mp hvI).2 hvB
  · ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hvB | ⟨hvK, _⟩)
      · exact p1BoundaryRoles_subset_component P cut c hvB
      · exact hvK
    · intro hvK
      by_cases hvB : v ∈ p1BoundaryRoles P cut c
      · exact Or.inl hvB
      · exact Or.inr ⟨hvK, hvB⟩

theorem rest_interior_count
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c) :
    Fintype.card (P1BoundaryRestLabel P dimension cut c z0) *
        Fintype.card (P1InteriorLabel P dimension cut c) =
      puncturedCount P dimension cut c z0 := by
  classical
  rw [card_boundaryRestLabel, card_interiorLabel]
  apply dimensionProduct_disjoint_union
  · apply Finset.disjoint_left.mpr
    intro v hvR hvI
    exact (Finset.mem_sdiff.mp hvI).2 (Finset.mem_sdiff.mp hvR).1
  · ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (⟨hvB, hne⟩ | ⟨hvK, hnotB⟩)
      · exact ⟨p1BoundaryRoles_subset_component P cut c hvB, hne⟩
      · refine ⟨hvK, ?_⟩
        intro h
        exact hnotB (h.symm ▸ hz0)
    · rintro ⟨hvK, hne⟩
      by_cases hvB : v ∈ p1BoundaryRoles P cut c
      · exact Or.inl ⟨hvB, hne⟩
      · exact Or.inr ⟨hvK, hvB⟩

/-- Splitting at z0 is a bijection on the actual dependent boundary labels. -/
def boundarySplitEquiv
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c) :
    (Fin (dimension z0) × P1BoundaryRestLabel P dimension cut c z0) ≃
      P1BoundaryLabel P dimension cut c where
  toFun jr := p1InsertBoundary P dimension cut c z0 hz0 jr.1 jr.2
  invFun b := (b ⟨z0, hz0⟩, fun v => b ⟨v.1, v.2.1⟩)
  left_inv jr := by
    rcases jr with ⟨j, r⟩
    apply Prod.ext
    · simp [p1InsertBoundary]
    · funext v
      simp [p1InsertBoundary, v.2.2]
  right_inv b := by
    funext v
    rcases v with ⟨v, hvB⟩
    by_cases hv : v = z0
    · subst v
      simp [p1InsertBoundary]
    · simp [p1InsertBoundary, hv]

theorem Q_eq_sum_R
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c) :
    p1Q P dimension cut c eps =
      ∑ j, p1R P dimension cut c z0 hz0 eps j := by
  classical
  unfold p1Q p1R
  calc
    _ = ∑ jr : Fin (dimension z0) × P1BoundaryRestLabel P dimension cut c z0,
        p1Gamma P dimension cut c
          (p1InsertBoundary P dimension cut c z0 hz0 jr.1 jr.2) eps ^ 2 :=
      (Equiv.sum_comp (boundarySplitEquiv P dimension cut c z0 hz0) _).symm
    _ = _ := by rw [Fintype.sum_prod_type]

/-- The singleton branch is an actual coefficient identity. -/
theorem gamma_singleton
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (v : Fin P.roles)
    (hK : p1ComponentRoles P cut c = {v})
    (b : P1BoundaryLabel P dimension cut c)
    (eps : P1InternalSample P dimension cut c) :
    p1Gamma P dimension cut c b eps = 1 := by
  classical
  have hB : p1BoundaryRoles P cut c = {v} := by
    obtain ⟨w, hw⟩ := p1BoundaryRoles_nonempty P cut c hActive
    have hwv : w = v := by
      have h := p1BoundaryRoles_subset_component P cut c hw
      simpa only [hK, Finset.mem_singleton] using h
    subst w
    apply Finset.Subset.antisymm
    · simpa only [hK] using p1BoundaryRoles_subset_component P cut c
    · exact Finset.singleton_subset_iff.mpr hw
  letI : IsEmpty (P1InternalEdge P cut c) :=
    p1InternalEdge_isEmpty_of_component_singleton P cut c v hK
  have hc : Fintype.card (P1InteriorLabel P dimension cut c) = 1 := by
    rw [card_interiorLabel]
    simp [interiorCount, p1DimensionProduct, hK, hB]
  simp [p1Gamma, p1GammaZ, p1InternalMonomialZ, hc]

/-- No internal edges forces the interior role type to be empty; this is
proved from the same genuine-component fact used for address recovery. -/
theorem interiorRole_isEmpty_of_no_internal_edges
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (hActive : c.IsActive)
    [IsEmpty (P1InternalEdge P cut c)] : IsEmpty (P1InteriorRole P cut c) := by
  refine ⟨?_⟩
  intro v
  obtain ⟨e, he⟩ := interior_incident_internal P cut c hActive v
  exact isEmptyElim e

/-- Empty interior roles alone yield a single Walsh character, not necessarily
one: internal edges may still join two boundary roles. -/
theorem gamma_sq_of_empty_interior
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    [IsEmpty (P1InteriorRole P cut c)]
    (b : P1BoundaryLabel P dimension cut c)
    (eps : P1InternalSample P dimension cut c) :
    p1Gamma P dimension cut c b eps ^ 2 = 1 := by
  letI : Unique (P1InteriorLabel P dimension cut c) :=
    { default := fun v => isEmptyElim v
      uniq := fun u => funext fun v => isEmptyElim v }
  simp [gamma_eq_character_sum]

/-- The stronger no-edge branch has coefficient exactly one. -/
theorem gamma_of_no_internal_edges
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) [IsEmpty (P1InternalEdge P cut c)]
    (b : P1BoundaryLabel P dimension cut c)
    (eps : P1InternalSample P dimension cut c) :
    p1Gamma P dimension cut c b eps = 1 := by
  letI : IsEmpty (P1InteriorRole P cut c) :=
    interiorRole_isEmpty_of_no_internal_edges P cut c hActive
  letI : Unique (P1InteriorLabel P dimension cut c) :=
    { default := fun v => isEmptyElim v
      uniq := fun u => funext fun v => isEmptyElim v }
  simp [gamma_eq_character_sum, character]

end GraphMatrixReplica.P1AD
