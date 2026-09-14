import R6.PaperR16ComponentSideScratch
import R6.PaperR16MinimumSeparatorPathScratch
import R6.PaperToPartiteBridge

set_option autoImplicit false

/-!
# C1: actual primitive observations after deleting active components

Adapted from the C1 return; proof statements are unchanged.
Local execution and source hashes are recorded in the integration validation run.

The two Scratch imports are unchanged copies of the corresponding files from
`scratch_lower_separator/` in the supplied C1 package, installed under `R6/`.

The observation definitions below contain only original boundary roles and
endpoints of actual fresh edge coordinates. In particular, they do NOT insert
`cut` by definition. The abstract `SeparatorScratch.rowRoles/colRoles` are
used only for the easy containment direction.

`false` = row, `true` = column. Edge identifiers and source/target ports are
retained throughout. An entire edge-address pair is placed on one side.

The first-hit and last-hit arguments use recursion on the actual `EdgePathToLeft`;
no path-simplicity, boundary-disjointness, boundary-core, or equal-dimension
hypothesis is introduced.
-/

noncomputable section

namespace GraphMatrixReplica.PaperR16.ActualPrimitiveObservations

open GraphMatrixReplica.PaperR16.SeparatorScratch

variable (G : PartiteShape) (cut : Finset (Fin G.roles))

/-! ## 1. Actual active union, retained roles, and fresh edges -/

/-- The union of the genuine active connected components of `G - cut`. -/
def activeUnion : Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ c : G.C079CutComponent cut,
      c.IsActive ∧ v ∈ G.c079ComponentRoles cut c

/-- Roles remaining after the active components have been summed out. -/
def retainedRoles : Finset (Fin G.roles) :=
  Finset.univ \ activeUnion G cut

/-- An edge is fresh exactly when neither endpoint was deleted.
Thus every edge with AT LEAST ONE endpoint in the active union is frozen. -/
def Fresh (e : Fin G.edges) : Prop :=
  G.source e ∈ retainedRoles G cut ∧ G.target e ∈ retainedRoles G cut

def freshEdges : Finset (Fin G.edges) := by
  classical
  exact Finset.univ.filter (Fresh G cut)

@[simp] theorem mem_activeUnion_iff (v : Fin G.roles) :
    v ∈ activeUnion G cut ↔
      ∃ c : G.C079CutComponent cut,
        c.IsActive ∧ v ∈ G.c079ComponentRoles cut c := by
  classical
  simp [activeUnion]

@[simp] theorem mem_retainedRoles_iff (v : Fin G.roles) :
    v ∈ retainedRoles G cut ↔ v ∉ activeUnion G cut := by
  classical
  simp [retainedRoles]

@[simp] theorem mem_freshEdges_iff (e : Fin G.edges) :
    e ∈ freshEdges G cut ↔ Fresh G cut e := by
  classical
  simp [freshEdges]

theorem fresh_iff_no_deleted_endpoint (e : Fin G.edges) :
    Fresh G cut e ↔
      G.source e ∉ activeUnion G cut ∧ G.target e ∉ activeUnion G cut := by
  simp only [Fresh, mem_retainedRoles_iff]

theorem cut_subset_retainedRoles : cut ⊆ retainedRoles G cut := by
  intro v hv
  apply (mem_retainedRoles_iff G cut v).2
  intro hD
  obtain ⟨c, _, hvc⟩ := (mem_activeUnion_iff G cut v).1 hD
  obtain ⟨hvCut, _⟩ := (G.mem_c079ComponentRoles_iff cut c v).1 hvc
  exact hvCut hv

theorem leftBoundary_subset_retainedRoles :
    G.leftBoundary ⊆ retainedRoles G cut := by
  intro v hv
  apply (mem_retainedRoles_iff G cut v).2
  intro hD
  obtain ⟨c, hActive, hvc⟩ := (mem_activeUnion_iff G cut v).1 hD
  exact (hActive.1 v hvc).1 hv

theorem rightBoundary_subset_retainedRoles :
    G.rightBoundary ⊆ retainedRoles G cut := by
  intro v hv
  apply (mem_retainedRoles_iff G cut v).2
  intro hD
  obtain ⟨c, hActive, hvc⟩ := (mem_activeUnion_iff G cut v).1 hD
  exact (hActive.1 v hvc).2 hv

/-- Outside the separator, membership in the active union is exactly
activity of the vertex's own genuine component. -/
theorem mem_activeUnion_iff_own_component_active
    {v : Fin G.roles} (hv : v ∉ cut) :
    v ∈ activeUnion G cut ↔
      (cutComponentOf G cut v hv).IsActive := by
  constructor
  · intro hD
    obtain ⟨c, hActive, hvc⟩ := (mem_activeUnion_iff G cut v).1 hD
    obtain ⟨hv', hEq⟩ := (G.mem_c079ComponentRoles_iff cut c v).1 hvc
    have hOwn : cutComponentOf G cut v hv = c := hEq
    rw [hOwn]
    exact hActive
  · intro hActive
    exact (mem_activeUnion_iff G cut v).2
      ⟨cutComponentOf G cut v hv, hActive,
        vertex_mem_own_component G cut v hv⟩

/-- A non-separator role in a right-boundary component is retained. -/
theorem retained_of_component_meets_right
    {v : Fin G.roles} (hv : v ∉ cut)
    (hRight : componentMeetsRight G cut (cutComponentOf G cut v hv)) :
    v ∈ retainedRoles G cut := by
  apply (mem_retainedRoles_iff G cut v).2
  intro hD
  have hActive := (mem_activeUnion_iff_own_component_active G cut hv).1 hD
  obtain ⟨b, hb, hbRight⟩ := hRight
  exact (hActive.1 b hb).2 hbRight

/-- A non-separator role in a left-boundary component is retained. -/
theorem retained_of_component_meets_left
    {v : Fin G.roles} (hv : v ∉ cut)
    (hLeft : componentMeetsLeft G cut (cutComponentOf G cut v hv)) :
    v ∈ retainedRoles G cut := by
  apply (mem_retainedRoles_iff G cut v).2
  intro hD
  have hActive := (mem_activeUnion_iff_own_component_active G cut hv).1 hD
  obtain ⟨b, hb, hbLeft⟩ := hLeft
  exact (hActive.1 b hb).1 hbLeft

/-- Deleting whole components cannot remove an edge incident to a retained
role outside the separator. This is proved, not supplied as a hypothesis. -/
theorem fresh_of_incident_retained_outside_cut
    {v : Fin G.roles} (hvC : v ∈ retainedRoles G cut) (hvCut : v ∉ cut)
    (e : Fin G.edges) (hve : G.EdgeIncident e v) : Fresh G cut e := by
  have hEnd : ∀ w : Fin G.roles, G.EdgeIncident e w →
      w ∈ retainedRoles G cut := by
    intro w hwe
    apply (mem_retainedRoles_iff G cut w).2
    intro hwD
    obtain ⟨c, hActive, hwc⟩ := (mem_activeUnion_iff G cut w).1 hwD
    have hvc := G.c079ComponentRoles_edge_closed_outside_cut
      cut c hwc e hwe hve hvCut
    have hvD : v ∈ activeUnion G cut :=
      (mem_activeUnion_iff G cut v).2 ⟨c, hActive, hvc⟩
    exact (mem_retainedRoles_iff G cut v).1 hvC hvD
  exact ⟨hEnd (G.source e) (Or.inl rfl),
    hEnd (G.target e) (Or.inr rfl)⟩

theorem retained_of_fresh_incident
    {e : Fin G.edges} (he : Fresh G cut e)
    {v : Fin G.roles} (hve : G.EdgeIncident e v) :
    v ∈ retainedRoles G cut := by
  rcases hve with hs | ht
  · simpa only [hs] using he.1
  · simpa only [ht] using he.2

/-! ## 2. Whole-edge side assignment -/

/-- A total auxiliary side function on original edge IDs. Only its restriction
to fresh edges is used as a primitive-coordinate assignment. -/
def edgeSide (e : Fin G.edges) : Bool := by
  classical
  exact if hs : G.source e ∈ cut then
    if ht : G.target e ∈ cut then false
    else componentSide G cut (cutComponentOf G cut (G.target e) ht)
  else componentSide G cut (cutComponentOf G cut (G.source e) hs)

/-- The actual domain consists only of remaining original edge IDs. -/
abbrev FreshEdge := {e : Fin G.edges // Fresh G cut e}

def freshEdgeSide (e : FreshEdge G cut) : Bool := edgeSide G cut e.1

/-- Each assigned edge retains its original ID and a proof of freshness. -/
abbrev EdgeOnSide (side : Bool) :=
  {e : Fin G.edges // Fresh G cut e ∧ edgeSide G cut e = side}

theorem edgeSide_eq_false_of_both_mem_cut
    {e : Fin G.edges} (hs : G.source e ∈ cut) (ht : G.target e ∈ cut) :
    edgeSide G cut e = false := by
  classical
  simp [edgeSide, hs, ht]

/-- Either non-cut endpoint determines the same side, including for a
self-loop or a path step whose two recorded roles coincide. -/
theorem edgeSide_eq_componentSide_of_incident
    {v : Fin G.roles} (hv : v ∉ cut)
    (e : Fin G.edges) (hve : G.EdgeIncident e v) :
    edgeSide G cut e = componentSide G cut (cutComponentOf G cut v hv) := by
  classical
  rcases hve with hsEq | htEq
  · subst v
    simp [edgeSide, hv]
  · subst v
    by_cases hs : G.source e ∈ cut
    · simp [edgeSide, hs, hv]
    · have hComp := cutComponentOf_eq_of_edge G cut hs hv e
        (Or.inl rfl) (Or.inr rfl)
      simpa only [edgeSide, dif_neg hs] using
        congrArg (componentSide G cut) hComp

theorem componentSide_true_of_meets_right
    (c : G.C079CutComponent cut) (hRight : componentMeetsRight G cut c) :
    componentSide G cut c = true := by
  classical
  simp [componentSide, hRight]

theorem componentSide_false_of_meets_left
    (hSep : G.IsRightLeftSeparator cut)
    (c : G.C079CutComponent cut) (hLeft : componentMeetsLeft G cut c) :
    componentSide G cut c = false := by
  classical
  have hNotRight : ¬ componentMeetsRight G cut c := by
    intro hRight
    exact separator_component_not_both G cut hSep c ⟨hRight, hLeft⟩
  simp [componentSide, hNotRight]

/-- A boundary-free component that survives deletion is not attached to the
separator; its incident edges are genuinely fresh and go to the row side. -/
theorem retained_boundaryFree_component_not_attached
    (c : G.C079CutComponent cut) (hFree : c.IsBoundaryFree)
    {v : Fin G.roles} (hvc : v ∈ G.c079ComponentRoles cut c)
    (hvC : v ∈ retainedRoles G cut) : ¬ c.IsAttached := by
  intro hAttached
  exact (mem_retainedRoles_iff G cut v).1 hvC
    ((mem_activeUnion_iff G cut v).2 ⟨c, ⟨hFree, hAttached⟩, hvc⟩)

theorem retained_boundaryFree_incident_edge_row
    (c : G.C079CutComponent cut) (hFree : c.IsBoundaryFree)
    {v : Fin G.roles} (hvc : v ∈ G.c079ComponentRoles cut c)
    (hvC : v ∈ retainedRoles G cut)
    (e : Fin G.edges) (hve : G.EdgeIncident e v) :
    Fresh G cut e ∧ edgeSide G cut e = false := by
  classical
  obtain ⟨hvCut, hOwn⟩ := (G.mem_c079ComponentRoles_iff cut c v).1 hvc
  have hNotRight : ¬ componentMeetsRight G cut c := by
    rintro ⟨b, hb, hbRight⟩
    exact (hFree b hb).2 hbRight
  have hSide : componentSide G cut c = false := by
    simp [componentSide, hNotRight]
  refine ⟨fresh_of_incident_retained_outside_cut G cut hvC hvCut e hve, ?_⟩
  calc
    edgeSide G cut e =
        componentSide G cut (cutComponentOf G cut v hvCut) :=
      edgeSide_eq_componentSide_of_incident G cut hvCut e hve
    _ = componentSide G cut c := congrArg (componentSide G cut) hOwn
    _ = false := hSide

/-! ## 3. Actual observation predicates: no inserted separator -/

def rowObserved : Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∈ G.leftBoundary ∨ ∃ e : Fin G.edges,
      Fresh G cut e ∧ edgeSide G cut e = false ∧ G.EdgeIncident e v

def colObserved : Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∈ G.rightBoundary ∨ ∃ e : Fin G.edges,
      Fresh G cut e ∧ edgeSide G cut e = true ∧ G.EdgeIncident e v

@[simp] theorem mem_rowObserved_iff (v : Fin G.roles) :
    v ∈ rowObserved G cut ↔
      v ∈ G.leftBoundary ∨ ∃ e : Fin G.edges,
        Fresh G cut e ∧ edgeSide G cut e = false ∧ G.EdgeIncident e v := by
  classical
  simp [rowObserved]

@[simp] theorem mem_colObserved_iff (v : Fin G.roles) :
    v ∈ colObserved G cut ↔
      v ∈ G.rightBoundary ∨ ∃ e : Fin G.edges,
        Fresh G cut e ∧ edgeSide G cut e = true ∧ G.EdgeIncident e v := by
  classical
  simp [colObserved]

theorem rowObserved_of_leftBoundary
    {v : Fin G.roles} (hv : v ∈ G.leftBoundary) : v ∈ rowObserved G cut :=
  (mem_rowObserved_iff G cut v).2 (Or.inl hv)

theorem colObserved_of_rightBoundary
    {v : Fin G.roles} (hv : v ∈ G.rightBoundary) : v ∈ colObserved G cut :=
  (mem_colObserved_iff G cut v).2 (Or.inl hv)

theorem rowObserved_of_fresh_edge
    {e : Fin G.edges} (he : Fresh G cut e) (hSide : edgeSide G cut e = false)
    {v : Fin G.roles} (hve : G.EdgeIncident e v) : v ∈ rowObserved G cut :=
  (mem_rowObserved_iff G cut v).2 (Or.inr ⟨e, he, hSide, hve⟩)

theorem colObserved_of_fresh_edge
    {e : Fin G.edges} (he : Fresh G cut e) (hSide : edgeSide G cut e = true)
    {v : Fin G.roles} (hve : G.EdgeIncident e v) : v ∈ colObserved G cut :=
  (mem_colObserved_iff G cut v).2 (Or.inr ⟨e, he, hSide, hve⟩)

theorem rowObserved_subset_retainedRoles :
    rowObserved G cut ⊆ retainedRoles G cut := by
  intro v hv
  rcases (mem_rowObserved_iff G cut v).1 hv with hLeft | ⟨e, he, _, hve⟩
  · exact leftBoundary_subset_retainedRoles G cut hLeft
  · exact retained_of_fresh_incident G cut he hve

theorem colObserved_subset_retainedRoles :
    colObserved G cut ⊆ retainedRoles G cut := by
  intro v hv
  rcases (mem_colObserved_iff G cut v).1 hv with hRight | ⟨e, he, _, hve⟩
  · exact rightBoundary_subset_retainedRoles G cut hRight
  · exact retained_of_fresh_incident G cut he hve

/-- Only this EASY direction uses the older abstract role partition. -/
theorem rowObserved_subset_abstract_rowRoles
    (hSep : G.IsRightLeftSeparator cut) :
    rowObserved G cut ⊆ SeparatorScratch.rowRoles G cut := by
  intro v hv
  rcases (mem_rowObserved_iff G cut v).1 hv with hLeft | ⟨e, _, hSide, hve⟩
  · exact SeparatorScratch.leftBoundary_subset_rowRoles G cut hSep hLeft
  · by_cases hvCut : v ∈ cut
    · exact mem_rowRoles_of_cut G cut hvCut
    · apply mem_rowRoles_of_side_false G cut hvCut
      exact (edgeSide_eq_componentSide_of_incident G cut hvCut e hve).symm.trans
        hSide

theorem colObserved_subset_abstract_colRoles :
    colObserved G cut ⊆ SeparatorScratch.colRoles G cut := by
  intro v hv
  rcases (mem_colObserved_iff G cut v).1 hv with hRight | ⟨e, _, hSide, hve⟩
  · exact SeparatorScratch.rightBoundary_subset_colRoles G cut hRight
  · by_cases hvCut : v ∈ cut
    · exact mem_colRoles_of_cut G cut hvCut
    · apply mem_colRoles_of_side_true G cut hvCut
      exact (edgeSide_eq_componentSide_of_incident G cut hvCut e hve).symm.trans
        hSide

theorem observed_inter_subset_cut (hSep : G.IsRightLeftSeparator cut) :
    rowObserved G cut ∩ colObserved G cut ⊆ cut := by
  intro v hv
  have hR := rowObserved_subset_abstract_rowRoles G cut hSep
    (Finset.mem_inter.1 hv).1
  have hC := colObserved_subset_abstract_colRoles G cut
    (Finset.mem_inter.1 hv).2
  have hBoth : v ∈ SeparatorScratch.rowRoles G cut ∩
      SeparatorScratch.colRoles G cut := Finset.mem_inter.2 ⟨hR, hC⟩
  simpa only [componentRoles_inter_eq_cut G cut] using hBoth

/-! ## 4. Recursive first-hit and last-hit proofs on the actual path type -/

/-- A recursive universal predicate on all path occurrences. -/
def pathAll (G : PartiteShape) {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (P : Fin G.roles → Prop) : Prop :=
  match path with
  | .finish v _ => P v
  | .step (v := v) _ _ _ _ tail => P v ∧ pathAll G tail P

/-- A recursive existential predicate on path occurrences. No uniqueness. -/
def pathAny (G : PartiteShape) {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (P : Fin G.roles → Prop) : Prop :=
  match path with
  | .finish v _ => P v
  | .step (v := v) _ _ _ _ tail => P v ∨ pathAny G tail P

theorem pathAll_head {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (P : Fin G.roles → Prop) (h : pathAll G path P) : P v := by
  cases path with
  | finish => exact h
  | step => exact h.1

theorem pathAll_of_vertexAt {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (P : Fin G.roles → Prop) :
    (∀ o : Fin path.vertexCount, P (path.vertexAt o)) → pathAll G path P := by
  induction path with
  | finish v hLeft =>
      intro h
      exact h ⟨0, by simp [PartiteShape.EdgePathToLeft.vertexCount]⟩
  | @step v e w hStart hEnd tail ih =>
      intro h
      refine ⟨?_, ih ?_⟩
      · exact h ⟨0, by simp [PartiteShape.EdgePathToLeft.vertexCount]⟩
      · intro o
        exact h (Fin.succ o)

theorem pathAny_of_vertexAt {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (P : Fin G.roles → Prop) :
    ∀ o : Fin path.vertexCount, P (path.vertexAt o) → pathAny G path P := by
  induction path with
  | finish v hLeft =>
      intro o h
      exact h
  | @step v e w hStart hEnd tail ih =>
      intro o
      refine Fin.cases ?_ (fun j => ?_) o
      · intro h
        exact Or.inl h
      · intro h
        exact Or.inr (ih j h)

/-- If the only possible cut role is z, a suffix containing no z avoids cut. -/
theorem pathAll_not_cut_of_sole_nohit
    (z : Fin G.roles) {v : Fin G.roles} (path : G.EdgePathToLeft v) :
    pathAll G path (fun x => x ∈ cut → x = z) →
    ¬ pathAny G path (fun x => x = z) →
    pathAll G path (fun x => x ∉ cut) := by
  induction path with
  | finish v hLeft =>
      intro hSole hNoHit hvCut
      exact hNoHit (hSole hvCut)
  | @step v e w hStart hEnd tail ih =>
      intro hSole hNoHit
      refine ⟨?_, ih hSole.2 ?_⟩
      · intro hvCut
        exact hNoHit (Or.inl (hSole.1 hvCut))
      · intro hTailHit
        exact hNoHit (Or.inr hTailHit)

/-- An entirely cut-avoiding suffix lies in the component of its terminal
left boundary. This is where the last-hit suffix is shown not to be deleted. -/
theorem avoiding_path_component_meets_left
    {v : Fin G.roles} (path : G.EdgePathToLeft v) :
    pathAll G path (fun x => x ∉ cut) →
    ∃ hv : v ∉ cut, componentMeetsLeft G cut (cutComponentOf G cut v hv) := by
  induction path with
  | finish v hLeft =>
      intro hv
      exact ⟨hv, v, vertex_mem_own_component G cut v hv, hLeft⟩
  | @step v e w hStart hEnd tail ih =>
      intro hAvoid
      obtain ⟨hwCut, hLeft⟩ := ih hAvoid.2
      refine ⟨hAvoid.1, ?_⟩
      have hComp := cutComponentOf_eq_of_edge G cut hAvoid.1 hwCut e hStart hEnd
      simpa only [hComp] using hLeft

/-- Search from the tail: recurse while z still occurs in the tail; otherwise
use the outgoing edge at the last occurrence of z, or the left boundary.
Every selected edge is proved fresh before being used as an observation. -/
theorem rowObserved_of_sole_hit_path
    (hSep : G.IsRightLeftSeparator cut) (z : Fin G.roles)
    {v : Fin G.roles} (path : G.EdgePathToLeft v) :
    pathAll G path (fun x => x ∈ cut → x = z) →
    pathAny G path (fun x => x = z) → z ∈ rowObserved G cut := by
  classical
  induction path with
  | finish v hLeft =>
      intro _ hHit
      change v = z at hHit
      exact rowObserved_of_leftBoundary G cut (by simpa only [hHit] using hLeft)
  | @step v e w hStart hEnd tail ih =>
      intro hSole hHit
      by_cases hTailHit : pathAny G tail (fun x => x = z)
      · exact ih hSole.2 hTailHit
      · have hvz : v = z := hHit.resolve_right hTailHit
        have hAvoid := pathAll_not_cut_of_sole_nohit G cut z tail hSole.2 hTailHit
        obtain ⟨hwCut, hLeft⟩ := avoiding_path_component_meets_left G cut tail hAvoid
        have hwC := retained_of_component_meets_left G cut hwCut hLeft
        have heFresh := fresh_of_incident_retained_outside_cut G cut hwC hwCut e hEnd
        have heSide : edgeSide G cut e = false :=
          (edgeSide_eq_componentSide_of_incident G cut hwCut e hEnd).trans
            (componentSide_false_of_meets_left G cut hSep _ hLeft)
        exact rowObserved_of_fresh_edge G cut heFresh heSide
          (by simpa only [hvz] using hStart)

/-- Search from the head, while carrying the actual right-boundary component.
The first step into cut supplies a fresh column edge. The rest of the path is
not required to avoid active components. -/
theorem colObserved_from_right_component
    (z : Fin G.roles) (hz : z ∈ cut)
    {v : Fin G.roles} (path : G.EdgePathToLeft v) :
    ∀ hv : v ∉ cut,
      componentMeetsRight G cut (cutComponentOf G cut v hv) →
      pathAll G path (fun x => x ∈ cut → x = z) →
      pathAny G path (fun x => x = z) → z ∈ colObserved G cut := by
  induction path with
  | finish v hLeft =>
      intro hv _ _ hHit
      change v = z at hHit
      exact False.elim (hv (by simpa only [hHit] using hz))
  | @step v e w hStart hEnd tail ih =>
      intro hvCut hRight hSole hHit
      have hTailHit : pathAny G tail (fun x => x = z) := by
        rcases hHit with hvz | ht
        · exact False.elim (hvCut (by simpa only [hvz] using hz))
        · exact ht
      by_cases hwCut : w ∈ cut
      · have hwz : w = z :=
          pathAll_head G tail (fun x => x ∈ cut → x = z) hSole.2 hwCut
        have hvC := retained_of_component_meets_right G cut hvCut hRight
        have heFresh := fresh_of_incident_retained_outside_cut G cut hvC hvCut e hStart
        have heSide : edgeSide G cut e = true :=
          (edgeSide_eq_componentSide_of_incident G cut hvCut e hStart).trans
            (componentSide_true_of_meets_right G cut _ hRight)
        exact colObserved_of_fresh_edge G cut heFresh heSide
          (by simpa only [hwz] using hEnd)
      · have hComp := cutComponentOf_eq_of_edge G cut hvCut hwCut e hStart hEnd
        have hwRight : componentMeetsRight G cut (cutComponentOf G cut w hwCut) := by
          simpa only [hComp] using hRight
        exact ih hwCut hwRight hSole.2 hTailHit

/-- The nontrivial C1 obligation: every separator role is observed by actual
primitive fields on BOTH sides. Neither observation definition inserts cut. -/
theorem cut_subset_actual_observed_inter
    (hMin : G.IsMinimumRightLeftSeparator cut) :
    cut ⊆ rowObserved G cut ∩ colObserved G cut := by
  intro z hz
  obtain ⟨v, hvRight, path, hHit, hSole⟩ :=
    minimumSeparator_vertex_has_sole_hit_path hMin hz
  have hAll : pathAll G path (fun x => x ∈ cut → x = z) :=
    pathAll_of_vertexAt G path _ hSole
  have hAny : pathAny G path (fun x => x = z) := by
    obtain ⟨o, ho⟩ := hHit
    exact pathAny_of_vertexAt G path _ o ho
  refine Finset.mem_inter.2 ⟨rowObserved_of_sole_hit_path G cut hMin.1 z path hAll hAny, ?_⟩
  by_cases hvCut : v ∈ cut
  · have hvz : v = z := pathAll_head G path _ hAll hvCut
    exact colObserved_of_rightBoundary G cut (by simpa only [hvz] using hvRight)
  · have hRight : componentMeetsRight G cut (cutComponentOf G cut v hvCut) :=
      ⟨v, vertex_mem_own_component G cut v hvCut, hvRight⟩
    exact colObserved_from_right_component G cut z hz path hvCut hRight hAll hAny

/-- Boundary overlap is handled by the actual zero-length path. -/
theorem common_boundary_mem_cut
    (hSep : G.IsRightLeftSeparator cut) {z : Fin G.roles}
    (hLeft : z ∈ G.leftBoundary) (hRight : z ∈ G.rightBoundary) : z ∈ cut := by
  obtain ⟨o, ho⟩ := hSep z hRight (.finish z hLeft)
  exact ho

/-! ## 5. The two C1 identities -/

theorem observed_inter_eq_cut
    (hMin : G.IsMinimumRightLeftSeparator cut) :
    rowObserved G cut ∩ colObserved G cut = cut := by
  apply Finset.Subset.antisymm
  · exact observed_inter_subset_cut G cut hMin.1
  · exact cut_subset_actual_observed_inter G cut hMin

theorem observed_union_eq_retainedRoles
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (hMin : G.IsMinimumRightLeftSeparator cut) :
    rowObserved G cut ∪ colObserved G cut = retainedRoles G cut := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_union.1 hv with hRow | hCol
    · exact rowObserved_subset_retainedRoles G cut hRow
    · exact colObserved_subset_retainedRoles G cut hCol
  · intro v hvC
    by_cases hvCut : v ∈ cut
    · exact Finset.mem_union.2 (Or.inl
        (Finset.mem_inter.1 (cut_subset_actual_observed_inter G cut hMin hvCut)).1)
    · rcases hCovered v with ⟨e, hve⟩ | hLeft | hRight
      · have heFresh := fresh_of_incident_retained_outside_cut G cut hvC hvCut e hve
        cases hSide : edgeSide G cut e with
        | false =>
            exact Finset.mem_union.2 (Or.inl
              (rowObserved_of_fresh_edge G cut heFresh hSide hve))
        | true =>
            exact Finset.mem_union.2 (Or.inr
              (colObserved_of_fresh_edge G cut heFresh hSide hve))
      · exact Finset.mem_union.2 (Or.inl (rowObserved_of_leftBoundary G cut hLeft))
      · exact Finset.mem_union.2 (Or.inr (colObserved_of_rightBoundary G cut hRight))

/-- General PartiteShape theorem: no simplicity, no nonempty-boundary
assumptions, no equal label sizes, and no boundary-core assumption. -/
theorem actual_observations
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (hMin : G.IsMinimumRightLeftSeparator cut) :
    (rowObserved G cut ∪ colObserved G cut = retainedRoles G cut) ∧
    (rowObserved G cut ∩ colObserved G cut = cut) :=
  ⟨observed_union_eq_retainedRoles G cut hCovered hMin,
    observed_inter_eq_cut G cut hMin⟩

/-! ## 6. PaperShape: actual ordered boundary slots and typed edge ports -/

section PaperCoordinates

variable (P : PaperShape) (S : Finset (Fin P.roles))

/-- One original row-boundary slot, or one port of one fresh row edge.
The edge primitive itself remains a PAIR; ports merely name its two fields. -/
abbrev RowField :=
  Sum (Fin P.leftSize) ((EdgeOnSide P.toPartiteShape S false) × Bool)

abbrev ColField :=
  Sum (Fin P.rightSize) ((EdgeOnSide P.toPartiteShape S true) × Bool)

/-- Port false = original source; port true = original target. -/
def rowFieldRole : RowField P S → Fin P.roles
  | .inl i => P.left i
  | .inr (e, false) => P.source e.1
  | .inr (e, true) => P.target e.1

def colFieldRole : ColField P S → Fin P.roles
  | .inl i => P.right i
  | .inr (e, false) => P.source e.1
  | .inr (e, true) => P.target e.1

/-- Roles observed by the actual row fields, rather than an abstract cover. -/
def paperRowObserved : Finset (Fin P.roles) := by
  classical
  exact Finset.univ.image (rowFieldRole P S)

def paperColObserved : Finset (Fin P.roles) := by
  classical
  exact Finset.univ.image (colFieldRole P S)

universe u

/-- The complete row primitive address. No common dimension is imposed. -/
abbrev RowAddress (X : Fin P.roles → Type u) :=
  ((i : Fin P.leftSize) → X (P.left i)) ×
  ((e : EdgeOnSide P.toPartiteShape S false) →
    X (P.source e.1) × X (P.target e.1))

abbrev ColAddress (X : Fin P.roles → Type u) :=
  ((i : Fin P.rightSize) → X (P.right i)) ×
  ((e : EdgeOnSide P.toPartiteShape S true) →
    X (P.source e.1) × X (P.target e.1))

/-- An actual read operation; repeated roles still have distinct field IDs. -/
def readRowField {X : Fin P.roles → Type u} (a : RowAddress P S X) :
    (f : RowField P S) → X (rowFieldRole P S f)
  | .inl i => a.1 i
  | .inr (e, false) => (a.2 e).1
  | .inr (e, true) => (a.2 e).2

def readColField {X : Fin P.roles → Type u} (a : ColAddress P S X) :
    (f : ColField P S) → X (colFieldRole P S f)
  | .inl i => a.1 i
  | .inr (e, false) => (a.2 e).1
  | .inr (e, true) => (a.2 e).2

/-- Exact bridge from ordered original boundary slots and fresh-edge fields
into the PartiteShape observation predicate. -/
theorem paperRowObserved_eq :
    paperRowObserved P S = rowObserved P.toPartiteShape S := by
  classical
  ext v
  constructor
  · intro hv
    change v ∈ Finset.univ.image (rowFieldRole P S) at hv
    obtain ⟨f, _, hf⟩ := Finset.mem_image.1 hv
    rcases f with i | ⟨e, port⟩
    · apply rowObserved_of_leftBoundary P.toPartiteShape S
      change v ∈ P.leftBoundaryFinset
      exact (P.mem_leftBoundaryFinset_iff v).2 ⟨i, hf⟩
    · apply rowObserved_of_fresh_edge P.toPartiteShape S e.2.1 e.2.2
      cases port with
      | false => exact Or.inl hf
      | true => exact Or.inr hf
  · intro hv
    change v ∈ Finset.univ.image (rowFieldRole P S)
    rcases (mem_rowObserved_iff P.toPartiteShape S v).1 hv with
      hLeft | ⟨e, he, hSide, hve⟩
    · obtain ⟨i, hi⟩ := (P.mem_leftBoundaryFinset_iff v).1 hLeft
      exact Finset.mem_image.2 ⟨Sum.inl i, Finset.mem_univ _, hi⟩
    · rcases hve with hs | ht
      · exact Finset.mem_image.2
          ⟨Sum.inr (⟨e, he, hSide⟩, false), Finset.mem_univ _, hs⟩
      · exact Finset.mem_image.2
          ⟨Sum.inr (⟨e, he, hSide⟩, true), Finset.mem_univ _, ht⟩

theorem paperColObserved_eq :
    paperColObserved P S = colObserved P.toPartiteShape S := by
  classical
  ext v
  constructor
  · intro hv
    change v ∈ Finset.univ.image (colFieldRole P S) at hv
    obtain ⟨f, _, hf⟩ := Finset.mem_image.1 hv
    rcases f with i | ⟨e, port⟩
    · apply colObserved_of_rightBoundary P.toPartiteShape S
      change v ∈ P.rightBoundaryFinset
      exact (P.mem_rightBoundaryFinset_iff v).2 ⟨i, hf⟩
    · apply colObserved_of_fresh_edge P.toPartiteShape S e.2.1 e.2.2
      cases port with
      | false => exact Or.inl hf
      | true => exact Or.inr hf
  · intro hv
    change v ∈ Finset.univ.image (colFieldRole P S)
    rcases (mem_colObserved_iff P.toPartiteShape S v).1 hv with
      hRight | ⟨e, he, hSide, hve⟩
    · obtain ⟨i, hi⟩ := (P.mem_rightBoundaryFinset_iff v).1 hRight
      exact Finset.mem_image.2 ⟨Sum.inl i, Finset.mem_univ _, hi⟩
    · rcases hve with hs | ht
      · exact Finset.mem_image.2
          ⟨Sum.inr (⟨e, he, hSide⟩, false), Finset.mem_univ _, hs⟩
      · exact Finset.mem_image.2
          ⟨Sum.inr (⟨e, he, hSide⟩, true), Finset.mem_univ _, ht⟩

/-- The requested theorem on the paper's actual ordered fields. -/
theorem paper_actual_observations
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) :
    (paperRowObserved P S ∪ paperColObserved P S =
      retainedRoles P.toPartiteShape S) ∧
    (paperRowObserved P S ∩ paperColObserved P S = S) := by
  rw [paperRowObserved_eq P S, paperColObserved_eq P S]
  exact actual_observations P.toPartiteShape S
    ((P.hasNoIsolatedMiddleRoles_iff_all_roleCovered).1 hNoIsolated) hMin

/-- Explicit real field witnesses for each separator vertex. There is no
surjectivity or visibility hypothesis: both witnesses have been proved. -/
theorem paper_separator_vertex_has_actual_fields
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    {z : Fin P.roles} (hz : z ∈ S) :
    (∃ f : RowField P S, rowFieldRole P S f = z) ∧
    (∃ f : ColField P S, colFieldRole P S f = z) := by
  classical
  have hBoth := cut_subset_actual_observed_inter P.toPartiteShape S hMin hz
  have hRow : z ∈ paperRowObserved P S := by
    rw [paperRowObserved_eq P S]
    exact (Finset.mem_inter.1 hBoth).1
  have hCol : z ∈ paperColObserved P S := by
    rw [paperColObserved_eq P S]
    exact (Finset.mem_inter.1 hBoth).2
  change z ∈ Finset.univ.image (rowFieldRole P S) at hRow
  change z ∈ Finset.univ.image (colFieldRole P S) at hCol
  obtain ⟨f, _, hf⟩ := Finset.mem_image.1 hRow
  obtain ⟨g, _, hg⟩ := Finset.mem_image.1 hCol
  exact ⟨⟨f, hf⟩, ⟨g, hg⟩⟩

end PaperCoordinates

#print axioms fresh_of_incident_retained_outside_cut
#print axioms cut_subset_actual_observed_inter
#print axioms actual_observations
#print axioms paper_actual_observations
#print axioms paper_separator_vertex_has_actual_fields

end GraphMatrixReplica.PaperR16.ActualPrimitiveObservations
