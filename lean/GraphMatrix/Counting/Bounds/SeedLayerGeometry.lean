import GraphMatrix.Counting.ActiveComponents
import GraphMatrix.Counting.Bounds.SeedCompatibility

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.ReplicaCounting

/-- Removing a smaller cut includes the old surviving graph into the new one. -/
def mainCutInclusion (G : PartiteShape) (P S : Finset (Fin G.roles)) (hSP : S ⊆ P) :
    G.c079CutGraph P →g G.c079CutGraph S where
  toFun v := ⟨v.1, fun hv => v.2 (hSP hv)⟩
  map_rel' h := h

/-- All old-cut neighbors of this genuine component are deleted by `S`. -/
def ComponentIsolatedAt {G : PartiteShape} {P : Finset (Fin G.roles)}
    (c : G.C079CutComponent P) (S : Finset (Fin G.roles)) : Prop :=
  ∀ v ∈ G.c079ComponentRoles P c, ∀ x ∈ P, ∀ e : Fin G.edges,
    G.EdgeIncident e v → G.EdgeIncident e x → x ∈ S

theorem main_component_mem_map (G : PartiteShape)
    (P S : Finset (Fin G.roles)) (hSP : S ⊆ P)
    (c : G.C079CutComponent P) (v : Fin G.roles)
    (hv : v ∈ G.c079ComponentRoles P c) :
    v ∈ G.c079ComponentRoles S (c.map (mainCutInclusion G P S hSP)) := by
  obtain ⟨hvP, hvc⟩ := (G.mem_c079ComponentRoles_iff P c v).1 hv
  refine (G.mem_c079ComponentRoles_iff S _ v).2 ⟨fun h => hvP (hSP h), ?_⟩
  rw [← hvc]
  rfl

/-- A walk in the new surviving graph cannot leave the old component. -/
theorem main_reachable_stays_in_component {G : PartiteShape}
    {P S : Finset (Fin G.roles)} (c : G.C079CutComponent P)
    (hIso : ComponentIsolatedAt c S)
    {u v : {x : Fin G.roles // x ∉ S}}
    (hu : u.1 ∈ G.c079ComponentRoles P c)
    (hReach : (G.c079CutGraph S).Reachable u v) :
    v.1 ∈ G.c079ComponentRoles P c := by
  have h := (SimpleGraph.reachable_iff_reflTransGen u v).1 hReach
  clear hReach
  induction h with
  | refl => exact hu
  | @tail y z hPath hAdj ih =>
    change (G.c079RoleGraph).Adj y.1 z.1 at hAdj
    obtain ⟨_, e, hey, hez⟩ := hAdj
    have hzP : z.1 ∉ P := by
      intro hz
      exact z.2 (hIso y.1 ih z.1 hz e hey hez)
    exact G.c079ComponentRoles_edge_closed_outside_cut P c ih e hey hez hzP

/-- The component survives with exactly its old vertex set, so it cannot
merge with another component through undeleted backbone vertices. -/
theorem main_component_roles_map_eq (G : PartiteShape)
    (P S : Finset (Fin G.roles)) (hSP : S ⊆ P)
    (c : G.C079CutComponent P) (hIso : ComponentIsolatedAt c S) :
    G.c079ComponentRoles S (c.map (mainCutInclusion G P S hSP)) =
      G.c079ComponentRoles P c := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu⟩ := G.c079ComponentRoles_nonempty P c
    have huNew := main_component_mem_map G P S hSP c u hu
    obtain ⟨huS, huComp⟩ := (G.mem_c079ComponentRoles_iff S _ u).1 huNew
    obtain ⟨hvS, hvComp⟩ := (G.mem_c079ComponentRoles_iff S _ v).1 hv
    have hReach : (G.c079CutGraph S).Reachable ⟨u, huS⟩ ⟨v, hvS⟩ :=
      SimpleGraph.ConnectedComponent.exact (huComp.trans hvComp.symm)
    exact main_reachable_stays_in_component c hIso hu hReach
  · exact main_component_mem_map G P S hSP c v

theorem main_component_map_active (G : PartiteShape)
    (P S : Finset (Fin G.roles)) (hSP : S ⊆ P)
    (c : G.C079CutComponent P) (hActive : c.IsActive)
    (hIso : ComponentIsolatedAt c S) :
    PartiteShape.C079CutComponent.IsActive (G := G) (cut := S)
      (c.map (mainCutInclusion G P S hSP)) := by
  have hRoles := main_component_roles_map_eq G P S hSP c hIso
  constructor
  · intro v hv
    rw [hRoles] at hv
    exact hActive.1 v hv
  · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := hActive.2
    exact ⟨v, hRoles.symm ▸ hv, x, hIso v hv x hx e hev hex, e, hev, hex⟩

theorem main_component_map_injective_on_isolated (G : PartiteShape)
    (P S : Finset (Fin G.roles)) (hSP : S ⊆ P)
    (c d : G.C079CutComponent P)
    (hc : ComponentIsolatedAt c S) (hd : ComponentIsolatedAt d S)
    (heq : c.map (mainCutInclusion G P S hSP) =
      d.map (mainCutInclusion G P S hSP)) : c = d := by
  have hRoles : G.c079ComponentRoles P c = G.c079ComponentRoles P d := by
    rw [← main_component_roles_map_eq G P S hSP c hc,
      ← main_component_roles_map_eq G P S hSP d hd, heq]
  obtain ⟨v, hv⟩ := G.c079ComponentRoles_nonempty P c
  have hvd : v ∈ G.c079ComponentRoles P d := hRoles ▸ hv
  obtain ⟨hvc, hcc⟩ := (G.mem_c079ComponentRoles_iff P c v).1 hv
  obtain ⟨hvdP, hdd⟩ := (G.mem_c079ComponentRoles_iff P d v).1 hvd
  exact hcc.symm.trans hdd

/-- Counting actual components via the constructed active-component injection. -/
theorem main_isolated_active_component_card_le (G : PartiteShape)
    (P S : Finset (Fin G.roles)) (hSP : S ⊆ P) :
    Nat.card {c : G.C079CutComponent P // c.IsActive ∧ ComponentIsolatedAt c S} ≤
      G.c079ActiveComponentCount S := by
  classical
  let A := {c : G.C079CutComponent P // c.IsActive ∧ ComponentIsolatedAt c S}
  let Z := {c : G.C079CutComponent S // c.IsActive}
  letI : Fintype A := Fintype.ofFinite _
  letI : Fintype Z := Fintype.ofFinite _
  let f : A → Z := fun c => ⟨c.1.map (mainCutInclusion G P S hSP),
    main_component_map_active G P S hSP c.1 c.2.1 c.2.2⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    exact main_component_map_injective_on_isolated G P S hSP c.1 d.1 c.2.2 d.2.2
      (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  simpa only [A, Z, Nat.card_eq_fintype_card, Fintype.card_subtype,
    PartiteShape.c079ActiveComponentCount] using h

open ReplicaEncoding
variable {G : PartiteShape} {p s : ℕ}
  {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
  {B : PathFiber p family d}
  {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}

def mainSeedState (seed : SeedFiber B forward) : ReplicaState G p :=
  Classical.choose (seedRecord_has_actual_state seed)

theorem mainSeedState_partition (seed : SeedFiber B forward) :
    (mainSeedState seed).partition = normalizedRecord (seedRecord seed) :=
  Classical.choose_spec (seedRecord_has_actual_state seed)

def mainSeedLayer (seed : SeedFiber B forward) (k : ℕ) : Finset (Fin G.roles) := by
  classical
  exact c079IntervalLayer
    (fun x => c079PartitionLower ((mainSeedState seed).partition x))
    (fun x => c079PartitionUpper ((mainSeedState seed).partition x)) k

theorem main_seedLayer_subset_backbone (seed : SeedFiber B forward) (k : ℕ) :
    mainSeedLayer seed k ⊆ family.backboneRoles := by
  classical
  intro x hx
  by_contra hxOff
  have hCount : partitionBlockCount ((mainSeedState seed).partition x) = p + 1 := by
    rw [mainSeedState_partition]
    exact normalizedRecord_off_blockCount seed x hxOff
  have hEnds : c079PartitionLower ((mainSeedState seed).partition x) =
      c079PartitionUpper ((mainSeedState seed).partition x) := by
    unfold c079PartitionLower c079PartitionUpper
    rw [hCount]
  have hMem : c079PartitionLower ((mainSeedState seed).partition x) < k ∧
      k ≤ c079PartitionUpper ((mainSeedState seed).partition x) :=
    (Finset.mem_filter.mp hx).2
  omega

theorem main_crossing_neighbors_mem_layer (seed : SeedFiber B forward)
    (c : G.C079CutComponent family.backboneRoles) (k : ℕ)
    (hCross : c079PartitionLower (neighborMeet B forward c) < k ∧
      k ≤ c079PartitionUpper (neighborMeet B forward c)) :
    backboneNeighbors family c ⊆ mainSeedLayer seed k := by
  classical
  apply c079_refined_seed_neighbors_mem_intervalLayer (mainSeedState seed)
    (backboneNeighbors family c) (neighborMeet B forward c) k _ hCross
  intro x hx
  have hxBack := (Finset.mem_filter.mp hx).1
  rw [mainSeedState_partition, normalizedRecord_backbone seed x hxBack]
  change (backboneNeighbors family c).inf (repairedAt B forward) ≤ repairedAt B forward x
  exact Finset.inf_le hx

theorem main_crossing_component_isolated (seed : SeedFiber B forward)
    (c : G.C079CutComponent family.backboneRoles) (k : ℕ)
    (hCross : c079PartitionLower (neighborMeet B forward c) < k ∧
      k ≤ c079PartitionUpper (neighborMeet B forward c)) :
    ComponentIsolatedAt c (mainSeedLayer seed k) := by
  classical
  intro v hv x hx e hev hex
  apply main_crossing_neighbors_mem_layer seed c k hCross
  exact Finset.mem_filter.mpr ⟨hx, v, hv, e, hex, hev⟩

abbrev CrossingFreeComponent
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d))
    (k : ℕ) :=
  {c : FreeComponent family //
    c079PartitionLower (neighborMeet B forward c.1) < k ∧
      k ≤ c079PartitionUpper (neighborMeet B forward c.1)}

/-- At each actual separator layer, the crossing free components inject
into genuine active components of that layer, without an incidence premise. -/
theorem main_crossing_free_card_le_active (hCore : G.IsBoundaryCore)
    (seed : SeedFiber B forward) (k : ℕ) :
    Nat.card (CrossingFreeComponent B forward k) ≤
      G.c079ActiveComponentCount (mainSeedLayer seed k) := by
  classical
  let P := family.backboneRoles
  let S := mainSeedLayer seed k
  have hSP : S ⊆ P := main_seedLayer_subset_backbone seed k
  let A := CrossingFreeComponent B forward k
  let Z := {c : G.C079CutComponent S // c.IsActive}
  letI : Fintype A := Fintype.ofFinite _
  letI : Fintype Z := Fintype.ofFinite _
  have hActive (c : A) : c.1.1.IsActive :=
    ⟨c.1.2, G.c079_boundaryFree_component_attached_of_boundaryCore hCore P c.1.1 c.1.2⟩
  have hIso (c : A) : ComponentIsolatedAt c.1.1 S :=
    main_crossing_component_isolated seed c.1.1 k c.2
  let f : A → Z := fun c => ⟨c.1.1.map (mainCutInclusion G P S hSP),
    main_component_map_active G P S hSP c.1.1 (hActive c) (hIso c)⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply Subtype.ext
    exact main_component_map_injective_on_isolated G P S hSP c.1.1 d.1.1
      (hIso c) (hIso d) (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  simpa only [A, Z, S, Nat.card_eq_fintype_card, Fintype.card_subtype,
    PartiteShape.c079ActiveComponentCount] using h


end GraphMatrixReplica.ReplicaCounting
