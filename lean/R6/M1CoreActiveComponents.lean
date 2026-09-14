import R6.M1CoreGraphParameters
import R6.C079ActiveComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

@[simp] theorem root_coreInclude_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (v : Fin (rootBoundaryCoreShape G).roles) :
    rootCoreInclude G v ∈ rootCoreLiftCut G cut ↔ v ∈ cut := by
  exact Finset.mem_map' (rootCoreInclude G)

def rootCoreCutHom (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles)) :
    (rootBoundaryCoreShape G).toPartiteShape.c079CutGraph cut →g
      G.toPartiteShape.c079CutGraph (rootCoreLiftCut G cut) where
  toFun v := ⟨rootCoreInclude G v.1, by simpa using v.2⟩
  map_rel' := by
    intro u v h
    obtain ⟨hne, e, hu, hv⟩ := h
    exact ⟨fun he => hne ((rootCoreInclude G).injective he), ((rootCoreEdgeIso G) e).1,
      (root_core_incident_iff G e u.1).mp hu,
      (root_core_incident_iff G e v.1).mp hv⟩

theorem root_core_component_mem_map (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (c : (rootBoundaryCoreShape G).toPartiteShape.C079CutComponent cut)
    (v : Fin (rootBoundaryCoreShape G).roles)
    (hv : v ∈ (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c) :
    rootCoreInclude G v ∈ G.toPartiteShape.c079ComponentRoles
      (rootCoreLiftCut G cut) (c.map (rootCoreCutHom G cut)) := by
  obtain ⟨hn, he⟩ :=
    ((rootBoundaryCoreShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  apply (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mpr
  refine ⟨by simpa using hn, ?_⟩
  rw [← he]
  rfl

theorem root_core_reachable_stays_component (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (c : (rootBoundaryCoreShape G).toPartiteShape.C079CutComponent cut)
    {u v : {x : Fin G.toPartiteShape.roles // x ∉ rootCoreLiftCut G cut}}
    (hu : ∃ a ∈ (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c,
      rootCoreInclude G a = u.1)
    (hReach : (G.toPartiteShape.c079CutGraph (rootCoreLiftCut G cut)).Reachable u v) :
    ∃ b ∈ (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c,
      rootCoreInclude G b = v.1 := by
  have h := (SimpleGraph.reachable_iff_reflTransGen u v).mp hReach
  clear hReach
  induction h with
  | refl => exact hu
  | @tail y z hPath hAdj ih =>
    obtain ⟨a, ha, he⟩ := ih
    obtain ⟨_, e, hey, hez⟩ := hAdj
    have hyCov : y.1 ∈ rootCoreRoles G := he ▸ (rootCoreRoleIso G a).2
    have hzCov := root_coreRoles_edgeClosed G y.1 hyCov e z.1 hey hez
    have heCore := root_incident_coreEdge G e hyCov hey
    let en := (rootCoreEdgeIso G).symm ⟨e, heCore⟩
    let b := rootCoreIndex G z.1 hzCov
    have hb : b ∉ cut := by
      intro hbc
      exact z.2 ((root_coreIndex_mem_liftCut G cut z.1 hzCov).mp hbc)
    have hae : (rootBoundaryCoreShape G).toPartiteShape.EdgeIncident en a :=
      (root_core_incident_iff G en a).mpr (by simpa [en] using (he.symm ▸ hey))
    have hbe : (rootBoundaryCoreShape G).toPartiteShape.EdgeIncident en b :=
      (root_core_incident_iff G en b).mpr (by simpa [en, b] using hez)
    exact ⟨b, (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles_edge_closed_outside_cut
      cut c ha en hae hbe hb, root_coreInclude_index G z.1 hzCov⟩

theorem root_core_component_roles_map (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (c : (rootBoundaryCoreShape G).toPartiteShape.C079CutComponent cut) :
    G.toPartiteShape.c079ComponentRoles (rootCoreLiftCut G cut) (c.map (rootCoreCutHom G cut)) =
      ((rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c).map
        (rootCoreInclude G) := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
    have haOld := root_core_component_mem_map G cut c a ha
    obtain ⟨haCut, haComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp haOld
    obtain ⟨hvCut, hvComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp hv
    have hReach := SimpleGraph.ConnectedComponent.exact (haComp.trans hvComp.symm)
    exact Finset.mem_map.mpr
      (root_core_reachable_stays_component G cut c ⟨a, ha, rfl⟩ hReach)
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact root_core_component_mem_map G cut c a ha

theorem root_core_component_map_injective (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles)) :
    Function.Injective (fun c : (rootBoundaryCoreShape G).toPartiteShape.C079CutComponent cut =>
      c.map (rootCoreCutHom G cut)) := by
  intro c d he
  have hRoles : (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c =
      (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut d := by
    apply Finset.map_injective (rootCoreInclude G)
    rw [← root_core_component_roles_map, ← root_core_component_roles_map]
    exact congrArg (G.toPartiteShape.c079ComponentRoles (rootCoreLiftCut G cut)) he
  obtain ⟨v, hv⟩ := (rootBoundaryCoreShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
  have hvd := hRoles ▸ hv
  obtain ⟨_, hc⟩ :=
    ((rootBoundaryCoreShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  obtain ⟨_, hd⟩ :=
    ((rootBoundaryCoreShape G).toPartiteShape.mem_c079ComponentRoles_iff cut d v).mp hvd
  exact hc.symm.trans hd

theorem root_core_component_map_active_iff (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (c : (rootBoundaryCoreShape G).toPartiteShape.C079CutComponent cut) :
    PartiteShape.C079CutComponent.IsActive (G := G.toPartiteShape)
      (cut := rootCoreLiftCut G cut) (c.map (rootCoreCutHom G cut)) ↔ c.IsActive := by
  have hRoles := root_core_component_roles_map G cut c
  constructor
  · intro h
    constructor
    · intro v hv
      have hb := h.1 _ (root_core_component_mem_map G cut c v hv)
      exact ⟨fun hl => hb.1 ((root_core_left_iff G v).mp hl),
        fun hr => hb.2 ((root_core_right_iff G v).mp hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hx
      have heCore := root_incident_coreEdge G e (rootCoreRoleIso G a).2 hev
      let en := (rootCoreEdgeIso G).symm ⟨e, heCore⟩
      exact ⟨a, ha, b, hb, en,
        (root_core_incident_iff G en a).mpr (by simpa [en] using hev),
        (root_core_incident_iff G en b).mpr (by simpa [en] using hex)⟩
  · intro h
    constructor
    · intro v hv
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      have hb := h.1 a ha
      exact ⟨fun hl => hb.1 ((root_core_left_iff G a).mpr hl),
        fun hr => hb.2 ((root_core_right_iff G a).mpr hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      exact ⟨rootCoreInclude G v, root_core_component_mem_map G cut c v hv,
        rootCoreInclude G x, (root_coreInclude_mem_liftCut G cut x).mpr hx, ((rootCoreEdgeIso G) e).1,
        (root_core_incident_iff G e v).mp hev,
        (root_core_incident_iff G e x).mp hex⟩

theorem root_active_component_in_core_image (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles))
    (c : G.toPartiteShape.C079CutComponent (rootCoreLiftCut G cut)) (hc : c.IsActive) :
    ∃ d : (rootBoundaryCoreShape G).toPartiteShape.C079CutComponent cut,
      d.map (rootCoreCutHom G cut) = c := by
  obtain ⟨v, hv, x, hx, e, hev, hex⟩ := hc.2
  obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hx
  have hxCore : x ∈ rootCoreRoles G := hbx ▸ (rootCoreRoleIso G b).2
  have hvCov := root_coreRoles_edgeClosed G x hxCore e v hex hev
  obtain ⟨hvCut, hvComp⟩ := (G.toPartiteShape.mem_c079ComponentRoles_iff _ c v).mp hv
  have hn : rootCoreIndex G v hvCov ∉ cut := by
    intro hh
    exact hvCut ((root_coreIndex_mem_liftCut G cut v hvCov).mp hh)
  refine ⟨(rootBoundaryCoreShape G).toPartiteShape.c079CutGraph cut |>.connectedComponentMk
    ⟨rootCoreIndex G v hvCov, hn⟩, ?_⟩
  change (G.toPartiteShape.c079CutGraph (rootCoreLiftCut G cut)).connectedComponentMk
    ((rootCoreCutHom G cut) ⟨rootCoreIndex G v hvCov, hn⟩) = c
  have he : (rootCoreCutHom G cut) ⟨rootCoreIndex G v hvCov, hn⟩ =
      ⟨v, hvCut⟩ := Subtype.ext (root_coreInclude_index G v hvCov)
  rw [he]
  exact hvComp

/-- Removing all detached components preserves the actual number of active cut components. -/
theorem root_core_activeComponentCount_eq (G : PaperShape)
    (cut : Finset (Fin (rootBoundaryCoreShape G).roles)) :
    (rootBoundaryCoreShape G).toPartiteShape.c079ActiveComponentCount cut =
      G.toPartiteShape.c079ActiveComponentCount (rootCoreLiftCut G cut) := by
  unfold PartiteShape.c079ActiveComponentCount
  apply Finset.card_bij (fun c _ => c.map (rootCoreCutHom G cut))
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (root_core_component_map_active_iff G cut c).mpr hc
  · intro c hc d hd he
    exact root_core_component_map_injective G cut he
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨d, hd⟩ := root_active_component_in_core_image G cut c hc
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (root_core_component_map_active_iff G cut d).mp (hd.symm ▸ hc)

/-- The manuscript's active maximum is unchanged, including empty boundaries. -/
theorem root_core_activeMaximum_eq (G : PaperShape) :
    (rootBoundaryCoreShape G).toPartiteShape.c079ActiveMaximum =
      G.toPartiteShape.c079ActiveMaximum := by
  apply Nat.le_antisymm
  · obtain ⟨cut, hm, he⟩ :=
      (rootBoundaryCoreShape G).toPartiteShape.exists_minimum_with_c079ActiveMaximum
    rw [← he, root_core_activeComponentCount_eq]
    exact G.toPartiteShape.c079ActiveComponentCount_le_maximum _ (root_coreLiftCut_minimal G cut hm)
  · obtain ⟨cut, hm, he⟩ := G.toPartiteShape.exists_minimum_with_c079ActiveMaximum
    have hcut : rootCoreLiftCut G (rootCorePullCut G cut) = cut := by
      rw [root_coreLiftPullCut_eq_inter,
        Finset.inter_eq_left.mpr (root_minSeparator_subset_core G cut hm)]
    rw [← he, ← hcut, ← root_core_activeComponentCount_eq]
    exact (rootBoundaryCoreShape G).toPartiteShape.c079ActiveComponentCount_le_maximum _
      (root_corePullCut_minimal G cut hm)

#print axioms root_core_component_roles_map
#print axioms root_core_component_map_injective
#print axioms root_core_component_map_active_iff
#print axioms root_active_component_in_core_image
#print axioms root_core_activeComponentCount_eq
#print axioms root_core_activeMaximum_eq
end GraphMatrixReplica

