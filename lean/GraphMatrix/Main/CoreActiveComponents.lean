import GraphMatrix.Main.CoreGraphParameters
import GraphMatrix.Counting.ActiveComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

@[simp] theorem main_coreInclude_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (v : Fin (mainBoundaryCoreShape G).roles) :
    mainCoreInclude G v ∈ mainCoreLiftCut G cut ↔ v ∈ cut := by
  exact Finset.mem_map' (mainCoreInclude G)

def mainCoreCutHom (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles)) :
    (mainBoundaryCoreShape G).toPartiteShape.c079CutGraph cut →g
      G.toPartiteShape.c079CutGraph (mainCoreLiftCut G cut) where
  toFun v := ⟨mainCoreInclude G v.1, by simpa using v.2⟩
  map_rel' := by
    intro u v h
    obtain ⟨hne, e, hu, hv⟩ := h
    exact ⟨fun he => hne ((mainCoreInclude G).injective he), ((mainCoreEdgeIso G) e).1,
      (main_core_incident_iff G e u.1).mp hu,
      (main_core_incident_iff G e v.1).mp hv⟩

theorem main_core_component_mem_map (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (c : (mainBoundaryCoreShape G).toPartiteShape.C079CutComponent cut)
    (v : Fin (mainBoundaryCoreShape G).roles)
    (hv : v ∈ (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c) :
    mainCoreInclude G v ∈ G.toPartiteShape.c079ComponentRoles
      (mainCoreLiftCut G cut) (c.map (mainCoreCutHom G cut)) := by
  obtain ⟨hn, he⟩ :=
    ((mainBoundaryCoreShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  apply (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mpr
  refine ⟨by simpa using hn, ?_⟩
  rw [← he]
  rfl

theorem main_core_reachable_stays_component (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (c : (mainBoundaryCoreShape G).toPartiteShape.C079CutComponent cut)
    {u v : {x : Fin G.toPartiteShape.roles // x ∉ mainCoreLiftCut G cut}}
    (hu : ∃ a ∈ (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c,
      mainCoreInclude G a = u.1)
    (hReach : (G.toPartiteShape.c079CutGraph (mainCoreLiftCut G cut)).Reachable u v) :
    ∃ b ∈ (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c,
      mainCoreInclude G b = v.1 := by
  have h := (SimpleGraph.reachable_iff_reflTransGen u v).mp hReach
  clear hReach
  induction h with
  | refl => exact hu
  | @tail y z hPath hAdj ih =>
    obtain ⟨a, ha, he⟩ := ih
    obtain ⟨_, e, hey, hez⟩ := hAdj
    have hyCov : y.1 ∈ mainCoreRoles G := he ▸ (mainCoreRoleIso G a).2
    have hzCov := main_coreRoles_edgeClosed G y.1 hyCov e z.1 hey hez
    have heCore := main_incident_coreEdge G e hyCov hey
    let en := (mainCoreEdgeIso G).symm ⟨e, heCore⟩
    let b := mainCoreIndex G z.1 hzCov
    have hb : b ∉ cut := by
      intro hbc
      exact z.2 ((main_coreIndex_mem_liftCut G cut z.1 hzCov).mp hbc)
    have hae : (mainBoundaryCoreShape G).toPartiteShape.EdgeIncident en a :=
      (main_core_incident_iff G en a).mpr (by simpa [en] using (he.symm ▸ hey))
    have hbe : (mainBoundaryCoreShape G).toPartiteShape.EdgeIncident en b :=
      (main_core_incident_iff G en b).mpr (by simpa [en, b] using hez)
    exact ⟨b, (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles_edge_closed_outside_cut
      cut c ha en hae hbe hb, main_coreInclude_index G z.1 hzCov⟩

theorem main_core_component_roles_map (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (c : (mainBoundaryCoreShape G).toPartiteShape.C079CutComponent cut) :
    G.toPartiteShape.c079ComponentRoles (mainCoreLiftCut G cut) (c.map (mainCoreCutHom G cut)) =
      ((mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c).map
        (mainCoreInclude G) := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
    have haOld := main_core_component_mem_map G cut c a ha
    obtain ⟨haCut, haComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp haOld
    obtain ⟨hvCut, hvComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp hv
    have hReach := SimpleGraph.ConnectedComponent.exact (haComp.trans hvComp.symm)
    exact Finset.mem_map.mpr
      (main_core_reachable_stays_component G cut c ⟨a, ha, rfl⟩ hReach)
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact main_core_component_mem_map G cut c a ha

theorem main_core_component_map_injective (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles)) :
    Function.Injective (fun c : (mainBoundaryCoreShape G).toPartiteShape.C079CutComponent cut =>
      c.map (mainCoreCutHom G cut)) := by
  intro c d he
  have hRoles : (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut c =
      (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles cut d := by
    apply Finset.map_injective (mainCoreInclude G)
    rw [← main_core_component_roles_map, ← main_core_component_roles_map]
    exact congrArg (G.toPartiteShape.c079ComponentRoles (mainCoreLiftCut G cut)) he
  obtain ⟨v, hv⟩ := (mainBoundaryCoreShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
  have hvd := hRoles ▸ hv
  obtain ⟨_, hc⟩ :=
    ((mainBoundaryCoreShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  obtain ⟨_, hd⟩ :=
    ((mainBoundaryCoreShape G).toPartiteShape.mem_c079ComponentRoles_iff cut d v).mp hvd
  exact hc.symm.trans hd

theorem main_core_component_map_active_iff (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (c : (mainBoundaryCoreShape G).toPartiteShape.C079CutComponent cut) :
    PartiteShape.C079CutComponent.IsActive (G := G.toPartiteShape)
      (cut := mainCoreLiftCut G cut) (c.map (mainCoreCutHom G cut)) ↔ c.IsActive := by
  have hRoles := main_core_component_roles_map G cut c
  constructor
  · intro h
    constructor
    · intro v hv
      have hb := h.1 _ (main_core_component_mem_map G cut c v hv)
      exact ⟨fun hl => hb.1 ((main_core_left_iff G v).mp hl),
        fun hr => hb.2 ((main_core_right_iff G v).mp hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hx
      have heCore := main_incident_coreEdge G e (mainCoreRoleIso G a).2 hev
      let en := (mainCoreEdgeIso G).symm ⟨e, heCore⟩
      exact ⟨a, ha, b, hb, en,
        (main_core_incident_iff G en a).mpr (by simpa [en] using hev),
        (main_core_incident_iff G en b).mpr (by simpa [en] using hex)⟩
  · intro h
    constructor
    · intro v hv
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      have hb := h.1 a ha
      exact ⟨fun hl => hb.1 ((main_core_left_iff G a).mpr hl),
        fun hr => hb.2 ((main_core_right_iff G a).mpr hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      exact ⟨mainCoreInclude G v, main_core_component_mem_map G cut c v hv,
        mainCoreInclude G x, (main_coreInclude_mem_liftCut G cut x).mpr hx, ((mainCoreEdgeIso G) e).1,
        (main_core_incident_iff G e v).mp hev,
        (main_core_incident_iff G e x).mp hex⟩

theorem main_active_component_in_core_image (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles))
    (c : G.toPartiteShape.C079CutComponent (mainCoreLiftCut G cut)) (hc : c.IsActive) :
    ∃ d : (mainBoundaryCoreShape G).toPartiteShape.C079CutComponent cut,
      d.map (mainCoreCutHom G cut) = c := by
  obtain ⟨v, hv, x, hx, e, hev, hex⟩ := hc.2
  obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hx
  have hxCore : x ∈ mainCoreRoles G := hbx ▸ (mainCoreRoleIso G b).2
  have hvCov := main_coreRoles_edgeClosed G x hxCore e v hex hev
  obtain ⟨hvCut, hvComp⟩ := (G.toPartiteShape.mem_c079ComponentRoles_iff _ c v).mp hv
  have hn : mainCoreIndex G v hvCov ∉ cut := by
    intro hh
    exact hvCut ((main_coreIndex_mem_liftCut G cut v hvCov).mp hh)
  refine ⟨(mainBoundaryCoreShape G).toPartiteShape.c079CutGraph cut |>.connectedComponentMk
    ⟨mainCoreIndex G v hvCov, hn⟩, ?_⟩
  change (G.toPartiteShape.c079CutGraph (mainCoreLiftCut G cut)).connectedComponentMk
    ((mainCoreCutHom G cut) ⟨mainCoreIndex G v hvCov, hn⟩) = c
  have he : (mainCoreCutHom G cut) ⟨mainCoreIndex G v hvCov, hn⟩ =
      ⟨v, hvCut⟩ := Subtype.ext (main_coreInclude_index G v hvCov)
  rw [he]
  exact hvComp

/-- Removing all detached components preserves the actual number of active cut components. -/
theorem main_core_activeComponentCount_eq (G : PaperShape)
    (cut : Finset (Fin (mainBoundaryCoreShape G).roles)) :
    (mainBoundaryCoreShape G).toPartiteShape.c079ActiveComponentCount cut =
      G.toPartiteShape.c079ActiveComponentCount (mainCoreLiftCut G cut) := by
  unfold PartiteShape.c079ActiveComponentCount
  apply Finset.card_bij (fun c _ => c.map (mainCoreCutHom G cut))
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (main_core_component_map_active_iff G cut c).mpr hc
  · intro c hc d hd he
    exact main_core_component_map_injective G cut he
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨d, hd⟩ := main_active_component_in_core_image G cut c hc
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (main_core_component_map_active_iff G cut d).mp (hd.symm ▸ hc)

/-- The manuscript's active maximum is unchanged, including empty boundaries. -/
theorem main_core_activeMaximum_eq (G : PaperShape) :
    (mainBoundaryCoreShape G).toPartiteShape.activeComponentMaximum =
      G.toPartiteShape.activeComponentMaximum := by
  apply Nat.le_antisymm
  · obtain ⟨cut, hm, he⟩ :=
      (mainBoundaryCoreShape G).toPartiteShape.exists_minimum_with_c079ActiveMaximum
    rw [← he, main_core_activeComponentCount_eq]
    exact G.toPartiteShape.c079ActiveComponentCount_le_maximum _ (main_coreLiftCut_minimal G cut hm)
  · obtain ⟨cut, hm, he⟩ := G.toPartiteShape.exists_minimum_with_c079ActiveMaximum
    have hcut : mainCoreLiftCut G (mainCorePullCut G cut) = cut := by
      rw [main_coreLiftPullCut_eq_inter,
        Finset.inter_eq_left.mpr (main_minSeparator_subset_core G cut hm)]
    rw [← he, ← hcut, ← main_core_activeComponentCount_eq]
    exact (mainBoundaryCoreShape G).toPartiteShape.c079ActiveComponentCount_le_maximum _
      (main_corePullCut_minimal G cut hm)

end GraphMatrixReplica
