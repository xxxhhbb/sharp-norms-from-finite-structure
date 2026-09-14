import GraphMatrix.Main.ReducedGraphParameters
import GraphMatrix.Counting.ActiveComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

@[simp] theorem main_include_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (v : Fin (mainIsolatedReducedShape G).roles) :
    mainReducedInclude G v ∈ mainLiftCut G cut ↔ v ∈ cut := by
  exact Finset.mem_map' (mainReducedInclude G)

def mainReducedCutHom (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles)) :
    (mainIsolatedReducedShape G).toPartiteShape.c079CutGraph cut →g
      G.toPartiteShape.c079CutGraph (mainLiftCut G cut) where
  toFun v := ⟨mainReducedInclude G v.1, by simpa using v.2⟩
  map_rel' := by
    intro u v h
    obtain ⟨hne, e, hu, hv⟩ := h
    exact ⟨fun he => hne ((mainReducedInclude G).injective he), e,
      (main_reduced_incident_iff G e u.1).mp hu,
      (main_reduced_incident_iff G e v.1).mp hv⟩

theorem main_reduced_component_mem_map (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (c : (mainIsolatedReducedShape G).toPartiteShape.C079CutComponent cut)
    (v : Fin (mainIsolatedReducedShape G).roles)
    (hv : v ∈ (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c) :
    mainReducedInclude G v ∈ G.toPartiteShape.c079ComponentRoles
      (mainLiftCut G cut) (c.map (mainReducedCutHom G cut)) := by
  obtain ⟨hn, he⟩ :=
    ((mainIsolatedReducedShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  apply (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mpr
  refine ⟨by simpa using hn, ?_⟩
  rw [← he]
  rfl

theorem main_reachable_stays_reduced_component (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (c : (mainIsolatedReducedShape G).toPartiteShape.C079CutComponent cut)
    {u v : {x : Fin G.toPartiteShape.roles // x ∉ mainLiftCut G cut}}
    (hu : ∃ a ∈ (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c,
      mainReducedInclude G a = u.1)
    (hReach : (G.toPartiteShape.c079CutGraph (mainLiftCut G cut)).Reachable u v) :
    ∃ b ∈ (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c,
      mainReducedInclude G b = v.1 := by
  have h := (SimpleGraph.reachable_iff_reflTransGen u v).mp hReach
  clear hReach
  induction h with
  | refl => exact hu
  | @tail y z hPath hAdj ih =>
    obtain ⟨a, ha, he⟩ := ih
    obtain ⟨_, e, hey, hez⟩ := hAdj
    have hzCov := main_incident_covered G e hez
    let b := mainReducedIndex G z.1 hzCov
    have hb : b ∉ cut := by
      intro hbc
      exact z.2 ((main_index_mem_liftCut G cut z.1 hzCov).mp hbc)
    have hae : (mainIsolatedReducedShape G).toPartiteShape.EdgeIncident e a :=
      (main_reduced_incident_iff G e a).mpr (he.symm ▸ hey)
    have hbe : (mainIsolatedReducedShape G).toPartiteShape.EdgeIncident e b :=
      (main_reduced_incident_iff G e b).mpr (by simpa [b] using hez)
    exact ⟨b, (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles_edge_closed_outside_cut
      cut c ha e hae hbe hb, main_include_index G z.1 hzCov⟩

theorem main_reduced_component_roles_map (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (c : (mainIsolatedReducedShape G).toPartiteShape.C079CutComponent cut) :
    G.toPartiteShape.c079ComponentRoles (mainLiftCut G cut) (c.map (mainReducedCutHom G cut)) =
      ((mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c).map
        (mainReducedInclude G) := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
    have haOld := main_reduced_component_mem_map G cut c a ha
    obtain ⟨haCut, haComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp haOld
    obtain ⟨hvCut, hvComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp hv
    have hReach := SimpleGraph.ConnectedComponent.exact (haComp.trans hvComp.symm)
    exact Finset.mem_map.mpr
      (main_reachable_stays_reduced_component G cut c ⟨a, ha, rfl⟩ hReach)
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact main_reduced_component_mem_map G cut c a ha

theorem main_reduced_component_map_injective (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles)) :
    Function.Injective (fun c : (mainIsolatedReducedShape G).toPartiteShape.C079CutComponent cut =>
      c.map (mainReducedCutHom G cut)) := by
  intro c d he
  have hRoles : (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c =
      (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut d := by
    apply Finset.map_injective (mainReducedInclude G)
    rw [← main_reduced_component_roles_map, ← main_reduced_component_roles_map]
    exact congrArg (G.toPartiteShape.c079ComponentRoles (mainLiftCut G cut)) he
  obtain ⟨v, hv⟩ := (mainIsolatedReducedShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
  have hvd := hRoles ▸ hv
  obtain ⟨_, hc⟩ :=
    ((mainIsolatedReducedShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  obtain ⟨_, hd⟩ :=
    ((mainIsolatedReducedShape G).toPartiteShape.mem_c079ComponentRoles_iff cut d v).mp hvd
  exact hc.symm.trans hd

theorem main_reduced_component_map_active_iff (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (c : (mainIsolatedReducedShape G).toPartiteShape.C079CutComponent cut) :
    PartiteShape.C079CutComponent.IsActive (G := G.toPartiteShape)
      (cut := mainLiftCut G cut) (c.map (mainReducedCutHom G cut)) ↔ c.IsActive := by
  have hRoles := main_reduced_component_roles_map G cut c
  constructor
  · intro h
    constructor
    · intro v hv
      have hb := h.1 _ (main_reduced_component_mem_map G cut c v hv)
      exact ⟨fun hl => hb.1 ((main_reduced_left_iff G v).mp hl),
        fun hr => hb.2 ((main_reduced_right_iff G v).mp hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨a, ha, b, hb, e, (main_reduced_incident_iff G e a).mpr hev,
        (main_reduced_incident_iff G e b).mpr hex⟩
  · intro h
    constructor
    · intro v hv
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      have hb := h.1 a ha
      exact ⟨fun hl => hb.1 ((main_reduced_left_iff G a).mpr hl),
        fun hr => hb.2 ((main_reduced_right_iff G a).mpr hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      exact ⟨mainReducedInclude G v, main_reduced_component_mem_map G cut c v hv,
        mainReducedInclude G x, (main_include_mem_liftCut G cut x).mpr hx, e,
        (main_reduced_incident_iff G e v).mp hev,
        (main_reduced_incident_iff G e x).mp hex⟩

theorem main_active_component_in_reduced_image (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles))
    (c : G.toPartiteShape.C079CutComponent (mainLiftCut G cut)) (hc : c.IsActive) :
    ∃ d : (mainIsolatedReducedShape G).toPartiteShape.C079CutComponent cut,
      d.map (mainReducedCutHom G cut) = c := by
  obtain ⟨v, hv, x, hx, e, hev, hex⟩ := hc.2
  have hvCov := main_incident_covered G e hev
  obtain ⟨hvCut, hvComp⟩ := (G.toPartiteShape.mem_c079ComponentRoles_iff _ c v).mp hv
  have hn : mainReducedIndex G v hvCov ∉ cut := by
    intro hh
    exact hvCut ((main_index_mem_liftCut G cut v hvCov).mp hh)
  refine ⟨(mainIsolatedReducedShape G).toPartiteShape.c079CutGraph cut |>.connectedComponentMk
    ⟨mainReducedIndex G v hvCov, hn⟩, ?_⟩
  change (G.toPartiteShape.c079CutGraph (mainLiftCut G cut)).connectedComponentMk
    ((mainReducedCutHom G cut) ⟨mainReducedIndex G v hvCov, hn⟩) = c
  have he : (mainReducedCutHom G cut) ⟨mainReducedIndex G v hvCov, hn⟩ =
      ⟨v, hvCut⟩ := Subtype.ext (main_include_index G v hvCov)
  rw [he]
  exact hvComp

/-- Removing isolated middle roles preserves the actual number of active cut components. -/
theorem main_reduced_activeComponentCount_eq (G : PaperShape)
    (cut : Finset (Fin (mainIsolatedReducedShape G).roles)) :
    (mainIsolatedReducedShape G).toPartiteShape.c079ActiveComponentCount cut =
      G.toPartiteShape.c079ActiveComponentCount (mainLiftCut G cut) := by
  unfold PartiteShape.c079ActiveComponentCount
  apply Finset.card_bij (fun c _ => c.map (mainReducedCutHom G cut))
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (main_reduced_component_map_active_iff G cut c).mpr hc
  · intro c hc d hd he
    exact main_reduced_component_map_injective G cut he
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨d, hd⟩ := main_active_component_in_reduced_image G cut c hc
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (main_reduced_component_map_active_iff G cut d).mp (hd.symm ▸ hc)

/-- The manuscript's active maximum is unchanged, including empty boundaries. -/
theorem main_reduced_activeMaximum_eq (G : PaperShape) :
    (mainIsolatedReducedShape G).toPartiteShape.activeComponentMaximum =
      G.toPartiteShape.activeComponentMaximum := by
  apply Nat.le_antisymm
  · obtain ⟨cut, hm, he⟩ :=
      (mainIsolatedReducedShape G).toPartiteShape.exists_minimum_with_c079ActiveMaximum
    rw [← he, main_reduced_activeComponentCount_eq]
    exact G.toPartiteShape.c079ActiveComponentCount_le_maximum _ (main_liftCut_minimal G cut hm)
  · obtain ⟨cut, hm, he⟩ := G.toPartiteShape.exists_minimum_with_c079ActiveMaximum
    have hcut : mainLiftCut G (mainPullCut G cut) = cut := by
      rw [main_lift_pullCut_eq_inter,
        Finset.inter_eq_left.mpr (main_minSeparator_subset_covered G cut hm)]
    rw [← he, ← hcut, ← main_reduced_activeComponentCount_eq]
    exact (mainIsolatedReducedShape G).toPartiteShape.c079ActiveComponentCount_le_maximum _
      (main_pullCut_minimal G cut hm)

end GraphMatrixReplica
