import R6.M1ReducedGraphParameters
import R6.C079ActiveComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

@[simp] theorem root_include_mem_liftCut (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (v : Fin (rootIsolatedReducedShape G).roles) :
    rootReducedInclude G v ∈ rootLiftCut G cut ↔ v ∈ cut := by
  exact Finset.mem_map' (rootReducedInclude G)

def rootReducedCutHom (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles)) :
    (rootIsolatedReducedShape G).toPartiteShape.c079CutGraph cut →g
      G.toPartiteShape.c079CutGraph (rootLiftCut G cut) where
  toFun v := ⟨rootReducedInclude G v.1, by simpa using v.2⟩
  map_rel' := by
    intro u v h
    obtain ⟨hne, e, hu, hv⟩ := h
    exact ⟨fun he => hne ((rootReducedInclude G).injective he), e,
      (root_reduced_incident_iff G e u.1).mp hu,
      (root_reduced_incident_iff G e v.1).mp hv⟩

theorem root_reduced_component_mem_map (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (c : (rootIsolatedReducedShape G).toPartiteShape.C079CutComponent cut)
    (v : Fin (rootIsolatedReducedShape G).roles)
    (hv : v ∈ (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c) :
    rootReducedInclude G v ∈ G.toPartiteShape.c079ComponentRoles
      (rootLiftCut G cut) (c.map (rootReducedCutHom G cut)) := by
  obtain ⟨hn, he⟩ :=
    ((rootIsolatedReducedShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  apply (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mpr
  refine ⟨by simpa using hn, ?_⟩
  rw [← he]
  rfl

theorem root_reachable_stays_reduced_component (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (c : (rootIsolatedReducedShape G).toPartiteShape.C079CutComponent cut)
    {u v : {x : Fin G.toPartiteShape.roles // x ∉ rootLiftCut G cut}}
    (hu : ∃ a ∈ (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c,
      rootReducedInclude G a = u.1)
    (hReach : (G.toPartiteShape.c079CutGraph (rootLiftCut G cut)).Reachable u v) :
    ∃ b ∈ (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c,
      rootReducedInclude G b = v.1 := by
  have h := (SimpleGraph.reachable_iff_reflTransGen u v).mp hReach
  clear hReach
  induction h with
  | refl => exact hu
  | @tail y z hPath hAdj ih =>
    obtain ⟨a, ha, he⟩ := ih
    obtain ⟨_, e, hey, hez⟩ := hAdj
    have hzCov := root_incident_covered G e hez
    let b := rootReducedIndex G z.1 hzCov
    have hb : b ∉ cut := by
      intro hbc
      exact z.2 ((root_index_mem_liftCut G cut z.1 hzCov).mp hbc)
    have hae : (rootIsolatedReducedShape G).toPartiteShape.EdgeIncident e a :=
      (root_reduced_incident_iff G e a).mpr (he.symm ▸ hey)
    have hbe : (rootIsolatedReducedShape G).toPartiteShape.EdgeIncident e b :=
      (root_reduced_incident_iff G e b).mpr (by simpa [b] using hez)
    exact ⟨b, (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles_edge_closed_outside_cut
      cut c ha e hae hbe hb, root_include_index G z.1 hzCov⟩

theorem root_reduced_component_roles_map (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (c : (rootIsolatedReducedShape G).toPartiteShape.C079CutComponent cut) :
    G.toPartiteShape.c079ComponentRoles (rootLiftCut G cut) (c.map (rootReducedCutHom G cut)) =
      ((rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c).map
        (rootReducedInclude G) := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
    have haOld := root_reduced_component_mem_map G cut c a ha
    obtain ⟨haCut, haComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp haOld
    obtain ⟨hvCut, hvComp⟩ :=
      (G.toPartiteShape.mem_c079ComponentRoles_iff _ _ _).mp hv
    have hReach := SimpleGraph.ConnectedComponent.exact (haComp.trans hvComp.symm)
    exact Finset.mem_map.mpr
      (root_reachable_stays_reduced_component G cut c ⟨a, ha, rfl⟩ hReach)
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact root_reduced_component_mem_map G cut c a ha

theorem root_reduced_component_map_injective (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles)) :
    Function.Injective (fun c : (rootIsolatedReducedShape G).toPartiteShape.C079CutComponent cut =>
      c.map (rootReducedCutHom G cut)) := by
  intro c d he
  have hRoles : (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut c =
      (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles cut d := by
    apply Finset.map_injective (rootReducedInclude G)
    rw [← root_reduced_component_roles_map, ← root_reduced_component_roles_map]
    exact congrArg (G.toPartiteShape.c079ComponentRoles (rootLiftCut G cut)) he
  obtain ⟨v, hv⟩ := (rootIsolatedReducedShape G).toPartiteShape.c079ComponentRoles_nonempty cut c
  have hvd := hRoles ▸ hv
  obtain ⟨_, hc⟩ :=
    ((rootIsolatedReducedShape G).toPartiteShape.mem_c079ComponentRoles_iff cut c v).mp hv
  obtain ⟨_, hd⟩ :=
    ((rootIsolatedReducedShape G).toPartiteShape.mem_c079ComponentRoles_iff cut d v).mp hvd
  exact hc.symm.trans hd

theorem root_reduced_component_map_active_iff (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (c : (rootIsolatedReducedShape G).toPartiteShape.C079CutComponent cut) :
    PartiteShape.C079CutComponent.IsActive (G := G.toPartiteShape)
      (cut := rootLiftCut G cut) (c.map (rootReducedCutHom G cut)) ↔ c.IsActive := by
  have hRoles := root_reduced_component_roles_map G cut c
  constructor
  · intro h
    constructor
    · intro v hv
      have hb := h.1 _ (root_reduced_component_mem_map G cut c v hv)
      exact ⟨fun hl => hb.1 ((root_reduced_left_iff G v).mp hl),
        fun hr => hb.2 ((root_reduced_right_iff G v).mp hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨a, ha, b, hb, e, (root_reduced_incident_iff G e a).mpr hev,
        (root_reduced_incident_iff G e b).mpr hex⟩
  · intro h
    constructor
    · intro v hv
      rw [hRoles] at hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
      have hb := h.1 a ha
      exact ⟨fun hl => hb.1 ((root_reduced_left_iff G a).mpr hl),
        fun hr => hb.2 ((root_reduced_right_iff G a).mpr hr)⟩
    · obtain ⟨v, hv, x, hx, e, hev, hex⟩ := h.2
      exact ⟨rootReducedInclude G v, root_reduced_component_mem_map G cut c v hv,
        rootReducedInclude G x, (root_include_mem_liftCut G cut x).mpr hx, e,
        (root_reduced_incident_iff G e v).mp hev,
        (root_reduced_incident_iff G e x).mp hex⟩

theorem root_active_component_in_reduced_image (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles))
    (c : G.toPartiteShape.C079CutComponent (rootLiftCut G cut)) (hc : c.IsActive) :
    ∃ d : (rootIsolatedReducedShape G).toPartiteShape.C079CutComponent cut,
      d.map (rootReducedCutHom G cut) = c := by
  obtain ⟨v, hv, x, hx, e, hev, hex⟩ := hc.2
  have hvCov := root_incident_covered G e hev
  obtain ⟨hvCut, hvComp⟩ := (G.toPartiteShape.mem_c079ComponentRoles_iff _ c v).mp hv
  have hn : rootReducedIndex G v hvCov ∉ cut := by
    intro hh
    exact hvCut ((root_index_mem_liftCut G cut v hvCov).mp hh)
  refine ⟨(rootIsolatedReducedShape G).toPartiteShape.c079CutGraph cut |>.connectedComponentMk
    ⟨rootReducedIndex G v hvCov, hn⟩, ?_⟩
  change (G.toPartiteShape.c079CutGraph (rootLiftCut G cut)).connectedComponentMk
    ((rootReducedCutHom G cut) ⟨rootReducedIndex G v hvCov, hn⟩) = c
  have he : (rootReducedCutHom G cut) ⟨rootReducedIndex G v hvCov, hn⟩ =
      ⟨v, hvCut⟩ := Subtype.ext (root_include_index G v hvCov)
  rw [he]
  exact hvComp

/-- Removing isolated middle roles preserves the actual number of active cut components. -/
theorem root_reduced_activeComponentCount_eq (G : PaperShape)
    (cut : Finset (Fin (rootIsolatedReducedShape G).roles)) :
    (rootIsolatedReducedShape G).toPartiteShape.c079ActiveComponentCount cut =
      G.toPartiteShape.c079ActiveComponentCount (rootLiftCut G cut) := by
  unfold PartiteShape.c079ActiveComponentCount
  apply Finset.card_bij (fun c _ => c.map (rootReducedCutHom G cut))
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (root_reduced_component_map_active_iff G cut c).mpr hc
  · intro c hc d hd he
    exact root_reduced_component_map_injective G cut he
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨d, hd⟩ := root_active_component_in_reduced_image G cut c hc
    refine ⟨d, ?_, hd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (root_reduced_component_map_active_iff G cut d).mp (hd.symm ▸ hc)

/-- The manuscript's active maximum is unchanged, including empty boundaries. -/
theorem root_reduced_activeMaximum_eq (G : PaperShape) :
    (rootIsolatedReducedShape G).toPartiteShape.c079ActiveMaximum =
      G.toPartiteShape.c079ActiveMaximum := by
  apply Nat.le_antisymm
  · obtain ⟨cut, hm, he⟩ :=
      (rootIsolatedReducedShape G).toPartiteShape.exists_minimum_with_c079ActiveMaximum
    rw [← he, root_reduced_activeComponentCount_eq]
    exact G.toPartiteShape.c079ActiveComponentCount_le_maximum _ (root_liftCut_minimal G cut hm)
  · obtain ⟨cut, hm, he⟩ := G.toPartiteShape.exists_minimum_with_c079ActiveMaximum
    have hcut : rootLiftCut G (rootPullCut G cut) = cut := by
      rw [root_lift_pullCut_eq_inter,
        Finset.inter_eq_left.mpr (root_minSeparator_subset_covered G cut hm)]
    rw [← he, ← hcut, ← root_reduced_activeComponentCount_eq]
    exact (rootIsolatedReducedShape G).toPartiteShape.c079ActiveComponentCount_le_maximum _
      (root_pullCut_minimal G cut hm)

#print axioms root_reduced_component_roles_map
#print axioms root_reduced_component_map_injective
#print axioms root_reduced_component_map_active_iff
#print axioms root_active_component_in_reduced_image
#print axioms root_reduced_activeComponentCount_eq
#print axioms root_reduced_activeMaximum_eq
end GraphMatrixReplica
