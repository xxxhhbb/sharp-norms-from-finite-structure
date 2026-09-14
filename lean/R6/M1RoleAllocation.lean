import R6.M1CoreMatrixIndices
import R6.PaperFinalFlattening

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

theorem root_raw_card_partition {W E : Type} [Fintype W] [Fintype E] [DecidableEq W]
    (S : PaperR16.RawFactorShape W E) :
    Fintype.card S.CanonicalCore + Fintype.card S.CanonicalUnused +
      (∑ j : S.DetachedComponent, Fintype.card (S.CanonicalDetached j)) = Fintype.card W := by
  have hd : (∑ j : S.DetachedComponent, Fintype.card (S.CanonicalDetached j)) =
      S.detachedRoles.card := by
    calc
      _ = Fintype.card S.ComponentRoleType := Fintype.card_sigma.symm
      _ = Fintype.card S.DetachedRoleType := Fintype.card_congr S.detachedRoleComponentEquiv
      _ = S.detachedRoles.card := by simp [PaperR16.RawFactorShape.DetachedRoleType,
          PaperR16.RawFactorShape.detachedRoles, Fintype.card_subtype]
  have hc : Fintype.card S.CanonicalCore = S.coreRoles.card := by
    simp [PaperR16.RawFactorShape.CanonicalCore, PaperR16.RawFactorShape.coreRoles,
      Fintype.card_subtype]
  have hu : Fintype.card S.CanonicalUnused = S.unusedMiddleRoles.card := by
    simp [PaperR16.RawFactorShape.CanonicalUnused, PaperR16.RawFactorShape.unusedMiddleRoles,
      Fintype.card_subtype]
  rw [hc, hu, hd, ← Finset.card_union_of_disjoint S.core_unused_disjoint,
    ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨S.core_detached_disjoint, S.unused_detached_disjoint⟩), S.role_finset_union]
  exact Finset.card_univ

theorem root_raw_unused_card (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fintype.card (rootGraphRawFactorShape G dimension).CanonicalUnused = G.isolatedMiddleRoles.card := by
  let e : (rootGraphRawFactorShape G dimension).CanonicalUnused ≃ ↥G.isolatedMiddleRoles :=
    Equiv.subtypeEquivRight fun v => (root_raw_unused_iff_isolatedMiddle G dimension v).trans
      (G.mem_isolatedMiddleRoles_iff v).symm
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem root_raw_core_card (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    Fintype.card (rootGraphRawFactorShape G dimension).CanonicalCore = (rootBoundaryCoreShape G).roles := by
  simpa using (Fintype.card_congr (rootCoreCanonicalRoleEquiv G dimension)).symm

theorem root_graph_role_allocation (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (rootBoundaryCoreShape G).roles + G.isolatedMiddleRoles.card +
      (∑ j : (rootGraphRawFactorShape G dimension).DetachedComponent,
        Fintype.card ((rootGraphRawFactorShape G dimension).CanonicalDetached j)) = G.roles := by
  simpa only [root_raw_core_card, root_raw_unused_card, Fintype.card_fin] using
    root_raw_card_partition (rootGraphRawFactorShape G dimension)

theorem root_unusedScalar_le_pow (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (n : ℕ) (hsize : ∀ v, dimension v ≤ n) :
    (rootGraphRawFactorShape G dimension).canonicalPreprocessedShape.unusedScalar ≤
      (n : ℝ) ^ G.isolatedMiddleRoles.card := by
  let S := rootGraphRawFactorShape G dimension
  calc
    S.canonicalPreprocessedShape.unusedScalar = ∏ u : S.CanonicalUnused, (dimension u.1 : ℝ) := rfl
    _ ≤ ∏ _u : S.CanonicalUnused, (n : ℝ) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun u _ => by exact_mod_cast hsize u.1)
    _ = (n : ℝ) ^ G.isolatedMiddleRoles.card := by simp [S, root_raw_unused_card]

#print axioms root_raw_card_partition
#print axioms root_graph_role_allocation
#print axioms root_unusedScalar_le_pow
end GraphMatrixReplica
