import GraphMatrix.Main.RoleAllocation
import GraphMatrix.Main.CoreActiveComponents
import GraphMatrix.Main.BoundaryCoreTypedSharp

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

def mainFullTypedGraphScale (G : PaperShape) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (((G.roles : ℝ) + G.isolatedMiddleRoles.card -
    G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
      Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2)

theorem main_fullTypedGraphScale_nonneg (G : PaperShape) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ mainFullTypedGraphScale G n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  unfold mainFullTypedGraphScale
  positivity

theorem main_typed_squared_scale_assembly (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (n : ℕ) (hn : 0 < n) (C : ℝ) :
    ((n : ℝ) ^ G.isolatedMiddleRoles.card) ^ 2 *
      ((C * mainTypedGraphScale (mainBoundaryCoreShape G) n) ^ 2 *
        (n : ℝ) ^ (∑ j : (mainGraphRawFactorShape G dimension).DetachedComponent,
          Fintype.card ((mainGraphRawFactorShape G dimension).CanonicalDetached j))) =
      (C * mainFullTypedGraphScale G n) ^ 2 := by
  let h := G.isolatedMiddleRoles.card
  let d := ∑ j : (mainGraphRawFactorShape G dimension).DetachedComponent,
    Fintype.card ((mainGraphRawFactorShape G dimension).CanonicalDetached j)
  have hroles : ((mainBoundaryCoreShape G).roles : ℝ) + h + d = G.roles := by
    exact_mod_cast main_graph_role_allocation G dimension
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ) ^ h) ^ 2 *
      (((n : ℝ) ^ ((((mainBoundaryCoreShape G).roles : ℝ) -
          G.toPartiteShape.rightLeftSeparatorNumber) / 2)) ^ 2 * (n : ℝ) ^ d) =
      ((n : ℝ) ^ (((G.roles : ℝ) + h - G.toPartiteShape.rightLeftSeparatorNumber) / 2)) ^ 2 := by
    simp only [← Real.rpow_natCast]
    rw [← Real.rpow_mul hnR.le, ← Real.rpow_mul hnR.le, ← Real.rpow_mul hnR.le,
      ← Real.rpow_add hnR, ← Real.rpow_add hnR]
    congr 1
    norm_num
    linarith
  unfold mainTypedGraphScale mainFullTypedGraphScale
  rw [main_core_separatorNumber_eq, main_core_activeMaximum_eq]
  simp only [mul_pow]
  calc
    _ = C ^ 2 * (((n : ℝ) ^ h) ^ 2 *
        (((n : ℝ) ^ ((((mainBoundaryCoreShape G).roles : ℝ) -
          G.toPartiteShape.rightLeftSeparatorNumber) / 2)) ^ 2 * (n : ℝ) ^ d)) *
          (Real.log (n : ℝ) ^ ((G.toPartiteShape.activeComponentMaximum : ℝ) / 2)) ^ 2 := by
            dsimp [h, d]; ring
    _ = _ := by rw [hp]; ring

end GraphMatrixReplica
