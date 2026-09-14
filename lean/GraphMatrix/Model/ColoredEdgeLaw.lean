import GraphMatrix.Model.ColoredNoiseLaw
import GraphMatrix.RoleColoredNoiseExtension

/-! # The ambient-to-typed edge-field law for fixed disjoint role colors

The no-collision theorem for colored shape-edge coordinates and the generic
finite Bool restriction law now imply that the selected coordinates of one
ambient paper noise sample have the independent joint law of typed edge
arrays.  This is a distribution statement for a fixed color partition; it
does not prove random-color averaging or the global upper norm transfer.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The already proved no-collision map, packaged as a genuine embedding. -/
def PaperRoleColoring.ambientEdgeEmbedding
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) :
    PaperColoredEdgeCoordinate G dimension ↪ Fin n × Fin n :=
  ⟨C.ambientEdge, C.ambientEdge_injective⟩

/-- A uniformly sampled ambient paper noise, read on the disjoint colored
edge coordinates, is exactly uniform on the complete typed edge-sample
space.  Equality is for every real test function, not merely moments. -/
theorem PaperRoleColoring.paperMean_coloredEdgeBoolField
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    [DecidableEq (PaperColoredEdgeCoordinate G dimension)]
    (C : PaperRoleColoring G dimension n)
    (f : (PaperColoredEdgeCoordinate G dimension → Bool) → ℝ) :
    paperMean (fun w : PaperNoise n =>
      f (fun z => w (C.ambientEdge z).1 (C.ambientEdge z).2)) =
        paperMean f := by
  classical
  calc
    paperMean (fun w : PaperNoise n =>
        f (fun z => w (C.ambientEdge z).1 (C.ambientEdge z).2)) =
        paperMean (fun w : (Fin n × Fin n) → Bool =>
          f (fun z => w (C.ambientEdge z))) := by
      exact (paperMean_equiv (Equiv.curry (Fin n) (Fin n) Bool)
        (fun w : PaperNoise n =>
          f (fun z => w (C.ambientEdge z).1
            (C.ambientEdge z).2))).symm
    _ = paperMean f :=
      paperMean_injectiveBoolRestriction C.ambientEdgeEmbedding f


end GraphMatrixReplica
