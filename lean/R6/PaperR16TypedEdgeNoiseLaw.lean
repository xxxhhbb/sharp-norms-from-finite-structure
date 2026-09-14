import R6.PaperR16ColoredEdgeLaw

/-! # Fixed-color typed sign sample read from uniform ambient noise

The paper's Bool convention is opposite to `rademacherSign`; hence the
selected ambient bits are complemented.  This module identifies their full
finite law with `JointEdgeSignSample` and supplies the sign identity required
by the existing colored entry bridge.  It is for one fixed disjoint role
coloring and does not average over colorings.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Repackage and complement a flat colored edge field as the independent
edgewise sign sample used by the fully-partite matrix. -/
def paperColoredEdgeFieldEquivJointSample
    (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (PaperColoredEdgeCoordinate G dimension → Bool) ≃
      JointEdgeSignSample (G := G.toPartiteShape) dimension where
  toFun field e ab := !(field ⟨e, ab⟩)
  invFun epsilon z := !(epsilon z.1 z.2)
  left_inv field := by
    funext z
    simp
  right_inv epsilon := by
    funext e ab
    simp

/-- The sign array extracted from one ambient sample on selected colored
unordered-edge coordinates. -/
def PaperRoleColoring.readJointEdgeSignSample
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) (w : PaperNoise n) :
    JointEdgeSignSample (G := G.toPartiteShape) dimension :=
  fun e ab => !(w (C.ambientEdge ⟨e, ab⟩).1
                    (C.ambientEdge ⟨e, ab⟩).2)

/-- Under ambient uniform sampling, the complete extracted typed sign
sample has its canonical joint uniform law. -/
theorem PaperRoleColoring.paperMean_readJointEdgeSignSample
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    [DecidableEq (PaperColoredEdgeCoordinate G dimension)]
    (C : PaperRoleColoring G dimension n)
    (f : JointEdgeSignSample (G := G.toPartiteShape) dimension → ℝ) :
    paperMean (fun w : PaperNoise n =>
      f (C.readJointEdgeSignSample w)) = paperMean f := by
  classical
  let E := paperColoredEdgeFieldEquivJointSample G dimension
  calc
    paperMean (fun w : PaperNoise n =>
        f (C.readJointEdgeSignSample w)) =
        paperMean (fun field :
            PaperColoredEdgeCoordinate G dimension → Bool =>
          f (E field)) := by
      exact C.paperMean_coloredEdgeBoolField (fun field => f (E field))
    _ = paperMean f := paperMean_equiv E f

/-- The extracted typed sign is exactly the selected ambient paper sign,
including the Boolean-convention complement. -/
theorem PaperRoleColoring.paperEdgeSign_eq_readJointEdgeSignSample
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) (w : PaperNoise n)
    (e : Fin G.edges) (a : Fin (dimension (G.source e)))
    (b : Fin (dimension (G.target e))) :
    paperEdgeSign w (C.embedding (G.source e) a)
        (C.embedding (G.target e) b) =
      (rademacherSign (C.readJointEdgeSignSample w e (a, b)) : ℝ) := by
  unfold paperEdgeSign PaperRoleColoring.readJointEdgeSignSample
    PaperRoleColoring.ambientEdge paperUnorderedPair
  cases w (min (C.embedding (G.source e) a)
                (C.embedding (G.target e) b))
          (max (C.embedding (G.source e) a)
                (C.embedding (G.target e) b)) <;>
    simp [rademacherSign]

/-- The fixed-color compressed paper matrix is pointwise the real cast of
the typed matrix driven by the ambient sample's extracted sign field. -/
theorem PaperRoleColoring.coloredBoundaryMatrix_eq_readTyped
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) (w : PaperNoise n) :
    paperRoleColoredBoundaryMatrix G dimension n C w =
      fun row col =>
        ((partiteBoundaryMatrix G.toPartiteShape dimension
          (C.readJointEdgeSignSample w) row col : ℚ) : ℝ) :=
  paperRoleColoredBoundaryMatrix_eq_partiteBoundaryMatrix
    G dimension n C w (C.readJointEdgeSignSample w)
    (C.paperEdgeSign_eq_readJointEdgeSignSample w)

#print axioms paperColoredEdgeFieldEquivJointSample
#print axioms PaperRoleColoring.paperMean_readJointEdgeSignSample
#print axioms PaperRoleColoring.paperEdgeSign_eq_readJointEdgeSignSample
#print axioms PaperRoleColoring.coloredBoundaryMatrix_eq_readTyped

end GraphMatrixReplica
