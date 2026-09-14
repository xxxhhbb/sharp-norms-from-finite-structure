import R6.PaperRoleColoredPartiteBridge
import R6.PaperGlobalEdgeParity

/-! # Extending edgewise signs to shared paper noise on disjoint role colors

The fully-partite model assigns an independent Boolean array to every shape
edge.  A disjoint role coloring embeds all of those arrays into the single
ambient unordered-edge noise used by the paper model.  The only possible
obstruction is a collision between two colored edge coordinates.  The strict
source/target order and injectivity of the edge list rule out exactly those
collisions.

The Boolean conventions on the two sides are opposite: `rademacherSign false`
is `+1`, while `paperEdgeSign` is `+1` when its Boolean input is `true`.
Accordingly the extension stores the Boolean complement of each edgewise
sample on the selected cross-color coordinates.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A shape edge together with one coordinate of its fully-partite sign
array. -/
abbrev PaperColoredEdgeCoordinate (G : PaperShape)
    (dimension : Fin G.roles → ℕ) :=
  Σ e : Fin G.edges,
    Fin (dimension (G.source e)) × Fin (dimension (G.target e))

/-- The ambient canonical unordered edge selected by a colored edge
coordinate. -/
def PaperRoleColoring.ambientEdge
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (z : PaperColoredEdgeCoordinate G dimension) : Fin n × Fin n :=
  paperUnorderedPair
    (C.embedding (G.source z.1) z.2.1)
    (C.embedding (G.target z.1) z.2.2)

/-- Disjoint role colors, strict endpoint order, and the paper shape's simple
edge assumption make the ambient unordered-edge coordinate collision-free. -/
theorem PaperRoleColoring.ambientEdge_injective
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) :
    Function.Injective C.ambientEdge := by
  rintro ⟨e, a, b⟩ ⟨f, c, d⟩ hPair
  have hSym :
      s(C.embedding (G.source e) a, C.embedding (G.target e) b) =
        s(C.embedding (G.source f) c, C.embedding (G.target f) d) := by
    apply paperCanonicalAmbientEdge_injective
    simpa [PaperRoleColoring.ambientEdge, paperUnorderedPair] using hPair
  rw [Sym2.eq_iff] at hSym
  rcases hSym with hDirect | hReverse
  · have hSource : G.source e = G.source f := by
      by_contra hne
      exact C.disjoint hne a c hDirect.1
    have hTarget : G.target e = G.target f := by
      by_contra hne
      exact C.disjoint hne b d hDirect.2
    have hef : e = f := G.edge_injective (Prod.ext hSource hTarget)
    subst f
    have hac : a = c := (C.embedding (G.source e)).injective hDirect.1
    have hbd : b = d := (C.embedding (G.target e)).injective hDirect.2
    subst c
    subst d
    rfl
  · have hSourceTarget : G.source e = G.target f := by
      by_contra hne
      exact C.disjoint hne a d hReverse.1
    have hTargetSource : G.target e = G.source f := by
      by_contra hne
      exact C.disjoint hne b c hReverse.2
    have heOrder := G.edge_order e
    have hfOrder := G.edge_order f
    omega

/-- Extend a joint family of edgewise Rademacher arrays to one ambient paper
noise.  Off the selected cross-color coordinates the value is fixed to
`false`; those values are irrelevant for the colored matrix block. -/
def PaperRoleColoring.extendJointEdgeSignSample
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    PaperNoise n :=
  fun i j =>
    if h : ∃ z : PaperColoredEdgeCoordinate G dimension,
        C.ambientEdge z = (i, j) then
      !(epsilon h.choose.1 h.choose.2)
    else false

/-- On every selected cross-color coordinate, the extension stores exactly
the complemented edgewise Boolean.  This is the reusable no-conflict
interface beneath the sign identity. -/
theorem PaperRoleColoring.extendJointEdgeSignSample_apply_ambientEdge
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension)
    (z : PaperColoredEdgeCoordinate G dimension) :
    C.extendJointEdgeSignSample epsilon (C.ambientEdge z).1
        (C.ambientEdge z).2 = !(epsilon z.1 z.2) := by
  unfold PaperRoleColoring.extendJointEdgeSignSample
  split
  next h =>
    have hz : h.choose = z :=
      C.ambientEdge_injective (h.choose_spec.trans rfl)
    exact congrArg
      (fun q : PaperColoredEdgeCoordinate G dimension =>
        !(epsilon q.1 q.2)) hz
  next h =>
    exact (h ⟨z, rfl⟩).elim

/-- The resulting ambient paper sign agrees with the real-valued cast of the
edgewise Rademacher sign at every shape edge and coordinate. -/
theorem PaperRoleColoring.paperEdgeSign_extendJointEdgeSignSample
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension)
    (e : Fin G.edges) (a : Fin (dimension (G.source e)))
    (b : Fin (dimension (G.target e))) :
    paperEdgeSign (C.extendJointEdgeSignSample epsilon)
        (C.embedding (G.source e) a) (C.embedding (G.target e) b) =
      (rademacherSign (epsilon e (a, b)) : ℝ) := by
  let z : PaperColoredEdgeCoordinate G dimension := ⟨e, (a, b)⟩
  have hApply := C.extendJointEdgeSignSample_apply_ambientEdge epsilon z
  change C.extendJointEdgeSignSample epsilon
      (min (C.embedding (G.source e) a) (C.embedding (G.target e) b))
      (max (C.embedding (G.source e) a) (C.embedding (G.target e) b)) =
        !(epsilon e (a, b)) at hApply
  rw [paperEdgeSign, hApply]
  cases epsilon e (a, b) <;> simp [rademacherSign]

/-- The colored paper matrix admits the fully-partite boundary matrix as an
actual shared-noise realization, with no additional sign-compatibility
hypothesis. -/
theorem paperRoleColoredBoundaryMatrix_extendJointEdgeSignSample
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (C : PaperRoleColoring G dimension n)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    paperRoleColoredBoundaryMatrix G dimension n C
        (C.extendJointEdgeSignSample epsilon) =
      fun row col =>
        ((partiteBoundaryMatrix G.toPartiteShape dimension epsilon row col : ℚ) : ℝ) :=
  paperRoleColoredBoundaryMatrix_eq_partiteBoundaryMatrix
    G dimension n C (C.extendJointEdgeSignSample epsilon) epsilon
    (C.paperEdgeSign_extendJointEdgeSignSample epsilon)

#print axioms PaperRoleColoring.ambientEdge_injective
#print axioms PaperRoleColoring.extendJointEdgeSignSample_apply_ambientEdge
#print axioms PaperRoleColoring.paperEdgeSign_extendJointEdgeSignSample
#print axioms paperRoleColoredBoundaryMatrix_extendJointEdgeSignSample

end GraphMatrixReplica
