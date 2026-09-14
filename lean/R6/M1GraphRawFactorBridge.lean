import R6.PaperR16LowerFactorCanonical
import R6.PaperIsolatedAmplitudeFactorization
import R6.C079BoundaryCoreScope
import R6.C027NormTransferInterface
import R6.PaperR16LowerFactorNormInterface

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GraphMatrixReplica

/-- The actual graph's occurrence list and vertex dimensions. Independence is
not asserted here; that belongs to the typed sample law. -/
def rootGraphRawFactorShape (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    PaperR16.RawFactorShape (Fin G.roles) (Fin G.edges) where
  size := dimension
  leftBoundary := G.toPartiteShape.leftBoundary
  rightBoundary := G.toPartiteShape.rightBoundary
  scope e := {G.source e, G.target e}
  scope_nonempty e := by simp

@[simp] theorem root_raw_scope_iff_incident (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (e : Fin G.edges) (v : Fin G.roles) :
    v ∈ (rootGraphRawFactorShape G dimension).scope e ↔ G.toPartiteShape.EdgeIncident e v := by
  change v ∈ ({G.source e, G.target e} : Finset _) ↔ G.source e = v ∨ G.target e = v
  simp [eq_comm]

theorem root_raw_coScope_iff (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (u v : Fin G.roles) :
    (rootGraphRawFactorShape G dimension).CoScope u v ↔
      ∃ e : Fin G.edges, G.toPartiteShape.EdgeIncident e u ∧ G.toPartiteShape.EdgeIncident e v := by
  simp [PaperR16.RawFactorShape.CoScope]

theorem root_raw_connected_prepend_boundary (G : PaperShape) (dimension : Fin G.roles → ℕ)
    {u v : Fin G.roles} (h : (rootGraphRawFactorShape G dimension).Connected u v) :
    Nonempty (G.toPartiteShape.EdgeWalkToBoundary v) →
      Nonempty (G.toPartiteShape.EdgeWalkToBoundary u) := by
  induction h with
  | refl w => exact id
  | @edge u v h =>
    intro ⟨tail⟩
    obtain ⟨e, hu, hv⟩ := (root_raw_coScope_iff G dimension u v).mp h
    exact ⟨.step e v hu hv tail⟩
  | trans h₁ h₂ ih₁ ih₂ => exact fun h => ih₁ (ih₂ h)

/-- The canonical factor core is precisely the actual graph's boundary-reachable roles. -/
theorem root_raw_core_iff_boundaryWalk (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (v : Fin G.toPartiteShape.roles) :
    (rootGraphRawFactorShape G dimension).CoreRole v ↔
      Nonempty (G.toPartiteShape.EdgeWalkToBoundary v) := by
  constructor
  · rintro ⟨b, hb, hConn⟩
    apply root_raw_connected_prepend_boundary G dimension hConn
    rcases Finset.mem_union.mp hb with hl | hr
    · exact ⟨PartiteShape.EdgeWalkToBoundary.finishLeft (G := G.toPartiteShape) b hl⟩
    · exact ⟨PartiteShape.EdgeWalkToBoundary.finishRight (G := G.toPartiteShape) b hr⟩
  · rintro ⟨walk⟩
    induction walk with
    | finishLeft v hl =>
      exact (rootGraphRawFactorShape G dimension).core_of_mem_boundary (Finset.mem_union_left _ hl)
    | finishRight v hr =>
      exact (rootGraphRawFactorShape G dimension).core_of_mem_boundary (Finset.mem_union_right _ hr)
    | @step v e w hv hw tail ih =>
      apply (rootGraphRawFactorShape G dimension).core_of_connected ih
      apply PaperR16.RawFactorShape.Connected.edge
      exact (root_raw_coScope_iff G dimension v w).mpr ⟨e, hv, hw⟩

theorem root_raw_unused_iff_isolatedMiddle (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (v : Fin G.roles) :
    (rootGraphRawFactorShape G dimension).UnusedMiddleRole v ↔ G.IsolatedMiddleRole v := by
  change ((¬ ∃ e : Fin G.edges, v ∈ ({G.source e, G.target e} : Finset _)) ∧
    v ∉ G.leftBoundaryFinset ∪ G.rightBoundaryFinset) ↔
      v ∉ G.leftBoundaryFinset ∧ v ∉ G.rightBoundaryFinset ∧
        ∀ e : Fin G.edges, G.source e ≠ v ∧ G.target e ≠ v
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, not_exists,
    not_or, ne_eq, eq_comm]
  tauto

theorem root_raw_detached_iff (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (v : Fin G.roles) :
    (rootGraphRawFactorShape G dimension).DetachedRole v ↔
      (∃ e : Fin G.edges, G.toPartiteShape.EdgeIncident e v) ∧
        ¬ Nonempty (G.toPartiteShape.EdgeWalkToBoundary v) := by
  simp only [PaperR16.RawFactorShape.DetachedRole, PaperR16.RawFactorShape.UsedRole,
    root_raw_scope_iff_incident, root_raw_core_iff_boundaryWalk]

theorem root_raw_all_core_iff (G : PaperShape) (dimension : Fin G.roles → ℕ) :
    (∀ v, (rootGraphRawFactorShape G dimension).CoreRole v) ↔
      G.toPartiteShape.IsBoundaryCore := by
  constructor
  · intro h v
    exact (root_raw_core_iff_boundaryWalk G dimension v).mp (h v)
  · intro h v
    exact (root_raw_core_iff_boundaryWalk G dimension v).mpr (h v)

/-- A concrete typed edge-sign sample, read through its exact two endpoint scope. -/
def rootGraphRawSignSample (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    (rootGraphRawFactorShape G dimension).RawSample where
  array e x := (rademacherSign (epsilon e
    (x ⟨G.source e, by simp [rootGraphRawFactorShape]⟩,
     x ⟨G.target e, by simp [rootGraphRawFactorShape]⟩)) : ℝ)

theorem root_raw_sign_amplitude_eq (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension)
    (x : PartiteRoleAssignment (G := G.toPartiteShape) dimension) :
    (rootGraphRawFactorShape G dimension).rawAmplitude (rootGraphRawSignSample G dimension epsilon) x =
      (partiteAssignmentEdgeMonomial epsilon x : ℝ) := by
  unfold PaperR16.RawFactorShape.rawAmplitude partiteAssignmentEdgeMonomial
  push_cast
  rfl

/-- Entrywise identification with the actual existing typed graph matrix,
including boundary overlap and arbitrary labelled dimensions. -/
theorem root_typed_matrix_eq_rawOperatorMatrix (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    c027PartiteBoundaryMatrixReal G dimension epsilon =
      (rootGraphRawFactorShape G dimension).rawOperatorMatrix
        (rootGraphRawSignSample G dimension epsilon) := by
  classical
  ext row col
  unfold c027PartiteBoundaryMatrixReal partiteBoundaryMatrix
    PaperR16.RawFactorShape.rawOperatorMatrix PaperR16.RawFactorShape.rawMatrix
  push_cast
  apply Finset.sum_congr
  · ext x; simp
  · intro x _
    change ((if partiteBoundaryEntryCompatible x row col then
        partiteAssignmentEdgeMonomial epsilon x else 0 : ℚ) : ℝ) =
      if partiteBoundaryEntryCompatible x row col then
        (rootGraphRawFactorShape G dimension).rawAmplitude
          (rootGraphRawSignSample G dimension epsilon) x else 0
    split_ifs <;> simp [root_raw_sign_amplitude_eq]

theorem root_typed_norm_eq_rawOperatorNorm (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ =
      ‖(rootGraphRawFactorShape G dimension).rawOperatorMatrix
        (rootGraphRawSignSample G dimension epsilon)‖ := by
  rw [root_typed_matrix_eq_rawOperatorMatrix]

/-- Exact deterministic component preprocessing on the existing typed matrix.
Only the typed sample is used; the original globally shared signs are not split. -/
theorem root_typed_norm_eq_scalar_mul_core (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ =
      |(rootGraphRawFactorShape G dimension).exactPreprocessingScalar
        (rootGraphRawSignSample G dimension epsilon)| *
      ‖(rootGraphRawFactorShape G dimension).coreOperatorMatrixNative
        (rootGraphRawSignSample G dimension epsilon)‖ := by
  rw [root_typed_norm_eq_rawOperatorNorm]
  exact (rootGraphRawFactorShape G dimension).rawOperatorMatrix_l2_opNorm_eq_native_core _

#print axioms rootGraphRawFactorShape
#print axioms root_raw_core_iff_boundaryWalk
#print axioms root_raw_unused_iff_isolatedMiddle
#print axioms root_raw_detached_iff
#print axioms root_raw_all_core_iff
#print axioms root_raw_sign_amplitude_eq
#print axioms root_typed_matrix_eq_rawOperatorMatrix
#print axioms root_typed_norm_eq_rawOperatorNorm
#print axioms root_typed_norm_eq_scalar_mul_core
end GraphMatrixReplica
