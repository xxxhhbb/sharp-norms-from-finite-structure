import R6.C2ActualChaosReindex

/-!
# C2 expansion of the original typed partite matrix after freezing nonfresh arrays

All sums and products below range over the original role and edge occurrence
IDs.  The target expansion is the actual retained-assignment formula with the
all-separator component weight from `C2AllSeparatorContraction`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators

namespace GraphMatrixReplica.PaperR16.C2Actual

open GraphMatrixReplica
open GraphMatrixReplica.P2a
open GraphMatrixReplica.PaperR16
open GraphMatrixReplica.PaperR16.ActualPrimitiveObservations

attribute [local instance] Classical.propDecidable

variable (P : PaperShape) (S : Finset (Fin P.roles))
variable (dimension : Fin P.roles → ℕ)

/-- Real coercion of the existing concrete rational typed partite matrix. -/
def partiteBoundaryMatrixReal (ε : JointEdgeSignSample (G := P.toPartiteShape) dimension) :
    Matrix (PartiteBoundaryRow (G := P.toPartiteShape) dimension) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ℝ :=
  fun row col => (partiteBoundaryMatrix P.toPartiteShape dimension ε row col : ℝ)

/-- The requested deterministic expansion after a complete frozen realization. -/
def retainedExpansion
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (ξ : FreshSample (G := P.toPartiteShape) S dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) : ℝ :=
  ∑ a : RetainedAssignment (G := P.toPartiteShape) S dimension,
    if retainedBoundaryCompatible P S dimension a row col then
      actualWeight (G := P.toPartiteShape) S dimension ω (retainedCutAssignment P S dimension a) *
        retainedFreshMonomial P S dimension ξ a
    else 0

/-- Full assignment assembled from a retained assignment and one assignment per
actual active component. -/
abbrev assembledAssignment
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension) : PartiteRoleAssignment (G := P.toPartiteShape) dimension :=
  (fullAssignmentEquiv (G := P.toPartiteShape) S dimension).symm (a, x)

@[simp] theorem assembledAssignment_retained
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension)
    (v : RetainedRole (G := P.toPartiteShape) S) :
    assembledAssignment P S dimension a x v.1 = a v := by
  exact fullAssignmentEquiv_symm_retained (G := P.toPartiteShape) S dimension (a, x) v

@[simp] theorem assembledAssignment_component
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension)
    (K : ActiveComponent P.toPartiteShape S) (v : ComponentRole K) :
    assembledAssignment P S dimension a x v.1 = x K v := by
  exact fullAssignmentEquiv_symm_component (G := P.toPartiteShape) S dimension (a, x) K v

/-- On an owner edge, the assembled full assignment reads exactly the endpoint
labels used by the direct owner-edge contraction. -/
theorem assembledAssignment_owned_source
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension)
    (K : ActiveComponent P.toPartiteShape S) (e : OwnedNonfreshEdge (G := P.toPartiteShape) S K) :
    assembledAssignment P S dimension a x (P.source e.1.1) =
      ownedSourceLabel (G := P.toPartiteShape) S dimension (retainedCutAssignment P S dimension a)
        K (x K) e := by
  classical
  rcases owned_source_mem_component_or_cut (G := P.toPartiteShape) S K e with hsK | hsS
  · rw [ownedSourceLabel_of_component (G := P.toPartiteShape) S dimension
      (retainedCutAssignment P S dimension a) K (x K) e hsK]
    exact assembledAssignment_component P S dimension a x K
      ⟨P.source e.1.1, hsK⟩
  · rw [ownedSourceLabel_of_cut (G := P.toPartiteShape) S dimension
      (retainedCutAssignment P S dimension a) K (x K) e hsS]
    exact assembledAssignment_retained P S dimension a x
      ⟨P.source e.1.1, cut_subset_retainedRoles P.toPartiteShape S hsS⟩

/-- Target-endpoint analogue. -/
theorem assembledAssignment_owned_target
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension)
    (K : ActiveComponent P.toPartiteShape S) (e : OwnedNonfreshEdge (G := P.toPartiteShape) S K) :
    assembledAssignment P S dimension a x (P.target e.1.1) =
      ownedTargetLabel (G := P.toPartiteShape) S dimension (retainedCutAssignment P S dimension a)
        K (x K) e := by
  classical
  rcases owned_target_mem_component_or_cut (G := P.toPartiteShape) S K e with htK | htS
  · rw [ownedTargetLabel_of_component (G := P.toPartiteShape) S dimension
      (retainedCutAssignment P S dimension a) K (x K) e htK]
    exact assembledAssignment_component P S dimension a x K
      ⟨P.target e.1.1, htK⟩
  · rw [ownedTargetLabel_of_cut (G := P.toPartiteShape) S dimension
      (retainedCutAssignment P S dimension a) K (x K) e htS]
    exact assembledAssignment_retained P S dimension a x
      ⟨P.target e.1.1, cut_subset_retainedRoles P.toPartiteShape S htS⟩

/-- Fresh endpoints are read from the retained half of the full assignment. -/
theorem assembledAssignment_fresh_source
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension)
    (e : FreshEdge P.toPartiteShape S) :
    assembledAssignment P S dimension a x (P.source e.1) =
      a ⟨P.source e.1, e.2.1⟩ :=
  assembledAssignment_retained P S dimension a x ⟨P.source e.1, e.2.1⟩

theorem assembledAssignment_fresh_target
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension)
    (e : FreshEdge P.toPartiteShape S) :
    assembledAssignment P S dimension a x (P.target e.1) =
      a ⟨P.target e.1, e.2.2⟩ :=
  assembledAssignment_retained P S dimension a x ⟨P.target e.1, e.2.2⟩

/-- Product on all nonfresh edges factors by the unique owner component. -/
theorem nonfreshMonomial_eq_owner_product
    (ω : FrozenSample (G := P.toPartiteShape) S dimension)
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension) :
    (∏ e : NonfreshEdge (G := P.toPartiteShape) S,
      (rademacherSign
        (ω e
          (assembledAssignment P S dimension a x (P.source e.1),
           assembledAssignment P S dimension a x (P.target e.1))) : ℝ)) =
      ∏ K : ActiveComponent P.toPartiteShape S,
        ownedComponentMonomial (G := P.toPartiteShape) S dimension ω
          (retainedCutAssignment P S dimension a) K (x K) := by
  classical
  rw [← Equiv.prod_comp (nonfreshEdgeOwnerEquiv (G := P.toPartiteShape) S).symm]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro K _hK
  apply Finset.prod_congr rfl
  intro e _he
  change (rademacherSign (ω e.1
    (assembledAssignment P S dimension a x (P.source e.1.1),
     assembledAssignment P S dimension a x (P.target e.1.1))) : ℝ) = _
  rw [assembledAssignment_owned_source P S dimension a x K e]
  rw [assembledAssignment_owned_target P S dimension a x K e]

/-- The original all-edge monomial, after assembling frozen/fresh arrays, is
exactly fresh times owner-factorized nonfresh. -/
theorem assembledEdgeMonomial_real
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (ξ : FreshSample (G := P.toPartiteShape) S dimension)
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension) :
    (partiteAssignmentEdgeMonomial
      (assembleSample (G := P.toPartiteShape) S dimension ω ξ) (assembledAssignment P S dimension a x) : ℝ) =
      retainedFreshMonomial P S dimension ξ a *
        (∏ K : ActiveComponent P.toPartiteShape S,
          ownedComponentMonomial (G := P.toPartiteShape) S dimension ω
            (retainedCutAssignment P S dimension a) K (x K)) := by
  classical
  unfold partiteAssignmentEdgeMonomial
  push_cast
  change (∏ e : Fin P.edges, (rademacherSign
    (assembleSample (G := P.toPartiteShape) S dimension ω ξ e
      (assembledAssignment P S dimension a x (P.source e),
       assembledAssignment P S dimension a x (P.target e))) : ℝ)) = _
  rw [← Equiv.prod_comp (edgeFreshSplitEquiv P S).symm]
  rw [Fintype.prod_sum_type]
  congr 1
  · unfold retainedFreshMonomial
    apply Finset.prod_congr rfl
    intro e _he
    change (rademacherSign (assembleSample (G := P.toPartiteShape) S dimension ω ξ e.1
      (assembledAssignment P S dimension a x (P.source e.1),
       assembledAssignment P S dimension a x (P.target e.1))) : ℝ) = _
    rw [assembleSample_fresh]
    rw [assembledAssignment_fresh_source P S dimension a x e]
    rw [assembledAssignment_fresh_target P S dimension a x e]
  · rw [← nonfreshMonomial_eq_owner_product P S dimension ω a x]
    apply Finset.prod_congr rfl
    intro e _he
    change (rademacherSign (assembleSample (G := P.toPartiteShape) S dimension ω ξ e.1
      (assembledAssignment P S dimension a x (P.source e.1),
       assembledAssignment P S dimension a x (P.target e.1))) : ℝ) = _
    rw [assembleSample_nonfresh]

/-- Summing all labels in all active components turns the owner-product into the
product of the genuine component contractions. -/
theorem activeFamily_sum_eq_actualWeight
    (ω : FrozenSample (G := P.toPartiteShape) S dimension)
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension) :
    (∑ x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension,
      ∏ K : ActiveComponent P.toPartiteShape S,
        ownedComponentMonomial (G := P.toPartiteShape) S dimension ω
          (retainedCutAssignment P S dimension a) K (x K)) =
      actualWeight (G := P.toPartiteShape) S dimension ω (retainedCutAssignment P S dimension a) := by
  classical
  rw [← Fintype.prod_sum]
  unfold actualWeight
  apply Finset.prod_congr rfl
  intro K _hK
  exact ownedComponentContraction_eq_actual (G := P.toPartiteShape) S dimension ω
    (retainedCutAssignment P S dimension a) K

/-- Main B1 expansion: this is proved from the existing `partiteBoundaryMatrix`
definition by the actual full-assignment equivalence; the right side is not a
replacement definition of the matrix. -/
theorem partiteBoundaryMatrixReal_eq_retainedExpansion
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (ξ : FreshSample (G := P.toPartiteShape) S dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    partiteBoundaryMatrixReal P dimension (assembleSample (G := P.toPartiteShape) S dimension ω ξ) row col =
      retainedExpansion P S dimension ω ξ row col := by
  classical
  unfold partiteBoundaryMatrixReal partiteBoundaryMatrix retainedExpansion
  push_cast
  simp only [apply_ite, Rat.cast_zero]
  let E := fullAssignmentEquiv (G := P.toPartiteShape) S dimension
  calc
    (∑ φ : PartiteRoleAssignment (G := P.toPartiteShape) dimension,
        if partiteBoundaryEntryCompatible φ row col then
          (partiteAssignmentEdgeMonomial (assembleSample (G := P.toPartiteShape) S dimension ω ξ) φ : ℝ)
        else 0) =
      ∑ p : RetainedAssignment (G := P.toPartiteShape) S dimension × ActiveFamilyAssignment (G := P.toPartiteShape) S dimension,
        if retainedBoundaryCompatible P S dimension p.1 row col then
          (partiteAssignmentEdgeMonomial (assembleSample (G := P.toPartiteShape) S dimension ω ξ)
            (E.symm p) : ℝ)
        else 0 := by
          rw [← Equiv.sum_comp E.symm]
          apply Finset.sum_congr rfl
          intro p _hp
          have he : fullAssignmentEquiv (G := P.toPartiteShape) S dimension (E.symm p) = p :=
            E.apply_symm_apply p
          simp only [partiteBoundaryEntryCompatible_iff_retained P S dimension, he]
    _ = ∑ a : RetainedAssignment (G := P.toPartiteShape) S dimension,
        ∑ x : ActiveFamilyAssignment (G := P.toPartiteShape) S dimension,
          if retainedBoundaryCompatible P S dimension a row col then
            retainedFreshMonomial P S dimension ξ a *
              (∏ K : ActiveComponent P.toPartiteShape S,
                ownedComponentMonomial (G := P.toPartiteShape) S dimension ω
                  (retainedCutAssignment P S dimension a) K (x K))
          else 0 := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro a _ha
            apply Finset.sum_congr rfl
            intro x _hx
            split
            · rw [assembledEdgeMonomial_real P S dimension ω ξ a x]
            · rfl
    _ = ∑ a : RetainedAssignment (G := P.toPartiteShape) S dimension,
        if retainedBoundaryCompatible P S dimension a row col then
          actualWeight (G := P.toPartiteShape) S dimension ω (retainedCutAssignment P S dimension a) *
            retainedFreshMonomial P S dimension ξ a
        else 0 := by
          apply Finset.sum_congr rfl
          intro a _ha
          by_cases h : retainedBoundaryCompatible P S dimension a row col
          · simp only [if_pos h]
            rw [← Finset.mul_sum]
            rw [activeFamily_sum_eq_actualWeight P S dimension ω a]
            ring
          · simp [h]


/-- For a fixed retained assignment there is exactly one fresh heterogeneous
multi-index that survives in the actual coefficient family.  Its sign product
is the genuine fresh-edge monomial. -/
theorem actualFreshIndexSum
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (ξ : FreshSample (G := P.toPartiteShape) S dimension)
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    (∑ j : lowerHeteroIndex (freshCount P S) (freshSize P S dimension),
      (∏ g : Fin (freshCount P S),
        (rademacherSign
          (freshSampleNoiseEquiv P S dimension ξ g (j g)) : ℝ)) *
        (if retainedBoundaryCompatible P S dimension a row col ∧
              j = freshIndexOfAssignment P S dimension a then
          actualWeight (G := P.toPartiteShape) S dimension ω (retainedCutAssignment P S dimension a)
        else 0)) =
      if retainedBoundaryCompatible P S dimension a row col then
        actualWeight (G := P.toPartiteShape) S dimension ω (retainedCutAssignment P S dimension a) *
          retainedFreshMonomial P S dimension ξ a
      else 0 := by
  classical
  by_cases hBoundary : retainedBoundaryCompatible P S dimension a row col
  · rw [Finset.sum_eq_single (freshIndexOfAssignment P S dimension a)]
    · simp only [hBoundary, true_and, if_pos]
      rw [freshSignProduct_assignment P S dimension ξ a]
      ring
    · intro j _hj hne
      have hji : ¬ j = freshIndexOfAssignment P S dimension a := hne
      simp [hBoundary, hji]
    · simp
  · simp [hBoundary]

/-- The recursively defined heterogeneous chaos is exactly the retained
assignment expansion obtained from the original typed matrix. -/
theorem lowerHeteroChaos_actual_eq_retainedExpansion
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (ξ : FreshSample (G := P.toPartiteShape) S dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    lowerHeteroChaos (freshCount P S) (freshSize P S dimension)
        (actualCoefficientFamily P S dimension ω)
        (freshSampleNoiseEquiv P S dimension ξ) row col =
      retainedExpansion P S dimension ω ξ row col := by
  classical
  rw [lowerHeteroChaos_apply_eq_sum]
  simp_rw [actualCoefficientFamily_entry P S dimension ω]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold retainedExpansion
  apply Finset.sum_congr rfl
  intro a _ha
  exact actualFreshIndexSum P S dimension ω ξ a row col

/-- B: after the actual fresh-sample encoding, the heterogeneous chaos is the
REAL coercion of the existing `partiteBoundaryMatrix` evaluated on the genuine
assembled original edge sample. -/
theorem lowerHeteroChaos_actual_eq_partiteBoundaryMatrixReal
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (ξ : FreshSample (G := P.toPartiteShape) S dimension) :
    lowerHeteroChaos (freshCount P S) (freshSize P S dimension)
        (actualCoefficientFamily P S dimension ω)
        (freshSampleNoiseEquiv P S dimension ξ) =
      partiteBoundaryMatrixReal P dimension (assembleSample (G := P.toPartiteShape) S dimension ω ξ) := by
  funext row col
  rw [lowerHeteroChaos_actual_eq_retainedExpansion P S dimension ω ξ row col]
  exact (partiteBoundaryMatrixReal_eq_retainedExpansion
    P S dimension ω ξ row col).symm

#print axioms nonfreshMonomial_eq_owner_product
#print axioms assembledEdgeMonomial_real
#print axioms activeFamily_sum_eq_actualWeight
#print axioms partiteBoundaryMatrixReal_eq_retainedExpansion

end GraphMatrixReplica.PaperR16.C2Actual
