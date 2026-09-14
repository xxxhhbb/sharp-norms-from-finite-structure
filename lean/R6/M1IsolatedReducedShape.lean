import R6.M1GlobalIsolatedFactorization
import Mathlib.Data.Finset.Sort

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rootCoveredRoleIso (G : PaperShape) :
    Fin (coveredRoles G.isolatedMiddleRoles).card ≃o (coveredRoles G.isolatedMiddleRoles) :=
  (coveredRoles G.isolatedMiddleRoles).orderIsoOfFin rfl

/-- Delete exactly the isolated middle roles, retaining ordered boundaries
and the complete original edge occurrence list. Increasing reindexing preserves
the simple graph's stored endpoint ordering. -/
def rootIsolatedReducedShape (G : PaperShape) : PaperShape where
  roles := (coveredRoles G.isolatedMiddleRoles).card
  edges := G.edges
  source e := (rootCoveredRoleIso G).symm ⟨G.source e, G.source_mem_coveredRoles_isolatedMiddle e⟩
  target e := (rootCoveredRoleIso G).symm ⟨G.target e, G.target_mem_coveredRoles_isolatedMiddle e⟩
  edge_order e := (rootCoveredRoleIso G).symm.strictMono (G.edge_order e)
  edge_injective := by
    intro e f h
    apply G.edge_injective
    apply Prod.ext
    · have hh := congrArg (fun z => ((rootCoveredRoleIso G) z.1).1) h
      simpa using hh
    · have hh := congrArg (fun z => ((rootCoveredRoleIso G) z.2).1) h
      simpa using hh
  leftSize := G.leftSize
  rightSize := G.rightSize
  left := ⟨fun i => (rootCoveredRoleIso G).symm ⟨G.left i, root_left_mem_covered G i⟩, by
    intro i j h
    apply G.left.injective
    have hh := congrArg (fun z => ((rootCoveredRoleIso G) z).1) h
    simpa using hh⟩
  right := ⟨fun i => (rootCoveredRoleIso G).symm ⟨G.right i, root_right_mem_covered G i⟩, by
    intro i j h
    apply G.right.injective
    have hh := congrArg (fun z => ((rootCoveredRoleIso G) z).1) h
    simpa using hh⟩

theorem root_reduced_roles (G : PaperShape) :
    (rootIsolatedReducedShape G).roles = G.roles - G.isolatedMiddleRoles.card := by
  change (Finset.univ \ G.isolatedMiddleRoles).card = _
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- Every surviving role really occurs in an edge or a boundary. -/
theorem root_reduced_not_isolated (G : PaperShape)
    (v : Fin (rootIsolatedReducedShape G).roles) :
    ¬ (rootIsolatedReducedShape G).IsolatedMiddleRole v := by
  let H := rootIsolatedReducedShape G
  let x := (rootCoveredRoleIso G) v
  intro hIso
  have hOrig : G.IsolatedMiddleRole x.1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro hx
      obtain ⟨i, hi⟩ := (G.mem_leftBoundaryFinset_iff _).mp hx
      apply hIso.1
      apply (H.mem_leftBoundaryFinset_iff _).mpr
      refine ⟨i, ?_⟩
      change (rootCoveredRoleIso G).symm ⟨G.left i, _⟩ = v
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext hi
    · intro hx
      obtain ⟨i, hi⟩ := (G.mem_rightBoundaryFinset_iff _).mp hx
      apply hIso.2.1
      apply (H.mem_rightBoundaryFinset_iff _).mpr
      refine ⟨i, ?_⟩
      change (rootCoveredRoleIso G).symm ⟨G.right i, _⟩ = v
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext hi
    · intro e
      constructor
      · intro he
        apply (hIso.2.2 e).1
        apply (rootCoveredRoleIso G).injective
        apply Subtype.ext
        simpa [H, rootIsolatedReducedShape, x] using he
      · intro he
        apply (hIso.2.2 e).2
        apply (rootCoveredRoleIso G).injective
        apply Subtype.ext
        simpa [H, rootIsolatedReducedShape, x] using he
  exact (Finset.mem_sdiff.mp x.2).2 ((G.mem_isolatedMiddleRoles_iff _).mpr hOrig)

theorem root_reduced_roleCovered (G : PaperShape)
    (v : Fin (rootIsolatedReducedShape G).roles) :
    (rootIsolatedReducedShape G).toPartiteShape.RoleCovered v :=
  ((rootIsolatedReducedShape G).toPartiteShape_roleCovered_iff_not_isolated v).mpr
    (root_reduced_not_isolated G v)

def rootCoveredAssignmentEquiv (G : PaperShape) (n : ℕ) :
    PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles) ≃
      PaperAssignment (rootIsolatedReducedShape G) n where
  toFun f := fun v => f ((rootCoveredRoleIso G) v)
  invFun f := fun v => f ((rootCoveredRoleIso G).symm v)
  left_inv f := by funext v; exact congrArg f ((rootCoveredRoleIso G).apply_symm_apply v)
  right_inv f := by funext v; exact congrArg f ((rootCoveredRoleIso G).symm_apply_apply v)

theorem root_reindexed_injective_iff (G : PaperShape) (n : ℕ)
    (f : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles)) :
    Function.Injective (rootCoveredAssignmentEquiv G n f) ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hh : (rootCoveredRoleIso G).symm x = (rootCoveredRoleIso G).symm y := by
      apply h
      simpa [rootCoveredAssignmentEquiv] using hxy
    exact (rootCoveredRoleIso G).symm.injective hh
  · intro h x y hxy
    apply (rootCoveredRoleIso G).injective
    exact h hxy

theorem root_reindexed_noise (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (f : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles)) :
    paperAssignmentNoiseProduct (rootIsolatedReducedShape G) w (rootCoveredAssignmentEquiv G n f) =
      paperCoveredNoiseProduct G w f := by
  dsimp [paperAssignmentNoiseProduct, paperAssignmentEdgeCoordinate, rootIsolatedReducedShape,
    rootCoveredAssignmentEquiv, paperCoveredNoiseProduct]
  simp only [OrderIso.apply_symm_apply]

theorem root_reindexed_entry_iff (G : PaperShape) (n : ℕ)
    (f : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles))
    (row : PaperRow G n) (col : PaperCol G n) :
    ((∀ i, rootCoveredAssignmentEquiv G n f ((rootIsolatedReducedShape G).left i) = row i) ∧
      (∀ j, rootCoveredAssignmentEquiv G n f ((rootIsolatedReducedShape G).right j) = col j)) ↔
      rootCoveredEntryCompatible G f row col := by
  dsimp [rootIsolatedReducedShape, rootCoveredAssignmentEquiv, rootCoveredEntryCompatible]
  simp only [OrderIso.apply_symm_apply]

/-- The reduced sum is exactly an original paper graph matrix of a concrete
finite simple shape, not merely a new matrix definition. -/
theorem root_coveredGlobalMatrix_eq_reducedGraphMatrix (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) :
    rootCoveredGlobalMatrix G n w = paperGraphMatrix (rootIsolatedReducedShape G) n w := by
  classical
  ext row col
  let H := rootIsolatedReducedShape G
  let term : PaperAssignment H n → ℝ := fun x =>
    if (∀ i, x (H.left i) = row i) ∧ (∀ j, x (H.right j) = col j) then
      paperAssignmentNoiseProduct H w x else 0
  have hZero : paperGraphMatrix H n w row col =
      ∑ x : PaperAssignment H n, if Function.Injective x then term x else 0 :=
    sum_paperRealization_eq_sum_assignment_if_injective H n term
  rw [hZero]
  unfold rootCoveredGlobalMatrix
  apply Fintype.sum_equiv (rootCoveredAssignmentEquiv G n)
  intro f
  dsimp only [term, H]
  simp only [root_reindexed_injective_iff, root_reindexed_entry_iff, root_reindexed_noise]

theorem root_global_eq_reduced_smul (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    paperGraphMatrix G n w =
      (((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) : ℝ) •
        paperGraphMatrix (rootIsolatedReducedShape G) n w := by
  rw [root_global_matrix_eq_isolated_smul, root_coveredGlobalMatrix_eq_reducedGraphMatrix]
  have hc : (coveredRoles G.isolatedMiddleRoles).card = G.roles - G.isolatedMiddleRoles.card :=
    root_reduced_roles G
  rw [hc]

#print axioms rootIsolatedReducedShape
#print axioms root_reduced_roles
#print axioms root_reduced_not_isolated
#print axioms root_reduced_roleCovered
#print axioms root_reindexed_injective_iff
#print axioms root_coveredGlobalMatrix_eq_reducedGraphMatrix
#print axioms root_global_eq_reduced_smul
end GraphMatrixReplica
