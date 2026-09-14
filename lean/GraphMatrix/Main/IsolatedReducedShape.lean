import GraphMatrix.Main.GlobalIsolatedFactorization
import Mathlib.Data.Finset.Sort

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
namespace GraphMatrixReplica
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def mainCoveredRoleIso (G : PaperShape) :
    Fin (coveredRoles G.isolatedMiddleRoles).card ≃o (coveredRoles G.isolatedMiddleRoles) :=
  (coveredRoles G.isolatedMiddleRoles).orderIsoOfFin rfl

/-- Delete exactly the isolated middle roles, retaining ordered boundaries
and the complete original edge occurrence list. Increasing reindexing preserves
the simple graph's stored endpoint ordering. -/
def mainIsolatedReducedShape (G : PaperShape) : PaperShape where
  roles := (coveredRoles G.isolatedMiddleRoles).card
  edges := G.edges
  source e := (mainCoveredRoleIso G).symm ⟨G.source e, G.source_mem_coveredRoles_isolatedMiddle e⟩
  target e := (mainCoveredRoleIso G).symm ⟨G.target e, G.target_mem_coveredRoles_isolatedMiddle e⟩
  edge_order e := (mainCoveredRoleIso G).symm.strictMono (G.edge_order e)
  edge_injective := by
    intro e f h
    apply G.edge_injective
    apply Prod.ext
    · have hh := congrArg (fun z => ((mainCoveredRoleIso G) z.1).1) h
      simpa using hh
    · have hh := congrArg (fun z => ((mainCoveredRoleIso G) z.2).1) h
      simpa using hh
  leftSize := G.leftSize
  rightSize := G.rightSize
  left := ⟨fun i => (mainCoveredRoleIso G).symm ⟨G.left i, main_left_mem_covered G i⟩, by
    intro i j h
    apply G.left.injective
    have hh := congrArg (fun z => ((mainCoveredRoleIso G) z).1) h
    simpa using hh⟩
  right := ⟨fun i => (mainCoveredRoleIso G).symm ⟨G.right i, main_right_mem_covered G i⟩, by
    intro i j h
    apply G.right.injective
    have hh := congrArg (fun z => ((mainCoveredRoleIso G) z).1) h
    simpa using hh⟩

theorem main_reduced_roles (G : PaperShape) :
    (mainIsolatedReducedShape G).roles = G.roles - G.isolatedMiddleRoles.card := by
  change (Finset.univ \ G.isolatedMiddleRoles).card = _
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- Every surviving role really occurs in an edge or a boundary. -/
theorem main_reduced_not_isolated (G : PaperShape)
    (v : Fin (mainIsolatedReducedShape G).roles) :
    ¬ (mainIsolatedReducedShape G).IsolatedMiddleRole v := by
  let H := mainIsolatedReducedShape G
  let x := (mainCoveredRoleIso G) v
  intro hIso
  have hOrig : G.IsolatedMiddleRole x.1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro hx
      obtain ⟨i, hi⟩ := (G.mem_leftBoundaryFinset_iff _).mp hx
      apply hIso.1
      apply (H.mem_leftBoundaryFinset_iff _).mpr
      refine ⟨i, ?_⟩
      change (mainCoveredRoleIso G).symm ⟨G.left i, _⟩ = v
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext hi
    · intro hx
      obtain ⟨i, hi⟩ := (G.mem_rightBoundaryFinset_iff _).mp hx
      apply hIso.2.1
      apply (H.mem_rightBoundaryFinset_iff _).mpr
      refine ⟨i, ?_⟩
      change (mainCoveredRoleIso G).symm ⟨G.right i, _⟩ = v
      rw [OrderIso.symm_apply_eq]
      exact Subtype.ext hi
    · intro e
      constructor
      · intro he
        apply (hIso.2.2 e).1
        apply (mainCoveredRoleIso G).injective
        apply Subtype.ext
        simpa [H, mainIsolatedReducedShape, x] using he
      · intro he
        apply (hIso.2.2 e).2
        apply (mainCoveredRoleIso G).injective
        apply Subtype.ext
        simpa [H, mainIsolatedReducedShape, x] using he
  exact (Finset.mem_sdiff.mp x.2).2 ((G.mem_isolatedMiddleRoles_iff _).mpr hOrig)

theorem main_reduced_roleCovered (G : PaperShape)
    (v : Fin (mainIsolatedReducedShape G).roles) :
    (mainIsolatedReducedShape G).toPartiteShape.RoleCovered v :=
  ((mainIsolatedReducedShape G).toPartiteShape_roleCovered_iff_not_isolated v).mpr
    (main_reduced_not_isolated G v)

def mainCoveredAssignmentEquiv (G : PaperShape) (n : ℕ) :
    PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles) ≃
      PaperAssignment (mainIsolatedReducedShape G) n where
  toFun f := fun v => f ((mainCoveredRoleIso G) v)
  invFun f := fun v => f ((mainCoveredRoleIso G).symm v)
  left_inv f := by funext v; exact congrArg f ((mainCoveredRoleIso G).apply_symm_apply v)
  right_inv f := by funext v; exact congrArg f ((mainCoveredRoleIso G).symm_apply_apply v)

theorem main_reindexed_injective_iff (G : PaperShape) (n : ℕ)
    (f : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles)) :
    Function.Injective (mainCoveredAssignmentEquiv G n f) ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hh : (mainCoveredRoleIso G).symm x = (mainCoveredRoleIso G).symm y := by
      apply h
      simpa [mainCoveredAssignmentEquiv] using hxy
    exact (mainCoveredRoleIso G).symm.injective hh
  · intro h x y hxy
    apply (mainCoveredRoleIso G).injective
    exact h hxy

theorem main_reindexed_noise (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (f : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles)) :
    paperAssignmentNoiseProduct (mainIsolatedReducedShape G) w (mainCoveredAssignmentEquiv G n f) =
      paperCoveredNoiseProduct G w f := by
  dsimp [paperAssignmentNoiseProduct, paperAssignmentEdgeCoordinate, mainIsolatedReducedShape,
    mainCoveredAssignmentEquiv, paperCoveredNoiseProduct]
  simp only [OrderIso.apply_symm_apply]

theorem main_reindexed_entry_iff (G : PaperShape) (n : ℕ)
    (f : PaperVisibleTuple n (coveredRoles G.isolatedMiddleRoles))
    (row : PaperRow G n) (col : PaperCol G n) :
    ((∀ i, mainCoveredAssignmentEquiv G n f ((mainIsolatedReducedShape G).left i) = row i) ∧
      (∀ j, mainCoveredAssignmentEquiv G n f ((mainIsolatedReducedShape G).right j) = col j)) ↔
      mainCoveredEntryCompatible G f row col := by
  dsimp [mainIsolatedReducedShape, mainCoveredAssignmentEquiv, mainCoveredEntryCompatible]
  simp only [OrderIso.apply_symm_apply]

/-- The reduced sum is exactly an original paper graph matrix of a concrete
finite simple shape, not merely a new matrix definition. -/
theorem main_coveredGlobalMatrix_eq_reducedGraphMatrix (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) :
    mainCoveredGlobalMatrix G n w = paperGraphMatrix (mainIsolatedReducedShape G) n w := by
  classical
  ext row col
  let H := mainIsolatedReducedShape G
  let term : PaperAssignment H n → ℝ := fun x =>
    if (∀ i, x (H.left i) = row i) ∧ (∀ j, x (H.right j) = col j) then
      paperAssignmentNoiseProduct H w x else 0
  have hZero : paperGraphMatrix H n w row col =
      ∑ x : PaperAssignment H n, if Function.Injective x then term x else 0 :=
    sum_paperRealization_eq_sum_assignment_if_injective H n term
  rw [hZero]
  unfold mainCoveredGlobalMatrix
  apply Fintype.sum_equiv (mainCoveredAssignmentEquiv G n)
  intro f
  dsimp only [term, H]
  simp only [main_reindexed_injective_iff, main_reindexed_entry_iff, main_reindexed_noise]

theorem main_global_eq_reduced_smul (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    paperGraphMatrix G n w =
      (((n - (G.roles - G.isolatedMiddleRoles.card)).descFactorial G.isolatedMiddleRoles.card : ℕ) : ℝ) •
        paperGraphMatrix (mainIsolatedReducedShape G) n w := by
  rw [main_global_matrix_eq_isolated_smul, main_coveredGlobalMatrix_eq_reducedGraphMatrix]
  have hc : (coveredRoles G.isolatedMiddleRoles).card = G.roles - G.isolatedMiddleRoles.card :=
    main_reduced_roles G
  rw [hc]

end GraphMatrixReplica
