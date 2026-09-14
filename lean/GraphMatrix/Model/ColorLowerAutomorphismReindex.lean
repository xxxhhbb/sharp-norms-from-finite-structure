import GraphMatrix.Model.ColorLowerAutomorphism
import GraphMatrix.Model.ColorLowerConcreteTag
import GraphMatrix.RoleColoredPartiteBridge

/-!
# Assignment reindexing by a boundary-fixing shape automorphism

For equal role-class sizes, a boundary-fixing automorphism permutes rolewise
assignments without changing their displayed boundary labels.  Its edge
permutation also preserves the product of the *original unordered ambient
signs* after the role colors are permuted.  This is a finite algebraic core of
the lower-transfer coefficient identification, not that full identity.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Reindex a uniform-size role assignment from source roles to target roles. -/
def PaperShape.R16BoundaryFixingAutomorphism.reindexAssignment
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m : ℕ} (a : PaperRoleColorAssignment G (fun _ => m)) :
    PaperRoleColorAssignment G (fun _ => m) :=
  fun v => a (f.role.symm v)

/-- The reindexing is a genuine finite equivalence, with inverse pullback
along the forward role permutation. -/
def PaperShape.R16BoundaryFixingAutomorphism.assignmentEquiv
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    (m : ℕ) :
    PaperRoleColorAssignment G (fun _ => m) ≃
      PaperRoleColorAssignment G (fun _ => m) where
  toFun := f.reindexAssignment
  invFun := fun a v => a (f.role v)
  left_inv := by
    intro a
    funext v
    change a (f.role.symm (f.role v)) = a v
    rw [f.role.symm_apply_apply]
  right_inv := by
    intro a
    funext v
    change a (f.role (f.role.symm v)) = a v
    rw [f.role.apply_symm_apply]

/-- A fixed boundary role retains its label under the assignment map. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.reindexAssignment_left
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m : ℕ} (a : PaperRoleColorAssignment G (fun _ => m))
    (v : Fin G.roles) (hv : v ∈ G.leftBoundaryFinset) :
    f.reindexAssignment a v = a v := by
  change a (f.role.symm v) = a v
  rw [f.left_fixed_symm v hv]

theorem PaperShape.R16BoundaryFixingAutomorphism.reindexAssignment_right
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m : ℕ} (a : PaperRoleColorAssignment G (fun _ => m))
    (v : Fin G.roles) (hv : v ∈ G.rightBoundaryFinset) :
    f.reindexAssignment a v = a v := by
  change a (f.role.symm v) = a v
  rw [f.right_fixed_symm v hv]

/-- Reindexing preserves and reflects the actual fully-partite boundary
entry-compatibility predicate. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.reindexAssignment_compatible_iff
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m : ℕ} (a : PaperRoleColorAssignment G (fun _ => m))
    (row : PartiteBoundaryRow (G := G.toPartiteShape) (fun _ => m))
    (col : PartiteBoundaryCol (G := G.toPartiteShape) (fun _ => m)) :
    partiteBoundaryEntryCompatible (f.reindexAssignment a) row col ↔
      partiteBoundaryEntryCompatible a row col := by
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro v
      simpa [f.reindexAssignment_left a v.1 v.2] using hl v
    · intro v
      simpa [f.reindexAssignment_right a v.1 v.2] using hr v
  · rintro ⟨hl, hr⟩
    constructor
    · intro v
      simpa [f.reindexAssignment_left a v.1 v.2] using hl v
    · intro v
      simpa [f.reindexAssignment_right a v.1 v.2] using hr v

/-- The original ambient sign monomial attached to one uniform typed
assignment. The same shared noise field is used on every shape edge. -/
def PaperRoleColoring.uniformEdgeProduct
    {G : PaperShape} {m n : ℕ}
    (C : PaperRoleColoring G (fun _ => m) n)
    (w : PaperNoise n) (a : PaperRoleColorAssignment G (fun _ => m)) : ℝ :=
  ∏ e : Fin G.edges,
    paperEdgeSign w
      (C.embedding (G.source e) (a (G.source e)))
      (C.embedding (G.target e) (a (G.target e)))

/-- At one source edge, the role-permuted ambient sign is the target-edge
sign of the reindexed assignment; the reversed endpoint case uses the
paper model's unordered-edge symmetry. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.reindexed_edge_sign
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m n : ℕ} (C : PaperRoleColoring G (fun _ => m) n)
    (w : PaperNoise n) (a : PaperRoleColorAssignment G (fun _ => m))
    (e : Fin G.edges) :
    paperEdgeSign w
      (C.embedding (f.role (G.source e)) (a (G.source e)))
      (C.embedding (f.role (G.target e)) (a (G.target e))) =
    paperEdgeSign w
      (C.embedding (G.source (f.edge e))
        (f.reindexAssignment a (G.source (f.edge e))))
      (C.embedding (G.target (f.edge e))
        (f.reindexAssignment a (G.target (f.edge e)))) := by
  rcases f.endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [← hs, ← ht]
    simp only [reindexAssignment]
    rw [f.role.symm_apply_apply, f.role.symm_apply_apply]
  · calc
      paperEdgeSign w
          (C.embedding (f.role (G.source e)) (a (G.source e)))
          (C.embedding (f.role (G.target e)) (a (G.target e))) =
        paperEdgeSign w
          (C.embedding (f.role (G.target e)) (a (G.target e)))
          (C.embedding (f.role (G.source e)) (a (G.source e))) :=
            paperEdgeSign_symmetric w _ _
      _ = _ := by
        rw [← ht, ← hs]
        simp only [reindexAssignment]
        rw [f.role.symm_apply_apply, f.role.symm_apply_apply]

/-- Reindexing all edges by the graph automorphism preserves the complete
unordered ambient edge product. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.reindexed_edge_product
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m n : ℕ} (C : PaperRoleColoring G (fun _ => m) n)
    (w : PaperNoise n) (a : PaperRoleColorAssignment G (fun _ => m)) :
    (∏ e : Fin G.edges,
      paperEdgeSign w
        (C.embedding (f.role (G.source e)) (a (G.source e)))
        (C.embedding (f.role (G.target e)) (a (G.target e)))) =
      C.uniformEdgeProduct w (f.reindexAssignment a) := by
  let target : Fin G.edges → ℝ := fun e =>
    paperEdgeSign w
      (C.embedding (G.source e) (f.reindexAssignment a (G.source e)))
      (C.embedding (G.target e) (f.reindexAssignment a (G.target e)))
  calc
    (∏ e : Fin G.edges,
      paperEdgeSign w
        (C.embedding (f.role (G.source e)) (a (G.source e)))
        (C.embedding (f.role (G.target e)) (a (G.target e)))) =
        ∏ e : Fin G.edges, target (f.edge e) := by
          apply Finset.prod_congr rfl
          intro e _
          exact f.reindexed_edge_sign C w a e
    _ = ∏ e : Fin G.edges, target e := f.edge.prod_comp target
    _ = C.uniformEdgeProduct w (f.reindexAssignment a) := rfl

/-- Given a typed assignment indexed by target roles, embed it into the
ambient paper model after applying a boundary-fixing role automorphism. -/
def PaperShape.R16BoundaryFixingAutomorphism.coloredRealization
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m n : ℕ} (C : PaperRoleColoring G (fun _ => m) n)
    (a : PaperRoleColorAssignment G (fun _ => m)) :
    PaperRealization G n where
  toFun v := C.embedding (f.role v) (a (f.role v))
  inj' := by
    intro v u h
    have hRole : f.role v = f.role u := by
      by_contra hneq
      exact C.disjoint hneq (a (f.role v)) (a (f.role u)) h
    exact f.role.injective hRole

/-- The concrete realization has exactly the automorphism's role color at
every source role. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.coloredRealization_roleTag
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m n : ℕ} (C : PaperRoleColoring G (fun _ => m) n)
    (a : PaperRoleColorAssignment G (fun _ => m))
    (v : Fin G.roles) :
    C.roleOfLabel? (f.coloredRealization C a v) = some (f.role v) :=
  C.roleOfLabel?_embedding _ _

/-- Because the automorphism fixes each displayed boundary role, its concrete
ambient realization has exactly the same selected boundary rows and columns
as the identity-colored realization of the typed assignment. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.coloredRealization_compatible_iff
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m n : ℕ} (C : PaperRoleColoring G (fun _ => m) n)
    (a : PaperRoleColorAssignment G (fun _ => m))
    (row : PartiteBoundaryRow (G := G.toPartiteShape) (fun _ => m))
    (col : PartiteBoundaryCol (G := G.toPartiteShape) (fun _ => m)) :
    paperEntryCompatible G (f.coloredRealization C a)
        (C.paperRow row) (C.paperCol col) ↔
      partiteBoundaryEntryCompatible a row col := by
  have hleft : ∀ i : Fin G.leftSize,
      f.coloredRealization C a (G.left i) =
        C.globalRealization a (G.left i) := by
    intro i
    have hv : G.left i ∈ G.leftBoundaryFinset :=
      (G.mem_leftBoundaryFinset_iff (G.left i)).2 ⟨i, rfl⟩
    change C.embedding (f.role (G.left i)) (a (f.role (G.left i))) =
      C.embedding (G.left i) (a (G.left i))
    rw [f.left_fixed (G.left i) hv]
  have hright : ∀ j : Fin G.rightSize,
      f.coloredRealization C a (G.right j) =
        C.globalRealization a (G.right j) := by
    intro j
    have hv : G.right j ∈ G.rightBoundaryFinset :=
      (G.mem_rightBoundaryFinset_iff (G.right j)).2 ⟨j, rfl⟩
    change C.embedding (f.role (G.right j)) (a (f.role (G.right j))) =
      C.embedding (G.right j) (a (G.right j))
    rw [f.right_fixed (G.right j) hv]
  have hiff :
      paperEntryCompatible G (f.coloredRealization C a)
        (C.paperRow row) (C.paperCol col) ↔
      paperEntryCompatible G (C.globalRealization a)
        (C.paperRow row) (C.paperCol col) := by
    constructor
    · rintro ⟨hl, hr⟩
      exact ⟨fun i => (hleft i).symm.trans (hl i),
        fun j => (hright j).symm.trans (hr j)⟩
    · rintro ⟨hl, hr⟩
      exact ⟨fun i => (hleft i).trans (hl i),
        fun j => (hright j).trans (hr j)⟩
  exact hiff.trans (C.paperEntryCompatible_globalRealization_iff a row col)

/-- Every edge of this realization has precisely its image-edge color. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.coloredRealization_edgeTag
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m n : ℕ} (C : PaperRoleColoring G (fun _ => m) n)
    (a : PaperRoleColorAssignment G (fun _ => m))
    (e : Fin G.edges) :
    C.targetEdgeTag
      (paperUnorderedPair
        (f.coloredRealization C a (G.source e))
        (f.coloredRealization C a (G.target e))) = some (f.edge e) := by
  rcases f.endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · apply C.targetEdgeTag_of_endpoint_roles
    · simpa [f.coloredRealization_roleTag C a] using congrArg some hs
    · simpa [f.coloredRealization_roleTag C a] using congrArg some ht
  · apply C.targetEdgeTag_of_endpoint_roles_swapped
    · simpa [f.coloredRealization_roleTag C a] using congrArg some hs
    · simpa [f.coloredRealization_roleTag C a] using congrArg some ht

/-- The original global-model edge monomial of the constructed realization
equals the colored typed monomial for the given target-indexed assignment. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.coloredRealization_edgeProduct
    {G : PaperShape} (f : G.R16BoundaryFixingAutomorphism)
    {m n : ℕ} (C : PaperRoleColoring G (fun _ => m) n)
    (w : PaperNoise n) (a : PaperRoleColorAssignment G (fun _ => m)) :
    (∏ e : Fin G.edges,
      paperEdgeSign w
        (f.coloredRealization C a (G.source e))
        (f.coloredRealization C a (G.target e))) =
      C.uniformEdgeProduct w a := by
  let b : PaperRoleColorAssignment G (fun _ => m) := fun v => a (f.role v)
  have hb : f.reindexAssignment b = a := by
    funext v
    change a (f.role (f.role.symm v)) = a v
    rw [f.role.apply_symm_apply]
  change (∏ e : Fin G.edges,
      paperEdgeSign w
        (C.embedding (f.role (G.source e)) (a (f.role (G.source e))))
        (C.embedding (f.role (G.target e)) (a (f.role (G.target e))))) =
      C.uniformEdgeProduct w a
  simpa only [b, hb] using f.reindexed_edge_product C w b


end GraphMatrixReplica
