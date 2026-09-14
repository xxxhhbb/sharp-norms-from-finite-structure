import R6.PaperR16LowerFactorRawReindex

/-!
# Detached factor components: role and occurrence reindexing

This module refines the raw core/detached split to the unique quotient
component of each detached role or occurrence. Equal factor scopes retain
their distinct occurrence indices.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.PaperR16.RawFactorShape

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

private theorem subtype_heq_of_pred_eq {α : Type*} {P Q : α → Prop}
    (hpq : P = Q) (x : {w : α // P w}) (y : {w : α // Q w})
    (hval : x.1 = y.1) : HEq x y := by
  cases hpq
  exact heq_of_eq (Subtype.ext hval)

abbrev DetachedRoleType := {w : W // S.DetachedRole w}
abbrev ComponentRoleType :=
  Σ j : S.DetachedComponent, S.CanonicalDetached j

def componentRoleToDetached (p : S.ComponentRoleType) :
    S.DetachedRoleType :=
  ⟨p.2.1, (S.mem_detachedComponentRoles.mp p.2.2).1⟩

def detachedRoleToComponent (w : S.DetachedRoleType) :
    S.ComponentRoleType :=
  ⟨S.detachedComponentOfRole w.1 w.2,
    ⟨w.1, S.mem_detachedComponentRoles.mpr ⟨w.2, rfl⟩⟩⟩

theorem component_detached_role (w : S.DetachedRoleType) :
    S.componentRoleToDetached (S.detachedRoleToComponent w) = w := by
  apply Subtype.ext
  rfl

theorem detached_component_role (p : S.ComponentRoleType) :
    S.detachedRoleToComponent (S.componentRoleToDetached p) = p := by
  rcases p with ⟨j, w⟩
  have hj : S.detachedComponentOfRole w.1
      (S.mem_detachedComponentRoles.mp w.2).1 = j := by
    apply Subtype.ext
    exact (S.mem_detachedComponentRoles.mp w.2).2
  apply Sigma.ext hj
  apply subtype_heq_of_pred_eq
    (congrArg (fun k : S.DetachedComponent =>
      fun u : W => u ∈ S.detachedComponentRoles k) hj)
  rfl

/-- The detached role subtype is exactly the disjoint union of its
component fibers. -/
def detachedRoleComponentEquiv :
    S.ComponentRoleType ≃ S.DetachedRoleType where
  toFun := S.componentRoleToDetached
  invFun := S.detachedRoleToComponent
  left_inv := S.detached_component_role
  right_inv := S.component_detached_role

abbrev ComponentDetachedAssignment :=
  ∀ j : S.DetachedComponent, ∀ d : S.CanonicalDetached j,
    Fin (S.size d.1)

/-- Exact dependent-Pi reindexing of all detached coordinates by their
canonical quotient component. -/
def detachedAssignmentComponentEquiv :
    S.DetachedRoleAssignment ≃ S.ComponentDetachedAssignment :=
  (Equiv.piCongrLeft'
    (fun d : S.DetachedRoleType => Fin (S.size d.1))
    S.detachedRoleComponentEquiv.symm).trans
      (Equiv.piCurry (fun (j : S.DetachedComponent)
        (d : S.CanonicalDetached j) => Fin (S.size d.1)))

abbrev ComponentOccurrenceType :=
  Σ j : S.DetachedComponent, S.CanonicalDetachedOccurrence j

def componentOccurrenceToDetached (p : S.ComponentOccurrenceType) :
    S.DetachedOccurrenceType :=
  ⟨p.2.1, ⟨p.1, p.2.2⟩⟩

def detachedOccurrenceToComponent (e : S.DetachedOccurrenceType) :
    S.ComponentOccurrenceType :=
  ⟨Classical.choose e.2, ⟨e.1, Classical.choose_spec e.2⟩⟩

theorem detached_occurrence_component_unique {e : E}
    {j k : S.DetachedComponent}
    (hj : S.DetachedOccurrence j e)
    (hk : S.DetachedOccurrence k e) : j = k := by
  obtain ⟨w, hw⟩ := S.scope_nonempty e
  apply Subtype.ext
  calc
    j.1 = S.component w :=
      (S.mem_detachedComponentRoles.mp (hj w hw)).2.symm
    _ = k.1 := (S.mem_detachedComponentRoles.mp (hk w hw)).2

theorem component_detached_occurrence (e : S.DetachedOccurrenceType) :
    S.componentOccurrenceToDetached (S.detachedOccurrenceToComponent e) = e := by
  apply Subtype.ext
  rfl

theorem detached_component_occurrence (p : S.ComponentOccurrenceType) :
    S.detachedOccurrenceToComponent (S.componentOccurrenceToDetached p) = p := by
  rcases p with ⟨j, e⟩
  have hj : Classical.choose (show ∃ k : S.DetachedComponent,
      S.DetachedOccurrence k e.1 from ⟨j, e.2⟩) = j :=
    S.detached_occurrence_component_unique
      (Classical.choose_spec (show ∃ k : S.DetachedComponent,
        S.DetachedOccurrence k e.1 from ⟨j, e.2⟩)) e.2
  apply Sigma.ext hj
  apply subtype_heq_of_pred_eq
    (congrArg (fun k : S.DetachedComponent =>
      fun r : E => S.DetachedOccurrence k r) hj)
  rfl

/-- Every detached occurrence has exactly one component index and retains
its original occurrence label under this equivalence. -/
def detachedOccurrenceComponentEquiv :
    S.ComponentOccurrenceType ≃ S.DetachedOccurrenceType where
  toFun := S.componentOccurrenceToDetached
  invFun := S.detachedOccurrenceToComponent
  left_inv := S.detached_component_occurrence
  right_inv := S.component_detached_occurrence

abbrev FullComponentAssignment :=
  S.CoreAssignment × S.UnusedAssignment × S.ComponentDetachedAssignment

/-- All raw role coordinates, including unused middle roles, are now
explicitly indexed by the exact partition used by the preprocessing theorem. -/
def fullComponentAssignmentEquiv :
    S.RawAssignment ≃ S.FullComponentAssignment :=
  S.assignmentEquiv.trans
    (Equiv.prodCongr (Equiv.refl S.CoreAssignment)
      (Equiv.prodCongr (Equiv.refl S.UnusedAssignment)
        S.detachedAssignmentComponentEquiv))

abbrev FullComponentOccurrence :=
  S.CanonicalCoreOccurrence ⊕ S.ComponentOccurrenceType

/-- Raw factor occurrences are exactly the core occurrences or the
component-indexed detached occurrences. Equal scopes keep different labels. -/
def fullComponentOccurrenceEquiv :
    E ≃ S.FullComponentOccurrence :=
  S.occurrenceEquiv.trans
    (Equiv.sumCongr (Equiv.refl S.CanonicalCoreOccurrence)
      S.detachedOccurrenceComponentEquiv.symm)

/-- Transfer each raw occurrence array to its canonical typed scope. The
array is selected by the *original occurrence index* `e.1`; equal scopes are
never identified. -/
def canonicalSample (ξ : S.RawSample) :
    (S.canonicalPreprocessedShape).Sample := by
  classical
  refine ⟨?_, ?_⟩
  · intro e coords
    exact ξ.array e.1 (fun w =>
      coords ⟨⟨w.1, e.2 w.1 w.2⟩, by
        simp [RawFactorShape.canonicalPreprocessedShape, w.2]⟩)
  · intro j e coords
    exact ξ.array e.1 (fun w =>
      coords ⟨⟨w.1, e.2 w.1 w.2⟩, by
        simp [RawFactorShape.canonicalPreprocessedShape, w.2]⟩)

theorem canonical_core_array_eval (ξ : S.RawSample)
    (x : S.RawAssignment) (e : S.CanonicalCoreOccurrence) :
    (S.canonicalSample ξ).core e
        (fun c => x c.1) =
      ξ.array e.1 (fun w => x w.1) := by
  rfl

theorem canonical_detached_array_eval (ξ : S.RawSample)
    (x : S.RawAssignment) (j : S.DetachedComponent)
    (e : S.CanonicalDetachedOccurrence j) :
    (S.canonicalSample ξ).detached j e
        (fun d => x d.1) =
      ξ.array e.1 (fun w => x w.1) := by
  rfl

/-- The row boundary is retained in the canonical core, even if no factor
reads one of its roles. -/
def canonicalRow (row : S.RawBoundaryTuple S.leftBoundary) :
    (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).leftBoundary := by
  classical
  intro c
  exact row ⟨c.1.1, by
    simpa [RawFactorShape.canonicalPreprocessedShape] using c.2⟩

def canonicalCol (col : S.RawBoundaryTuple S.rightBoundary) :
    (S.canonicalPreprocessedShape).BoundaryTuple
      (S.canonicalPreprocessedShape).rightBoundary := by
  classical
  intro c
  exact col ⟨c.1.1, by
    simpa [RawFactorShape.canonicalPreprocessedShape] using c.2⟩

#print axioms RawFactorShape.detachedRoleComponentEquiv
#print axioms RawFactorShape.detachedAssignmentComponentEquiv
#print axioms RawFactorShape.detachedOccurrenceComponentEquiv
#print axioms RawFactorShape.fullComponentAssignmentEquiv
#print axioms RawFactorShape.fullComponentOccurrenceEquiv
#print axioms RawFactorShape.canonicalSample
#print axioms RawFactorShape.canonical_core_array_eval
#print axioms RawFactorShape.canonical_detached_array_eval
#print axioms RawFactorShape.canonicalRow
#print axioms RawFactorShape.canonicalCol

end GraphMatrixReplica.PaperR16.RawFactorShape
