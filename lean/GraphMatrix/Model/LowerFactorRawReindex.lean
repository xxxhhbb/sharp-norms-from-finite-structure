import GraphMatrix.Model.LowerFactorCanonical

/-!
# Raw independent-factor Cartesian matrix and canonical assignment reindex

The raw scope list is occurrence indexed. Two equal scopes still select two
different sample arrays. This module compares its unpartitioned assignment
space with the core / unused / detached role spaces extracted canonically.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.Model.RawFactorShape

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

abbrev RawAssignment := ∀ w : W, Fin (S.size w)
abbrev CoreAssignment :=
  ∀ c : S.CanonicalCore, Fin (S.size c.1)
abbrev UnusedAssignment :=
  ∀ u : S.CanonicalUnused, Fin (S.size u.1)
abbrev DetachedRoleAssignment :=
  ∀ d : {w : W // S.DetachedRole w}, Fin (S.size d.1)

abbrev CanonicalAssignment :=
  S.CoreAssignment × S.UnusedAssignment × S.DetachedRoleAssignment

/-- Restrict a raw tuple to the three canonical role classes. -/
def restrictAssignment (x : S.RawAssignment) : S.CanonicalAssignment :=
  ⟨fun c => x c.1, fun u => x u.1, fun d => x d.1⟩

/-- Assemble a full tuple by the exhaustive, disjoint canonical role
classification. The last branch is necessarily a detached role. -/
def assembleAssignment (t : S.CanonicalAssignment) : S.RawAssignment := by
  classical
  intro w
  by_cases hc : S.CoreRole w
  · exact t.1 ⟨w, hc⟩
  by_cases hu : S.UnusedMiddleRole w
  · exact t.2.1 ⟨w, hu⟩
  have hd : S.DetachedRole w := by
    rcases S.role_partition w with hc' | hu' | hd'
    · exact False.elim (hc hc')
    · exact False.elim (hu hu')
    · exact hd'
  exact t.2.2 ⟨w, hd⟩

theorem assemble_restrict (x : S.RawAssignment) :
    S.assembleAssignment (S.restrictAssignment x) = x := by
  funext w
  classical
  unfold assembleAssignment restrictAssignment
  split_ifs <;> rfl

theorem restrict_assemble (t : S.CanonicalAssignment) :
    S.restrictAssignment (S.assembleAssignment t) = t := by
  classical
  rcases t with ⟨c, u, d⟩
  apply Prod.ext
  · funext w
    simp [restrictAssignment, assembleAssignment, w.2]
  · apply Prod.ext
    · funext w
      have hc : ¬ S.CoreRole w.1 := by
        intro hcore
        exact S.core_not_unused hcore w.2
      simp [restrictAssignment, assembleAssignment, hc, w.2]
    · funext w
      have hc : ¬ S.CoreRole w.1 := w.2.2
      have hu : ¬ S.UnusedMiddleRole w.1 :=
        fun hUnused => S.unused_not_detached hUnused w.2
      simp [restrictAssignment, assembleAssignment, hc, hu]

/-- Explicit bijection of the raw Cartesian assignment space with the
canonically extracted three-block role assignment space. Grouping detached
roles by quotient components is a further reindexing obligation. -/
def assignmentEquiv : S.RawAssignment ≃ S.CanonicalAssignment where
  toFun := S.restrictAssignment
  invFun := S.assembleAssignment
  left_inv := S.assemble_restrict
  right_inv := S.restrict_assemble

noncomputable instance canonicalAssignmentFintype :
    Fintype S.CanonicalAssignment :=
  Fintype.ofEquiv S.RawAssignment S.assignmentEquiv

/-- The detached occurrence type keeps each raw occurrence index. -/
abbrev DetachedOccurrenceType :=
  {e : E // ∃ j : S.DetachedComponent, S.DetachedOccurrence j e}

theorem not_coreOccurrence_iff_detached (e : E) :
    ¬ S.CoreOccurrence e ↔
      ∃ j : S.DetachedComponent, S.DetachedOccurrence j e := by
  constructor
  · intro hn
    rcases S.occurrence_core_or_detached e with hc | ⟨j, hj, _⟩
    · exact False.elim (hn hc)
    · exact ⟨j, hj⟩
  · intro ⟨j, hd⟩ hc
    exact S.core_occurrence_not_detached e hc j hd

abbrev OccurrencePiece :=
  S.CanonicalCoreOccurrence ⊕ S.DetachedOccurrenceType

def restrictOccurrence (e : E) : S.OccurrencePiece := by
  classical
  by_cases hc : S.CoreOccurrence e
  · exact Sum.inl ⟨e, hc⟩
  · exact Sum.inr ⟨e, (S.not_coreOccurrence_iff_detached e).mp hc⟩

def assembleOccurrence (p : S.OccurrencePiece) : E :=
  match p with
  | Sum.inl e => e.1
  | Sum.inr e => e.1

theorem assemble_restrictOccurrence (e : E) :
    S.assembleOccurrence (S.restrictOccurrence e) = e := by
  classical
  unfold restrictOccurrence
  split_ifs <;> rfl

theorem restrict_assembleOccurrence (p : S.OccurrencePiece) :
    S.restrictOccurrence (S.assembleOccurrence p) = p := by
  classical
  cases p with
  | inl e =>
      simp [restrictOccurrence, assembleOccurrence, e.2]
  | inr e =>
      have hn : ¬ S.CoreOccurrence e.1 :=
        (S.not_coreOccurrence_iff_detached e.1).mpr e.2
      simp [restrictOccurrence, assembleOccurrence, hn]

/-- Explicit core/detached occurrence bijection. The canonical module
separately proves each detached occurrence has a unique component. -/
def occurrenceEquiv : E ≃ S.OccurrencePiece where
  toFun := S.restrictOccurrence
  invFun := S.assembleOccurrence
  left_inv := S.assemble_restrictOccurrence
  right_inv := S.restrict_assembleOccurrence

noncomputable instance coreOccurrenceFintype :
    Fintype S.CanonicalCoreOccurrence := by
  classical exact Fintype.ofFinite _

noncomputable instance detachedOccurrenceFintype :
    Fintype S.DetachedOccurrenceType := by
  classical exact Fintype.ofFinite _

/-- Original row and column labels are restrictions of raw role tuples. -/
abbrev RawBoundaryTuple (B : Finset W) :=
  ∀ w : {w : W // w ∈ B}, Fin (S.size w.1)

/-- Each occurrence owns a separate scope-indexed array. -/
structure RawSample where
  array : ∀ e : E,
    (∀ w : {w : W // w ∈ S.scope e}, Fin (S.size w.1)) → ℝ

def rawAmplitude (ξ : S.RawSample) (x : S.RawAssignment) : ℝ :=
  ∏ e : E, ξ.array e (fun w => x w.1)

/-- The occurrence product separates into the two canonical occurrence
classes, without identifying arrays at equal scopes. The detached class is
not yet split into connected components. -/
theorem rawAmplitude_core_detached_split
    (ξ : S.RawSample) (x : S.RawAssignment) :
    S.rawAmplitude ξ x =
      (∏ e : S.CanonicalCoreOccurrence,
        ξ.array e.1 (fun w => x w.1)) *
      (∏ e : S.DetachedOccurrenceType,
        ξ.array e.1 (fun w => x w.1)) := by
  classical
  unfold rawAmplitude
  calc
    (∏ e : E, ξ.array e (fun w => x w.1)) =
      ∏ p : S.OccurrencePiece,
        ξ.array (S.assembleOccurrence p) (fun w => x w.1) := by
      apply Fintype.prod_equiv S.occurrenceEquiv
      intro e
      change ξ.array e (fun w => x w.1) =
        ξ.array (S.assembleOccurrence (S.restrictOccurrence e))
          (fun w => x w.1)
      rw [S.assemble_restrictOccurrence]
    _ = (∏ e : S.CanonicalCoreOccurrence,
          ξ.array e.1 (fun w => x w.1)) *
        (∏ e : S.DetachedOccurrenceType,
          ξ.array e.1 (fun w => x w.1)) := by
      simp [OccurrencePiece, assembleOccurrence]

/-- Exact typed Cartesian-sum entry of the paper's original factor matrix. -/
def rawMatrix (ξ : S.RawSample)
    (row : S.RawBoundaryTuple S.leftBoundary)
    (col : S.RawBoundaryTuple S.rightBoundary) : ℝ :=
  ∑ x : S.RawAssignment,
    if (∀ w : {w : W // w ∈ S.leftBoundary}, x w.1 = row w) ∧
        (∀ w : {w : W // w ∈ S.rightBoundary}, x w.1 = col w) then
      S.rawAmplitude ξ x
    else 0

/-- Reindex the genuine raw matrix entry by the proved role-assignment
bijection. This retains the complete original occurrence product. Separating
that product and grouping detached assignments by components remain the next
algebraic steps. -/
theorem rawMatrix_reindex_assignment (ξ : S.RawSample)
    (row : S.RawBoundaryTuple S.leftBoundary)
    (col : S.RawBoundaryTuple S.rightBoundary) :
    S.rawMatrix ξ row col =
      ∑ t : S.CanonicalAssignment,
        if (∀ w : {w : W // w ∈ S.leftBoundary},
              S.assembleAssignment t w.1 = row w) ∧
            (∀ w : {w : W // w ∈ S.rightBoundary},
              S.assembleAssignment t w.1 = col w) then
          S.rawAmplitude ξ (S.assembleAssignment t)
        else 0 := by
  classical
  unfold rawMatrix
  apply Fintype.sum_equiv S.assignmentEquiv
  intro x
  simp [assignmentEquiv, S.assemble_restrict]


end GraphMatrixReplica.Model.RawFactorShape
