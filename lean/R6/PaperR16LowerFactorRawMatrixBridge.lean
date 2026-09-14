import R6.PaperR16LowerFactorComponentReindex

/-!
# Raw factor matrix to canonical typed matrix: exact finite interfaces

This module checks boundary agreement, occurrence products, and finite-sum
reindexing without changing the independent occurrence arrays.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.PaperR16.RawFactorShape

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

/-- A boundary set lies inside the core, so testing a raw role tuple against
its labels is equivalent to testing the restricted core tuple. -/
theorem raw_boundary_agreement_iff
    (B : Finset W) (hB : B ⊆ S.boundary)
    (x : S.RawAssignment) (label : S.RawBoundaryTuple B) :
    (∀ w : {w : W // w ∈ B}, x w.1 = label w) ↔
      (∀ c : {c : S.CanonicalCore // c.1 ∈ B},
        x c.1.1 = label ⟨c.1.1, c.2⟩) := by
  constructor
  · intro h c
    exact h ⟨c.1.1, c.2⟩
  · intro h w
    let c : S.CanonicalCore :=
      ⟨w.1, S.core_of_mem_boundary (hB w.2)⟩
    exact h ⟨c, w.2⟩

theorem raw_row_agreement_iff (x : S.RawAssignment)
    (row : S.RawBoundaryTuple S.leftBoundary) :
    (∀ w : {w : W // w ∈ S.leftBoundary}, x w.1 = row w) ↔
      (∀ c : {c : S.CanonicalCore //
          c ∈ (S.canonicalPreprocessedShape).leftBoundary},
        x c.1.1 = S.canonicalRow row c) := by
  classical
  have hSub : S.leftBoundary ⊆ S.boundary := Finset.subset_union_left
  rw [S.raw_boundary_agreement_iff S.leftBoundary hSub x row]
  constructor
  · intro h c
    have hc : c.1.1 ∈ S.leftBoundary := by
      simpa [RawFactorShape.canonicalPreprocessedShape] using c.2
    simpa [canonicalRow] using h ⟨c.1, hc⟩
  · intro h c
    have hc : c.1 ∈ (S.canonicalPreprocessedShape).leftBoundary := by
      simpa [RawFactorShape.canonicalPreprocessedShape] using c.2
    simpa [canonicalRow] using h ⟨c.1, hc⟩

theorem raw_col_agreement_iff (x : S.RawAssignment)
    (col : S.RawBoundaryTuple S.rightBoundary) :
    (∀ w : {w : W // w ∈ S.rightBoundary}, x w.1 = col w) ↔
      (∀ c : {c : S.CanonicalCore //
          c ∈ (S.canonicalPreprocessedShape).rightBoundary},
        x c.1.1 = S.canonicalCol col c) := by
  classical
  have hSub : S.rightBoundary ⊆ S.boundary := Finset.subset_union_right
  rw [S.raw_boundary_agreement_iff S.rightBoundary hSub x col]
  constructor
  · intro h c
    have hc : c.1.1 ∈ S.rightBoundary := by
      simpa [RawFactorShape.canonicalPreprocessedShape] using c.2
    simpa [canonicalCol] using h ⟨c.1, hc⟩
  · intro h c
    have hc : c.1 ∈ (S.canonicalPreprocessedShape).rightBoundary := by
      simpa [RawFactorShape.canonicalPreprocessedShape] using c.2
    simpa [canonicalCol] using h ⟨c.1, hc⟩

noncomputable instance detachedComponentFintype :
    Fintype S.DetachedComponent := by
  classical
  have hSurj : Function.Surjective S.component := by
    intro c
    induction c using Quotient.inductionOn with
    | _ w => exact ⟨w, rfl⟩
  letI : Finite S.Component := Finite.of_surjective S.component hSurj
  change Fintype {c : S.Component //
    ∃ w : W, S.DetachedRole w ∧ S.component w = c}
  exact Fintype.ofFinite _

noncomputable instance canonicalDetachedOccurrenceFintype
    (j : S.DetachedComponent) :
    Fintype (S.CanonicalDetachedOccurrence j) := by
  classical exact Fintype.ofFinite _

/-- The detached occurrence product is exactly the product of its canonical
component products. Each factor is still indexed by its original occurrence
label, even when two labels have equal scopes. -/
theorem raw_detached_product_grouped
    (ξ : S.RawSample) (x : S.RawAssignment) :
    (∏ e : S.DetachedOccurrenceType,
      ξ.array e.1 (fun w => x w.1)) =
    ∏ j : S.DetachedComponent,
      ∏ e : S.CanonicalDetachedOccurrence j,
        ξ.array e.1 (fun w => x w.1) := by
  classical
  calc
    (∏ e : S.DetachedOccurrenceType,
      ξ.array e.1 (fun w => x w.1)) =
      ∏ p : S.ComponentOccurrenceType,
        ξ.array (S.componentOccurrenceToDetached p).1
          (fun w => x w.1) := by
      apply Fintype.prod_equiv S.detachedOccurrenceComponentEquiv.symm
      intro e
      change ξ.array e.1 (fun w => x w.1) =
        ξ.array
          (S.componentOccurrenceToDetached
            (S.detachedOccurrenceToComponent e)).1
          (fun w => x w.1)
      rw [S.component_detached_occurrence]
    _ = ∏ j : S.DetachedComponent,
          ∏ e : S.CanonicalDetachedOccurrence j,
            ξ.array e.1 (fun w => x w.1) := by
      exact Fintype.prod_sigma
        (fun p : S.ComponentOccurrenceType =>
          ξ.array p.2.1 (fun w => x w.1))

noncomputable instance canonicalCoreFintype :
    Fintype S.CanonicalCore := by
  classical exact Fintype.ofFinite _

noncomputable instance canonicalUnusedFintype :
    Fintype S.CanonicalUnused := by
  classical exact Fintype.ofFinite _

noncomputable instance canonicalDetachedRoleFintype
    (j : S.DetachedComponent) :
    Fintype (S.CanonicalDetached j) := by
  classical exact Fintype.ofFinite _

noncomputable instance canonicalCoreDecidableEq :
    DecidableEq S.CanonicalCore := Classical.decEq _

noncomputable instance canonicalUnusedDecidableEq :
    DecidableEq S.CanonicalUnused := Classical.decEq _

noncomputable instance detachedComponentDecidableEq :
    DecidableEq S.DetachedComponent := Classical.decEq _

noncomputable instance canonicalDetachedRoleDecidableEq
    (j : S.DetachedComponent) :
    DecidableEq (S.CanonicalDetached j) := Classical.decEq _

/-- Pointwise equality of the original full occurrence product and the
canonical core product times the component-indexed detached products. -/
theorem rawAmplitude_eq_preprocessed_components
    (ξ : S.RawSample) (x : S.RawAssignment) :
    S.rawAmplitude ξ x =
      (S.canonicalPreprocessedShape).coreAmplitude
          (S.canonicalSample ξ) (fun c => x c.1) *
        ∏ j : S.DetachedComponent,
          (S.canonicalPreprocessedShape).detachedAmplitude
            (S.canonicalSample ξ) j (fun d => x d.1) := by
  classical
  rw [S.rawAmplitude_core_detached_split,
    S.raw_detached_product_grouped]
  congr 1

set_option maxHeartbeats 1000000 in
/-- Every original raw summand is the corresponding canonical core entry
times the independent detached-component occurrence product. -/
theorem rawEntry_eq_preprocessed_components
    (ξ : S.RawSample)
    (row : S.RawBoundaryTuple S.leftBoundary)
    (col : S.RawBoundaryTuple S.rightBoundary)
    (x : S.RawAssignment) :
    (if (∀ w : {w : W // w ∈ S.leftBoundary}, x w.1 = row w) ∧
        (∀ w : {w : W // w ∈ S.rightBoundary}, x w.1 = col w) then
      S.rawAmplitude ξ x else 0) =
      (∏ j : S.DetachedComponent,
        (S.canonicalPreprocessedShape).detachedAmplitude
          (S.canonicalSample ξ) j (fun d => x d.1)) *
      (S.canonicalPreprocessedShape).coreEntry
        (S.canonicalSample ξ) (S.canonicalRow row)
        (S.canonicalCol col) (fun c => x c.1) := by
  classical
  simp only [S.raw_row_agreement_iff x row,
    S.raw_col_agreement_iff x col]
  simp only [GraphMatrixReplica.PaperR16.PreprocessedFactorShape.coreEntry]
  simp only [mul_ite, mul_zero]
  congr 1
  rw [S.rawAmplitude_eq_preprocessed_components]
  exact mul_comm _ _

theorem fullComponentAssignmentEquiv_apply_core
    (x : S.RawAssignment) (c : S.CanonicalCore) :
    (S.fullComponentAssignmentEquiv x).1 c = x c.1 := by
  rfl

theorem fullComponentAssignmentEquiv_apply_unused
    (x : S.RawAssignment) (u : S.CanonicalUnused) :
    (S.fullComponentAssignmentEquiv x).2.1 u = x u.1 := by
  rfl

theorem fullComponentAssignmentEquiv_apply_detached
    (x : S.RawAssignment) (j : S.DetachedComponent)
    (d : S.CanonicalDetached j) :
    (S.fullComponentAssignmentEquiv x).2.2 j d = x d.1 := by
  rfl

set_option maxHeartbeats 1000000 in
/-- The original unpartitioned finite factor matrix is exactly the full
matrix of the canonically extracted preprocessing shape. -/
theorem rawMatrix_eq_canonicalFullMatrix (ξ : S.RawSample)
    (row : S.RawBoundaryTuple S.leftBoundary)
    (col : S.RawBoundaryTuple S.rightBoundary) :
    S.rawMatrix ξ row col =
      (S.canonicalPreprocessedShape).fullMatrix
        (S.canonicalSample ξ) (S.canonicalRow row) (S.canonicalCol col) := by
  classical
  unfold rawMatrix GraphMatrixReplica.PaperR16.PreprocessedFactorShape.fullMatrix
  calc
    (∑ x : S.RawAssignment,
      if (∀ w : {w : W // w ∈ S.leftBoundary}, x w.1 = row w) ∧
          (∀ w : {w : W // w ∈ S.rightBoundary}, x w.1 = col w) then
        S.rawAmplitude ξ x else 0) =
      ∑ x : S.RawAssignment,
        (∏ j : S.DetachedComponent,
          (S.canonicalPreprocessedShape).detachedAmplitude
            (S.canonicalSample ξ) j (fun d => x d.1)) *
        (S.canonicalPreprocessedShape).coreEntry
          (S.canonicalSample ξ) (S.canonicalRow row)
          (S.canonicalCol col) (fun c => x c.1) := by
        apply Finset.sum_congr rfl
        intro x _
        exact S.rawEntry_eq_preprocessed_components ξ row col x
    _ = ∑ t : S.FullComponentAssignment,
          (∏ j : S.DetachedComponent,
            (S.canonicalPreprocessedShape).detachedAmplitude
              (S.canonicalSample ξ) j (t.2.2 j)) *
          (S.canonicalPreprocessedShape).coreEntry
            (S.canonicalSample ξ) (S.canonicalRow row)
            (S.canonicalCol col) t.1 := by
        apply Fintype.sum_equiv S.fullComponentAssignmentEquiv
        intro x
        rfl
    _ = ∑ core : (S.canonicalPreprocessedShape).CoreTuple,
          ∑ _unused : (S.canonicalPreprocessedShape).UnusedTuple,
          ∑ detached : (S.canonicalPreprocessedShape).AllDetachedTuple,
            (∏ j : S.DetachedComponent,
              (S.canonicalPreprocessedShape).detachedAmplitude
                (S.canonicalSample ξ) j (detached j)) *
            (S.canonicalPreprocessedShape).coreEntry
              (S.canonicalSample ξ) (S.canonicalRow row)
              (S.canonicalCol col) core := by
        simp only [Fintype.sum_prod_type]
        rfl

#print axioms RawFactorShape.raw_boundary_agreement_iff
#print axioms RawFactorShape.raw_row_agreement_iff
#print axioms RawFactorShape.raw_col_agreement_iff
#print axioms RawFactorShape.raw_detached_product_grouped
#print axioms RawFactorShape.rawAmplitude_eq_preprocessed_components
#print axioms RawFactorShape.rawEntry_eq_preprocessed_components
#print axioms RawFactorShape.fullComponentAssignmentEquiv_apply_detached
#print axioms RawFactorShape.rawMatrix_eq_canonicalFullMatrix

end GraphMatrixReplica.PaperR16.RawFactorShape
