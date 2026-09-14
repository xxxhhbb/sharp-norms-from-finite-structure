import GraphMatrix.Model.ActualPrimitiveObservations
import GraphMatrix.Model.TypedCoefficient

/-!
Instantiate on C1's genuine retained roles and original primitive fields.
The observed-role cover and separator intersection are proved from C1.
Each occurrence is an original boundary slot or an original fresh-edge port;
equal roles do not identify distinct fields. The coefficient is the finite
assignment sum from C2, with the frozen component weight supplied as data.
Identification with the original graph matrix's mixed flattening remains a
separate reindexing step; no such equality is assumed in these theorems.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model.C1C2

open Classical in
attribute [local instance] propDecidable

open ActualPrimitiveObservations

variable (P : PaperShape) (S : Finset (Fin P.roles))

abbrev Retained := {v : Fin P.roles // v ∈ retainedRoles P.toPartiteShape S}

def rows : Finset (Retained P S) :=
  Finset.univ.filter fun v => v.1 ∈ paperRowObserved P S

def cols : Finset (Retained P S) :=
  Finset.univ.filter fun v => v.1 ∈ paperColObserved P S

def separator : Finset (Retained P S) :=
  Finset.univ.filter fun v => v.1 ∈ S

abbrev RowOccurrence (v : {v : Retained P S // v ∈ rows P S}) :=
  {f : RowField P S // rowFieldRole P S f = v.1.1}

abbrev ColOccurrence (v : {v : Retained P S // v ∈ cols P S}) :=
  {f : ColField P S // colFieldRole P S f = v.1.1}

instance rowOccurrence_nonempty (v : {v : Retained P S // v ∈ rows P S}) :
    Nonempty (RowOccurrence P S v) := by
  have hv : v.1.1 ∈ paperRowObserved P S := (Finset.mem_filter.mp v.2).2
  change v.1.1 ∈ Finset.univ.image (rowFieldRole P S) at hv
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hv
  exact ⟨⟨f, hf⟩⟩

instance colOccurrence_nonempty (v : {v : Retained P S // v ∈ cols P S}) :
    Nonempty (ColOccurrence P S v) := by
  have hv : v.1.1 ∈ paperColObserved P S := (Finset.mem_filter.mp v.2).2
  change v.1.1 ∈ Finset.univ.image (colFieldRole P S) at hv
  obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hv
  exact ⟨⟨f, hf⟩⟩

theorem actual_cover
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) :
    rows P S ∪ cols P S = Finset.univ := by
  have h := (paper_actual_observations P S hNoIsolated hMin).1
  ext v
  have hv : v.1 ∈ paperRowObserved P S ∪ paperColObserved P S := by
    rw [h]
    exact v.2
  simpa [rows, cols] using hv

theorem actual_inter
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S) :
    rows P S ∩ cols P S = separator P S := by
  have h := (paper_actual_observations P S hNoIsolated hMin).2
  ext v
  have hv := congrArg (fun A : Finset (Fin P.roles) => v.1 ∈ A) h
  simpa [rows, cols, separator] using hv

universe u
variable (X : Fin P.roles → Type u)
variable [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] [∀ v, Nonempty (X v)]

abbrev retainedLabel : Retained P S → Type u := fun v => X v.1

abbrev SeparatorAssignment := C2.RoleAssign (retainedLabel P S X) (separator P S)

def coefficient (w : SeparatorAssignment P S X → ℝ) :=
  C2.actualCoefficient (retainedLabel P S X) (RowOccurrence P S) (ColOccurrence P S) w

/-- The separator block entry follows by invoking with C1's proved cover
and intersection, not with externally supplied visibility assumptions. -/
theorem coefficient_entry
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (w : SeparatorAssignment P S X → ℝ)
    (s t : SeparatorAssignment P S X)
    (l : C2.RoleAssign (retainedLabel P S X) (rows P S \ separator P S))
    (r : C2.RoleAssign (retainedLabel P S X) (cols P S \ separator P S)) :
    coefficient P S X w
      (C2.primitiveEmbedding (retainedLabel P S X) (Occ := RowOccurrence P S)
        (C2.sep_subset_row_of_inter_eq (actual_inter P S hNoIsolated hMin)) (l, s))
      (C2.primitiveEmbedding (retainedLabel P S X) (Occ := ColOccurrence P S)
        (C2.sep_subset_col_of_inter_eq (actual_inter P S hNoIsolated hMin)) (r, t)) =
      if s = t then w s else 0 := by
  exact C2.actualCoefficient_entry (retainedLabel P S X)
    (RowOccurrence P S) (ColOccurrence P S) w
    (actual_cover P S hNoIsolated hMin) (actual_inter P S hNoIsolated hMin) s t l r

/-- An inconsistent tuple of original row fields has zero coefficient. -/
theorem coefficient_row_zero
    (w : SeparatorAssignment P S X → ℝ)
    (p : C2.Primitive (retainedLabel P S X) (rows P S) (RowOccurrence P S))
    (hp : ¬ C2.PrimitiveConsistent (retainedLabel P S X) p)
    (q : C2.Primitive (retainedLabel P S X) (cols P S) (ColOccurrence P S)) :
    coefficient P S X w p q = 0 := by
  exact C2.actualCoefficient_row_zero_of_inconsistent (retainedLabel P S X)
    (RowOccurrence P S) (ColOccurrence P S) w p hp q

/-- Proof of the exact norm of the C1-instantiated assignment-sum coefficient.
The inferred equality retains C2's precise finite-index operator-norm instances. -/
def coefficient_norm
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (w : SeparatorAssignment P S X → ℝ) :=
  C2.actualCoefficient_norm_eq_sqrt_product (retainedLabel P S X)
    (RowOccurrence P S) (ColOccurrence P S) w
    (actual_cover P S hNoIsolated hMin) (actual_inter P S hNoIsolated hMin)


end GraphMatrixReplica.Model.C1C2
