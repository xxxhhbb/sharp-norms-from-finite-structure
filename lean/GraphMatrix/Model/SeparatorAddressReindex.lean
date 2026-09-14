import GraphMatrix.Model.SeparatorActualCoefficientBridge
import GraphMatrix.PartialNCKStageReindexIsometry

/-!
The actual ordered boundary slots and fresh-edge pairs are equivalent to C2's
role-indexed primitive fields. Repeated fields retain their individual IDs.
This proves address reindexing of the retained-assignment sum. Identification
of that sum with the original matrix after active-component contraction is a
separate obligation.
-/

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model.C1C2

open ActualPrimitiveObservations
open Classical in
attribute [local instance] propDecidable

universe u
variable (P : PaperShape) (S : Finset (Fin P.roles))
variable (X : Fin P.roles → Type u)

def rowAddressFieldEquiv : RowAddress P S X ≃
    ((f : RowField P S) → X (rowFieldRole P S f)) where
  toFun := readRowField P S
  invFun a := ⟨fun i => a (.inl i),
    fun e => ⟨a (.inr (e, false)), a (.inr (e, true))⟩⟩
  left_inv a := by rfl
  right_inv a := by
    funext f
    rcases f with i | ⟨e, b⟩
    · rfl
    · cases b <;> rfl

def colAddressFieldEquiv : ColAddress P S X ≃
    ((f : ColField P S) → X (colFieldRole P S f)) where
  toFun := readColField P S
  invFun a := ⟨fun i => a (.inl i),
    fun e => ⟨a (.inr (e, false)), a (.inr (e, true))⟩⟩
  left_inv a := by rfl
  right_inv a := by
    funext f
    rcases f with i | ⟨e, b⟩
    · rfl
    · cases b <;> rfl

def rowFieldIndex (f : RowField P S) : {v : Retained P S // v ∈ rows P S} := by
  have hf : rowFieldRole P S f ∈ paperRowObserved P S :=
    Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
  have hr : rowFieldRole P S f ∈ retainedRoles P.toPartiteShape S := by
    apply rowObserved_subset_retainedRoles P.toPartiteShape S
    rw [paperRowObserved_eq P S] at hf
    exact hf
  exact ⟨⟨rowFieldRole P S f, hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩

def colFieldIndex (f : ColField P S) : {v : Retained P S // v ∈ cols P S} := by
  have hf : colFieldRole P S f ∈ paperColObserved P S :=
    Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
  have hr : colFieldRole P S f ∈ retainedRoles P.toPartiteShape S := by
    apply colObserved_subset_retainedRoles P.toPartiteShape S
    rw [paperColObserved_eq P S] at hf
    exact hf
  exact ⟨⟨colFieldRole P S f, hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩

def rowFieldPrimitiveEquiv :
    ((f : RowField P S) → X (rowFieldRole P S f)) ≃
      C2.Primitive (retainedLabel P S X) (rows P S) (RowOccurrence P S) where
  toFun a v f := cast (congrArg X f.2) (a f.1)
  invFun p f := p (rowFieldIndex P S f) ⟨f, rfl⟩
  left_inv a := by rfl
  right_inv p := by
    funext v f
    rcases v with ⟨⟨v, hv⟩, hrow⟩
    rcases f with ⟨f, hf⟩
    dsimp [RowOccurrence] at hf
    cases hf
    rfl

def colFieldPrimitiveEquiv :
    ((f : ColField P S) → X (colFieldRole P S f)) ≃
      C2.Primitive (retainedLabel P S X) (cols P S) (ColOccurrence P S) where
  toFun a v f := cast (congrArg X f.2) (a f.1)
  invFun p f := p (colFieldIndex P S f) ⟨f, rfl⟩
  left_inv a := by rfl
  right_inv p := by
    funext v f
    rcases v with ⟨⟨v, hv⟩, hcol⟩
    rcases f with ⟨f, hf⟩
    dsimp [ColOccurrence] at hf
    cases hf
    rfl

def rowAddressPrimitiveEquiv : RowAddress P S X ≃
    C2.Primitive (retainedLabel P S X) (rows P S) (RowOccurrence P S) :=
  (rowAddressFieldEquiv P S X).trans (rowFieldPrimitiveEquiv P S X)

def colAddressPrimitiveEquiv : ColAddress P S X ≃
    C2.Primitive (retainedLabel P S X) (cols P S) (ColOccurrence P S) :=
  (colAddressFieldEquiv P S X).trans (colFieldPrimitiveEquiv P S X)

def retainedRowAddress (a : C2.FullAssign (retainedLabel P S X)) : RowAddress P S X :=
  (rowAddressFieldEquiv P S X).symm (fun f => a (rowFieldIndex P S f).1)

def retainedColAddress (a : C2.FullAssign (retainedLabel P S X)) : ColAddress P S X :=
  (colAddressFieldEquiv P S X).symm (fun f => a (colFieldIndex P S f).1)

theorem retainedRowAddress_primitive (a : C2.FullAssign (retainedLabel P S X)) :
    rowAddressPrimitiveEquiv P S X (retainedRowAddress P S X a) =
      C2.fullPrimitive (retainedLabel P S X) (Occ := RowOccurrence P S) a := by
  funext v f
  rcases v with ⟨⟨v, hv⟩, hrow⟩
  rcases f with ⟨f, hf⟩
  dsimp [RowOccurrence] at hf
  cases hf
  change (rowAddressFieldEquiv P S X)
    ((rowAddressFieldEquiv P S X).symm (fun f => a (rowFieldIndex P S f).1)) f = _
  exact congrFun ((rowAddressFieldEquiv P S X).apply_symm_apply _) f

theorem retainedColAddress_primitive (a : C2.FullAssign (retainedLabel P S X)) :
    colAddressPrimitiveEquiv P S X (retainedColAddress P S X a) =
      C2.fullPrimitive (retainedLabel P S X) (Occ := ColOccurrence P S) a := by
  funext v f
  rcases v with ⟨⟨v, hv⟩, hcol⟩
  rcases f with ⟨f, hf⟩
  dsimp [ColOccurrence] at hf
  cases hf
  change (colAddressFieldEquiv P S X)
    ((colAddressFieldEquiv P S X).symm (fun f => a (colFieldIndex P S f).1)) f = _
  exact congrFun ((colAddressFieldEquiv P S X).apply_symm_apply _) f

variable [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] [∀ v, Nonempty (X v)]

def retainedAddressCoefficient (w : SeparatorAssignment P S X → ℝ)
    (p : RowAddress P S X) (q : ColAddress P S X) : ℝ :=
  ∑ a : C2.FullAssign (retainedLabel P S X),
    if retainedRowAddress P S X a = p ∧ retainedColAddress P S X a = q then
      w (fun v => a v.1) else 0

theorem retainedAddressCoefficient_eq (w : SeparatorAssignment P S X → ℝ)
    (p : RowAddress P S X) (q : ColAddress P S X) :
    retainedAddressCoefficient P S X w p q = coefficient P S X w
      (rowAddressPrimitiveEquiv P S X p) (colAddressPrimitiveEquiv P S X q) := by
  unfold retainedAddressCoefficient coefficient C2.actualCoefficient
  apply Finset.sum_congr rfl
  intro a _
  have hr : retainedRowAddress P S X a = p ↔
      C2.fullPrimitive (retainedLabel P S X) (Occ := RowOccurrence P S) a =
        rowAddressPrimitiveEquiv P S X p := by
    rw [← retainedRowAddress_primitive]
    exact (rowAddressPrimitiveEquiv P S X).injective.eq_iff.symm
  have hc : retainedColAddress P S X a = q ↔
      C2.fullPrimitive (retainedLabel P S X) (Occ := ColOccurrence P S) a =
        colAddressPrimitiveEquiv P S X q := by
    rw [← retainedColAddress_primitive]
    exact (colAddressPrimitiveEquiv P S X).injective.eq_iff.symm
  simp only [hr, hc]
  split
  · apply congrArg w
    funext v
    rfl
  · rfl

theorem retainedAddressCoefficient_reindex (w : SeparatorAssignment P S X → ℝ) :
    (retainedAddressCoefficient P S X w : Matrix (RowAddress P S X) (ColAddress P S X) ℝ) =
      Matrix.reindex (rowAddressPrimitiveEquiv P S X).symm
        (colAddressPrimitiveEquiv P S X).symm (coefficient P S X w) := by
  funext p q
  exact retainedAddressCoefficient_eq P S X w p q

local instance rowPrimitive_fintype :
    Fintype (C2.Primitive (retainedLabel P S X) (rows P S) (RowOccurrence P S)) := by
  classical
  unfold C2.Primitive
  infer_instance

local instance colPrimitive_fintype :
    Fintype (C2.Primitive (retainedLabel P S X) (cols P S) (ColOccurrence P S)) := by
  classical
  unfold C2.Primitive
  infer_instance

theorem retainedAddressCoefficient_norm (w : SeparatorAssignment P S X → ℝ) :
    @norm (Matrix (RowAddress P S X) (ColAddress P S X) ℝ)
      Matrix.instL2OpNormedAddCommGroup.toNorm (retainedAddressCoefficient P S X w) =
    @norm (Matrix
      (C2.Primitive (retainedLabel P S X) (rows P S) (RowOccurrence P S))
      (C2.Primitive (retainedLabel P S X) (cols P S) (ColOccurrence P S)) ℝ)
      Matrix.instL2OpNormedAddCommGroup.toNorm (coefficient P S X w) := by
  rw [retainedAddressCoefficient_reindex]
  exact paper_l2_opNorm_reindex (rowAddressPrimitiveEquiv P S X).symm
    (colAddressPrimitiveEquiv P S X).symm (coefficient P S X w)


end GraphMatrixReplica.Model.C1C2
