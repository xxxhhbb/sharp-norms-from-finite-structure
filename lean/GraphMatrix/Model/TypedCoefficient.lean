import Mathlib
import GraphMatrix.Model.SeparatorCoordinates
import GraphMatrix.Model.LowerStackingMixed

/-!
# typed primitive consistency and exact separator coefficient

This module formalizes the deterministic/combinatorial core of after the
active-component arrays have been frozen and after has supplied the actual
row/column observed-role sets `row`, `col` with

* `row ∪ col = univ`, and
* `row ∩ col = sep`.

Repeated primitive occurrences are *not* identified.  They are represented by
role-indexed finite occurrence families `RowOcc` and `ColOcc`; consistency says
that all occurrences reading the same role carry the same typed label.

The actual coefficient is defined as a finite sum over complete retained role
assignments.  The separator-block entry formula and zero support are proved
from this sum; they are not hypotheses.

What is deliberately not claimed here: the current package does not contain
a Lean definition of the paper's fully typed independent-edge-array graph
matrix, so the graph-specific identification of its mixed flattening with this
`actualCoefficient` is left as an explicit norm-reindexing premise in the final
bridge theorem.  No axiom, `sorry`, or `admit` is used below.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model.C2

open Classical in
attribute [local instance] propDecidable

variable {Role : Type*} [Fintype Role] [DecidableEq Role]
variable (Label : Role → Type*)
variable [∀ v, Fintype (Label v)]
variable [∀ v, DecidableEq (Label v)]
variable [∀ v, Nonempty (Label v)]

/-- Typed assignment on a finite set of roles. -/
abbrev RoleAssign (A : Finset Role) :=
  ∀ v : {v // v ∈ A}, Label v.1

/-- Complete typed assignment on all retained roles. -/
abbrev FullAssign := ∀ v : Role, Label v

/-- Repeated primitive fields on one side.  `Occ v` contains the actual
occurrence addresses that read role `v`; no occurrence is merged away. -/
abbrev Primitive (A : Finset Role)
    (Occ : {v // v ∈ A} → Type*) :=
  ∀ v : {v // v ∈ A}, Occ v → Label v.1

/-- Every occurrence of a role reads the same typed label. -/
def PrimitiveConsistent {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    (p : Primitive Label A Occ) : Prop :=
  ∀ v (o o' : Occ v), p v o = p v o'

/-- Encode a role assignment into all of its repeated primitive occurrences. -/
def primitiveEncode {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    (x : RoleAssign Label A) : Primitive Label A Occ :=
  fun v _ => x v

/-- A primitive tuple produced from a role assignment is consistent. -/
theorem primitiveEncode_consistent {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    (x : RoleAssign Label A) :
    PrimitiveConsistent Label (primitiveEncode Label (Occ := Occ) x) := by
  intro v o o'
  rfl

/-- Nonempty occurrence fibers make primitive encoding injective. -/
theorem primitiveEncode_injective {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    [∀ v, Nonempty (Occ v)] :
    Function.Injective (primitiveEncode Label (Occ := Occ)) := by
  intro x y h
  funext v
  have hv := congrFun h v
  exact congrFun hv (Classical.choice (inferInstance : Nonempty (Occ v)))

/-- Decode a primitive tuple by reading one actual occurrence for each role. -/
def primitiveDecode {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    [∀ v, Nonempty (Occ v)]
    (p : Primitive Label A Occ) : RoleAssign Label A :=
  fun v => p v (Classical.choice (inferInstance : Nonempty (Occ v)))

@[simp] theorem primitiveDecode_encode {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    [∀ v, Nonempty (Occ v)]
    (x : RoleAssign Label A) :
    primitiveDecode Label (Occ := Occ)
      (primitiveEncode Label (Occ := Occ) x) = x := by
  funext v
  rfl

/-- For a consistent tuple, decoding and re-encoding recovers every repeated
occurrence, not merely one representative. -/
theorem primitiveEncode_decode_of_consistent {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    [∀ v, Nonempty (Occ v)]
    (p : Primitive Label A Occ)
    (hp : PrimitiveConsistent Label p) :
    primitiveEncode Label (Occ := Occ)
        (primitiveDecode Label (Occ := Occ) p) = p := by
  funext v o
  exact hp v (Classical.choice (inferInstance : Nonempty (Occ v))) o

/-- Restrict a complete assignment to a finite role set. -/
def restrictFull (A : Finset Role) (a : FullAssign Label) :
    RoleAssign Label A :=
  fun v => a v.1

/-- Split off the nonseparator roles on one side. -/
def splitSide {A sep : Finset Role}
    (hSep : sep ⊆ A) (x : RoleAssign Label A) :
    RoleAssign Label (A \ sep) × RoleAssign Label sep :=
  (fun v => x ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩,
   fun v => x ⟨v.1, hSep v.2⟩)

/-- Glue separator and side-only assignments into the complete assignment on
that observed side. -/
def glueSide {A sep : Finset Role}
    (hSep : sep ⊆ A)
    (u : RoleAssign Label (A \ sep))
    (s : RoleAssign Label sep) : RoleAssign Label A :=
  fun v => if hs : v.1 ∈ sep then s ⟨v.1, hs⟩
    else u ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hs⟩⟩

@[simp] theorem glueSide_split {A sep : Finset Role}
    (hSep : sep ⊆ A) (x : RoleAssign Label A) :
    glueSide Label hSep (splitSide Label hSep x).1
      (splitSide Label hSep x).2 = x := by
  funext v
  by_cases hs : v.1 ∈ sep
  · simp [glueSide, splitSide, hs]
  · simp [glueSide, splitSide, hs]

@[simp] theorem splitSide_glue {A sep : Finset Role}
    (hSep : sep ⊆ A)
    (u : RoleAssign Label (A \ sep))
    (s : RoleAssign Label sep) :
    splitSide Label hSep (glueSide Label hSep u s) = (u, s) := by
  apply Prod.ext
  · funext v
    have hvn : v.1 ∉ sep := (Finset.mem_sdiff.mp v.2).2
    simp [splitSide, glueSide, hvn]
  · funext v
    simp [splitSide, glueSide, v.2]

/-- The side split/glue operation is a genuine typed equivalence. -/
def sideSplitEquiv {A sep : Finset Role}
    (hSep : sep ⊆ A) :
    (RoleAssign Label (A \ sep) × RoleAssign Label sep) ≃
      RoleAssign Label A where
  toFun us := glueSide Label hSep us.1 us.2
  invFun x := splitSide Label hSep x
  left_inv us := by
    rcases us with ⟨u, s⟩
    exact splitSide_glue Label hSep u s
  right_inv x := glueSide_split Label hSep x

/-- Actual embedding of `(side-only labels, separator labels)` into the raw
repeated primitive fields. -/
def primitiveEmbedding {A sep : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    [∀ v, Nonempty (Occ v)]
    (hSep : sep ⊆ A) :
    (RoleAssign Label (A \ sep) × RoleAssign Label sep) ↪
      Primitive Label A Occ where
  toFun us := primitiveEncode Label (Occ := Occ)
    (glueSide Label hSep us.1 us.2)
  inj' := by
    intro a b h
    have hRole :
        glueSide Label hSep a.1 a.2 = glueSide Label hSep b.1 b.2 :=
      primitiveEncode_injective Label (Occ := Occ) h
    have hs := congrArg (splitSide Label hSep) hRole
    simpa using hs

/-- The range of the concrete primitive embedding is exactly the consistent
raw primitive tuples. -/
theorem mem_range_primitiveEmbedding_iff_consistent
    {A sep : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    [∀ v, Nonempty (Occ v)]
    (hSep : sep ⊆ A) (p : Primitive Label A Occ) :
    p ∈ Set.range (primitiveEmbedding Label (Occ := Occ) hSep) ↔
      PrimitiveConsistent Label p := by
  constructor
  · rintro ⟨us, rfl⟩
    exact primitiveEncode_consistent Label _
  · intro hp
    let x : RoleAssign Label A := primitiveDecode Label (Occ := Occ) p
    let us := splitSide Label hSep x
    refine ⟨us, ?_⟩
    change primitiveEncode Label (Occ := Occ)
        (glueSide Label hSep us.1 us.2) = p
    calc
      primitiveEncode Label (Occ := Occ)
          (glueSide Label hSep us.1 us.2) =
          primitiveEncode Label (Occ := Occ) x := by
            rw [show glueSide Label hSep us.1 us.2 = x by
              simpa [us] using glueSide_split Label hSep x]
      _ = p := primitiveEncode_decode_of_consistent Label p hp

/-- Agreement of two role-side assignments on their overlap. -/
def SideAgree {row col : Finset Role}
    (x : RoleAssign Label row) (y : RoleAssign Label col) : Prop :=
  ∀ v (hr : v ∈ row) (hc : v ∈ col),
    x ⟨v, hr⟩ = y ⟨v, hc⟩

/-- Glue row-side and column-side role assignments to one complete retained
assignment.  The cover assumption is exactly C1's `R₀ ∪ C₀ = C`, after
renaming the retained role type to `Role`. -/
def glueFull {row col : Finset Role}
    (hCover : row ∪ col = Finset.univ)
    (x : RoleAssign Label row) (y : RoleAssign Label col) :
    FullAssign Label :=
  fun v => if hr : v ∈ row then x ⟨v, hr⟩ else
    y ⟨v, by
      have hv : v ∈ row ∨ v ∈ col := by
        have h : v ∈ (Finset.univ : Finset Role) := Finset.mem_univ v
        rw [← hCover, Finset.mem_union] at h
        exact h
      exact hv.resolve_left hr⟩

@[simp] theorem restrictFull_glueFull_row {row col : Finset Role}
    (hCover : row ∪ col = Finset.univ)
    (x : RoleAssign Label row) (y : RoleAssign Label col) :
    restrictFull Label row (glueFull Label hCover x y) = x := by
  funext v
  simp [restrictFull, glueFull, v.2]

@[simp] theorem restrictFull_glueFull_col {row col : Finset Role}
    (hCover : row ∪ col = Finset.univ)
    (x : RoleAssign Label row) (y : RoleAssign Label col)
    (hAgree : SideAgree Label x y) :
    restrictFull Label col (glueFull Label hCover x y) = y := by
  funext v
  by_cases hr : v.1 ∈ row
  · simpa [restrictFull, glueFull, hr] using hAgree v.1 hr v.2
  · simp [restrictFull, glueFull, hr]

/-- The glued complete assignment is unique. -/
theorem glueFull_unique {row col : Finset Role}
    (hCover : row ∪ col = Finset.univ)
    (x : RoleAssign Label row) (y : RoleAssign Label col)
    (hAgree : SideAgree Label x y)
    (a : FullAssign Label)
    (hRow : restrictFull Label row a = x)
    (hCol : restrictFull Label col a = y) :
    a = glueFull Label hCover x y := by
  funext v
  by_cases hr : v ∈ row
  · have hv := congrFun hRow ⟨v, hr⟩
    simpa [restrictFull, glueFull, hr] using hv
  · have hc : v ∈ col := by
      have hv : v ∈ row ∨ v ∈ col := by
        have h : v ∈ (Finset.univ : Finset Role) := Finset.mem_univ v
        rw [← hCover, Finset.mem_union] at h
        exact h
      exact hv.resolve_left hr
    have hv := congrFun hCol ⟨v, hc⟩
    simpa [restrictFull, glueFull, hr] using hv

/-- `sep = row ∩ col` implies that every separator role is observed on the
row side. -/
theorem sep_subset_row_of_inter_eq {row col sep : Finset Role}
    (hInter : row ∩ col = sep) : sep ⊆ row := by
  intro v hv
  have hv' : v ∈ row ∩ col := by
    rw [hInter]
    exact hv
  exact (Finset.mem_inter.mp hv').1

/-- `sep = row ∩ col` implies that every separator role is observed on the
column side. -/
theorem sep_subset_col_of_inter_eq {row col sep : Finset Role}
    (hInter : row ∩ col = sep) : sep ⊆ col := by
  intro v hv
  have hv' : v ∈ row ∩ col := by
    rw [hInter]
    exact hv
  exact (Finset.mem_inter.mp hv').2

/-- If the two side assignments use the same separator tuple, then they agree
on every role observed by both sides. -/
theorem gluedSides_agree {row col sep : Finset Role}
    (hInter : row ∩ col = sep)
    (l : RoleAssign Label (row \ sep))
    (s : RoleAssign Label sep)
    (r : RoleAssign Label (col \ sep)) :
    SideAgree Label
      (glueSide Label (sep_subset_row_of_inter_eq hInter) l s)
      (glueSide Label (sep_subset_col_of_inter_eq hInter) r s) := by
  intro v hr hc
  have hs : v ∈ sep := by
    have hv : v ∈ row ∩ col := Finset.mem_inter.mpr ⟨hr, hc⟩
    simpa [hInter] using hv
  simp [glueSide, hs]

/-- Full assignment encoded into the actual repeated primitive fields. -/
def fullPrimitive {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    (a : FullAssign Label) : Primitive Label A Occ :=
  primitiveEncode Label (Occ := Occ) (restrictFull Label A a)

/-- The actual post-conditioning coefficient: a finite sum over complete
retained assignments whose row and column primitive fields match the supplied
raw addresses.  `w` is the already-produced active-component weight. -/
def actualCoefficient
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    (w : RoleAssign Label sep → ℝ) :
    Matrix (Primitive Label row RowOcc) (Primitive Label col ColOcc) ℝ :=
  fun p q => ∑ a : FullAssign Label,
    if fullPrimitive Label (Occ := RowOcc) a = p ∧
       fullPrimitive Label (Occ := ColOcc) a = q
    then w (restrictFull Label sep a)
    else 0

/-- An inconsistent repeated row primitive cannot be produced by any complete
assignment, hence the actual coefficient row is zero. -/
theorem actualCoefficient_row_zero_of_inconsistent
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    (w : RoleAssign Label sep → ℝ)
    (p : Primitive Label row RowOcc)
    (hp : ¬ PrimitiveConsistent Label p)
    (q : Primitive Label col ColOcc) :
    actualCoefficient Label RowOcc ColOcc w p q = 0 := by
  classical
  unfold actualCoefficient
  apply Finset.sum_eq_zero
  intro a _
  have hnot : ¬ (fullPrimitive Label (Occ := RowOcc) a = p ∧
      fullPrimitive Label (Occ := ColOcc) a = q) := by
    intro h
    apply hp
    have hc : PrimitiveConsistent Label
        (fullPrimitive Label (Occ := RowOcc) a) :=
      primitiveEncode_consistent Label _
    rw [h.1] at hc
    exact hc
  simp [hnot]

/-- The column analogue of `actualCoefficient_row_zero_of_inconsistent`. -/
theorem actualCoefficient_col_zero_of_inconsistent
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    (w : RoleAssign Label sep → ℝ)
    (q : Primitive Label col ColOcc)
    (hq : ¬ PrimitiveConsistent Label q)
    (p : Primitive Label row RowOcc) :
    actualCoefficient Label RowOcc ColOcc w p q = 0 := by
  classical
  unfold actualCoefficient
  apply Finset.sum_eq_zero
  intro a _
  have hnot : ¬ (fullPrimitive Label (Occ := RowOcc) a = p ∧
      fullPrimitive Label (Occ := ColOcc) a = q) := by
    intro h
    apply hq
    have hc : PrimitiveConsistent Label
        (fullPrimitive Label (Occ := ColOcc) a) :=
      primitiveEncode_consistent Label _
    rw [h.2] at hc
    exact hc
  simp [hnot]

/-- Equality of complete primitive encodings is equivalent to equality of the
underlying side-role assignments, because every observed role has a real
primitive occurrence. -/
theorem fullPrimitive_eq_primitiveEncode_iff
    {A : Finset Role}
    {Occ : {v // v ∈ A} → Type*}
    [∀ v, Nonempty (Occ v)]
    (a : FullAssign Label) (x : RoleAssign Label A) :
    fullPrimitive Label (Occ := Occ) a =
        primitiveEncode Label (Occ := Occ) x ↔
      restrictFull Label A a = x := by
  constructor
  · intro h
    exact primitiveEncode_injective Label (Occ := Occ) h
  · intro h
    exact congrArg (primitiveEncode Label (Occ := Occ)) h

/-- If one complete assignment matches two embedded primitive sides, then the
separator tuples on those sides must be identical. -/
theorem separator_eq_of_primitive_matches
    {row col sep : Finset Role}
    {RowOcc : {v // v ∈ row} → Type*}
    {ColOcc : {v // v ∈ col} → Type*}
    [∀ v, Nonempty (RowOcc v)]
    [∀ v, Nonempty (ColOcc v)]
    (hInter : row ∩ col = sep)
    (a : FullAssign Label)
    (l : RoleAssign Label (row \ sep))
    (s : RoleAssign Label sep)
    (r : RoleAssign Label (col \ sep))
    (t : RoleAssign Label sep)
    (hRow : fullPrimitive Label (Occ := RowOcc) a =
      primitiveEmbedding Label (Occ := RowOcc)
        (sep_subset_row_of_inter_eq hInter) (l, s))
    (hCol : fullPrimitive Label (Occ := ColOcc) a =
      primitiveEmbedding Label (Occ := ColOcc)
        (sep_subset_col_of_inter_eq hInter) (r, t)) :
    s = t := by
  have hRowRole : restrictFull Label row a =
      glueSide Label (sep_subset_row_of_inter_eq hInter) l s := by
    exact primitiveEncode_injective Label (Occ := RowOcc) hRow
  have hColRole : restrictFull Label col a =
      glueSide Label (sep_subset_col_of_inter_eq hInter) r t := by
    exact primitiveEncode_injective Label (Occ := ColOcc) hCol
  funext z
  have hzRow := congrFun hRowRole
    ⟨z.1, sep_subset_row_of_inter_eq hInter z.2⟩
  have hzCol := congrFun hColRole
    ⟨z.1, sep_subset_col_of_inter_eq hInter z.2⟩
  have hs : a z.1 = s z := by
    simpa [restrictFull, glueSide, z.2] using hzRow
  have ht : a z.1 = t z := by
    simpa [restrictFull, glueSide, z.2] using hzCol
  exact hs.symm.trans ht

/-- For equal separator labels there is exactly one complete retained
assignment contributing to the actual coefficient, and its contribution is
exactly `w s`.  This is the no-extra-summation-multiplicity statement. -/
theorem actualCoefficient_entry_same_separator
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    [∀ v, Fintype (RowOcc v)] [∀ v, Fintype (ColOcc v)]
    [∀ v, Nonempty (RowOcc v)] [∀ v, Nonempty (ColOcc v)]
    (w : RoleAssign Label sep → ℝ)
    (hCover : row ∪ col = Finset.univ)
    (hInter : row ∩ col = sep)
    (l : RoleAssign Label (row \ sep))
    (s : RoleAssign Label sep)
    (r : RoleAssign Label (col \ sep)) :
    actualCoefficient Label RowOcc ColOcc w
      (primitiveEmbedding Label (Occ := RowOcc)
        (sep_subset_row_of_inter_eq hInter) (l, s))
      (primitiveEmbedding Label (Occ := ColOcc)
        (sep_subset_col_of_inter_eq hInter) (r, s)) = w s := by
  classical
  let x : RoleAssign Label row :=
    glueSide Label (sep_subset_row_of_inter_eq hInter) l s
  let y : RoleAssign Label col :=
    glueSide Label (sep_subset_col_of_inter_eq hInter) r s
  have hAgree : SideAgree Label x y := by
    simpa [x, y] using gluedSides_agree Label hInter l s r
  let a0 : FullAssign Label := glueFull Label hCover x y
  have hRowRole : restrictFull Label row a0 = x := by
    simpa [a0] using restrictFull_glueFull_row Label hCover x y
  have hColRole : restrictFull Label col a0 = y := by
    simpa [a0] using restrictFull_glueFull_col Label hCover x y hAgree
  have hRow0 : fullPrimitive Label (Occ := RowOcc) a0 =
      primitiveEmbedding Label (Occ := RowOcc)
        (sep_subset_row_of_inter_eq hInter) (l, s) := by
    change primitiveEncode Label (Occ := RowOcc)
        (restrictFull Label row a0) =
      primitiveEncode Label (Occ := RowOcc) x
    exact congrArg (primitiveEncode Label (Occ := RowOcc)) hRowRole
  have hCol0 : fullPrimitive Label (Occ := ColOcc) a0 =
      primitiveEmbedding Label (Occ := ColOcc)
        (sep_subset_col_of_inter_eq hInter) (r, s) := by
    change primitiveEncode Label (Occ := ColOcc)
        (restrictFull Label col a0) =
      primitiveEncode Label (Occ := ColOcc) y
    exact congrArg (primitiveEncode Label (Occ := ColOcc)) hColRole
  have hSep0 : restrictFull Label sep a0 = s := by
    funext z
    have hz := congrFun hRowRole
      ⟨z.1, sep_subset_row_of_inter_eq hInter z.2⟩
    simpa [restrictFull, x, glueSide, z.2] using hz
  unfold actualCoefficient
  rw [Finset.sum_eq_single a0]
  · simp [hRow0, hCol0, hSep0]
  · intro a _ hne
    have hnot : ¬ (fullPrimitive Label (Occ := RowOcc) a =
          primitiveEmbedding Label (Occ := RowOcc)
            (sep_subset_row_of_inter_eq hInter) (l, s) ∧
        fullPrimitive Label (Occ := ColOcc) a =
          primitiveEmbedding Label (Occ := ColOcc)
            (sep_subset_col_of_inter_eq hInter) (r, s)) := by
      intro hm
      apply hne
      apply glueFull_unique Label hCover x y hAgree a
      · exact primitiveEncode_injective Label (Occ := RowOcc) hm.1
      · exact primitiveEncode_injective Label (Occ := ColOcc) hm.2
    simp [hnot]
  · simp

/-- Different separator labels produce no complete retained assignment, so the
entry is exactly zero. -/
theorem actualCoefficient_entry_different_separator
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    [∀ v, Fintype (RowOcc v)] [∀ v, Fintype (ColOcc v)]
    [∀ v, Nonempty (RowOcc v)] [∀ v, Nonempty (ColOcc v)]
    (w : RoleAssign Label sep → ℝ)
    (hInter : row ∩ col = sep)
    (l : RoleAssign Label (row \ sep))
    (s : RoleAssign Label sep)
    (r : RoleAssign Label (col \ sep))
    (t : RoleAssign Label sep)
    (hst : s ≠ t) :
    actualCoefficient Label RowOcc ColOcc w
      (primitiveEmbedding Label (Occ := RowOcc)
        (sep_subset_row_of_inter_eq hInter) (l, s))
      (primitiveEmbedding Label (Occ := ColOcc)
        (sep_subset_col_of_inter_eq hInter) (r, t)) = 0 := by
  classical
  unfold actualCoefficient
  apply Finset.sum_eq_zero
  intro a _
  have hnot : ¬ (fullPrimitive Label (Occ := RowOcc) a =
        primitiveEmbedding Label (Occ := RowOcc)
          (sep_subset_row_of_inter_eq hInter) (l, s) ∧
      fullPrimitive Label (Occ := ColOcc) a =
        primitiveEmbedding Label (Occ := ColOcc)
          (sep_subset_col_of_inter_eq hInter) (r, t)) := by
    intro hm
    apply hst
    exact separator_eq_of_primitive_matches Label hInter a l s r t hm.1 hm.2
  simp [hnot]

/-- Exact separator-block entry formula, proved from the actual assignment sum. -/
theorem actualCoefficient_entry
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    [∀ v, Fintype (RowOcc v)] [∀ v, Fintype (ColOcc v)]
    [∀ v, Nonempty (RowOcc v)] [∀ v, Nonempty (ColOcc v)]
    (w : RoleAssign Label sep → ℝ)
    (hCover : row ∪ col = Finset.univ)
    (hInter : row ∩ col = sep)
    (s t : RoleAssign Label sep)
    (l : RoleAssign Label (row \ sep))
    (r : RoleAssign Label (col \ sep)) :
    actualCoefficient Label RowOcc ColOcc w
      (primitiveEmbedding Label (Occ := RowOcc)
        (sep_subset_row_of_inter_eq hInter) (l, s))
      (primitiveEmbedding Label (Occ := ColOcc)
        (sep_subset_col_of_inter_eq hInter) (r, t)) =
      if s = t then w s else 0 := by
  classical
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl]
    exact actualCoefficient_entry_same_separator Label RowOcc ColOcc w
      hCover hInter l s r
  · rw [if_neg hst]
    exact actualCoefficient_entry_different_separator Label RowOcc ColOcc w
      hInter l s r t hst

/-- Outside the embedded consistent row coordinates the actual coefficient is
zero, derived from consistency rather than postulated. -/
theorem actualCoefficient_row_zero_outside_range
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    [∀ v, Nonempty (RowOcc v)]
    (w : RoleAssign Label sep → ℝ)
    (hSepRow : sep ⊆ row)
    (p : Primitive Label row RowOcc)
    (hp : p ∉ Set.range (primitiveEmbedding Label (Occ := RowOcc) hSepRow))
    (q : Primitive Label col ColOcc) :
    actualCoefficient Label RowOcc ColOcc w p q = 0 := by
  apply actualCoefficient_row_zero_of_inconsistent Label RowOcc ColOcc w p
  intro hCons
  exact hp ((mem_range_primitiveEmbedding_iff_consistent Label hSepRow p).2 hCons)

/-- Column-side zero padding, again derived from actual consistency. -/
theorem actualCoefficient_col_zero_outside_range
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    [∀ v, Nonempty (ColOcc v)]
    (w : RoleAssign Label sep → ℝ)
    (hSepCol : sep ⊆ col)
    (q : Primitive Label col ColOcc)
    (hq : q ∉ Set.range (primitiveEmbedding Label (Occ := ColOcc) hSepCol))
    (p : Primitive Label row RowOcc) :
    actualCoefficient Label RowOcc ColOcc w p q = 0 := by
  apply actualCoefficient_col_zero_of_inconsistent Label RowOcc ColOcc w q
  intro hCons
  exact hq ((mem_range_primitiveEmbedding_iff_consistent Label hSepCol q).2 hCons)

/-- Exact operator norm of the actual assignment-sum coefficient after C1's
cover/intersection conclusions.  This instantiates the existing coordinate
zero-padding theorem; the block entry and zero-support premises have all been
proved above. -/
theorem actualCoefficient_norm_eq_sqrt_product
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    [∀ v, Fintype (RowOcc v)] [∀ v, Fintype (ColOcc v)]
    [∀ v, Nonempty (RowOcc v)] [∀ v, Nonempty (ColOcc v)]
    (w : RoleAssign Label sep → ℝ)
    (hCover : row ∪ col = Finset.univ)
    (hInter : row ∩ col = sep) :
    ‖actualCoefficient Label RowOcc ColOcc w‖ =
      Real.sqrt
        ((Fintype.card (RoleAssign Label (row \ sep)) : ℝ) *
         (Fintype.card (RoleAssign Label (col \ sep)) : ℝ)) *
      Finset.univ.sup' Finset.univ_nonempty
        (fun s : RoleAssign Label sep => |w s|) := by
  classical
  let er := primitiveEmbedding Label (Occ := RowOcc)
    (sep_subset_row_of_inter_eq hInter)
  let ec := primitiveEmbedding Label (Occ := ColOcc)
    (sep_subset_col_of_inter_eq hInter)
  apply GraphMatrixReplica.Model.Separator.norm_of_consistency_zero_padding_eq_sqrt_product
    er ec
      (actualCoefficient Label RowOcc ColOcc w) w
  · intro s t l r
    exact actualCoefficient_entry Label RowOcc ColOcc w hCover hInter s t l r
  · intro p hp q
    exact actualCoefficient_row_zero_outside_range Label RowOcc ColOcc w
      (sep_subset_row_of_inter_eq hInter) p hp q
  · intro q hq p
    exact actualCoefficient_col_zero_outside_range Label RowOcc ColOcc w
      (sep_subset_col_of_inter_eq hInter) q hq p

/-- Cardinality of a typed role-assignment space is the product of the
individual role label cardinalities. -/
theorem card_roleAssign (A : Finset Role) :
    Fintype.card (RoleAssign Label A) =
      ∏ v : {v // v ∈ A}, Fintype.card (Label v.1) := by
  classical
  rw [Fintype.card_pi]

/-- Formal mixed-stacking bridge.  The only remaining graph-specific Lean
premise is `hReindexNorm`: the paper's typed independent-edge mixed flattening
must be shown, by the actual primitive reindexing, to have the same norm as the
`actualCoefficient` above.  Once that premise is supplied, the existing mixed
stacking theorem and the exact coefficient norm give the weighted flattening
inequality immediately. -/
theorem weightedFlattening_of_mixed_reindex
    {row col sep : Finset Role}
    (RowOcc : {v // v ∈ row} → Type*)
    (ColOcc : {v // v ∈ col} → Type*)
    [∀ v, Fintype (RowOcc v)] [∀ v, Fintype (ColOcc v)]
    [∀ v, Nonempty (RowOcc v)] [∀ v, Nonempty (ColOcc v)]
    (w : RoleAssign Label sep → ℝ)
    (hCover : row ∪ col = Finset.univ)
    (hInter : row ∩ col = sep)
    (q : ℕ) (size : Fin q → ℕ) (dir : Fin q → Bool)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : GraphMatrixReplica.Model.lowerHeteroIndex q size →
      Matrix ι κ ℝ)
    (hReindexNorm :
      ‖GraphMatrixReplica.Model.lowerMixedFlatten q size dir A‖ =
        ‖actualCoefficient Label RowOcc ColOcc w‖) :
    Real.sqrt
        ((Fintype.card (RoleAssign Label (row \ sep)) : ℝ) *
         (Fintype.card (RoleAssign Label (col \ sep)) : ℝ)) *
      Finset.univ.sup' Finset.univ_nonempty
        (fun s : RoleAssign Label sep => |w s|) ≤
      Real.sqrt 3 ^ q *
        GraphMatrixReplica.Model.lowerHeteroMean q size
          (fun noise =>
            ‖GraphMatrixReplica.Model.lowerHeteroChaos q size A noise‖) := by
  have hStack := GraphMatrixReplica.Model.lowerMixedFlatten_norm_le
    q size dir A
  rw [hReindexNorm,
    actualCoefficient_norm_eq_sqrt_product Label RowOcc ColOcc w hCover hInter]
    at hStack
  exact hStack


end GraphMatrixReplica.Model.C2
