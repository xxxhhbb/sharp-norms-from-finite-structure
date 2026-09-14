import R6.C2ActualMatrixExpansion
import R6.PaperR16C1C2AddressReindex

/-!
# C2: semantic reindexing of the actual mixed flattening

The key convention is fixed once and for all here:
`freshDir g = !(edgeSide ... e)`.  Thus C1 row edges (`edgeSide=false`)
are exactly the groups stacked on rows (`dir=true`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.PaperR16.C2Actual

open GraphMatrixReplica
open GraphMatrixReplica.PaperR16
open GraphMatrixReplica.PaperR16.ActualPrimitiveObservations

attribute [local instance] Classical.propDecidable

/-! ## 1. Semantic payload of the recursive mixed indices -/

/-- A row stores the coordinate of exactly the groups whose mixed direction is
`true`; all other groups carry a unique unit placeholder. -/
def mixRowCoordType {q : ℕ} (size : Fin q → ℕ) (dir : Fin q → Bool)
    (g : Fin q) : Type :=
  match dir g with
  | true => Fin (size g)
  | false => PUnit

/-- A column stores exactly the complementary (`dir=false`) coordinates. -/
def mixColCoordType {q : ℕ} (size : Fin q → ℕ) (dir : Fin q → Bool)
    (g : Fin q) : Type :=
  match dir g with
  | true => PUnit
  | false => Fin (size g)

abbrev MixRowPayload (q : ℕ) (size : Fin q → ℕ) (dir : Fin q → Bool) :=
  (g : Fin q) → mixRowCoordType size dir g

abbrev MixColPayload (q : ℕ) (size : Fin q → ℕ) (dir : Fin q → Bool) :=
  (g : Fin q) → mixColCoordType size dir g

/-- Read a selected row coordinate. -/
def mixRowPayloadGet {q : ℕ} {size : Fin q → ℕ} {dir : Fin q → Bool}
    (p : MixRowPayload q size dir) (g : Fin q) (hg : dir g = true) :
    Fin (size g) := by
  simpa [mixRowCoordType, hg] using p g

/-- Read a selected column coordinate. -/
def mixColPayloadGet {q : ℕ} {size : Fin q → ℕ} {dir : Fin q → Bool}
    (p : MixColPayload q size dir) (g : Fin q) (hg : dir g = false) :
    Fin (size g) := by
  simpa [mixColCoordType, hg] using p g

/-- Split a row payload into the head group and the tail groups. -/
def mixRowPayloadSplitEquiv (q : ℕ) (size : Fin (q + 1) → ℕ)
    (dir : Fin (q + 1) → Bool) :
    MixRowPayload (q + 1) size dir ≃
      mixRowCoordType size dir 0 ×
        MixRowPayload q (fun g => size g.succ) (fun g => dir g.succ) :=
  (Fin.consEquiv (fun g : Fin (q + 1) => mixRowCoordType size dir g)).symm

/-- Split a column payload into head and tail. -/
def mixColPayloadSplitEquiv (q : ℕ) (size : Fin (q + 1) → ℕ)
    (dir : Fin (q + 1) → Bool) :
    MixColPayload (q + 1) size dir ≃
      mixColCoordType size dir 0 ×
        MixColPayload q (fun g => size g.succ) (fun g => dir g.succ) :=
  (Fin.consEquiv (fun g : Fin (q + 1) => mixColCoordType size dir g)).symm

/-- If the head group is a row group, append its genuine coordinate to the
recursive row payload. -/
def mixRowPayloadConsTrueEquiv
    (q : ℕ) (size : Fin (q + 1) → ℕ) (dir : Fin (q + 1) → Bool)
    (h : dir 0 = true) (ι : Type*) :
    (MixRowPayload q (fun g => size g.succ) (fun g => dir g.succ) ×
        (Fin (size 0) × ι)) ≃
      (MixRowPayload (q + 1) size dir × ι) := by
  let e0 : Fin (size 0) ≃ mixRowCoordType size dir 0 := Equiv.cast (by simp [mixRowCoordType, h])
  exact (Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl ι)).trans
      (Equiv.prodCongr ((Equiv.prodCongr e0 (Equiv.refl _)).trans
        (mixRowPayloadSplitEquiv q size dir).symm) (Equiv.refl ι)))

/-- If the head group is a column group, a row payload only inserts its unique
unit placeholder. -/
def mixRowPayloadConsFalseEquiv
    (q : ℕ) (size : Fin (q + 1) → ℕ) (dir : Fin (q + 1) → Bool)
    (h : dir 0 = false) (ι : Type*) :
    (MixRowPayload q (fun g => size g.succ) (fun g => dir g.succ) × ι) ≃
      (MixRowPayload (q + 1) size dir × ι) := by
  let e0 : PUnit ≃ mixRowCoordType size dir 0 := Equiv.cast (by simp [mixRowCoordType, h])
  exact Equiv.prodCongr
    ((Equiv.punitProd _).symm.trans
      ((Equiv.prodCongr e0 (Equiv.refl _)).trans (mixRowPayloadSplitEquiv q size dir).symm))
    (Equiv.refl ι)

/-- Column analogue: a row-directed head group contributes only a unit. -/
def mixColPayloadConsTrueEquiv
    (q : ℕ) (size : Fin (q + 1) → ℕ) (dir : Fin (q + 1) → Bool)
    (h : dir 0 = true) (κ : Type*) :
    (MixColPayload q (fun g => size g.succ) (fun g => dir g.succ) × κ) ≃
      (MixColPayload (q + 1) size dir × κ) := by
  let e0 : PUnit ≃ mixColCoordType size dir 0 := Equiv.cast (by simp [mixColCoordType, h])
  exact Equiv.prodCongr
    ((Equiv.punitProd _).symm.trans
      ((Equiv.prodCongr e0 (Equiv.refl _)).trans (mixColPayloadSplitEquiv q size dir).symm))
    (Equiv.refl κ)

/-- Column analogue: a column-directed head group contributes its coordinate. -/
def mixColPayloadConsFalseEquiv
    (q : ℕ) (size : Fin (q + 1) → ℕ) (dir : Fin (q + 1) → Bool)
    (h : dir 0 = false) (κ : Type*) :
    (MixColPayload q (fun g => size g.succ) (fun g => dir g.succ) ×
        (Fin (size 0) × κ)) ≃
      (MixColPayload (q + 1) size dir × κ) := by
  let e0 : Fin (size 0) ≃ mixColCoordType size dir 0 := Equiv.cast (by simp [mixColCoordType, h])
  exact (Equiv.prodAssoc _ _ _).symm.trans
    ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl κ)).trans
      (Equiv.prodCongr ((Equiv.prodCongr e0 (Equiv.refl _)).trans
        (mixColPayloadSplitEquiv q size dir).symm) (Equiv.refl κ)))

/-- Exact semantic form of the recursively nested mixed row index. -/
def lowerMixedRowsPayloadEquiv :
    (q : ℕ) → (size : Fin q → ℕ) → (dir : Fin q → Bool) → (ι : Type*) →
      lowerMixedRows q size dir ι ≃ (MixRowPayload q size dir × ι)
  | 0, size, dir, ι =>
      { toFun := fun r => ⟨(fun g => Fin.elim0 g), r⟩
        invFun := fun x => x.2
        left_inv := by intro r; rfl
        right_inv := by
          intro x
          rcases x with ⟨p, r⟩
          apply Prod.ext
          · funext g
            exact Fin.elim0 g
          · rfl }
  | q + 1, size, dir, ι => by
      cases h : dir 0 with
      | false =>
          let tailSize : Fin q → ℕ := fun g => size g.succ
          let tailDir : Fin q → Bool := fun g => dir g.succ
          let E := lowerMixedRowsPayloadEquiv q tailSize tailDir ι
          let E' : lowerMixedRows (q + 1) size dir ι ≃
              (MixRowPayload q tailSize tailDir × ι) := by
            simpa [lowerMixedRows, lowerMixDirOfFn, lowerMixRowsD, h,
              tailSize, tailDir] using E
          exact E'.trans (mixRowPayloadConsFalseEquiv q size dir h ι)
      | true =>
          let tailSize : Fin q → ℕ := fun g => size g.succ
          let tailDir : Fin q → Bool := fun g => dir g.succ
          let E := lowerMixedRowsPayloadEquiv q tailSize tailDir (Fin (size 0) × ι)
          let E' : lowerMixedRows (q + 1) size dir ι ≃
              (MixRowPayload q tailSize tailDir × (Fin (size 0) × ι)) := by
            simpa [lowerMixedRows, lowerMixDirOfFn, lowerMixRowsD, h,
              tailSize, tailDir] using E
          exact E'.trans (mixRowPayloadConsTrueEquiv q size dir h ι)

/-- Exact semantic form of the recursively nested mixed column index. -/
def lowerMixedColsPayloadEquiv :
    (q : ℕ) → (size : Fin q → ℕ) → (dir : Fin q → Bool) → (κ : Type*) →
      lowerMixedCols q size dir κ ≃ (MixColPayload q size dir × κ)
  | 0, size, dir, κ =>
      { toFun := fun c => ⟨(fun g => Fin.elim0 g), c⟩
        invFun := fun x => x.2
        left_inv := by intro c; rfl
        right_inv := by
          intro x
          rcases x with ⟨p, c⟩
          apply Prod.ext
          · funext g
            exact Fin.elim0 g
          · rfl }
  | q + 1, size, dir, κ => by
      cases h : dir 0 with
      | false =>
          let tailSize : Fin q → ℕ := fun g => size g.succ
          let tailDir : Fin q → Bool := fun g => dir g.succ
          let E := lowerMixedColsPayloadEquiv q tailSize tailDir (Fin (size 0) × κ)
          let E' : lowerMixedCols (q + 1) size dir κ ≃
              (MixColPayload q tailSize tailDir × (Fin (size 0) × κ)) := by
            simpa [lowerMixedCols, lowerMixDirOfFn, lowerMixColsD, h,
              tailSize, tailDir] using E
          exact E'.trans (mixColPayloadConsFalseEquiv q size dir h κ)
      | true =>
          let tailSize : Fin q → ℕ := fun g => size g.succ
          let tailDir : Fin q → Bool := fun g => dir g.succ
          let E := lowerMixedColsPayloadEquiv q tailSize tailDir κ
          let E' : lowerMixedCols (q + 1) size dir κ ≃
              (MixColPayload q tailSize tailDir × κ) := by
            simpa [lowerMixedCols, lowerMixDirOfFn, lowerMixColsD, h,
              tailSize, tailDir] using E
          exact E'.trans (mixColPayloadConsTrueEquiv q size dir h κ)

/-! ## 2. Coherence with `lowerMixDecodeD` -/

/-- The base row carried by the semantic row equivalence is exactly the base row
returned by the actual mixed decoder. -/
theorem lowerMixedRowsPayload_base :
    ∀ q (size : Fin q → ℕ) (dir : Fin q → Bool)
      {ι κ : Type*}
      (r : lowerMixedRows q size dir ι)
      (c : lowerMixedCols q size dir κ),
      (lowerMixedRowsPayloadEquiv q size dir ι r).2 =
        (lowerMixDecodeD q size (lowerMixDirOfFn q dir) r c).2.1 := by
  intro q
  induction q with
  | zero =>
      intro size dir ι κ r c
      rfl
  | succ q ih =>
      intro size dir ι κ r c
      obtain ⟨⟨head, tail⟩, rfl⟩ :=
        (Fin.consEquiv (fun _ : Fin (q + 1) => Bool)).surjective dir
      cases head with
      | false =>
          let dir : Fin (q + 1) → Bool := Fin.cons false tail
          have h : dir 0 = false := rfl
          exact ih (fun g => size g.succ) (fun g => dir g.succ) r c
      | true =>
          let dir : Fin (q + 1) → Bool := Fin.cons true tail
          have h : dir 0 = true := rfl
          have hIH := ih (fun g => size g.succ) (fun g => dir g.succ) r c
          have hBase := congrArg Prod.snd hIH
          exact hBase

/-- Every coordinate selected on the row side is the corresponding coordinate
of the complete multi-index returned by `lowerMixDecodeD`. -/
theorem lowerMixedRowsPayload_coord :
    ∀ q (size : Fin q → ℕ) (dir : Fin q → Bool)
      {ι κ : Type*}
      (r : lowerMixedRows q size dir ι)
      (c : lowerMixedCols q size dir κ)
      (g : Fin q) (hg : dir g = true),
      mixRowPayloadGet (lowerMixedRowsPayloadEquiv q size dir ι r).1 g hg =
        (lowerMixDecodeD q size (lowerMixDirOfFn q dir) r c).1 g := by
  intro q
  induction q with
  | zero =>
      intro size dir ι κ r c g
      exact Fin.elim0 g
  | succ q ih =>
      intro size dir ι κ r c g hg
      obtain ⟨⟨head, tail⟩, rfl⟩ :=
        (Fin.consEquiv (fun _ : Fin (q + 1) => Bool)).surjective dir
      cases head with
      | false =>
          let dir : Fin (q + 1) → Bool := Fin.cons false tail
          have h0 : dir 0 = false := rfl
          revert hg
          refine Fin.cases ?_ (fun gt => ?_) g
          · intro hg
            simp [dir] at hg
          · intro hg
            exact ih (fun t => size t.succ) (fun t => dir t.succ) r c gt (by simpa [dir] using hg)
      | true =>
          let dir : Fin (q + 1) → Bool := Fin.cons true tail
          have h0 : dir 0 = true := rfl
          revert hg
          refine Fin.cases ?_ (fun gt => ?_) g
          · intro hg
            have hBase := lowerMixedRowsPayload_base q
                (fun t => size t.succ) (fun t => dir t.succ) r c
            have hHead := congrArg Prod.fst hBase
            exact hHead
          · intro hg
            exact ih (fun t => size t.succ) (fun t => dir t.succ) r c gt (by simpa [dir] using hg)

/-- Base-column coherence. -/
theorem lowerMixedColsPayload_base :
    ∀ q (size : Fin q → ℕ) (dir : Fin q → Bool)
      {ι κ : Type*}
      (r : lowerMixedRows q size dir ι)
      (c : lowerMixedCols q size dir κ),
      (lowerMixedColsPayloadEquiv q size dir κ c).2 =
        (lowerMixDecodeD q size (lowerMixDirOfFn q dir) r c).2.2 := by
  intro q
  induction q with
  | zero =>
      intro size dir ι κ r c
      rfl
  | succ q ih =>
      intro size dir ι κ r c
      obtain ⟨⟨head, tail⟩, rfl⟩ :=
        (Fin.consEquiv (fun _ : Fin (q + 1) => Bool)).surjective dir
      cases head with
      | false =>
          let dir : Fin (q + 1) → Bool := Fin.cons false tail
          have h : dir 0 = false := rfl
          have hIH := ih (fun g => size g.succ) (fun g => dir g.succ) r c
          have hBase := congrArg Prod.snd hIH
          exact hBase
      | true =>
          let dir : Fin (q + 1) → Bool := Fin.cons true tail
          have h : dir 0 = true := rfl
          exact ih (fun g => size g.succ) (fun g => dir g.succ) r c

/-- Every coordinate selected on the column side is the corresponding decoded
complete multi-index coordinate. -/
theorem lowerMixedColsPayload_coord :
    ∀ q (size : Fin q → ℕ) (dir : Fin q → Bool)
      {ι κ : Type*}
      (r : lowerMixedRows q size dir ι)
      (c : lowerMixedCols q size dir κ)
      (g : Fin q) (hg : dir g = false),
      mixColPayloadGet (lowerMixedColsPayloadEquiv q size dir κ c).1 g hg =
        (lowerMixDecodeD q size (lowerMixDirOfFn q dir) r c).1 g := by
  intro q
  induction q with
  | zero =>
      intro size dir ι κ r c g
      exact Fin.elim0 g
  | succ q ih =>
      intro size dir ι κ r c g hg
      obtain ⟨⟨head, tail⟩, rfl⟩ :=
        (Fin.consEquiv (fun _ : Fin (q + 1) => Bool)).surjective dir
      cases head with
      | false =>
          let dir : Fin (q + 1) → Bool := Fin.cons false tail
          have h0 : dir 0 = false := rfl
          revert hg
          refine Fin.cases ?_ (fun gt => ?_) g
          · intro hg
            have hBase := lowerMixedColsPayload_base q
                (fun t => size t.succ) (fun t => dir t.succ) r c
            have hHead := congrArg Prod.fst hBase
            exact hHead
          · intro hg
            exact ih (fun t => size t.succ) (fun t => dir t.succ) r c gt (by simpa [dir] using hg)
      | true =>
          let dir : Fin (q + 1) → Bool := Fin.cons true tail
          have h0 : dir 0 = true := rfl
          revert hg
          refine Fin.cases ?_ (fun gt => ?_) g
          · intro hg
            simp [dir] at hg
          · intro hg
            exact ih (fun t => size t.succ) (fun t => dir t.succ) r c gt (by simpa [dir] using hg)

/-! ## 3. Ordered boundary assignments are genuine equivalences -/

variable (P : PaperShape) (dimension : Fin P.roles → ℕ)

/-- Unique original left slot representing a role in the set-indexed left
boundary. -/
def leftBoundarySlot
    (v : {v : Fin P.roles // v ∈ P.toPartiteShape.leftBoundary}) : Fin P.leftSize :=
  Classical.choose ((P.mem_leftBoundaryFinset_iff v.1).1 v.2)

@[simp] theorem leftBoundarySlot_spec
    (v : {v : Fin P.roles // v ∈ P.toPartiteShape.leftBoundary}) :
    P.left (leftBoundarySlot P v) = v.1 :=
  Classical.choose_spec ((P.mem_leftBoundaryFinset_iff v.1).1 v.2)

/-- Right-boundary counterpart. -/
def rightBoundarySlot
    (v : {v : Fin P.roles // v ∈ P.toPartiteShape.rightBoundary}) : Fin P.rightSize :=
  Classical.choose ((P.mem_rightBoundaryFinset_iff v.1).1 v.2)

@[simp] theorem rightBoundarySlot_spec
    (v : {v : Fin P.roles // v ∈ P.toPartiteShape.rightBoundary}) :
    P.right (rightBoundarySlot P v) = v.1 :=
  Classical.choose_spec ((P.mem_rightBoundaryFinset_iff v.1).1 v.2)

/-- Convert ordered left slots back to the set-indexed boundary row. -/
def boundaryRowOfOrdered
    (x : (i : Fin P.leftSize) → Fin (dimension (P.left i))) :
    PartiteBoundaryRow (G := P.toPartiteShape) dimension :=
  fun v => cast
    (congrArg (fun z : Fin P.roles => Fin (dimension z))
      (leftBoundarySlot_spec P v))
    (x (leftBoundarySlot P v))

/-- Convert ordered right slots back to the set-indexed boundary column. -/
def boundaryColOfOrdered
    (x : (i : Fin P.rightSize) → Fin (dimension (P.right i))) :
    PartiteBoundaryCol (G := P.toPartiteShape) dimension :=
  fun v => cast
    (congrArg (fun z : Fin P.roles => Fin (dimension z))
      (rightBoundarySlot_spec P v))
    (x (rightBoundarySlot P v))

/-- The original ordered left slots and the set-indexed partite boundary row
contain exactly the same typed labels. -/
def leftSlotBoundaryEquiv :
    Fin P.leftSize ≃ {v : Fin P.roles // v ∈ P.toPartiteShape.leftBoundary} where
  toFun i := ⟨P.left i, (P.mem_leftBoundaryFinset_iff _).2 ⟨i, rfl⟩⟩
  invFun := leftBoundarySlot P
  left_inv i := P.left.injective (leftBoundarySlot_spec P _)
  right_inv v := Subtype.ext (leftBoundarySlot_spec P v)

def boundaryRowOrderedEquiv :
    PartiteBoundaryRow (G := P.toPartiteShape) dimension ≃
      ((i : Fin P.leftSize) → Fin (dimension (P.left i))) :=
  (Equiv.piCongr (leftSlotBoundaryEquiv P) (fun _ => Equiv.refl _)).symm

@[simp] theorem boundaryRowOrderedEquiv_apply (x : PartiteBoundaryRow (G := P.toPartiteShape) dimension) :
    boundaryRowOrderedEquiv P dimension x = orderedRowOfBoundary P dimension x := by
  rfl

/-- Right-boundary ordered/set-indexed equivalence. -/
def rightSlotBoundaryEquiv :
    Fin P.rightSize ≃ {v : Fin P.roles // v ∈ P.toPartiteShape.rightBoundary} where
  toFun i := ⟨P.right i, (P.mem_rightBoundaryFinset_iff _).2 ⟨i, rfl⟩⟩
  invFun := rightBoundarySlot P
  left_inv i := P.right.injective (rightBoundarySlot_spec P _)
  right_inv v := Subtype.ext (rightBoundarySlot_spec P v)

def boundaryColOrderedEquiv :
    PartiteBoundaryCol (G := P.toPartiteShape) dimension ≃
      ((i : Fin P.rightSize) → Fin (dimension (P.right i))) :=
  (Equiv.piCongr (rightSlotBoundaryEquiv P) (fun _ => Equiv.refl _)).symm

@[simp] theorem boundaryColOrderedEquiv_apply (x : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    boundaryColOrderedEquiv P dimension x = orderedColOfBoundary P dimension x := by
  rfl

/-! ## 4. Payloads are exactly C1 fresh-edge address fields -/

variable (S : Finset (Fin P.roles))

/-- Actual row-side fresh-edge field type. -/
abbrev ActualRowFreshFields :=
  (e : EdgeOnSide P.toPartiteShape S false) →
    EdgeSignCoordinate dimension e.1

/-- Actual column-side fresh-edge field type. -/
abbrev ActualColFreshFields :=
  (e : EdgeOnSide P.toPartiteShape S true) →
    EdgeSignCoordinate dimension e.1

/-- A C1 row edge is exactly a fresh group with `freshDir=true`. -/
theorem freshDir_of_rowEdge (e : EdgeOnSide P.toPartiteShape S false) :
    freshDir P S ((freshEdgeEquiv P S).symm ⟨e.1, e.2.1⟩) = true := by
  simpa [freshDir] using congrArg Bool.not e.2.2

/-- A C1 column edge is exactly a fresh group with `freshDir=false`. -/
theorem freshDir_of_colEdge (e : EdgeOnSide P.toPartiteShape S true) :
    freshDir P S ((freshEdgeEquiv P S).symm ⟨e.1, e.2.1⟩) = false := by
  simpa [freshDir] using congrArg Bool.not e.2.2

/-- Restrict a dependent product to its nontrivial coordinates. -/
def payloadRestrictEquiv {I : Type*} (F : I → Type*) (pred : I → Prop)
    [DecidablePred pred] (unit : ∀ i, ¬ pred i → Unique (F i)) :
    ((i : I) → F i) ≃ ((i : {i // pred i}) → F i.1) where
  toFun x i := x i.1
  invFun x i := if h : pred i then x ⟨i, h⟩ else (unit i h).default
  left_inv x := by
    funext i
    by_cases h : pred i
    · simp [h]
    · simp only [dif_neg h]
      exact ((unit i h).uniq (x i)).symm
  right_inv x := by
    funext i
    simp [i.2]

def selectedRowPayloadEquiv (q : ℕ) (size : Fin q → ℕ) (dir : Fin q → Bool) :
    MixRowPayload q size dir ≃ ((g : {g : Fin q // dir g = true}) → Fin (size g.1)) :=
  (payloadRestrictEquiv (mixRowCoordType size dir) (fun g => dir g = true)
    (fun g hg => by
      have hd : dir g = false := by cases h : dir g <;> simp_all
      simpa [mixRowCoordType, hd] using (inferInstance : Unique PUnit))).trans
    (Equiv.piCongrRight (fun g => Equiv.cast (by simp [mixRowCoordType, g.2])))

def selectedRowEdgeEquiv :
    {g : Fin (freshCount P S) // freshDir P S g = true} ≃
      EdgeOnSide P.toPartiteShape S false where
  toFun g := ⟨(freshEdgeEquiv P S g.1).1, (freshEdgeEquiv P S g.1).2, by
    have h := g.2
    simpa [freshDir] using h⟩
  invFun e := ⟨(freshEdgeEquiv P S).symm ⟨e.1, e.2.1⟩,
    freshDir_of_rowEdge P S e⟩
  left_inv g := Subtype.ext ((freshEdgeEquiv P S).symm_apply_apply g.1)
  right_inv e := Subtype.ext (congrArg (fun z : FreshEdge P.toPartiteShape S => z.1)
    ((freshEdgeEquiv P S).apply_symm_apply ⟨e.1, e.2.1⟩))

def actualRowFreshPayloadEquiv :
    MixRowPayload (freshCount P S) (freshSize P S dimension) (freshDir P S) ≃
      ActualRowFreshFields P dimension S :=
  (selectedRowPayloadEquiv (freshCount P S) (freshSize P S dimension) (freshDir P S)).trans
    (Equiv.piCongr (selectedRowEdgeEquiv P S)
      (fun g => (freshCoordinateEquiv P S dimension g.1).symm))

def selectedColPayloadEquiv (q : ℕ) (size : Fin q → ℕ) (dir : Fin q → Bool) :
    MixColPayload q size dir ≃ ((g : {g : Fin q // dir g = false}) → Fin (size g.1)) :=
  (payloadRestrictEquiv (mixColCoordType size dir) (fun g => dir g = false)
    (fun g hg => by
      have hd : dir g = true := by cases h : dir g <;> simp_all
      simpa [mixColCoordType, hd] using (inferInstance : Unique PUnit))).trans
    (Equiv.piCongrRight (fun g => Equiv.cast (by simp [mixColCoordType, g.2])))

def selectedColEdgeEquiv :
    {g : Fin (freshCount P S) // freshDir P S g = false} ≃
      EdgeOnSide P.toPartiteShape S true where
  toFun g := ⟨(freshEdgeEquiv P S g.1).1, (freshEdgeEquiv P S g.1).2, by
    have h := g.2
    simpa [freshDir] using h⟩
  invFun e := ⟨(freshEdgeEquiv P S).symm ⟨e.1, e.2.1⟩,
    freshDir_of_colEdge P S e⟩
  left_inv g := Subtype.ext ((freshEdgeEquiv P S).symm_apply_apply g.1)
  right_inv e := Subtype.ext (congrArg (fun z : FreshEdge P.toPartiteShape S => z.1)
    ((freshEdgeEquiv P S).apply_symm_apply ⟨e.1, e.2.1⟩))

def actualColFreshPayloadEquiv :
    MixColPayload (freshCount P S) (freshSize P S dimension) (freshDir P S) ≃
      ActualColFreshFields P dimension S :=
  (selectedColPayloadEquiv (freshCount P S) (freshSize P S dimension) (freshDir P S)).trans
    (Equiv.piCongr (selectedColEdgeEquiv P S)
      (fun g => (freshCoordinateEquiv P S dimension g.1).symm))

/-! ## 5. The actual row/column equivalences and entrywise flatten identity -/

/-- Required semantic row reindexing. -/
def mixedRowAddressEquiv :
    lowerMixedRows (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (PartiteBoundaryRow (G := P.toPartiteShape) dimension) ≃
      RowAddress P S (X dimension) :=
  (lowerMixedRowsPayloadEquiv (freshCount P S) (freshSize P S dimension)
      (freshDir P S) (PartiteBoundaryRow (G := P.toPartiteShape) dimension)).trans
    ((Equiv.prodCongr (actualRowFreshPayloadEquiv P dimension S)
      (boundaryRowOrderedEquiv P dimension)).trans
      (Equiv.prodComm _ _))

/-- Required semantic column reindexing. -/
def mixedColAddressEquiv :
    lowerMixedCols (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ≃
      ColAddress P S (X dimension) :=
  (lowerMixedColsPayloadEquiv (freshCount P S) (freshSize P S dimension)
      (freshDir P S) (PartiteBoundaryCol (G := P.toPartiteShape) dimension)).trans
    ((Equiv.prodCongr (actualColFreshPayloadEquiv P dimension S)
      (boundaryColOrderedEquiv P dimension)).trans
      (Equiv.prodComm _ _))

/-- `Matrix.reindex` expects an equivalence from the OLD address index to
the NEW mixed index.  This is the orientation used in the displayed C2 identity. -/
def actualRowEquiv :
    RowAddress P S (X dimension) ≃
      lowerMixedRows (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (PartiteBoundaryRow (G := P.toPartiteShape) dimension) :=
  (mixedRowAddressEquiv P dimension S).symm

/-- Column reindexing in the `Matrix.reindex` orientation. -/
def actualColEquiv :
    ColAddress P S (X dimension) ≃
      lowerMixedCols (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (PartiteBoundaryCol (G := P.toPartiteShape) dimension) :=
  (mixedColAddressEquiv P dimension S).symm

/-- The row semantic reindex reads exactly the decoded coefficient row address. -/
theorem actualRowEquiv_apply
    (r : lowerMixedRows (freshCount P S) (freshSize P S dimension) (freshDir P S)
      (PartiteBoundaryRow (G := P.toPartiteShape) dimension))
    (c : lowerMixedCols (freshCount P S) (freshSize P S dimension) (freshDir P S)
      (PartiteBoundaryCol (G := P.toPartiteShape) dimension)) :
    (mixedRowAddressEquiv P dimension S) r =
      rowAddressOfIndex P S dimension
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).1
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).2.1 := by
  let dec := lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
    (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c
  apply Prod.ext
  · change boundaryRowOrderedEquiv P dimension
        (lowerMixedRowsPayloadEquiv (freshCount P S) (freshSize P S dimension)
          (freshDir P S) (PartiteBoundaryRow (G := P.toPartiteShape) dimension) r).2 =
      orderedRowOfBoundary P dimension dec.2.1
    rw [boundaryRowOrderedEquiv_apply]
    exact congrArg (orderedRowOfBoundary P dimension)
      (lowerMixedRowsPayload_base (freshCount P S) (freshSize P S dimension) (freshDir P S) r c)
  · funext e
    change actualRowFreshPayloadEquiv P dimension S
        (lowerMixedRowsPayloadEquiv (freshCount P S) (freshSize P S dimension)
          (freshDir P S) (PartiteBoundaryRow (G := P.toPartiteShape) dimension) r).1 e =
      freshAddressOfIndex P S dimension dec.1 ⟨e.1, e.2.1⟩
    obtain ⟨g, rfl⟩ := (selectedRowEdgeEquiv P S).surjective e
    have hc := lowerMixedRowsPayload_coord (freshCount P S) (freshSize P S dimension)
      (freshDir P S) r c g.1 g.2
    simp only [actualRowFreshPayloadEquiv, Equiv.trans_apply, Equiv.piCongr_apply_apply]
    change (freshCoordinateEquiv P S dimension g.1).symm
        (selectedRowPayloadEquiv (freshCount P S) (freshSize P S dimension) (freshDir P S)
          (lowerMixedRowsPayloadEquiv (freshCount P S) (freshSize P S dimension)
            (freshDir P S) (PartiteBoundaryRow (G := P.toPartiteShape) dimension) r).1 g) =
      freshIndexAddressEquiv P S dimension dec.1 (freshEdgeEquiv P S g.1)
    rw [freshIndexAddressEquiv, Equiv.piCongr_apply_apply]
    congr 1

/-- Column semantic reindex analogue. -/
theorem actualColEquiv_apply
    (r : lowerMixedRows (freshCount P S) (freshSize P S dimension) (freshDir P S)
      (PartiteBoundaryRow (G := P.toPartiteShape) dimension))
    (c : lowerMixedCols (freshCount P S) (freshSize P S dimension) (freshDir P S)
      (PartiteBoundaryCol (G := P.toPartiteShape) dimension)) :
    (mixedColAddressEquiv P dimension S) c =
      colAddressOfIndex P S dimension
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).1
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).2.2 := by
  let dec := lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
    (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c
  apply Prod.ext
  · change boundaryColOrderedEquiv P dimension
        (lowerMixedColsPayloadEquiv (freshCount P S) (freshSize P S dimension)
          (freshDir P S) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) c).2 =
      orderedColOfBoundary P dimension dec.2.2
    rw [boundaryColOrderedEquiv_apply]
    exact congrArg (orderedColOfBoundary P dimension)
      (lowerMixedColsPayload_base (freshCount P S) (freshSize P S dimension) (freshDir P S) r c)
  · funext e
    change actualColFreshPayloadEquiv P dimension S
        (lowerMixedColsPayloadEquiv (freshCount P S) (freshSize P S dimension)
          (freshDir P S) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) c).1 e =
      freshAddressOfIndex P S dimension dec.1 ⟨e.1, e.2.1⟩
    obtain ⟨g, rfl⟩ := (selectedColEdgeEquiv P S).surjective e
    have hc := lowerMixedColsPayload_coord (freshCount P S) (freshSize P S dimension)
      (freshDir P S) r c g.1 g.2
    simp only [actualColFreshPayloadEquiv, Equiv.trans_apply, Equiv.piCongr_apply_apply]
    change (freshCoordinateEquiv P S dimension g.1).symm
        (selectedColPayloadEquiv (freshCount P S) (freshSize P S dimension) (freshDir P S)
          (lowerMixedColsPayloadEquiv (freshCount P S) (freshSize P S dimension)
            (freshDir P S) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) c).1 g) =
      freshIndexAddressEquiv P S dimension dec.1 (freshEdgeEquiv P S g.1)
    rw [freshIndexAddressEquiv, Equiv.piCongr_apply_apply]
    congr 1

/-- C1: the actual mixed flattening is entrywise the retained-address
coefficient matrix after the semantic row/column reindexing. -/
theorem lowerMixedFlatten_actual_reindex
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    lowerMixedFlatten (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (actualCoefficientFamily P S dimension ω) =
      Matrix.reindex (actualRowEquiv P dimension S) (actualColEquiv P dimension S)
        (C1C2.retainedAddressCoefficient P S (X dimension)
          (c1c2ActualWeight P S dimension ω)) := by
  funext r c
  rw [lowerMixedFlatten_apply]
  simp only [Matrix.reindex_apply]
  unfold actualCoefficientFamily
  have hr : (actualRowEquiv P dimension S).symm r =
      rowAddressOfIndex P S dimension
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).1
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).2.1 := by
    simpa [actualRowEquiv] using actualRowEquiv_apply P dimension S r c
  have hc : (actualColEquiv P dimension S).symm c =
      colAddressOfIndex P S dimension
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).1
        (lowerMixDecodeD (freshCount P S) (freshSize P S dimension)
          (lowerMixDirOfFn (freshCount P S) (freshDir P S)) r c).2.2 := by
    simpa [actualColEquiv] using actualColEquiv_apply P dimension S r c
  simpa only [Matrix.submatrix_apply, hr, hc]

/-- C2: the missing `hReindexNorm` is now a theorem, obtained from the actual
entrywise reindex and the native Euclidean L2-operator reindex isometry. -/
theorem actual_mixed_reindex_norm
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    ‖lowerMixedFlatten (freshCount P S) (freshSize P S dimension) (freshDir P S)
        (actualCoefficientFamily P S dimension ω)‖ =
      @norm (Matrix (RowAddress P S (X dimension)) (ColAddress P S (X dimension)) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm
        (C1C2.retainedAddressCoefficient P S (X dimension) (c1c2ActualWeight P S dimension ω)) := by
  rw [lowerMixedFlatten_actual_reindex P dimension S ω]
  exact paper_l2_opNorm_reindex (actualRowEquiv P dimension S)
    (actualColEquiv P dimension S)
    (C1C2.retainedAddressCoefficient P S (X dimension)
      (c1c2ActualWeight P S dimension ω))

#print axioms lowerMixedRowsPayloadEquiv
#print axioms lowerMixedColsPayloadEquiv
#print axioms actualRowEquiv
#print axioms actualColEquiv
#print axioms lowerMixedFlatten_actual_reindex
#print axioms actual_mixed_reindex_norm

end GraphMatrixReplica.PaperR16.C2Actual



