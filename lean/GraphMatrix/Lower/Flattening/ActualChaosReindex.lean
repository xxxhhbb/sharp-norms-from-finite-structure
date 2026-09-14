import GraphMatrix.Lower.Flattening.AllSeparatorContraction
import GraphMatrix.Model.SeparatorAddressReindex
import GraphMatrix.Model.LowerStackingMixed
import GraphMatrix.PartiteBoundaryMatrixTrace

/-!
# actual fresh-edge chaos coordinates

This module fixes the concrete finite enumeration of the *actual* fresh edge
occurrences and their typed rectangular coordinates.  It also gives the exact
conversion between C1/separator assignments and the cut-role assignment
used by the all-separator contraction.

The matrix-valued coefficient family below is not arbitrary: each coefficient
is the already-proved `retainedAddressCoefficient`, evaluated at the ordered
boundary fields and at the genuine fresh-edge coordinate selected by the
heterogeneous index.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model.C2Actual

open GraphMatrixReplica
open GraphMatrixReplica.P2a
open GraphMatrixReplica.Model
open GraphMatrixReplica.Model.ActualPrimitiveObservations

attribute [local instance] Classical.propDecidable

variable (P : PaperShape) (S : Finset (Fin P.roles))
variable (dimension : Fin P.roles → ℕ)

abbrev X {n : ℕ} (d : Fin n → ℕ) := fun v : Fin n => Fin (d v)

/-- Restrict an actual retained-role assignment to the genuine separator. -/
def retainedCutAssignment
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension) : CutAssignment (G := P.toPartiteShape) S dimension :=
  fun u => a ⟨u.1, cut_subset_retainedRoles P.toPartiteShape S u.2⟩

/-- Convert the C1/separator subtype back to the original cut-role subtype. -/
def c1c2ToCutAssignment
    (s : C1C2.SeparatorAssignment P S (X dimension)) : CutAssignment (G := P.toPartiteShape) S dimension :=
  fun u => s ⟨⟨u.1, cut_subset_retainedRoles P.toPartiteShape S u.2⟩, by
    classical
    simp [C1C2.separator, u.2]⟩

/-- Convert an original cut-role assignment to C1/C2's retained separator
assignment. -/
def cutToC1C2Assignment
    (s : CutAssignment (G := P.toPartiteShape) S dimension) :
    C1C2.SeparatorAssignment P S (X dimension) :=
  fun u => s ⟨u.1.1, by
    classical
    simpa [C1C2.separator] using (Finset.mem_filter.mp u.2).2⟩

@[simp] theorem c1c2ToCut_cutToC1C2
    (s : CutAssignment (G := P.toPartiteShape) S dimension) :
    c1c2ToCutAssignment P S dimension (cutToC1C2Assignment P S dimension s) = s := by
  funext u
  rfl

@[simp] theorem cutToC1C2_c1c2ToCut
    (s : C1C2.SeparatorAssignment P S (X dimension)) :
    cutToC1C2Assignment P S dimension (c1c2ToCutAssignment P S dimension s) = s := by
  funext u
  rfl

/-- The exact weight expected by the existing C1/assignment-sum theorem. -/
def c1c2ActualWeight (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    C1C2.SeparatorAssignment P S (X dimension) → ℝ :=
  fun s => actualWeight (G := P.toPartiteShape) S dimension ω (c1c2ToCutAssignment P S dimension s)

@[simp] theorem c1c2ActualWeight_cut
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) (s : CutAssignment (G := P.toPartiteShape) S dimension) :
    c1c2ActualWeight P S dimension ω (cutToC1C2Assignment P S dimension s) =
      actualWeight (G := P.toPartiteShape) S dimension ω s := by
  simp [c1c2ActualWeight]

/-- Number of genuine fresh original edge occurrences. -/
abbrev freshCount : ℕ :=
  Fintype.card (FreshEdge P.toPartiteShape S)

/-- Canonical finite enumeration of genuine fresh edge IDs. -/
def freshEdgeEquiv : Fin (freshCount P S) ≃ FreshEdge P.toPartiteShape S :=
  (Fintype.equivFin (FreshEdge P.toPartiteShape S)).symm

/-- Heterogeneous size of one genuine fresh rectangular edge array. -/
def freshSize (g : Fin (freshCount P S)) : ℕ :=
  Fintype.card (EdgeSignCoordinate dimension (freshEdgeEquiv P S g).1)

/-- No common role dimension is introduced: each fresh rectangular coordinate
is independently encoded by a `Fin` of its own actual cardinality. -/
def freshCoordinateEquiv (g : Fin (freshCount P S)) :
    EdgeSignCoordinate dimension (freshEdgeEquiv P S g).1 ≃
      Fin (freshSize P S dimension g) :=
  Fintype.equivFin (EdgeSignCoordinate dimension (freshEdgeEquiv P S g).1)

/-- Exact reindexing of all genuine fresh coordinates. -/
def freshIndexAddressEquiv :
    lowerHeteroIndex (freshCount P S) (freshSize P S dimension) ≃
      ((e : FreshEdge P.toPartiteShape S) → EdgeSignCoordinate dimension e.1) :=
  Equiv.piCongr (freshEdgeEquiv P S)
    (fun g => (freshCoordinateEquiv P S dimension g).symm)

/-- Decode an index using the actual edge enumeration and coordinate equivalences. -/
def freshAddressOfIndex
    (j : lowerHeteroIndex (freshCount P S) (freshSize P S dimension))
    (e : FreshEdge P.toPartiteShape S) : EdgeSignCoordinate dimension e.1 :=
  freshIndexAddressEquiv P S dimension j e

/-- Reindex the actual independent sign arrays without adding or dropping coordinates. -/
def freshSampleNoiseEquiv :
    FreshSample (G := P.toPartiteShape) S dimension ≃
      lowerHeteroNoise (freshCount P S) (freshSize P S dimension) :=
  (Equiv.piCongr (freshEdgeEquiv P S)
    (fun g => Equiv.arrowCongr (freshCoordinateEquiv P S dimension g).symm
      (Equiv.refl Bool))).symm

/-- The required Boolean reversal: `edgeSide=false` is a row edge, whereas
`lowerMixedFlatten` uses `dir=true` for row stacking. -/
def freshDir (g : Fin (freshCount P S)) : Bool :=
  !(edgeSide P.toPartiteShape S (freshEdgeEquiv P S g).1)

/-- Read an original `PartiteBoundaryRow` in the paper's ordered left slots. -/
def orderedRowOfBoundary (r : PartiteBoundaryRow (G := P.toPartiteShape) dimension) :
    (i : Fin P.leftSize) → Fin (dimension (P.left i)) :=
  fun i => r ⟨P.left i, by
    change P.left i ∈ P.leftBoundaryFinset
    exact (P.mem_leftBoundaryFinset_iff (P.left i)).2 ⟨i, rfl⟩⟩

/-- Ordered right-boundary analogue. -/
def orderedColOfBoundary (c : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    (i : Fin P.rightSize) → Fin (dimension (P.right i)) :=
  fun i => c ⟨P.right i, by
    change P.right i ∈ P.rightBoundaryFinset
    exact (P.mem_rightBoundaryFinset_iff (P.right i)).2 ⟨i, rfl⟩⟩

/-- Actual row address selected by a fresh multi-index and an original
boundary row.  Only C1-row-side fresh edges are read. -/
def rowAddressOfIndex
    (j : lowerHeteroIndex (freshCount P S) (freshSize P S dimension))
    (r : PartiteBoundaryRow (G := P.toPartiteShape) dimension) :
    RowAddress P S (X dimension) :=
  ⟨orderedRowOfBoundary P dimension r,
    fun e => freshAddressOfIndex P S dimension j ⟨e.1, e.2.1⟩⟩

/-- Actual column address selected by the same complete fresh multi-index. -/
def colAddressOfIndex
    (j : lowerHeteroIndex (freshCount P S) (freshSize P S dimension))
    (c : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    ColAddress P S (X dimension) :=
  ⟨orderedColOfBoundary P dimension c,
    fun e => freshAddressOfIndex P S dimension j ⟨e.1, e.2.1⟩⟩


/-- Direct retained row address: ordered left boundary slots plus the two endpoint
labels of every actual row-side fresh edge. -/
def directRetainedRowAddress (a : RetainedAssignment (G := P.toPartiteShape) S dimension) :
    RowAddress P S (X dimension) :=
  ⟨fun i => a ⟨P.left i,
      leftBoundary_subset_retainedRoles P.toPartiteShape S
        ((P.mem_leftBoundaryFinset_iff (P.left i)).2 ⟨i, rfl⟩)⟩,
    fun e =>
      (a ⟨P.source e.1, e.2.1.1⟩, a ⟨P.target e.1, e.2.1.2⟩)⟩

/-- Direct retained column address. -/
def directRetainedColAddress (a : RetainedAssignment (G := P.toPartiteShape) S dimension) :
    ColAddress P S (X dimension) :=
  ⟨fun i => a ⟨P.right i,
      rightBoundary_subset_retainedRoles P.toPartiteShape S
        ((P.mem_rightBoundaryFinset_iff (P.right i)).2 ⟨i, rfl⟩)⟩,
    fun e =>
      (a ⟨P.source e.1, e.2.1.1⟩, a ⟨P.target e.1, e.2.1.2⟩)⟩

/-- The direct address is definitionally the same data as the current formal C1/C2
address bridge; differences in membership proofs are irrelevant. -/
theorem retainedRowAddress_eq_direct (a : RetainedAssignment (G := P.toPartiteShape) S dimension) :
    C1C2.retainedRowAddress P S (X dimension) a =
      directRetainedRowAddress P S dimension a := by
  rfl

theorem retainedColAddress_eq_direct (a : RetainedAssignment (G := P.toPartiteShape) S dimension) :
    C1C2.retainedColAddress P S (X dimension) a =
      directRetainedColAddress P S dimension a := by
  rfl

/-- The original boundary compatibility predicate rewritten on the retained
assignment.  Boundary roles are retained by the already-proved geometry. -/
def retainedBoundaryCompatible
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) : Prop :=
  (∀ v : {v : Fin P.roles // v ∈ P.toPartiteShape.leftBoundary},
      a ⟨v.1, leftBoundary_subset_retainedRoles P.toPartiteShape S v.2⟩ = row v) ∧
  (∀ v : {v : Fin P.roles // v ∈ P.toPartiteShape.rightBoundary},
      a ⟨v.1, rightBoundary_subset_retainedRoles P.toPartiteShape S v.2⟩ = col v)

instance retainedBoundaryCompatibleDecidable
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    Decidable (retainedBoundaryCompatible P S dimension a row col) := inferInstance


/-- Set-indexed boundary compatibility is equivalent to compatibility on the
paper's original ordered boundary slots. -/
theorem retainedBoundaryCompatible_iff_ordered
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    retainedBoundaryCompatible P S dimension a row col ↔
      ((∀ i : Fin P.leftSize,
          (directRetainedRowAddress P S dimension a).1 i =
            orderedRowOfBoundary P dimension row i) ∧
       (∀ i : Fin P.rightSize,
          (directRetainedColAddress P S dimension a).1 i =
            orderedColOfBoundary P dimension col i)) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [directRetainedRowAddress, orderedRowOfBoundary] using
        h.1 ⟨P.left i, (P.mem_leftBoundaryFinset_iff (P.left i)).2 ⟨i, rfl⟩⟩
    · intro i
      simpa [directRetainedColAddress, orderedColOfBoundary] using
        h.2 ⟨P.right i, (P.mem_rightBoundaryFinset_iff (P.right i)).2 ⟨i, rfl⟩⟩
  · rintro ⟨hL, hR⟩
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨i, hi⟩ := (P.mem_leftBoundaryFinset_iff v).1 hv
      subst v
      simpa [directRetainedRowAddress, orderedRowOfBoundary] using hL i
    · rintro ⟨v, hv⟩
      obtain ⟨i, hi⟩ := (P.mem_rightBoundaryFinset_iff v).1 hv
      subst v
      simpa [directRetainedColAddress, orderedColOfBoundary] using hR i

/-- Original compatibility is determined entirely by the retained half of the
full-assignment equivalence. -/
theorem partiteBoundaryEntryCompatible_iff_retained
    (φ : PartiteRoleAssignment (G := P.toPartiteShape) dimension)
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    partiteBoundaryEntryCompatible φ row col ↔
      retainedBoundaryCompatible P S dimension
        (fullAssignmentEquiv (G := P.toPartiteShape) S dimension φ).1 row col := by
  constructor
  · intro h
    constructor
    · intro v
      exact h.1 v
    · intro v
      exact h.2 v
  · intro h
    constructor
    · intro v
      exact h.1 v
    · intro v
      exact h.2 v

/-- Exact partition of the original edge-ID type into genuine fresh and
nonfresh occurrences. -/
def edgeFreshSplitEquiv :
    Fin P.edges ≃ Sum (FreshEdge P.toPartiteShape S) (NonfreshEdge (G := P.toPartiteShape) S) where
  toFun e := by
    classical
    by_cases h : Fresh P.toPartiteShape S e
    · exact Sum.inl ⟨e, h⟩
    · exact Sum.inr ⟨e, h⟩
  invFun z := Sum.elim Subtype.val Subtype.val z
  left_inv e := by
    classical
    by_cases h : Fresh P.toPartiteShape S e <;> simp [h]
  right_inv z := by
    classical
    rcases z with e | e
    · simp [e.2]
    · simp [e.2]

/-- A retained assignment reads the separator through the same proof-irrelevant
subtype as `retainedCutAssignment`. -/
@[simp] theorem retainedCutAssignment_apply
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension) (u : SeparatorRole P.toPartiteShape S) :
    retainedCutAssignment P S dimension a u =
      a ⟨u.1, cut_subset_retainedRoles P.toPartiteShape S u.2⟩ := rfl

/-- Fresh-edge sign product selected by one retained assignment. -/
def retainedFreshMonomial
    (ξ : FreshSample (G := P.toPartiteShape) S dimension) (a : RetainedAssignment (G := P.toPartiteShape) S dimension) : ℝ :=
  ∏ e : FreshEdge P.toPartiteShape S,
    (rademacherSign
      (ξ e
        (a ⟨P.source e.1, e.2.1⟩,
         a ⟨P.target e.1, e.2.2⟩)) : ℝ)


/-- The complete fresh coordinate choice determined by one retained assignment. -/
def freshIndexOfAssignment
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension) :
    lowerHeteroIndex (freshCount P S) (freshSize P S dimension) :=
  fun g =>
    freshCoordinateEquiv P S dimension g
      (a ⟨P.source (freshEdgeEquiv P S g).1, (freshEdgeEquiv P S g).2.1⟩,
       a ⟨P.target (freshEdgeEquiv P S g).1, (freshEdgeEquiv P S g).2.2⟩)

/-- Decoding the coordinate selected by `freshIndexOfAssignment` recovers the
actual source/target labels of the retained assignment. -/
@[simp] theorem freshAddressOfIndex_assignment
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (e : FreshEdge P.toPartiteShape S) :
    freshAddressOfIndex P S dimension (freshIndexOfAssignment P S dimension a) e =
      (a ⟨P.source e.1, e.2.1⟩, a ⟨P.target e.1, e.2.2⟩) := by
  classical
  obtain ⟨g, rfl⟩ := (freshEdgeEquiv P S).surjective e
  simp [freshAddressOfIndex, freshIndexAddressEquiv, freshIndexOfAssignment]


/-- There is exactly one heterogeneous multi-index whose fresh typed address is
that induced by a fixed retained assignment. -/
theorem freshAddress_matches_iff
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (j : lowerHeteroIndex (freshCount P S) (freshSize P S dimension)) :
    (∀ e : FreshEdge P.toPartiteShape S,
      freshAddressOfIndex P S dimension j e =
        (a ⟨P.source e.1, e.2.1⟩, a ⟨P.target e.1, e.2.2⟩)) ↔
      j = freshIndexOfAssignment P S dimension a := by
  constructor
  · intro h
    apply (freshIndexAddressEquiv P S dimension).injective
    funext e
    exact (h e).trans (freshAddressOfIndex_assignment P S dimension a e).symm
  · intro h
    subst j
    exact freshAddressOfIndex_assignment P S dimension a


/- Matching both actual primitive addresses is exactly boundary compatibility
plus the unique complete fresh coordinate choice.  The proof uses the required
side convention `edgeSide=false` on rows and `edgeSide=true` on columns. -/
/-- Matrix-valued coefficient family obtained from the actual retained
assignment expansion and the actual all-separator component weight. -/
def actualCoefficientFamily (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    lowerHeteroIndex (freshCount P S) (freshSize P S dimension) →
      Matrix (PartiteBoundaryRow (G := P.toPartiteShape) dimension) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ℝ :=
  fun j r c =>
    C1C2.retainedAddressCoefficient P S (X dimension)
      (c1c2ActualWeight P S dimension ω)
      (rowAddressOfIndex P S dimension j r)
      (colAddressOfIndex P S dimension j c)

theorem retainedAddresses_match_iff
    (a : RetainedAssignment (G := P.toPartiteShape) S dimension)
    (j : lowerHeteroIndex (freshCount P S) (freshSize P S dimension))
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    (C1C2.retainedRowAddress P S (X dimension) a =
        rowAddressOfIndex P S dimension j row ∧
     C1C2.retainedColAddress P S (X dimension) a =
        colAddressOfIndex P S dimension j col) ↔
      (retainedBoundaryCompatible P S dimension a row col ∧
        j = freshIndexOfAssignment P S dimension a) := by
  classical
  constructor
  · rintro ⟨hr, hc⟩
    rw [retainedRowAddress_eq_direct P S dimension a] at hr
    rw [retainedColAddress_eq_direct P S dimension a] at hc
    have hL : ∀ i : Fin P.leftSize,
        (directRetainedRowAddress P S dimension a).1 i =
          orderedRowOfBoundary P dimension row i := by
      intro i
      exact congrFun (congrArg Prod.fst hr) i
    have hR : ∀ i : Fin P.rightSize,
        (directRetainedColAddress P S dimension a).1 i =
          orderedColOfBoundary P dimension col i := by
      intro i
      exact congrFun (congrArg Prod.fst hc) i
    have hBoundary : retainedBoundaryCompatible P S dimension a row col :=
      (retainedBoundaryCompatible_iff_ordered P S dimension a row col).2 ⟨hL, hR⟩
    have hFresh : ∀ e : FreshEdge P.toPartiteShape S,
        freshAddressOfIndex P S dimension j e =
          (a ⟨P.source e.1, e.2.1⟩, a ⟨P.target e.1, e.2.2⟩) := by
      intro e
      cases hs : edgeSide P.toPartiteShape S e.1 with
      | false =>
          let er : EdgeOnSide P.toPartiteShape S false := ⟨e.1, e.2, hs⟩
          have hp := congrFun (congrArg Prod.snd hr) er
          exact hp.symm
      | true =>
          let ec : EdgeOnSide P.toPartiteShape S true := ⟨e.1, e.2, hs⟩
          have hp := congrFun (congrArg Prod.snd hc) ec
          exact hp.symm
    exact ⟨hBoundary, (freshAddress_matches_iff P S dimension a j).1 hFresh⟩
  · rintro ⟨hBoundary, hj⟩
    subst j
    rw [retainedRowAddress_eq_direct P S dimension a,
      retainedColAddress_eq_direct P S dimension a]
    have hOrdered := (retainedBoundaryCompatible_iff_ordered
      P S dimension a row col).1 hBoundary
    constructor
    · apply Prod.ext
      · funext i
        exact hOrdered.1 i
      · funext e
        symm
        exact freshAddressOfIndex_assignment P S dimension a ⟨e.1, e.2.1⟩
    · apply Prod.ext
      · funext i
        exact hOrdered.2 i
      · funext e
        symm
        exact freshAddressOfIndex_assignment P S dimension a ⟨e.1, e.2.1⟩

/-- Consequently the actual coefficient family has exactly one surviving fresh
multi-index for each retained assignment; there is no multiplicity. -/
theorem actualCoefficientFamily_entry
    (ω : FrozenSample (G := P.toPartiteShape) S dimension)
    (j : lowerHeteroIndex (freshCount P S) (freshSize P S dimension))
    (row : PartiteBoundaryRow (G := P.toPartiteShape) dimension) (col : PartiteBoundaryCol (G := P.toPartiteShape) dimension) :
    actualCoefficientFamily P S dimension ω j row col =
      ∑ a : RetainedAssignment (G := P.toPartiteShape) S dimension,
        if retainedBoundaryCompatible P S dimension a row col ∧
            j = freshIndexOfAssignment P S dimension a then
          actualWeight (G := P.toPartiteShape) S dimension ω (retainedCutAssignment P S dimension a)
        else 0 := by
  classical
  unfold actualCoefficientFamily C1C2.retainedAddressCoefficient
  apply Finset.sum_congr
  · ext a
    simp
  intro a _ha
  simp only [retainedAddresses_match_iff P S dimension a j row col]
  by_cases h : retainedBoundaryCompatible P S dimension a row col ∧
      j = freshIndexOfAssignment P S dimension a
  · simp [h, c1c2ActualWeight, c1c2ToCutAssignment, retainedCutAssignment,
      C1C2.separator]
    rfl
  · simp [h]


/-- Entrywise closed form of the recursive heterogeneous chaos: one sum over a
complete coordinate choice, weighted by the product of its actual Rademacher
signs. -/
theorem lowerHeteroChaos_apply_eq_sum
    (q : ℕ) (size : Fin q → ℕ)
    {ι κ : Type*}
    (A : lowerHeteroIndex q size → Matrix ι κ ℝ)
    (w : lowerHeteroNoise q size) (r : ι) (c : κ) :
    lowerHeteroChaos q size A w r c =
      ∑ j : lowerHeteroIndex q size,
        (∏ g : Fin q, (rademacherSign (w g (j g)) : ℝ)) * A j r c := by
  classical
  induction q with
  | zero =>
      simp [lowerHeteroChaos]
      exact congrArg (fun j => A j r c) (Subsingleton.elim _ _)
  | succ q ih =>
      let tailSize : Fin q → ℕ := fun g => size g.succ
      let tailA : Fin (size 0) → lowerHeteroIndex q tailSize → Matrix ι κ ℝ :=
        fun e tail => A (Fin.cons e tail)
      let tailW : lowerHeteroNoise q tailSize := fun g => w g.succ
      change (∑ e : Fin (size 0),
        (if w 0 e then (-1 : ℝ) else 1) *
          lowerHeteroChaos q tailSize (tailA e) tailW r c) = _
      simp_rw [ih]
      have hsign : ∀ e : Fin (size 0),
          (if w 0 e then (-1 : ℝ) else 1) =
            (rademacherSign (w 0 e) : ℝ) := by
        intro e
        cases h : w 0 e <;> simp [h, rademacherSign]
      simp_rw [hsign]
      -- Distribute the head sign over the recursively expanded tail sum.
      simp_rw [Finset.mul_sum]
      dsimp [tailA, tailW, tailSize]
      let E := Fin.consEquiv (fun g : Fin (q + 1) => Fin (size g))
      let f : lowerHeteroIndex (q + 1) size → ℝ :=
        fun j => (∏ g : Fin (q + 1), (rademacherSign (w g (j g)) : ℝ)) * A j r c
      calc
        _ = ∑ p : Fin (size 0) × lowerHeteroIndex q tailSize, f (E p) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro e _
          apply Finset.sum_congr rfl
          intro j _
          simp [f, E, Fin.prod_univ_succ, mul_assoc]
          exact Or.inl (Or.inl rfl)
        _ = _ := Equiv.sum_comp E f

/-- Product of heterogeneous chaos signs at the assignment-selected index is
exactly the product over the genuine fresh edge arrays. -/
theorem freshSignProduct_assignment
    (ξ : FreshSample (G := P.toPartiteShape) S dimension) (a : RetainedAssignment (G := P.toPartiteShape) S dimension) :
    (∏ g : Fin (freshCount P S),
      (rademacherSign
        (freshSampleNoiseEquiv P S dimension ξ g
          (freshIndexOfAssignment P S dimension a g)) : ℝ)) =
      retainedFreshMonomial P S dimension ξ a := by
  classical
  unfold retainedFreshMonomial
  apply Fintype.prod_equiv (freshEdgeEquiv P S)
  intro g
  simp [freshSampleNoiseEquiv, freshIndexOfAssignment, freshCoordinateEquiv]

/-- Actual fresh sample converted to lower-chaos noise reads precisely the
same sign coordinate selected by a multi-index. -/
theorem freshSampleNoise_apply
    (ξ : FreshSample (G := P.toPartiteShape) S dimension)
    (g : Fin (freshCount P S))
    (k : Fin (freshSize P S dimension g)) :
    freshSampleNoiseEquiv P S dimension ξ g k =
      ξ (freshEdgeEquiv P S g)
        ((freshCoordinateEquiv P S dimension g).symm k) := rfl


end GraphMatrixReplica.Model.C2Actual
