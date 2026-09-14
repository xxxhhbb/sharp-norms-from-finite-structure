import GraphMatrix.NearlyCombinatorialModel
import GraphMatrix.CoordinateSupportCount
import GraphMatrix.Formula21SchurBridge

/-! # Coordinate support of a nearly-combinatorial flattening

This file isolates the deterministic support-counting step behind formula
(21).  A row and a column are restrictions of the *same* full assignment.
On the active support of the bounded weight, the two restrictions are assumed
to determine that assignment jointly.  Thus a matrix entry contains at most
one active summand.  Nonzero columns in a fixed row (and dually nonzero rows
in a fixed column) inject into compatible full assignments, which are counted
by the complementary coordinates.

The joint-determination hypothesis is explicit.  In particular, this module
does not assert a decoupling or a noncommutative Khintchine estimate, and it
does not silently identify the original boundary matrix with a later paper
flattening whose coordinate sets have not yet been instantiated.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Tuples carried by a selected finite set of role coordinates. -/
abbrev PaperVisibleTuple
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (visible : Finset α) :=
  {x : α // x ∈ visible} → Fin n

/-- Restrict a full assignment to the coordinates visible on one side of a
flattening. -/
def paperAssignmentRestriction
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (visible : Finset α) (assignment : α → Fin n) :
    PaperVisibleTuple n visible :=
  fun x => assignment x.1

/-- Generic faithful data for a nearly-combinatorial coordinate flattening.
Only active (nonzero-weight) assignments must be determined by their paired
row and column coordinates. -/
structure PaperNearlyCombinatorialFlatteningData
    (α : Type*) [Fintype α] [DecidableEq α]
    (n : ℕ) (rowRoles colRoles : Finset α) where
  weight : (α → Fin n) → ℝ
  weight_abs_le_one : ∀ assignment, |weight assignment| ≤ 1
  active_jointly_injective :
    ∀ {a b : α → Fin n},
      weight a ≠ 0 → weight b ≠ 0 →
      paperAssignmentRestriction rowRoles a =
          paperAssignmentRestriction rowRoles b →
      paperAssignmentRestriction colRoles a =
          paperAssignmentRestriction colRoles b →
      a = b

/-- The matrix obtained by placing every bounded assignment weight at the
pair of visible coordinate tuples selected by the flattening. -/
def PaperNearlyCombinatorialFlatteningData.matrix
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles) :
    Matrix (PaperVisibleTuple n rowRoles)
      (PaperVisibleTuple n colRoles) ℝ := by
  classical
  exact fun row col =>
    ∑ assignment : α → Fin n,
      if paperAssignmentRestriction rowRoles assignment = row ∧
          paperAssignmentRestriction colRoles assignment = col then
        D.weight assignment
      else
        0

/-- A nonzero entry has an active full-assignment witness with exactly the
prescribed row and column coordinates. -/
theorem PaperNearlyCombinatorialFlatteningData.exists_active_assignment_of_ne_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles)
    (col : PaperVisibleTuple n colRoles)
    (hEntry : D.matrix row col ≠ 0) :
    ∃ assignment : α → Fin n,
      D.weight assignment ≠ 0 ∧
      paperAssignmentRestriction rowRoles assignment = row ∧
      paperAssignmentRestriction colRoles assignment = col := by
  classical
  by_contra h
  push Not at h
  apply hEntry
  unfold PaperNearlyCombinatorialFlatteningData.matrix
  apply Finset.sum_eq_zero
  intro assignment _
  by_cases hMatch :
      paperAssignmentRestriction rowRoles assignment = row ∧
        paperAssignmentRestriction colRoles assignment = col
  · simp only [if_pos hMatch]
    by_contra hWeight
    exact h assignment hWeight hMatch.1 hMatch.2
  · simp [hMatch]

/-- The assignment witnessing a nonzero entry. -/
def PaperNearlyCombinatorialFlatteningData.activeAssignment
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles)
    (col : PaperVisibleTuple n colRoles)
    (hEntry : D.matrix row col ≠ 0) : α → Fin n :=
  Classical.choose (D.exists_active_assignment_of_ne_zero row col hEntry)

theorem PaperNearlyCombinatorialFlatteningData.activeAssignment_weight_ne_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles)
    (col : PaperVisibleTuple n colRoles)
    (hEntry : D.matrix row col ≠ 0) :
    D.weight (D.activeAssignment row col hEntry) ≠ 0 :=
  (Classical.choose_spec
    (D.exists_active_assignment_of_ne_zero row col hEntry)).1

theorem PaperNearlyCombinatorialFlatteningData.activeAssignment_row
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles)
    (col : PaperVisibleTuple n colRoles)
    (hEntry : D.matrix row col ≠ 0) :
    paperAssignmentRestriction rowRoles
        (D.activeAssignment row col hEntry) = row :=
  (Classical.choose_spec
    (D.exists_active_assignment_of_ne_zero row col hEntry)).2.1

theorem PaperNearlyCombinatorialFlatteningData.activeAssignment_col
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles)
    (col : PaperVisibleTuple n colRoles)
    (hEntry : D.matrix row col ≠ 0) :
    paperAssignmentRestriction colRoles
        (D.activeAssignment row col hEntry) = col :=
  (Classical.choose_spec
    (D.exists_active_assignment_of_ne_zero row col hEntry)).2.2

/-- Joint determination makes the entry equal to its unique active weight;
hence every entry inherits the weight's `ℓ∞` bound. -/
theorem PaperNearlyCombinatorialFlatteningData.abs_matrix_apply_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles)
    (col : PaperVisibleTuple n colRoles) :
    |D.matrix row col| ≤ 1 := by
  classical
  by_cases hEntry : D.matrix row col = 0
  · simp [hEntry]
  · let a₀ := D.activeAssignment row col hEntry
    have ha₀w : D.weight a₀ ≠ 0 :=
      D.activeAssignment_weight_ne_zero row col hEntry
    have ha₀row : paperAssignmentRestriction rowRoles a₀ = row :=
      D.activeAssignment_row row col hEntry
    have ha₀col : paperAssignmentRestriction colRoles a₀ = col :=
      D.activeAssignment_col row col hEntry
    have hMatrix : D.matrix row col = D.weight a₀ := by
      unfold PaperNearlyCombinatorialFlatteningData.matrix
      rw [Finset.sum_eq_single a₀]
      · simp [ha₀row, ha₀col]
      · intro b _ hb
        by_cases hbMatch :
            paperAssignmentRestriction rowRoles b = row ∧
              paperAssignmentRestriction colRoles b = col
        · have hbw : D.weight b = 0 := by
            by_contra hbw
            have hba : b = a₀ := D.active_jointly_injective hbw ha₀w
              (hbMatch.1.trans ha₀row.symm)
              (hbMatch.2.trans ha₀col.symm)
            exact hb hba
          simp [hbMatch, hbw]
        · simp [hbMatch]
      · simp
    rw [hMatrix]
    exact D.weight_abs_le_one a₀

/-- Encode every nonzero column in a fixed row by its unique active full
assignment, viewed as a constrained completion of that row tuple. -/
def PaperNearlyCombinatorialFlatteningData.rowSupportCompletion
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles) :
    {col : PaperVisibleTuple n colRoles //
      col ∈ matrixRowSupport D.matrix row} →
      CoordinateCompletion n rowRoles row (fun a => D.weight a ≠ 0) :=
  fun col => by
    have hEntry : D.matrix row col.1 ≠ 0 := by
      simpa [matrixRowSupport] using col.2
    refine ⟨D.activeAssignment row col.1 hEntry, ?_,
      D.activeAssignment_weight_ne_zero row col.1 hEntry⟩
    intro x hx
    exact congrFun (D.activeAssignment_row row col.1 hEntry) ⟨x, hx⟩

theorem PaperNearlyCombinatorialFlatteningData.rowSupportCompletion_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (row : PaperVisibleTuple n rowRoles) :
    Function.Injective (D.rowSupportCompletion row) := by
  classical
  intro col₁ col₂ h
  apply Subtype.ext
  have hAssignments :
      (D.rowSupportCompletion row col₁).1 =
        (D.rowSupportCompletion row col₂).1 :=
    congrArg Subtype.val h
  have hEntry₁ : D.matrix row col₁.1 ≠ 0 := by
    simpa [matrixRowSupport] using col₁.2
  have hEntry₂ : D.matrix row col₂.1 ≠ 0 := by
    simpa [matrixRowSupport] using col₂.2
  calc
    col₁.1 = paperAssignmentRestriction colRoles
        (D.activeAssignment row col₁.1 hEntry₁) :=
      (D.activeAssignment_col row col₁.1 hEntry₁).symm
    _ = paperAssignmentRestriction colRoles
        (D.activeAssignment row col₂.1 hEntry₂) := by
      exact congrArg (paperAssignmentRestriction colRoles) hAssignments
    _ = col₂.1 := D.activeAssignment_col row col₂.1 hEntry₂

/-- Dual encoding of every nonzero row in a fixed column. -/
def PaperNearlyCombinatorialFlatteningData.colSupportCompletion
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (col : PaperVisibleTuple n colRoles) :
    {row : PaperVisibleTuple n rowRoles //
      row ∈ matrixColSupport D.matrix col} →
      CoordinateCompletion n colRoles col (fun a => D.weight a ≠ 0) :=
  fun row => by
    have hEntry : D.matrix row.1 col ≠ 0 := by
      simpa [matrixColSupport] using row.2
    refine ⟨D.activeAssignment row.1 col hEntry, ?_,
      D.activeAssignment_weight_ne_zero row.1 col hEntry⟩
    intro x hx
    exact congrFun (D.activeAssignment_col row.1 col hEntry) ⟨x, hx⟩

theorem PaperNearlyCombinatorialFlatteningData.colSupportCompletion_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles)
    (col : PaperVisibleTuple n colRoles) :
    Function.Injective (D.colSupportCompletion col) := by
  classical
  intro row₁ row₂ h
  apply Subtype.ext
  have hAssignments :
      (D.colSupportCompletion col row₁).1 =
        (D.colSupportCompletion col row₂).1 :=
    congrArg Subtype.val h
  have hEntry₁ : D.matrix row₁.1 col ≠ 0 := by
    simpa [matrixColSupport] using row₁.2
  have hEntry₂ : D.matrix row₂.1 col ≠ 0 := by
    simpa [matrixColSupport] using row₂.2
  calc
    row₁.1 = paperAssignmentRestriction rowRoles
        (D.activeAssignment row₁.1 col hEntry₁) :=
      (D.activeAssignment_row row₁.1 col hEntry₁).symm
    _ = paperAssignmentRestriction rowRoles
        (D.activeAssignment row₂.1 col hEntry₂) := by
      exact congrArg (paperAssignmentRestriction rowRoles) hAssignments
    _ = row₂.1 := D.activeAssignment_row row₂.1 col hEntry₂

/-- Formula (21)'s row-degree bound from complementary-coordinate counting. -/
theorem PaperNearlyCombinatorialFlatteningData.rowSupport_card_le_pow_complement
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles) :
    ∀ row, (matrixRowSupport D.matrix row).card ≤
      n ^ (Finset.univ \ rowRoles).card := by
  classical
  intro row
  exact finset_card_le_pow_complement_of_injective_to_completion
    (matrixRowSupport D.matrix row) n rowRoles row
    (fun a => D.weight a ≠ 0) (D.rowSupportCompletion row)
    (D.rowSupportCompletion_injective row)

/-- Formula (21)'s column-degree bound from complementary-coordinate
counting. -/
theorem PaperNearlyCombinatorialFlatteningData.colSupport_card_le_pow_complement
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles) :
    ∀ col, (matrixColSupport D.matrix col).card ≤
      n ^ (Finset.univ \ colRoles).card := by
  classical
  intro col
  exact finset_card_le_pow_complement_of_injective_to_completion
    (matrixColSupport D.matrix col) n colRoles col
    (fun a => D.weight a ≠ 0) (D.colSupportCompletion col)
    (D.colSupportCompletion_injective col)

/-- Complete deterministic nearly-combinatorial support bridge to formula
(21): bounded active weights and jointly determining coordinates imply the
squared operator-norm complement exponent. -/
theorem PaperNearlyCombinatorialFlatteningData.formula21_squaredNorm_le
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {rowRoles colRoles : Finset α}
    (D : PaperNearlyCombinatorialFlatteningData α n rowRoles colRoles) :
    ‖D.matrix‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent rowRoles colRoles := by
  classical
  exact matrix_l2_opNorm_sq_le_flatteningComplementPower
    rowRoles colRoles D.matrix n
    D.abs_matrix_apply_le_one
    D.rowSupport_card_le_pow_complement
    D.colSupport_card_le_pow_complement

/-! ## Concrete oriented assignment weights

The next definitions instantiate the generic support theorem with the exact
formula-(20) oriented weight and the original shared unordered-edge noise.
The elementary covering condition says precisely when the chosen row and
column coordinate restrictions jointly remember every role. -/

/-- If the two visible coordinate sets cover all roles, their paired
restrictions determine every full assignment. -/
theorem paperAssignmentRestriction_pair_injective_of_union_eq_univ
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (rowRoles colRoles : Finset α)
    (hCover : rowRoles ∪ colRoles = Finset.univ) :
    Function.Injective (fun assignment : α → Fin n =>
      (paperAssignmentRestriction rowRoles assignment,
        paperAssignmentRestriction colRoles assignment)) := by
  intro a b h
  funext x
  by_cases hx : x ∈ rowRoles
  · exact congrFun (congrArg Prod.fst h) ⟨x, hx⟩
  · have hxUnion : x ∈ rowRoles ∪ colRoles := by
      rw [hCover]
      exact Finset.mem_univ x
    have hxCol : x ∈ colRoles := (Finset.mem_union.mp hxUnion).resolve_left hx
    exact congrFun (congrArg Prod.snd h) ⟨x, hxCol⟩

/-- The exact scalar attached to one assignment in the oriented formula-(20)
sum.  The noise is still the shared unordered `PaperNoise`; no independent
edge copies are introduced. -/
def paperOrientedFlatteningAmplitude
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (assignment : PaperAssignment G n) : ℝ :=
  paperOrientedAssignmentWeight G orientation assignment *
    paperAssignmentNoiseProduct G w assignment

/-- A product of the shared edge signs has absolute value one. -/
theorem abs_paperAssignmentNoiseProduct_eq_one
    (G : PaperShape) {n : ℕ} (w : PaperNoise n)
    (assignment : PaperAssignment G n) :
    |paperAssignmentNoiseProduct G w assignment| = 1 := by
  classical
  rw [paperAssignmentNoiseProduct, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro e _
  unfold paperEdgeSign
  split <;> norm_num

/-- Formula-(20)'s full oriented amplitude retains the weight's unit bound. -/
theorem abs_paperOrientedFlatteningAmplitude_le_one
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (assignment : PaperAssignment G n) :
    |paperOrientedFlatteningAmplitude G n orientation w assignment| ≤ 1 := by
  rw [paperOrientedFlatteningAmplitude, abs_mul,
    abs_paperAssignmentNoiseProduct_eq_one]
  simpa using
    abs_paperOrientedAssignmentWeight_le_one G orientation assignment

/-- Concrete faithful coordinate flattening of the oriented assignment sum.
The coverage assumption is exposed because the original boundary row/column
types need not see the internal roles. -/
def paperOrientedNearlyCombinatorialFlatteningData
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (rowRoles colRoles : Finset (Fin G.roles))
    (hCover : rowRoles ∪ colRoles = Finset.univ) :
    PaperNearlyCombinatorialFlatteningData
      (Fin G.roles) n rowRoles colRoles where
  weight := paperOrientedFlatteningAmplitude G n orientation w
  weight_abs_le_one :=
    abs_paperOrientedFlatteningAmplitude_le_one G n orientation w
  active_jointly_injective := by
    intro a b _ _ hRow hCol
    apply paperAssignmentRestriction_pair_injective_of_union_eq_univ
      rowRoles colRoles hCover
    exact Prod.ext hRow hCol

/-- Entrywise expansion of the concrete coordinate flattening, displaying
the same assignment, oriented `0/1` weight, and shared-noise product as the
oriented formula-(20) model. -/
theorem paperOrientedNearlyCombinatorialFlatteningData_matrix_apply
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (rowRoles colRoles : Finset (Fin G.roles))
    (hCover : rowRoles ∪ colRoles = Finset.univ)
    (row : PaperVisibleTuple n rowRoles)
    (col : PaperVisibleTuple n colRoles) :
    (paperOrientedNearlyCombinatorialFlatteningData
      G n orientation w rowRoles colRoles hCover).matrix row col =
      ∑ assignment : PaperAssignment G n,
        if paperAssignmentRestriction rowRoles assignment = row ∧
            paperAssignmentRestriction colRoles assignment = col then
          paperOrientedAssignmentWeight G orientation assignment *
            paperAssignmentNoiseProduct G w assignment
        else
          0 := by
  rfl

/-- Formula (21) for the concrete oriented coordinate flattening whenever
the chosen coordinate sets cover every role. -/
theorem paperOrientedNearlyCombinatorialFlattening_formula21_squaredNorm_le
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (rowRoles colRoles : Finset (Fin G.roles))
    (hCover : rowRoles ∪ colRoles = Finset.univ) :
    ‖(paperOrientedNearlyCombinatorialFlatteningData
      G n orientation w rowRoles colRoles hCover).matrix‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent rowRoles colRoles :=
  (paperOrientedNearlyCombinatorialFlatteningData
    G n orientation w rowRoles colRoles hCover).formula21_squaredNorm_le


end GraphMatrixReplica
