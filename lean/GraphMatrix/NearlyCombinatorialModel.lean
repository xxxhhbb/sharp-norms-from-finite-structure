import GraphMatrix.EdgeOrientationDecomposition

/-! # Oriented graph matrices as nearly-combinatorial chaoses

BLNvH v2 writes each oriented piece of a graph matrix in the form (20): the
sum ranges over every assignment of ambient labels to shape roles, while a
bounded weight removes non-injective assignments and assignments with the
wrong edge orientation.  This file records that zero-padding exactly.

The noise remains the original shared unordered-edge noise `PaperNoise n`.
In particular, the definitions below do not assert that different shape-edge
coordinates are independent and do not perform a decoupling step.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- An unrestricted assignment of ambient labels to all roles. -/
abbrev PaperAssignment (G : PaperShape) (n : ℕ) :=
  Fin G.roles → Fin n

/-- Formula (20)'s ordered-pair coordinate associated with a shape edge. -/
def paperAssignmentEdgeCoordinate (G : PaperShape) {n : ℕ}
    (assignment : PaperAssignment G n) (e : Fin G.edges) :
    Fin n × Fin n :=
  (assignment (G.source e), assignment (G.target e))

/-- Formula (20)'s tuple of left matrix coordinates. -/
def paperAssignmentLeftTuple (G : PaperShape) {n : ℕ}
    (assignment : PaperAssignment G n) : PaperRow G n :=
  fun i => assignment (G.left i)

/-- Formula (20)'s tuple of right matrix coordinates. -/
def paperAssignmentRightTuple (G : PaperShape) {n : ℕ}
    (assignment : PaperAssignment G n) : PaperCol G n :=
  fun i => assignment (G.right i)

/-- Entry compatibility expressed only through the two boundary tuple maps. -/
def paperAssignmentEntryCompatible (G : PaperShape) {n : ℕ}
    (assignment : PaperAssignment G n)
    (row : PaperRow G n) (col : PaperCol G n) : Prop :=
  paperAssignmentLeftTuple G assignment = row ∧
    paperAssignmentRightTuple G assignment = col

instance paperAssignmentEntryCompatibleDecidable (G : PaperShape) {n : ℕ}
    (assignment : PaperAssignment G n)
    (row : PaperRow G n) (col : PaperCol G n) :
    Decidable (paperAssignmentEntryCompatible G assignment row col) :=
  inferInstanceAs (Decidable
    (paperAssignmentLeftTuple G assignment = row ∧
      paperAssignmentRightTuple G assignment = col))

/-- The selected strict orientation written for an unrestricted assignment. -/
def paperAssignmentOrientationCompatible (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool)
    (assignment : PaperAssignment G n) : Prop :=
  orientation = fun e => decide
    (assignment (G.source e) < assignment (G.target e))

/-- The bounded nearly-combinatorial weight: it is one precisely on globally
injective assignments having the selected orientation, and zero otherwise. -/
def paperOrientedAssignmentWeight (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool)
    (assignment : PaperAssignment G n) : ℝ := by
  classical
  exact if Function.Injective assignment ∧
      paperAssignmentOrientationCompatible G orientation assignment then
    1
  else
    0

/-- The weight is literally a `0/1` indicator. -/
theorem paperOrientedAssignmentWeight_eq_zero_or_one
    (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool)
    (assignment : PaperAssignment G n) :
    paperOrientedAssignmentWeight G orientation assignment = 0 ∨
      paperOrientedAssignmentWeight G orientation assignment = 1 := by
  classical
  unfold paperOrientedAssignmentWeight
  split <;> simp

/-- The `ℓ∞` bound required of the weight in Definition 3.6 / formula (20). -/
theorem abs_paperOrientedAssignmentWeight_le_one
    (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool)
    (assignment : PaperAssignment G n) :
    |paperOrientedAssignmentWeight G orientation assignment| ≤ 1 := by
  rcases paperOrientedAssignmentWeight_eq_zero_or_one G orientation assignment
    with h | h <;> rw [h] <;> norm_num

/-- Product of the original shared unordered-edge signs, written through the
ordered-pair coordinate maps of formula (20). -/
def paperAssignmentNoiseProduct (G : PaperShape) {n : ℕ}
    (w : PaperNoise n) (assignment : PaperAssignment G n) : ℝ :=
  ∏ e : Fin G.edges,
    paperEdgeSign w (paperAssignmentEdgeCoordinate G assignment e).1
      (paperAssignmentEdgeCoordinate G assignment e).2

/-- A realization is equivalently an unrestricted assignment accompanied by
global injectivity. -/
def paperRealizationEquivInjectiveAssignment (G : PaperShape) (n : ℕ) :
    PaperRealization G n ≃
      {assignment : PaperAssignment G n // Function.Injective assignment} where
  toFun phi := ⟨phi, phi.injective⟩
  invFun assignment := ⟨assignment.1, assignment.2⟩
  left_inv phi := by
    cases phi
    rfl
  right_inv assignment := by
    cases assignment
    rfl

/-- Generic finite zero-padding identity used to replace a sum over global
embeddings by a sum over all role assignments. -/
theorem sum_paperRealization_eq_sum_assignment_if_injective
    (G : PaperShape) (n : ℕ)
    (term : PaperAssignment G n → ℝ) :
    (∑ phi : PaperRealization G n, term phi) =
      ∑ assignment : PaperAssignment G n,
        if Function.Injective assignment then term assignment else 0 := by
  classical
  calc
    (∑ phi : PaperRealization G n, term phi) =
        ∑ assignment :
            {assignment : PaperAssignment G n //
              Function.Injective assignment},
          term assignment.1 := by
      exact Fintype.sum_equiv
        (paperRealizationEquivInjectiveAssignment G n)
        (fun phi => term phi)
        (fun assignment => term assignment.1)
        (fun _ => rfl)
    _ = ∑ assignment : PaperAssignment G n,
          if Function.Injective assignment then term assignment else 0 := by
      rw [← Finset.sum_subtype
        (s := Finset.univ.filter Function.Injective)
        (fun assignment => by simp)]
      rw [← Finset.sum_filter]

@[simp] theorem paperAssignmentEntryCompatible_realization_iff
    (G : PaperShape) {n : ℕ} (phi : PaperRealization G n)
    (row : PaperRow G n) (col : PaperCol G n) :
    paperAssignmentEntryCompatible G phi row col ↔
      paperEntryCompatible G phi row col := by
  constructor
  · rintro ⟨hLeft, hRight⟩
    constructor
    · intro i
      exact congrFun hLeft i
    · intro i
      exact congrFun hRight i
  · rintro ⟨hLeft, hRight⟩
    constructor
    · funext i
      exact hLeft i
    · funext i
      exact hRight i

@[simp] theorem paperAssignmentOrientationCompatible_realization_iff
    (G : PaperShape) {n : ℕ}
    (orientation : Fin G.edges → Bool) (phi : PaperRealization G n) :
    paperAssignmentOrientationCompatible G orientation phi ↔
      paperOrientationCompatible G orientation phi := by
  rfl

@[simp] theorem paperAssignmentNoiseProduct_realization
    (G : PaperShape) {n : ℕ} (w : PaperNoise n)
    (phi : PaperRealization G n) :
    paperAssignmentNoiseProduct G w phi =
      ∏ e : Fin G.edges,
        paperEdgeSign w (phi (G.source e)) (phi (G.target e)) := by
  rfl

/-- The formula-(20) matrix obtained by summing over every role assignment.
The boundary tuple indicator supplies the matrix basis coordinates entrywise. -/
def paperNearlyCombinatorialOrientedMatrix (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ := by
  classical
  exact fun row col =>
    ∑ assignment : PaperAssignment G n,
      paperOrientedAssignmentWeight G orientation assignment *
        if paperAssignmentEntryCompatible G assignment row col then
          paperAssignmentNoiseProduct G w assignment
        else
          0

/-- Exact entrywise zero-padding identity: the existing oriented graph matrix
is the formula-(20) assignment sum with a bounded `0/1` weight. -/
theorem paperOrientedGraphMatrix_eq_nearlyCombinatorial
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    paperOrientedGraphMatrix G n orientation w =
      paperNearlyCombinatorialOrientedMatrix G n orientation w := by
  classical
  ext row col
  unfold paperOrientedGraphMatrix paperNearlyCombinatorialOrientedMatrix
  calc
    (∑ phi : PaperRealization G n,
        if paperEntryCompatible G phi row col ∧
            paperOrientationCompatible G orientation phi then
          ∏ e : Fin G.edges,
            paperEdgeSign w (phi (G.source e)) (phi (G.target e))
        else 0) =
        ∑ phi : PaperRealization G n,
          if paperAssignmentEntryCompatible G phi row col ∧
              paperAssignmentOrientationCompatible G orientation phi then
            paperAssignmentNoiseProduct G w phi
          else 0 := by
      apply Finset.sum_congr rfl
      intro phi _
      by_cases hEntry : paperEntryCompatible G phi row col <;>
        by_cases hOrientation :
          paperOrientationCompatible G orientation phi <;>
        simp [hEntry, hOrientation,
          paperAssignmentEntryCompatible_realization_iff,
          paperAssignmentOrientationCompatible_realization_iff,
          paperAssignmentNoiseProduct_realization]
    _ = ∑ assignment : PaperAssignment G n,
          if Function.Injective assignment then
            (if paperAssignmentEntryCompatible G assignment row col ∧
                paperAssignmentOrientationCompatible G orientation assignment then
              paperAssignmentNoiseProduct G w assignment
            else 0)
          else 0 := by
      simpa only using
        (sum_paperRealization_eq_sum_assignment_if_injective G n
          (fun assignment =>
            if paperAssignmentEntryCompatible G assignment row col ∧
                paperAssignmentOrientationCompatible G orientation assignment then
              paperAssignmentNoiseProduct G w assignment
            else 0))
    _ = ∑ assignment : PaperAssignment G n,
          paperOrientedAssignmentWeight G orientation assignment *
            if paperAssignmentEntryCompatible G assignment row col then
              paperAssignmentNoiseProduct G w assignment
            else 0 := by
      apply Finset.sum_congr rfl
      intro assignment _
      by_cases hInjective : Function.Injective assignment <;>
        by_cases hOrientation :
          paperAssignmentOrientationCompatible G orientation assignment <;>
        by_cases hEntry :
          paperAssignmentEntryCompatible G assignment row col <;>
        simp [hInjective, hOrientation, hEntry,
          paperOrientedAssignmentWeight]

/-- Entrywise form of the preceding matrix identity, convenient for later
flattening and support calculations. -/
theorem paperOrientedGraphMatrix_apply_eq_assignment_sum
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (row : PaperRow G n) (col : PaperCol G n) :
    paperOrientedGraphMatrix G n orientation w row col =
      ∑ assignment : PaperAssignment G n,
        paperOrientedAssignmentWeight G orientation assignment *
          if paperAssignmentEntryCompatible G assignment row col then
            paperAssignmentNoiseProduct G w assignment
          else
            0 := by
  classical
  rw [paperOrientedGraphMatrix_eq_nearlyCombinatorial]
  rfl


end GraphMatrixReplica
