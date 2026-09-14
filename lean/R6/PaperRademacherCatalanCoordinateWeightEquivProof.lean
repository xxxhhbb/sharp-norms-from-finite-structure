import R6.PaperRademacherCatalanCoordinateEquivRecursive

/-! # Pointwise weight preservation for the Catalan coordinate split

The edge/coordinate equivalence is already completely explicit.  Here its
recursive scalar semantics is made explicit and proved to agree pointwise
with the original typed occurrence weight.  Thus the remaining construction
is only the finite path-coordinate equivalence from cycle rows and columns.
-/

noncomputable section

namespace GraphMatrixReplica

@[simp] theorem rademacherRowOccurrenceCoordinateEquiv_node_apply
    {ε ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : ι) (e : ε) (c₁ c₀ : κ)
    (dout : RademacherRowOccurrenceDecoration ε ι κ outside mid j)
    (din : RademacherColumnOccurrenceDecoration ε ι κ inside c₀ c₁) :
    rademacherRowOccurrenceCoordinateEquiv (.node inside outside) i j
        ⟨mid, e, c₁, c₀, dout, din⟩ =
      ((rademacherCompatibleOccurrenceWordNodeEquiv inside outside).symm
        (e,
          (rademacherColumnOccurrenceCoordinateEquiv inside c₀ c₁ din).1,
          (rademacherRowOccurrenceCoordinateEquiv outside mid j dout).1),
        ⟨mid, c₁, c₀,
          (rademacherRowOccurrenceCoordinateEquiv outside mid j dout).2,
          (rademacherColumnOccurrenceCoordinateEquiv inside c₀ c₁ din).2⟩) := by
  rfl

@[simp] theorem rademacherColumnOccurrenceCoordinateEquiv_node_apply
    {ε ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : κ) (e : ε) (r₁ r₀ : ι)
    (dout : RademacherColumnOccurrenceDecoration ε ι κ outside mid j)
    (din : RademacherRowOccurrenceDecoration ε ι κ inside r₀ r₁) :
    rademacherColumnOccurrenceCoordinateEquiv (.node inside outside) i j
        ⟨mid, e, r₁, r₀, dout, din⟩ =
      ((rademacherCompatibleOccurrenceWordNodeEquiv inside outside).symm
        (e,
          (rademacherRowOccurrenceCoordinateEquiv inside r₀ r₁ din).1,
          (rademacherColumnOccurrenceCoordinateEquiv outside mid j dout).1),
        ⟨mid, r₁, r₀,
          (rademacherColumnOccurrenceCoordinateEquiv outside mid j dout).2,
          (rademacherRowOccurrenceCoordinateEquiv inside r₀ r₁ din).2⟩) := by
  rfl

mutual
  /-- Scalar weight of an edge-free row coordinate decoration after a
  genuine compatible edge word has been supplied. -/
  def rademacherRowCoordinateWeight
      {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) :
      {n : ℕ} → {M : RademacherNoncrossingMatching n} → {i j : ι} →
      RademacherCompatibleOccurrenceWord ε M →
      RademacherRowCoordinateDecoration ι κ M i j → ℝ
    | 0, .empty, _, _, _, _ => 1
    | _, .node inside outside, i, _, word, d =>
        let edgeData :=
          rademacherCompatibleOccurrenceWordNodeEquiv inside outside word
        A edgeData.1 i d.2.2.1 *
          rademacherColumnCoordinateWeight A edgeData.2.1 d.2.2.2.2 *
          A edgeData.1 d.1 d.2.1 *
          rademacherRowCoordinateWeight A edgeData.2.2 d.2.2.2.1

  /-- Transpose-typed column coordinate weight. -/
  def rademacherColumnCoordinateWeight
      {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) :
      {n : ℕ} → {M : RademacherNoncrossingMatching n} → {i j : κ} →
      RademacherCompatibleOccurrenceWord ε M →
      RademacherColumnCoordinateDecoration ι κ M i j → ℝ
    | 0, .empty, _, _, _, _ => 1
    | _, .node inside outside, i, _, word, d =>
        let edgeData :=
          rademacherCompatibleOccurrenceWordNodeEquiv inside outside word
        A edgeData.1 d.2.2.1 i *
          rademacherRowCoordinateWeight A edgeData.2.1 d.2.2.2.2 *
          A edgeData.1 d.2.1 d.1 *
          rademacherColumnCoordinateWeight A edgeData.2.2 d.2.2.2.1
end

@[simp] theorem rademacherRowCoordinateWeight_node_apply
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ)
    {a b : ℕ} (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : ι) (c₁ c₀ : κ)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    (dout : RademacherRowCoordinateDecoration ι κ outside mid j)
    (din : RademacherColumnCoordinateDecoration ι κ inside c₀ c₁) :
    @rademacherRowCoordinateWeight ε ι κ A _ (.node inside outside) i j
        word ⟨mid, c₁, c₀, dout, din⟩ =
      let edgeData :=
        rademacherCompatibleOccurrenceWordNodeEquiv inside outside word
      A edgeData.1 i c₀ * rademacherColumnCoordinateWeight A edgeData.2.1 din *
        A edgeData.1 mid c₁ *
          rademacherRowCoordinateWeight A edgeData.2.2 dout := rfl

@[simp] theorem rademacherColumnCoordinateWeight_node_apply
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ)
    {a b : ℕ} (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : κ) (r₁ r₀ : ι)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    (dout : RademacherColumnCoordinateDecoration ι κ outside mid j)
    (din : RademacherRowCoordinateDecoration ι κ inside r₀ r₁) :
    @rademacherColumnCoordinateWeight ε ι κ A _ (.node inside outside) i j
        word ⟨mid, r₁, r₀, dout, din⟩ =
      let edgeData :=
        rademacherCompatibleOccurrenceWordNodeEquiv inside outside word
      A edgeData.1 r₀ i * rademacherRowCoordinateWeight A edgeData.2.1 din *
        A edgeData.1 r₁ mid *
          rademacherColumnCoordinateWeight A edgeData.2.2 dout := rfl

/-- Row-oriented node induction step for pointwise weight preservation.  It
uses only the two child preservation equalities; the parent edge word is the
genuine non-contiguous Catalan assembly. -/
theorem rademacherRowOccurrenceCoordinateWeight_node_of_children
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ)
    {a b : ℕ} (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : ι) (e : ε) (c₁ c₀ : κ)
    (dout : RademacherRowOccurrenceDecoration ε ι κ outside mid j)
    (din : RademacherColumnOccurrenceDecoration ε ι κ inside c₀ c₁)
    (hout : rademacherRowOccurrenceWeight A dout =
      rademacherRowCoordinateWeight A
        (rademacherRowOccurrenceCoordinateEquiv outside mid j dout).1
        (rademacherRowOccurrenceCoordinateEquiv outside mid j dout).2)
    (hin : rademacherColumnOccurrenceWeight A din =
      rademacherColumnCoordinateWeight A
        (rademacherColumnOccurrenceCoordinateEquiv inside c₀ c₁ din).1
        (rademacherColumnOccurrenceCoordinateEquiv inside c₀ c₁ din).2) :
    rademacherRowOccurrenceWeight A
        (show RademacherRowOccurrenceDecoration ε ι κ
          (.node inside outside) i j from
          ⟨mid, e, c₁, c₀, dout, din⟩) =
      @rademacherRowCoordinateWeight ε ι κ A _ (.node inside outside) i j
        ((rademacherCompatibleOccurrenceWordNodeEquiv inside outside).symm
          (e,
            (rademacherColumnOccurrenceCoordinateEquiv inside c₀ c₁ din).1,
            (rademacherRowOccurrenceCoordinateEquiv outside mid j dout).1))
        ⟨mid, c₁, c₀,
          (rademacherRowOccurrenceCoordinateEquiv outside mid j dout).2,
          (rademacherColumnOccurrenceCoordinateEquiv inside c₀ c₁ din).2⟩ := by
  rw [rademacherRowOccurrenceWeight_node_apply, hin, hout]
  rw [rademacherRowCoordinateWeight_node_apply]
  rw [(rademacherCompatibleOccurrenceWordNodeEquiv
    inside outside).apply_symm_apply]

/-- Column-oriented symmetric node induction step. -/
theorem rademacherColumnOccurrenceCoordinateWeight_node_of_children
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ)
    {a b : ℕ} (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : κ) (e : ε) (r₁ r₀ : ι)
    (dout : RademacherColumnOccurrenceDecoration ε ι κ outside mid j)
    (din : RademacherRowOccurrenceDecoration ε ι κ inside r₀ r₁)
    (hout : rademacherColumnOccurrenceWeight A dout =
      rademacherColumnCoordinateWeight A
        (rademacherColumnOccurrenceCoordinateEquiv outside mid j dout).1
        (rademacherColumnOccurrenceCoordinateEquiv outside mid j dout).2)
    (hin : rademacherRowOccurrenceWeight A din =
      rademacherRowCoordinateWeight A
        (rademacherRowOccurrenceCoordinateEquiv inside r₀ r₁ din).1
        (rademacherRowOccurrenceCoordinateEquiv inside r₀ r₁ din).2) :
    rademacherColumnOccurrenceWeight A
        (show RademacherColumnOccurrenceDecoration ε ι κ
          (.node inside outside) i j from
          ⟨mid, e, r₁, r₀, dout, din⟩) =
      @rademacherColumnCoordinateWeight ε ι κ A _ (.node inside outside) i j
        ((rademacherCompatibleOccurrenceWordNodeEquiv inside outside).symm
          (e,
            (rademacherRowOccurrenceCoordinateEquiv inside r₀ r₁ din).1,
            (rademacherColumnOccurrenceCoordinateEquiv outside mid j dout).1))
        ⟨mid, r₁, r₀,
          (rademacherColumnOccurrenceCoordinateEquiv outside mid j dout).2,
          (rademacherRowOccurrenceCoordinateEquiv inside r₀ r₁ din).2⟩ := by
  rw [rademacherColumnOccurrenceWeight_node_apply, hin, hout]
  rw [rademacherColumnCoordinateWeight_node_apply]
  rw [(rademacherCompatibleOccurrenceWordNodeEquiv
    inside outside).apply_symm_apply]

/-- Mutual induction closes pointwise preservation for every Catalan tree. -/
theorem rademacherOccurrenceCoordinateEquiv_weight_eq
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    (∀ i j : ι, ∀ d : RademacherRowOccurrenceDecoration ε ι κ M i j,
      rademacherRowOccurrenceWeight A d =
        rademacherRowCoordinateWeight A
          (rademacherRowOccurrenceCoordinateEquiv M i j d).1
          (rademacherRowOccurrenceCoordinateEquiv M i j d).2) ∧
    (∀ i j : κ, ∀ d : RademacherColumnOccurrenceDecoration ε ι κ M i j,
      rademacherColumnOccurrenceWeight A d =
        rademacherColumnCoordinateWeight A
          (rademacherColumnOccurrenceCoordinateEquiv M i j d).1
          (rademacherColumnOccurrenceCoordinateEquiv M i j d).2) := by
  induction M with
  | empty =>
      constructor <;> intro i j d <;>
        simp [rademacherRowOccurrenceCoordinateEquiv,
          rademacherColumnOccurrenceCoordinateEquiv,
          rademacherRowOccurrenceWeight, rademacherColumnOccurrenceWeight,
          rademacherRowCoordinateWeight, rademacherColumnCoordinateWeight]
  | @node a b inside outside ihInside ihOutside =>
      constructor
      · intro i j d
        rcases d with ⟨mid, e, c₁, c₀, dout, din⟩
        rw [rademacherRowOccurrenceCoordinateEquiv_node_apply]
        exact
          rademacherRowOccurrenceCoordinateWeight_node_of_children
            A inside outside i j mid e c₁ c₀ dout din
              (ihOutside.1 mid j dout) (ihInside.2 c₀ c₁ din)
      · intro i j d
        rcases d with ⟨mid, e, r₁, r₀, dout, din⟩
        rw [rademacherColumnOccurrenceCoordinateEquiv_node_apply]
        exact
          rademacherColumnOccurrenceCoordinateWeight_node_of_children
            A inside outside i j mid e r₁ r₀ dout din
              (ihOutside.2 mid j dout) (ihInside.1 r₀ r₁ din)

/-- The closed occurrence reconstruction therefore preserves the separated
coordinate weight pointwise. -/
theorem rademacherClosedOccurrenceEdgeCoordinateEquiv_symm_weight
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    (coordinates : Σ i : ι, RademacherRowCoordinateDecoration ι κ
      (.node inside outside) i i) :
    rademacherRowOccurrenceWeight A
        ((rademacherClosedOccurrenceEdgeCoordinateEquiv inside outside).symm
          (word, coordinates)).2 =
      rademacherRowCoordinateWeight A word coordinates.2 := by
  let E := rademacherClosedOccurrenceEdgeCoordinateEquiv
    (ε := ε) (ι := ι) (κ := κ) inside outside
  let d := E.symm (word, coordinates)
  have h := (rademacherOccurrenceCoordinateEquiv_weight_eq
    A (.node inside outside)).1 d.1 d.1 d.2
  have hsplit : E d = (word, coordinates) := E.apply_symm_apply _
  change rademacherRowOccurrenceWeight A d.2 =
    rademacherRowCoordinateWeight A word coordinates.2
  change rademacherRowOccurrenceWeight A d.2 =
    rademacherRowCoordinateWeight A (E d).1 (E d).2.2 at h
  rw [hsplit] at h
  exact h

/-- The final residual stripped of all occurrence-decoration bookkeeping:
an equivalence from the two literal cycle coordinate functions to the
edge-free coordinate decoration, preserving the explicit recursive weight
for every compatible edge word. -/
structure RademacherCatalanCycleCoordinateEquiv
    {ε ι κ : Type} {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) where
  toEquiv :
    ((Fin (a + b + 1) → ι) × (Fin (a + b + 1) → κ)) ≃
      (Σ i : ι, RademacherRowCoordinateDecoration ι κ
        (.node inside outside) i i)
  weight_eq : ∀
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    (coordinates :
      (Fin (a + b + 1) → ι) × (Fin (a + b + 1) → κ)),
    let choiceData :=
      (rademacherCompatibleChoiceOccurrenceWordEquiv
        (.node inside outside)).symm word
    rademacherGramCycleCoefficient A coordinates.1 coordinates.2
        choiceData.1 =
      rademacherRowCoordinateWeight A word (toEquiv coordinates).2

/-- This pure cycle-coordinate residual supplies the previously packaged
coordinate/occurrence interface. -/
def RademacherCatalanCycleCoordinateEquiv.toCoordinateWeightEquiv
    {ε ι κ : Type} {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (C : RademacherCatalanCycleCoordinateEquiv A inside outside) :
    RademacherCatalanCoordinateWeightEquiv A inside outside where
  toEquiv := C.toEquiv
  weight_eq word coordinates := by
    exact (C.weight_eq word coordinates).trans
      (rademacherClosedOccurrenceEdgeCoordinateEquiv_symm_weight
        A inside outside word (C.toEquiv coordinates)).symm

#print axioms rademacherRowCoordinateWeight_node_apply
#print axioms rademacherColumnCoordinateWeight_node_apply
#print axioms rademacherRowOccurrenceCoordinateWeight_node_of_children
#print axioms rademacherColumnOccurrenceCoordinateWeight_node_of_children
#print axioms rademacherOccurrenceCoordinateEquiv_weight_eq
#print axioms rademacherClosedOccurrenceEdgeCoordinateEquiv_symm_weight
#print axioms
  RademacherCatalanCycleCoordinateEquiv.toCoordinateWeightEquiv

end GraphMatrixReplica
