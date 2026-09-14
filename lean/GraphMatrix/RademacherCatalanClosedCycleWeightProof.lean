import GraphMatrix.RademacherCatalanClosedCycleWeight

/-! # Recursive open-path weight behind the closed Catalan cycle -/

noncomputable section
namespace GraphMatrixReplica

mutual
  def rademacherRowPathWeight
      {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) : {n : ℕ} →
      (M : RademacherNoncrossingMatching n) →
      RademacherCompatibleOccurrenceWord ε M → {i j : ι} →
      RademacherRowCoordinatePath ι κ M i j → ℝ
    | 0, .empty, _, _, _, _ => 1
    | _, @RademacherNoncrossingMatching.node a b inside outside, word, i, _, p =>
        let edgeData := rademacherCompatibleOccurrenceWordNodeEquiv
          inside outside word
        A edgeData.1 i (p.1.2 0) *
          rademacherColumnPathWeight A inside edgeData.2.1
            (rademacherRowPathInside p) *
          A edgeData.1 (p.1.1 ⟨a + 1, by omega⟩)
            (p.1.2 ⟨a, by omega⟩) *
          rademacherRowPathWeight A outside edgeData.2.2
            (rademacherRowPathOutside p)

  def rademacherColumnPathWeight
      {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) : {n : ℕ} →
      (M : RademacherNoncrossingMatching n) →
      RademacherCompatibleOccurrenceWord ε M → {i j : κ} →
      RademacherColumnCoordinatePath ι κ M i j → ℝ
    | 0, .empty, _, _, _, _ => 1
    | _, @RademacherNoncrossingMatching.node a b inside outside, word, i, _, p =>
        let edgeData := rademacherCompatibleOccurrenceWordNodeEquiv
          inside outside word
        A edgeData.1 (p.1.1 0) i *
          rademacherRowPathWeight A inside edgeData.2.1
            (rademacherColumnPathInside p) *
          A edgeData.1 (p.1.1 ⟨a, by omega⟩)
            (p.1.2 ⟨a + 1, by omega⟩) *
          rademacherColumnPathWeight A outside edgeData.2.2
            (rademacherColumnPathOutside p)
end

theorem rademacherPathCoordinateDecoration_weight_eq
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    (∀ i j (word : RademacherCompatibleOccurrenceWord ε M)
      (p : RademacherRowCoordinatePath ι κ M i j),
      rademacherRowPathWeight A M word p =
        rademacherRowCoordinateWeight A word
          (rademacherRowPathCoordinateDecorationEquiv M i j p)) ∧
    (∀ i j (word : RademacherCompatibleOccurrenceWord ε M)
      (p : RademacherColumnCoordinatePath ι κ M i j),
      rademacherColumnPathWeight A M word p =
        rademacherColumnCoordinateWeight A word
          (rademacherColumnPathCoordinateDecorationEquiv M i j p)) := by
  induction M with
  | empty =>
      constructor <;> intro i j word p <;>
        simp [rademacherRowPathWeight, rademacherColumnPathWeight,
          rademacherRowPathCoordinateDecorationEquiv,
          rademacherColumnPathCoordinateDecorationEquiv,
          rademacherRowCoordinateWeight, rademacherColumnCoordinateWeight]
  | @node a b inside outside ihInside ihOutside =>
      constructor
      · intro i j word p
        simp only [rademacherRowPathWeight,
          rademacherRowCoordinateWeight_node_apply]
        rw [ihInside.2, ihOutside.1]
        rfl
      · intro i j word p
        simp only [rademacherColumnPathWeight,
          rademacherColumnCoordinateWeight_node_apply]
        rw [ihInside.1, ihOutside.2]
        rfl

theorem rademacherClosedCyclePathWeight_eq_coordinateWeight
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    (coordinates :
      (Fin (a + b + 1) → ι) × (Fin (a + b + 1) → κ)) :
    rademacherRowPathWeight A (.node inside outside) word
        (rademacherClosedCycleToRowPath (by omega)
          (.node inside outside) coordinates).2 =
      rademacherRowCoordinateWeight A word
        (rademacherClosedCycleCoordinateDecorationEquiv
          inside outside coordinates).2 := by
  let p := rademacherClosedCycleToRowPath (ι := ι) (κ := κ) (by omega)
    (.node inside outside) coordinates
  have hcycle :
      rademacherClosedCycleRowPathEquiv (ι := ι) (κ := κ) (by omega)
          (.node inside outside) coordinates = p := rfl
  change rademacherRowPathWeight A (.node inside outside) word p.2 =
    rademacherRowCoordinateWeight A word
      ((Equiv.sigmaCongrRight fun i =>
        rademacherRowPathCoordinateDecorationEquiv
          (.node inside outside) i i)
        (rademacherClosedCycleRowPathEquiv (by omega)
          (.node inside outside) coordinates)).2
  rw [hcycle]
  exact (rademacherPathCoordinateDecoration_weight_eq
    A (.node inside outside)).1 p.1 p.1 word p.2

/-- The remaining indexing lemma after the recursive matrix weight itself has
been identified.  It says only that the sequential `Fin (2*n)` occurrence
enumeration is the non-contiguous Catalan recursion. -/
def RademacherCatalanClosedPathProductCompatibility
    {ε ι κ : Type} [Fintype ε] {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) : Prop :=
  ∀ (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    (coordinates :
      (Fin (a + b + 1) → ι) × (Fin (a + b + 1) → κ)),
    (∏ s : Fin (2 * (a + b + 1)),
      A (word.1 s)
        (rademacherCycleOccurrenceRow coordinates.1 s)
        (rademacherCycleOccurrenceCol coordinates.2 s)) =
      rademacherRowPathWeight A (.node inside outside) word
        (rademacherClosedCycleToRowPath (by omega)
          (.node inside outside) coordinates).2

theorem rademacherCatalanClosedCycleWeightCompatibility_of_pathProduct
    {ε ι κ : Type} [Fintype ε] {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (h : RademacherCatalanClosedPathProductCompatibility A inside outside) :
    RademacherCatalanClosedCycleWeightCompatibility A inside outside := by
  intro word coordinates
  exact (h word coordinates).trans
    (rademacherClosedCyclePathWeight_eq_coordinateWeight
      A inside outside word coordinates)

/-! ## Sequential path products

These two factors retain the literal `Fin (2*n)` order.  The row version
uses the two entries `row t -- col t -- row (t+1)`; the column version is
its typed transpose. -/

def rademacherRowPathOccurrenceFactor
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    {M : RademacherNoncrossingMatching n}
    (word : RademacherCompatibleOccurrenceWord ε M) {i j : ι}
    (p : RademacherRowCoordinatePath ι κ M i j)
    (s : Fin (2 * n)) : ℝ :=
  let q := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  if q.2 then
    A (word.1 s) (p.1.1 ⟨q.1.1 + 1, by omega⟩) (p.1.2 q.1)
  else A (word.1 s) (p.1.1 ⟨q.1.1, by omega⟩) (p.1.2 q.1)

def rademacherColumnPathOccurrenceFactor
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    {M : RademacherNoncrossingMatching n}
    (word : RademacherCompatibleOccurrenceWord ε M) {i j : κ}
    (p : RademacherColumnCoordinatePath ι κ M i j)
    (s : Fin (2 * n)) : ℝ :=
  let q := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  if q.2 then
    A (word.1 s) (p.1.1 q.1) (p.1.2 ⟨q.1.1 + 1, by omega⟩)
  else A (word.1 s) (p.1.1 q.1) (p.1.2 ⟨q.1.1, by omega⟩)

@[simp] theorem rademacherRowPathOccurrenceFactor_even
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    {M : RademacherNoncrossingMatching n}
    (word : RademacherCompatibleOccurrenceWord ε M) {i j : ι}
    (p : RademacherRowCoordinatePath ι κ M i j) (t : Fin n) :
    rademacherRowPathOccurrenceFactor A word p
        (rademacherAlternatingOccurrenceIndexEquiv n (t, false)) =
      A (word.1 (rademacherAlternatingOccurrenceIndexEquiv n (t, false)))
        (p.1.1 ⟨t.1, by omega⟩) (p.1.2 t) := by
  simp [rademacherRowPathOccurrenceFactor]

@[simp] theorem rademacherRowPathOccurrenceFactor_odd
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    {M : RademacherNoncrossingMatching n}
    (word : RademacherCompatibleOccurrenceWord ε M) {i j : ι}
    (p : RademacherRowCoordinatePath ι κ M i j) (t : Fin n) :
    rademacherRowPathOccurrenceFactor A word p
        (rademacherAlternatingOccurrenceIndexEquiv n (t, true)) =
      A (word.1 (rademacherAlternatingOccurrenceIndexEquiv n (t, true)))
        (p.1.1 ⟨t.1 + 1, by omega⟩) (p.1.2 t) := by
  simp [rademacherRowPathOccurrenceFactor]

@[simp] theorem rademacherColumnPathOccurrenceFactor_even
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    {M : RademacherNoncrossingMatching n}
    (word : RademacherCompatibleOccurrenceWord ε M) {i j : κ}
    (p : RademacherColumnCoordinatePath ι κ M i j) (t : Fin n) :
    rademacherColumnPathOccurrenceFactor A word p
        (rademacherAlternatingOccurrenceIndexEquiv n (t, false)) =
      A (word.1 (rademacherAlternatingOccurrenceIndexEquiv n (t, false)))
        (p.1.1 t) (p.1.2 ⟨t.1, by omega⟩) := by
  simp [rademacherColumnPathOccurrenceFactor]

@[simp] theorem rademacherColumnPathOccurrenceFactor_odd
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    {M : RademacherNoncrossingMatching n}
    (word : RademacherCompatibleOccurrenceWord ε M) {i j : κ}
    (p : RademacherColumnCoordinatePath ι κ M i j) (t : Fin n) :
    rademacherColumnPathOccurrenceFactor A word p
        (rademacherAlternatingOccurrenceIndexEquiv n (t, true)) =
      A (word.1 (rademacherAlternatingOccurrenceIndexEquiv n (t, true)))
        (p.1.1 t) (p.1.2 ⟨t.1 + 1, by omega⟩) := by
  simp [rademacherColumnPathOccurrenceFactor]

theorem rademacherRowPathOccurrenceFactor_node_rootFirst
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : ι} (p : RademacherRowCoordinatePath ι κ
      (.node inside outside) i j) :
    rademacherRowPathOccurrenceFactor A word p ⟨0, by omega⟩ =
      A (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).1
        i (p.1.2 ⟨0, by omega⟩) := by
  let t : Fin (a + b + 1) := ⟨0, by omega⟩
  have hs : rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
      (t, false) = (⟨0, by omega⟩ : Fin (2 * (a + b + 1))) := by
    apply Fin.ext
    simp [rademacherAlternatingOccurrenceIndexEquiv, t]
  rw [← hs, rademacherRowPathOccurrenceFactor_even]
  dsimp [t] at hs ⊢
  rw [hs]
  change A (word.1 ⟨0, by omega⟩) (p.1.1 ⟨0, by omega⟩)
    (p.1.2 ⟨0, by omega⟩) = _
  rw [p.2.1]
  rfl

theorem rademacherRowPathOccurrenceFactor_node_rootSecond
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : ι} (p : RademacherRowCoordinatePath ι κ
      (.node inside outside) i j) :
    rademacherRowPathOccurrenceFactor A word p
        ⟨2 * a + 1, by omega⟩ =
      A (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).1
        (p.1.1 ⟨a + 1, by omega⟩) (p.1.2 ⟨a, by omega⟩) := by
  let t : Fin (a + b + 1) := ⟨a, by omega⟩
  have hs : rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
      (t, true) = (⟨2 * a + 1, by omega⟩ : Fin (2 * (a + b + 1))) := by
    apply Fin.ext
    simp [rademacherAlternatingOccurrenceIndexEquiv, t]
    omega
  rw [← hs, rademacherRowPathOccurrenceFactor_odd]
  rw [hs]
  change A (word.1 ⟨2 * a + 1, by omega⟩)
      (p.1.1 ⟨a + 1, by omega⟩) (p.1.2 ⟨a, by omega⟩) =
    A (word.1 ⟨0, by omega⟩)
      (p.1.1 ⟨a + 1, by omega⟩) (p.1.2 ⟨a, by omega⟩)
  congr 1
  exact word.2 0 (2 * a + 1) (by
    simp [RademacherNoncrossingMatching.pairList]) |>.symm

theorem rademacherRowPathOccurrenceFactor_node_inside
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : ι} (p : RademacherRowCoordinatePath ι κ
      (.node inside outside) i j) (s : Fin (2 * a)) :
    rademacherRowPathOccurrenceFactor A word p ⟨s.1 + 1, by omega⟩ =
      rademacherColumnPathOccurrenceFactor A
        (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).2.1
        (rademacherRowPathInside p) s := by
  let q := (rademacherAlternatingOccurrenceIndexEquiv a).symm s
  have hq : rademacherAlternatingOccurrenceIndexEquiv a q = s :=
    (rademacherAlternatingOccurrenceIndexEquiv a).apply_symm_apply s
  rcases q with ⟨t, bit⟩
  cases bit
  · have hs :
        (⟨s.1 + 1, by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1, by omega⟩, true) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherRowPathOccurrenceFactor_odd]
    rw [← hq, rademacherColumnPathOccurrenceFactor_even]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordInside, rademacherRowPathInside]
    rw [hq, hs]
  · have hs :
        (⟨s.1 + 1, by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1 + 1, by omega⟩, false) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherRowPathOccurrenceFactor_even]
    rw [← hq, rademacherColumnPathOccurrenceFactor_odd]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordInside, rademacherRowPathInside]
    rw [hq, hs]

theorem rademacherRowPathOccurrenceFactor_node_outside
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : ι} (p : RademacherRowCoordinatePath ι κ
      (.node inside outside) i j) (s : Fin (2 * b)) :
    rademacherRowPathOccurrenceFactor A word p
        ⟨s.1 + (2 * a + 2), by omega⟩ =
      rademacherRowPathOccurrenceFactor A
        (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).2.2
        (rademacherRowPathOutside p) s := by
  let q := (rademacherAlternatingOccurrenceIndexEquiv b).symm s
  have hq : rademacherAlternatingOccurrenceIndexEquiv b q = s :=
    (rademacherAlternatingOccurrenceIndexEquiv b).apply_symm_apply s
  rcases q with ⟨t, bit⟩
  cases bit
  · have hs :
        (⟨s.1 + (2 * a + 2), by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1 + (a + 1), by omega⟩, false) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherRowPathOccurrenceFactor_even]
    rw [← hq, rademacherRowPathOccurrenceFactor_even]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordOutside, rademacherRowPathOutside]
    rw [hq, hs]
  · have hs :
        (⟨s.1 + (2 * a + 2), by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1 + (a + 1), by omega⟩, true) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherRowPathOccurrenceFactor_odd]
    rw [← hq, rademacherRowPathOccurrenceFactor_odd]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordOutside, rademacherRowPathOutside]
    rw [hq, hs]
    have hind :
        (⟨t.1 + (a + 1) + 1, by omega⟩ : Fin (a + b + 2)) =
          ⟨t.1 + 1 + (a + 1), by omega⟩ := by
      apply Fin.ext
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [hind]

theorem rademacherColumnPathOccurrenceFactor_node_rootFirst
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : κ} (p : RademacherColumnCoordinatePath ι κ
      (.node inside outside) i j) :
    rademacherColumnPathOccurrenceFactor A word p ⟨0, by omega⟩ =
      A (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).1
        (p.1.1 ⟨0, by omega⟩) i := by
  let t : Fin (a + b + 1) := ⟨0, by omega⟩
  have hs : rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
      (t, false) = (⟨0, by omega⟩ : Fin (2 * (a + b + 1))) := by
    apply Fin.ext
    simp [rademacherAlternatingOccurrenceIndexEquiv, t]
  rw [← hs, rademacherColumnPathOccurrenceFactor_even]
  dsimp [t] at hs ⊢
  rw [hs]
  change A (word.1 ⟨0, by omega⟩) (p.1.1 ⟨0, by omega⟩)
    (p.1.2 ⟨0, by omega⟩) = _
  rw [p.2.1]
  rfl

theorem rademacherColumnPathOccurrenceFactor_node_rootSecond
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : κ} (p : RademacherColumnCoordinatePath ι κ
      (.node inside outside) i j) :
    rademacherColumnPathOccurrenceFactor A word p
        ⟨2 * a + 1, by omega⟩ =
      A (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).1
        (p.1.1 ⟨a, by omega⟩) (p.1.2 ⟨a + 1, by omega⟩) := by
  let t : Fin (a + b + 1) := ⟨a, by omega⟩
  have hs : rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
      (t, true) = (⟨2 * a + 1, by omega⟩ : Fin (2 * (a + b + 1))) := by
    apply Fin.ext
    simp [rademacherAlternatingOccurrenceIndexEquiv, t]
    omega
  rw [← hs, rademacherColumnPathOccurrenceFactor_odd]
  rw [hs]
  change A (word.1 ⟨2 * a + 1, by omega⟩)
      (p.1.1 ⟨a, by omega⟩) (p.1.2 ⟨a + 1, by omega⟩) =
    A (word.1 ⟨0, by omega⟩)
      (p.1.1 ⟨a, by omega⟩) (p.1.2 ⟨a + 1, by omega⟩)
  congr 1
  exact word.2 0 (2 * a + 1) (by
    simp [RademacherNoncrossingMatching.pairList]) |>.symm

theorem rademacherColumnPathOccurrenceFactor_node_inside
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : κ} (p : RademacherColumnCoordinatePath ι κ
      (.node inside outside) i j) (s : Fin (2 * a)) :
    rademacherColumnPathOccurrenceFactor A word p ⟨s.1 + 1, by omega⟩ =
      rademacherRowPathOccurrenceFactor A
        (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).2.1
        (rademacherColumnPathInside p) s := by
  let q := (rademacherAlternatingOccurrenceIndexEquiv a).symm s
  have hq : rademacherAlternatingOccurrenceIndexEquiv a q = s :=
    (rademacherAlternatingOccurrenceIndexEquiv a).apply_symm_apply s
  rcases q with ⟨t, bit⟩
  cases bit
  · have hs :
        (⟨s.1 + 1, by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1, by omega⟩, true) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherColumnPathOccurrenceFactor_odd]
    rw [← hq, rademacherRowPathOccurrenceFactor_even]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordInside, rademacherColumnPathInside]
    rw [hq, hs]
  · have hs :
        (⟨s.1 + 1, by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1 + 1, by omega⟩, false) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherColumnPathOccurrenceFactor_even]
    rw [← hq, rademacherRowPathOccurrenceFactor_odd]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordInside, rademacherColumnPathInside]
    rw [hq, hs]

theorem rademacherColumnPathOccurrenceFactor_node_outside
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (word : RademacherCompatibleOccurrenceWord ε (.node inside outside))
    {i j : κ} (p : RademacherColumnCoordinatePath ι κ
      (.node inside outside) i j) (s : Fin (2 * b)) :
    rademacherColumnPathOccurrenceFactor A word p
        ⟨s.1 + (2 * a + 2), by omega⟩ =
      rademacherColumnPathOccurrenceFactor A
        (rademacherCompatibleOccurrenceWordNodeEquiv inside outside word).2.2
        (rademacherColumnPathOutside p) s := by
  let q := (rademacherAlternatingOccurrenceIndexEquiv b).symm s
  have hq : rademacherAlternatingOccurrenceIndexEquiv b q = s :=
    (rademacherAlternatingOccurrenceIndexEquiv b).apply_symm_apply s
  rcases q with ⟨t, bit⟩
  cases bit
  · have hs :
        (⟨s.1 + (2 * a + 2), by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1 + (a + 1), by omega⟩, false) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherColumnPathOccurrenceFactor_even]
    rw [← hq, rademacherColumnPathOccurrenceFactor_even]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordOutside, rademacherColumnPathOutside]
    rw [hq, hs]
  · have hs :
        (⟨s.1 + (2 * a + 2), by omega⟩ : Fin (2 * (a + b + 1))) =
          rademacherAlternatingOccurrenceIndexEquiv (a + b + 1)
            (⟨t.1 + (a + 1), by omega⟩, true) := by
        apply Fin.ext
        have hv := congrArg Fin.val hq
        simp [rademacherAlternatingOccurrenceIndexEquiv] at hv ⊢
        omega
    rw [hs, rademacherColumnPathOccurrenceFactor_odd]
    rw [← hq, rademacherColumnPathOccurrenceFactor_odd]
    simp [rademacherCompatibleOccurrenceWordNodeEquiv,
      rademacherCompatibleOccurrenceWordOutside, rademacherColumnPathOutside]
    rw [hq, hs]
    have hind :
        (⟨t.1 + (a + 1) + 1, by omega⟩ : Fin (a + b + 2)) =
          ⟨t.1 + 1 + (a + 1), by omega⟩ := by
      apply Fin.ext
      simp [Nat.add_comm, Nat.add_left_comm]
    rw [hind]

/-- The literal sequential product is exactly the recursively segmented
Catalan path weight, in both endpoint orientations. -/
theorem rademacherPathOccurrenceProduct_eq_weight
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    (∀ i j (word : RademacherCompatibleOccurrenceWord ε M)
      (p : RademacherRowCoordinatePath ι κ M i j),
      (∏ s : Fin (2 * n),
        rademacherRowPathOccurrenceFactor A word p s) =
          rademacherRowPathWeight A M word p) ∧
    (∀ i j (word : RademacherCompatibleOccurrenceWord ε M)
      (p : RademacherColumnCoordinatePath ι κ M i j),
      (∏ s : Fin (2 * n),
        rademacherColumnPathOccurrenceFactor A word p s) =
          rademacherColumnPathWeight A M word p) := by
  induction M with
  | empty =>
      constructor <;> intro i j word p <;>
        simp [rademacherRowPathWeight, rademacherColumnPathWeight]
  | @node a b inside outside ihInside ihOutside =>
      constructor
      · intro i j word p
        rw [prod_catalanOccurrences_eq_root_inside_outside]
        rw [rademacherRowPathOccurrenceFactor_node_rootFirst
          A inside outside word p]
        rw [rademacherRowPathOccurrenceFactor_node_rootSecond
          A inside outside word p]
        simp_rw [rademacherRowPathOccurrenceFactor_node_inside
          A inside outside word p]
        simp_rw [rademacherRowPathOccurrenceFactor_node_outside
          A inside outside word p]
        rw [ihInside.2, ihOutside.1]
        simp only [rademacherRowPathWeight]
        have hroot :
            A (rademacherCompatibleOccurrenceWordNodeEquiv
                inside outside word).1 i (p.1.2 ⟨0, by omega⟩) =
              A (rademacherCompatibleOccurrenceWordNodeEquiv
                inside outside word).1 i (p.1.2 0) := by
          apply congrArg (fun c => A
            (rademacherCompatibleOccurrenceWordNodeEquiv
              inside outside word).1 i c)
          apply congrArg p.1.2
          apply Fin.ext
          rfl
        rw [hroot]
        ring
      · intro i j word p
        rw [prod_catalanOccurrences_eq_root_inside_outside]
        rw [rademacherColumnPathOccurrenceFactor_node_rootFirst
          A inside outside word p]
        rw [rademacherColumnPathOccurrenceFactor_node_rootSecond
          A inside outside word p]
        simp_rw [rademacherColumnPathOccurrenceFactor_node_inside
          A inside outside word p]
        simp_rw [rademacherColumnPathOccurrenceFactor_node_outside
          A inside outside word p]
        rw [ihInside.1, ihOutside.2]
        simp only [rademacherColumnPathWeight]
        have hroot :
            A (rademacherCompatibleOccurrenceWordNodeEquiv
                inside outside word).1 (p.1.1 ⟨0, by omega⟩) i =
              A (rademacherCompatibleOccurrenceWordNodeEquiv
                inside outside word).1 (p.1.1 0) i := by
          apply congrArg (fun r => A
            (rademacherCompatibleOccurrenceWordNodeEquiv
              inside outside word).1 r i)
          apply congrArg p.1.1
          apply Fin.ext
          rfl
        rw [hroot]
        ring

theorem rademacherClosedCycleToRowPath_row_current
    {ι κ : Type} {n : ℕ} (hn : 0 < n)
    (M : RademacherNoncrossingMatching n)
    (coordinates : (Fin n → ι) × (Fin n → κ)) (t : Fin n) :
    (rademacherClosedCycleToRowPath hn M coordinates).2.1.1
        ⟨t.1, by omega⟩ = coordinates.1 t := by
  simp [rademacherClosedCycleToRowPath, t.2]

theorem rademacherClosedCycleToRowPath_row_next
    {ι κ : Type} {n : ℕ} (hn : 0 < n)
    (M : RademacherNoncrossingMatching n)
    (coordinates : (Fin n → ι) × (Fin n → κ)) (t : Fin n) :
    (rademacherClosedCycleToRowPath hn M coordinates).2.1.1
        ⟨t.1 + 1, by omega⟩ = coordinates.1 (finRotate n t) := by
  rw [finRotate_apply]
  by_cases hlt : t.1 + 1 < n
  · simp only [rademacherClosedCycleToRowPath, hlt, dif_pos]
    apply congrArg coordinates.1
    apply Fin.ext
    simp [Fin.add_def, Nat.mod_eq_of_lt hlt]
  · have heq : t.1 + 1 = n := by omega
    simp only [rademacherClosedCycleToRowPath, hlt, dif_neg]
    apply congrArg coordinates.1
    apply Fin.ext
    simp [Fin.add_def, heq, hn]

theorem rademacherClosedCycle_rowPathFactor_eq_literal
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (hn : 0 < n) (M : RademacherNoncrossingMatching n)
    (word : RademacherCompatibleOccurrenceWord ε M)
    (coordinates : (Fin n → ι) × (Fin n → κ))
    (s : Fin (2 * n)) :
    rademacherRowPathOccurrenceFactor A word
        (rademacherClosedCycleToRowPath hn M coordinates).2 s =
      A (word.1 s) (rademacherCycleOccurrenceRow coordinates.1 s)
        (rademacherCycleOccurrenceCol coordinates.2 s) := by
  unfold rademacherRowPathOccurrenceFactor
  unfold rademacherCycleOccurrenceRow rademacherCycleOccurrenceCol
  let q := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  change (if q.2 then
      A (word.1 s)
        ((rademacherClosedCycleToRowPath hn M coordinates).2.1.1
          ⟨q.1.1 + 1, by omega⟩)
        ((rademacherClosedCycleToRowPath hn M coordinates).2.1.2 q.1)
    else
      A (word.1 s)
        ((rademacherClosedCycleToRowPath hn M coordinates).2.1.1
          ⟨q.1.1, by omega⟩)
        ((rademacherClosedCycleToRowPath hn M coordinates).2.1.2 q.1)) =
      A (word.1 s) (if q.2 then coordinates.1 (finRotate n q.1)
        else coordinates.1 q.1) (coordinates.2 q.1)
  cases hbit : q.2
  · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
    rw [rademacherClosedCycleToRowPath_row_current]
    rfl
  · simp only [hbit, ↓reduceIte]
    rw [rademacherClosedCycleToRowPath_row_next]
    rfl

theorem rademacherCatalanClosedPathProductCompatibility
    {ε ι κ : Type} [Fintype ε] {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanClosedPathProductCompatibility A inside outside := by
  intro word coordinates
  calc
    (∏ s : Fin (2 * (a + b + 1)),
      A (word.1 s)
        (rademacherCycleOccurrenceRow coordinates.1 s)
        (rademacherCycleOccurrenceCol coordinates.2 s)) =
        ∏ s : Fin (2 * (a + b + 1)),
          rademacherRowPathOccurrenceFactor A word
            (rademacherClosedCycleToRowPath (by omega)
              (.node inside outside) coordinates).2 s := by
      apply Finset.prod_congr rfl
      intro s _
      exact (rademacherClosedCycle_rowPathFactor_eq_literal
        A (by omega) (.node inside outside) word coordinates s).symm
    _ = rademacherRowPathWeight A (.node inside outside) word
          (rademacherClosedCycleToRowPath (by omega)
            (.node inside outside) coordinates).2 :=
      (rademacherPathOccurrenceProduct_eq_weight
        A (.node inside outside)).1 _ _ word _

/-- The formerly isolated closed-cycle scalar compatibility is unconditional:
it is just the literal even/odd path product segmented by the Catalan node. -/
theorem rademacherCatalanClosedCycleWeightCompatibility
    {ε ι κ : Type} [Fintype ε] {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanClosedCycleWeightCompatibility A inside outside :=
  rademacherCatalanClosedCycleWeightCompatibility_of_pathProduct
    A inside outside
      (rademacherCatalanClosedPathProductCompatibility A inside outside)

def rademacherCatalanCycleCoordinateEquiv
    {ε ι κ : Type} [Fintype ε] {a b : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanCycleCoordinateEquiv A inside outside :=
  rademacherCatalanCycleCoordinateEquiv_of_closedCycleWeight
    A inside outside
      (rademacherCatalanClosedCycleWeightCompatibility A inside outside)

def rademacherCatalanAssignmentOccurrenceEquiv
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanAssignmentOccurrenceEquiv A inside outside :=
  rademacherCatalanAssignmentOccurrenceEquiv_of_closedCycleWeight
    A inside outside
      (rademacherCatalanClosedCycleWeightCompatibility A inside outside)

theorem rademacherCatalanContributionTraceBridge
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanContributionTraceBridge A (.node inside outside) :=
  rademacherCatalanContributionTraceBridge_of_closedCycleWeight
    A inside outside
      (rademacherCatalanClosedCycleWeightCompatibility A inside outside)

theorem abs_rademacherNoncrossingMatchingContribution_le_catalan
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    |rademacherNoncrossingMatchingContribution A (.node inside outside)| ≤
      (Fintype.card ι : ℝ) *
        rademacherVarianceNormMax A ^ (a + b + 1) :=
  abs_rademacherNoncrossingMatchingContribution_le_of_closedCycleWeight
    A inside outside
      (rademacherCatalanClosedCycleWeightCompatibility A inside outside)

end GraphMatrixReplica
