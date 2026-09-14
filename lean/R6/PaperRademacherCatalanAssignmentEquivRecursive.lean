import R6.PaperRademacherCatalanAssignmentEquiv

/-! # Recursive occurrence segmentation for Catalan assignments

The outer pair of a Catalan node occupies positions `0` and `2*a+1` in the
actual alternating word.  The inside child occupies `1,...,2*a`, hence starts
with the opposite (column) orientation; the outside child begins at
`2*a+2` and keeps the row orientation.  This file gives the exact finite
equivalence implementing that non-contiguous split.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The genuine non-contiguous occurrence split at a Catalan node. -/
def rademacherCatalanRecursiveOccurrenceEquiv (a b : ℕ) :
    Fin 2 ⊕ (Fin (2 * a) ⊕ Fin (2 * b)) ≃
      Fin (2 * (a + b + 1)) where
  toFun
    | Sum.inl r =>
        if h : r.1 = 0 then ⟨0, by omega⟩ else ⟨2 * a + 1, by omega⟩
    | Sum.inr (Sum.inl s) => ⟨s.1 + 1, by omega⟩
    | Sum.inr (Sum.inr s) => ⟨s.1 + (2 * a + 2), by omega⟩
  invFun s :=
    if h0 : s.1 = 0 then Sum.inl ⟨0, by omega⟩
    else if hi : s.1 ≤ 2 * a then
      Sum.inr (Sum.inl ⟨s.1 - 1, by omega⟩)
    else if hr : s.1 = 2 * a + 1 then Sum.inl ⟨1, by omega⟩
    else Sum.inr (Sum.inr ⟨s.1 - (2 * a + 2), by omega⟩)
  left_inv x := by
    rcases x with r | x
    · fin_cases r <;> simp
    · rcases x with s | s
      · simp
      · have hi : ¬(s.1 + (2 * a + 2) ≤ 2 * a) := by omega
        have hr : s.1 + (2 * a + 2) ≠ 2 * a + 1 := by omega
        simp [hi, hr]
  right_inv s := by
    by_cases h0 : s.1 = 0
    · apply Fin.ext
      simp [h0]
    · by_cases hi : s.1 ≤ 2 * a
      · apply Fin.ext
        simp [h0, hi]
        omega
      · by_cases hr : s.1 = 2 * a + 1
        · apply Fin.ext
          simp [h0, hi, hr]
        · apply Fin.ext
          simp [h0, hi, hr]
          omega

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_rootFirst
    (a b : ℕ) :
    rademacherCatalanRecursiveOccurrenceEquiv a b
        (Sum.inl (0 : Fin 2)) = ⟨0, by omega⟩ := by
  rfl

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_rootSecond
    (a b : ℕ) :
    rademacherCatalanRecursiveOccurrenceEquiv a b
        (Sum.inl (1 : Fin 2)) = ⟨2 * a + 1, by omega⟩ := by
  rfl

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_inside
    (a b : ℕ) (s : Fin (2 * a)) :
    rademacherCatalanRecursiveOccurrenceEquiv a b
        (Sum.inr (Sum.inl s)) = ⟨s.1 + 1, by omega⟩ := by
  rfl

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_outside
    (a b : ℕ) (s : Fin (2 * b)) :
    rademacherCatalanRecursiveOccurrenceEquiv a b
        (Sum.inr (Sum.inr s)) =
      ⟨s.1 + (2 * a + 2), by omega⟩ := by
  rfl

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_symm_rootFirst
    (a b : ℕ) :
    (rademacherCatalanRecursiveOccurrenceEquiv a b).symm ⟨0, by omega⟩ =
      Sum.inl (0 : Fin 2) := by
  apply (rademacherCatalanRecursiveOccurrenceEquiv a b).symm_apply_eq.mpr
  exact rademacherCatalanRecursiveOccurrenceEquiv_rootFirst a b

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_symm_rootSecond
    (a b : ℕ) :
    (rademacherCatalanRecursiveOccurrenceEquiv a b).symm
        ⟨2 * a + 1, by omega⟩ = Sum.inl (1 : Fin 2) := by
  apply (rademacherCatalanRecursiveOccurrenceEquiv a b).symm_apply_eq.mpr
  exact rademacherCatalanRecursiveOccurrenceEquiv_rootSecond a b

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_symm_inside
    (a b : ℕ) (s : Fin (2 * a)) :
    (rademacherCatalanRecursiveOccurrenceEquiv a b).symm
        ⟨s.1 + 1, by omega⟩ = Sum.inr (Sum.inl s) := by
  apply (rademacherCatalanRecursiveOccurrenceEquiv a b).symm_apply_eq.mpr
  exact rademacherCatalanRecursiveOccurrenceEquiv_inside a b s

@[simp] theorem rademacherCatalanRecursiveOccurrenceEquiv_symm_outside
    (a b : ℕ) (s : Fin (2 * b)) :
    (rademacherCatalanRecursiveOccurrenceEquiv a b).symm
        ⟨s.1 + (2 * a + 2), by omega⟩ = Sum.inr (Sum.inr s) := by
  apply (rademacherCatalanRecursiveOccurrenceEquiv a b).symm_apply_eq.mpr
  exact rademacherCatalanRecursiveOccurrenceEquiv_outside a b s

/-- Every commutative occurrence product splits into the two non-contiguous
root positions, the shifted inside segment, and the outside segment. -/
theorem prod_catalanOccurrences_eq_root_inside_outside
    {R : Type} [CommMonoid R] {a b : ℕ}
    (F : Fin (2 * (a + b + 1)) → R) :
    (∏ s, F s) =
      (F ⟨0, by omega⟩ * F ⟨2 * a + 1, by omega⟩) *
        (∏ s : Fin (2 * a), F ⟨s.1 + 1, by omega⟩) *
        (∏ s : Fin (2 * b), F ⟨s.1 + (2 * a + 2), by omega⟩) := by
  let E := rademacherCatalanRecursiveOccurrenceEquiv a b
  calc
    (∏ s, F s) =
        ∏ z : Fin 2 ⊕ (Fin (2 * a) ⊕ Fin (2 * b)), F (E z) := by
      exact (E.prod_comp F).symm
    _ = (∏ r : Fin 2, F (E (Sum.inl r))) *
          ∏ z : Fin (2 * a) ⊕ Fin (2 * b), F (E (Sum.inr z)) := by
      rw [Fintype.prod_sum_type]
    _ = (F ⟨0, by omega⟩ * F ⟨2 * a + 1, by omega⟩) *
          ((∏ s : Fin (2 * a), F (E (Sum.inr (Sum.inl s)))) *
            ∏ s : Fin (2 * b), F (E (Sum.inr (Sum.inr s)))) := by
      rw [Fintype.prod_sum_type]
      simp [E, Fin.prod_univ_two]
    _ = _ := by
      simp only [E, rademacherCatalanRecursiveOccurrenceEquiv_inside,
        rademacherCatalanRecursiveOccurrenceEquiv_outside]
      ac_rfl

/-- Edge label carried by a concrete occurrence of a cycle assignment. -/
def rademacherCycleOccurrenceEdge
    {ε : Type} {n : ℕ} (choice : Fin n → ε × ε)
    (s : Fin (2 * n)) : ε :=
  let p := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  if p.2 then (choice p.1).2 else (choice p.1).1

/-- Row coordinate carried by a concrete occurrence. -/
def rademacherCycleOccurrenceRow
    {ι : Type} {n : ℕ} (rows : Fin n → ι) (s : Fin (2 * n)) : ι :=
  let p := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  if p.2 then rows (finRotate n p.1) else rows p.1

/-- Column coordinates are shared by the two occurrences at one Gram-cycle
position. -/
def rademacherCycleOccurrenceCol
    {κ : Type} {n : ℕ} (cols : Fin n → κ) (s : Fin (2 * n)) : κ :=
  let p := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  cols p.1

/-- The scalar occurrence factor is exactly evaluation at the extracted edge,
row, and column coordinates. -/
theorem rademacherAlternatingOccurrenceFactor_eq_extracted
    {ε ι κ : Type} {n : ℕ} (A : ε → Matrix ι κ ℝ)
    (rows : Fin n → ι) (cols : Fin n → κ)
    (choice : Fin n → ε × ε) (s : Fin (2 * n)) :
    rademacherAlternatingOccurrenceFactor A rows cols choice s =
      A (rademacherCycleOccurrenceEdge choice s)
        (rademacherCycleOccurrenceRow rows s)
        (rademacherCycleOccurrenceCol cols s) := by
  unfold rademacherAlternatingOccurrenceFactor
  unfold rademacherCycleOccurrenceEdge
  unfold rademacherCycleOccurrenceRow
  unfold rademacherCycleOccurrenceCol
  let p := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  change (if p.2 then
      A (choice p.1).2 (rows (finRotate n p.1)) (cols p.1)
    else A (choice p.1).1 (rows p.1) (cols p.1)) =
    A (if p.2 then (choice p.1).2 else (choice p.1).1)
      (if p.2 then rows (finRotate n p.1) else rows p.1) (cols p.1)
  cases p.2 <;> rfl

/-! ## Compatible edge words

The recursive decoration carries one edge label for every matched pair.
The following subtype is the exact occurrence-word presentation of that
data.  Unlike a `Fin n → ε × ε` choice, its coordinates are already in the
linear `2*n` order used by `pairList`; consequently the inside shift by one
and the outside shift by `2*a+2` are literal.
-/

/-- An edge-labelled occurrence word whose labels agree on every pair of a
recursive noncrossing matching. -/
def RademacherCompatibleOccurrenceWord
    (ε : Type) {n : ℕ} (M : RademacherNoncrossingMatching n) :=
  {w : Fin (2 * n) → ε //
    ∀ i j, ∀ h : (i, j) ∈ M.pairList,
      w ⟨i, (M.pairList_endpoints_lt h).1⟩ =
        w ⟨j, (M.pairList_endpoints_lt h).2⟩}

/-- The unconstrained occurrence word is exactly the original pair-valued
choice function, merely reindexed by the alternating occurrence
equivalence. -/
def rademacherChoiceOccurrenceWordEquiv (ε : Type) (n : ℕ) :
    (Fin n → ε × ε) ≃ (Fin (2 * n) → ε) where
  toFun choice s :=
    let p := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
    if p.2 then (choice p.1).2 else (choice p.1).1
  invFun w t :=
    (w (rademacherAlternatingOccurrenceIndexEquiv n (t, false)),
      w (rademacherAlternatingOccurrenceIndexEquiv n (t, true)))
  left_inv choice := by
    funext t
    apply Prod.ext <;> simp
  right_inv w := by
    funext s
    let p := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
    have hs : rademacherAlternatingOccurrenceIndexEquiv n p = s :=
      (rademacherAlternatingOccurrenceIndexEquiv n).apply_symm_apply s
    cases hp : p.2
    · change (if p.2 then
          w (rademacherAlternatingOccurrenceIndexEquiv n (p.1, true))
        else w (rademacherAlternatingOccurrenceIndexEquiv n (p.1, false))) = w s
      rw [hp]
      apply congrArg w
      rw [← hs]
      apply congrArg (rademacherAlternatingOccurrenceIndexEquiv n)
      exact Prod.ext rfl hp.symm
    · change (if p.2 then
          w (rademacherAlternatingOccurrenceIndexEquiv n (p.1, true))
        else w (rademacherAlternatingOccurrenceIndexEquiv n (p.1, false))) = w s
      rw [hp]
      apply congrArg w
      rw [← hs]
      apply congrArg (rademacherAlternatingOccurrenceIndexEquiv n)
      exact Prod.ext rfl hp.symm

@[simp] theorem rademacherChoiceOccurrenceWordEquiv_apply_even
    {ε : Type} {n : ℕ} (choice : Fin n → ε × ε) (t : Fin n) :
    rademacherChoiceOccurrenceWordEquiv ε n choice
        (rademacherAlternatingOccurrenceIndexEquiv n (t, false)) =
      (choice t).1 := by
  simp [rademacherChoiceOccurrenceWordEquiv]

@[simp] theorem rademacherChoiceOccurrenceWordEquiv_apply_odd
    {ε : Type} {n : ℕ} (choice : Fin n → ε × ε) (t : Fin n) :
    rademacherChoiceOccurrenceWordEquiv ε n choice
        (rademacherAlternatingOccurrenceIndexEquiv n (t, true)) =
      (choice t).2 := by
  simp [rademacherChoiceOccurrenceWordEquiv]

/-- The occurrence reindexing agrees pointwise with the edge extractor used
by the coefficient-cycle factorization. -/
theorem rademacherChoiceOccurrenceWordEquiv_apply
    {ε : Type} {n : ℕ} (choice : Fin n → ε × ε)
    (s : Fin (2 * n)) :
    rademacherChoiceOccurrenceWordEquiv ε n choice s =
      rademacherCycleOccurrenceEdge choice s := by
  rfl

/-- The occurrence-word value at a bounded natural position is the original
`rademacherNatEdgeLabel`. -/
theorem rademacherChoiceOccurrenceWordEquiv_apply_nat
    {ε : Type} {n : ℕ} (choice : Fin n → ε × ε)
    (i : ℕ) (hi : i < 2 * n) :
    rademacherChoiceOccurrenceWordEquiv ε n choice ⟨i, hi⟩ =
      rademacherNatEdgeLabel choice i hi := by
  let u : Fin (n * 2) := ⟨i, by omega⟩
  let p := (rademacherCanonicalMatching n).symm u
  have hp : rademacherCanonicalMatching n p = u :=
    (rademacherCanonicalMatching n).apply_symm_apply u
  rcases p with ⟨t, bit⟩
  cases bit
  · have hiEq : i = t.1 * 2 := by
      have hv := congrArg Fin.val hp
      simpa [u] using hv.symm
    subst i
    calc
      rademacherChoiceOccurrenceWordEquiv ε n choice ⟨t.1 * 2, hi⟩ =
          (choice t).1 := by
        convert rademacherChoiceOccurrenceWordEquiv_apply_even choice t <;>
          simp [rademacherAlternatingOccurrenceIndexEquiv]
      _ = rademacherNatEdgeLabel choice (t.1 * 2) hi := by
        symm
        convert rademacherNatEdgeLabel_even choice t
  · have hiEq : i = t.1 * 2 + 1 := by
      have hv := congrArg Fin.val hp
      simpa [u] using hv.symm
    subst i
    calc
      rademacherChoiceOccurrenceWordEquiv ε n choice
          ⟨t.1 * 2 + 1, hi⟩ = (choice t).2 := by
        convert rademacherChoiceOccurrenceWordEquiv_apply_odd choice t <;>
          simp [rademacherAlternatingOccurrenceIndexEquiv]
      _ = rademacherNatEdgeLabel choice (t.1 * 2 + 1) hi := by
        symm
        convert rademacherNatEdgeLabel_odd choice t

/-- Original `pairList` compatibility is literally compatibility of the
reindexed occurrence word. -/
theorem rademacherNoncrossingCompatible_iff_occurrenceWord
    {ε : Type} {n : ℕ} (M : RademacherNoncrossingMatching n)
    (choice : Fin n → ε × ε) :
    RademacherNoncrossingCompatible M choice ↔
      ∀ i j, ∀ h : (i, j) ∈ M.pairList,
        rademacherChoiceOccurrenceWordEquiv ε n choice
            ⟨i, (M.pairList_endpoints_lt h).1⟩ =
          rademacherChoiceOccurrenceWordEquiv ε n choice
            ⟨j, (M.pairList_endpoints_lt h).2⟩ := by
  unfold RademacherNoncrossingCompatible
  constructor <;> intro h i j hp
  · simpa only [rademacherChoiceOccurrenceWordEquiv_apply_nat] using h i j hp
  · simpa only [rademacherChoiceOccurrenceWordEquiv_apply_nat] using h i j hp

/-- Therefore the original compatible choices and compatible occurrence
words are equivalent, not merely equinumerous. -/
def rademacherCompatibleChoiceOccurrenceWordEquiv
    {ε : Type} {n : ℕ} (M : RademacherNoncrossingMatching n) :
    {choice : Fin n → ε × ε //
      RademacherNoncrossingCompatible M choice} ≃
      RademacherCompatibleOccurrenceWord ε M :=
  Equiv.subtypeEquiv (rademacherChoiceOccurrenceWordEquiv ε n)
    (fun choice =>
      rademacherNoncrossingCompatible_iff_occurrenceWord M choice)

/-! ## Exact Catalan-node recursion on edge words -/

/-- Restriction of a node occurrence word to the shifted inside segment. -/
def rademacherCompatibleOccurrenceWordInside
    {ε : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (w : RademacherCompatibleOccurrenceWord ε (.node inside outside)) :
    RademacherCompatibleOccurrenceWord ε inside :=
  ⟨fun s => w.1 ⟨s.1 + 1, by omega⟩, by
    intro i j hp
    apply w.2 (i + 1) (j + 1)
    simp [RademacherNoncrossingMatching.pairList, hp]⟩

/-- Restriction of a node occurrence word to the shifted outside segment. -/
def rademacherCompatibleOccurrenceWordOutside
    {ε : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (w : RademacherCompatibleOccurrenceWord ε (.node inside outside)) :
    RademacherCompatibleOccurrenceWord ε outside :=
  ⟨fun s => w.1 ⟨s.1 + (2 * a + 2), by omega⟩, by
    intro i j hp
    apply w.2 (i + (2 * a + 2)) (j + (2 * a + 2))
    simp [RademacherNoncrossingMatching.pairList, hp]⟩

/-- Assemble a compatible node word from its root label and its two child
words.  The two non-contiguous root positions both receive the same label. -/
def rademacherCompatibleOccurrenceWordAssemble
    {ε : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (x : ε × RademacherCompatibleOccurrenceWord ε inside ×
      RademacherCompatibleOccurrenceWord ε outside) :
    RademacherCompatibleOccurrenceWord ε (.node inside outside) := by
  let w : Fin (2 * (a + b + 1)) → ε := fun s =>
    if h0 : s.1 = 0 then x.1
    else if hi : s.1 ≤ 2 * a then x.2.1.1 ⟨s.1 - 1, by omega⟩
    else if hr : s.1 = 2 * a + 1 then x.1
    else x.2.2.1 ⟨s.1 - (2 * a + 2), by omega⟩
  refine ⟨w, ?_⟩
  intro i j hp
  rw [RademacherNoncrossingMatching.pairList] at hp
  rcases List.mem_cons.mp hp with hroot | hrest
  · injection hroot with hi hj
    subst i
    subst j
    change w ⟨0, by omega⟩ = w ⟨2 * a + 1, by omega⟩
    simp [w]
  · rcases List.mem_append.mp hrest with hin | hout
    · obtain ⟨⟨i', j'⟩, hp', hij⟩ := List.mem_map.mp hin
      have hi' := (inside.pairList_endpoints_lt hp').1
      have hj' := (inside.pairList_endpoints_lt hp').2
      injection hij with hi hj
      subst i
      subst j
      change w ⟨i' + 1, by omega⟩ = w ⟨j' + 1, by omega⟩
      have hchild := x.2.1.2 i' j' hp'
      simpa [w, hi', hj'] using hchild
    · obtain ⟨⟨i', j'⟩, hp', hij⟩ := List.mem_map.mp hout
      have hi' := (outside.pairList_endpoints_lt hp').1
      have hj' := (outside.pairList_endpoints_lt hp').2
      injection hij with hi hj
      subst i
      subst j
      change w ⟨i' + (2 * a + 2), by omega⟩ =
        w ⟨j' + (2 * a + 2), by omega⟩
      have hchild := x.2.2.2 i' j' hp'
      have hile : ¬(i' + (2 * a + 2) ≤ 2 * a) := by omega
      have hjle : ¬(j' + (2 * a + 2) ≤ 2 * a) := by omega
      have hieq : i' + (2 * a + 2) ≠ 2 * a + 1 := by omega
      have hjeq : j' + (2 * a + 2) ≠ 2 * a + 1 := by omega
      simpa [w, hile, hjle, hieq, hjeq] using hchild

@[simp] theorem rademacherCompatibleOccurrenceWordAssemble_rootFirst
    {ε : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (x : ε × RademacherCompatibleOccurrenceWord ε inside ×
      RademacherCompatibleOccurrenceWord ε outside) :
    (rademacherCompatibleOccurrenceWordAssemble x).1 ⟨0, by omega⟩ = x.1 := by
  simp [rademacherCompatibleOccurrenceWordAssemble]

@[simp] theorem rademacherCompatibleOccurrenceWordAssemble_rootSecond
    {ε : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (x : ε × RademacherCompatibleOccurrenceWord ε inside ×
      RademacherCompatibleOccurrenceWord ε outside) :
    (rademacherCompatibleOccurrenceWordAssemble x).1
        ⟨2 * a + 1, by omega⟩ = x.1 := by
  simp [rademacherCompatibleOccurrenceWordAssemble]

@[simp] theorem rademacherCompatibleOccurrenceWordAssemble_inside
    {ε : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (x : ε × RademacherCompatibleOccurrenceWord ε inside ×
      RademacherCompatibleOccurrenceWord ε outside)
    (s : Fin (2 * a)) :
    (rademacherCompatibleOccurrenceWordAssemble x).1
        ⟨s.1 + 1, by omega⟩ = x.2.1.1 s := by
  have h0 : s.1 + 1 ≠ 0 := by omega
  have hi : s.1 + 1 ≤ 2 * a := by omega
  simp [rademacherCompatibleOccurrenceWordAssemble, h0, hi]

@[simp] theorem rademacherCompatibleOccurrenceWordAssemble_outside
    {ε : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    (x : ε × RademacherCompatibleOccurrenceWord ε inside ×
      RademacherCompatibleOccurrenceWord ε outside)
    (s : Fin (2 * b)) :
    (rademacherCompatibleOccurrenceWordAssemble x).1
        ⟨s.1 + (2 * a + 2), by omega⟩ = x.2.2.1 s := by
  have h0 : s.1 + (2 * a + 2) ≠ 0 := by omega
  have hi : ¬(s.1 + (2 * a + 2) ≤ 2 * a) := by omega
  have hr : s.1 + (2 * a + 2) ≠ 2 * a + 1 := by omega
  simp [rademacherCompatibleOccurrenceWordAssemble, h0, hi, hr]

/-- A compatible Catalan-node edge word contains exactly one root edge and
two recursively compatible child words. -/
def rademacherCompatibleOccurrenceWordNodeEquiv
    {ε : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCompatibleOccurrenceWord ε (.node inside outside) ≃
      ε × RademacherCompatibleOccurrenceWord ε inside ×
        RademacherCompatibleOccurrenceWord ε outside where
  toFun w :=
    (w.1 ⟨0, by omega⟩,
      rademacherCompatibleOccurrenceWordInside w,
      rademacherCompatibleOccurrenceWordOutside w)
  invFun := rademacherCompatibleOccurrenceWordAssemble
  left_inv w := by
    apply Subtype.ext
    funext s
    by_cases h0 : s.1 = 0
    · have hs : s = ⟨0, by omega⟩ := Fin.ext h0
      rw [hs]
      exact rademacherCompatibleOccurrenceWordAssemble_rootFirst _
    · by_cases hi : s.1 ≤ 2 * a
      · let u : Fin (2 * a) := ⟨s.1 - 1, by omega⟩
        have hs : (⟨u.1 + 1, by omega⟩ : Fin (2 * (a + b + 1))) = s := by
          apply Fin.ext
          dsimp [u]
          omega
        rw [← hs]
        exact rademacherCompatibleOccurrenceWordAssemble_inside _ u
      · by_cases hr : s.1 = 2 * a + 1
        · have hs : s = ⟨2 * a + 1, by omega⟩ := Fin.ext hr
          rw [hs]
          rw [rademacherCompatibleOccurrenceWordAssemble_rootSecond]
          apply w.2 0 (2 * a + 1)
          simp [RademacherNoncrossingMatching.pairList]
        · let u : Fin (2 * b) :=
            ⟨s.1 - (2 * a + 2), by omega⟩
          have hs :
              (⟨u.1 + (2 * a + 2), by omega⟩ :
                Fin (2 * (a + b + 1))) = s := by
            apply Fin.ext
            dsimp [u]
            omega
          rw [← hs]
          exact rademacherCompatibleOccurrenceWordAssemble_outside _ u
  right_inv x := by
    rcases x with ⟨e, win, wout⟩
    apply Prod.ext
    · exact rademacherCompatibleOccurrenceWordAssemble_rootFirst
        (x := (e, win, wout))
    · apply Prod.ext
      · apply Subtype.ext
        funext s
        exact rademacherCompatibleOccurrenceWordAssemble_inside
          (x := (e, win, wout)) s
      · apply Subtype.ext
        funext s
        exact rademacherCompatibleOccurrenceWordAssemble_outside
          (x := (e, win, wout)) s

/-- The same recursive split, stated directly for the paper's original
pair-valued choice functions.  In particular, the inside child's first
occurrence is the parent's odd position `1`; it is not incorrectly obtained
by restricting the parent's `Fin n → ε × ε` coordinates. -/
def rademacherCompatibleChoiceNodeEquiv
    {ε : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    {choice : Fin (a + b + 1) → ε × ε //
      RademacherNoncrossingCompatible (.node inside outside) choice} ≃
      ε ×
        {choice : Fin a → ε × ε //
          RademacherNoncrossingCompatible inside choice} ×
        {choice : Fin b → ε × ε //
          RademacherNoncrossingCompatible outside choice} :=
  (rademacherCompatibleChoiceOccurrenceWordEquiv
      (.node inside outside)).trans
    ((rademacherCompatibleOccurrenceWordNodeEquiv inside outside).trans
      (Equiv.prodCongr (Equiv.refl ε)
        (Equiv.prodCongr
          (rademacherCompatibleChoiceOccurrenceWordEquiv inside).symm
          (rademacherCompatibleChoiceOccurrenceWordEquiv outside).symm)))

#print axioms rademacherChoiceOccurrenceWordEquiv
#print axioms rademacherNoncrossingCompatible_iff_occurrenceWord
#print axioms rademacherCompatibleChoiceOccurrenceWordEquiv
#print axioms rademacherCompatibleOccurrenceWordNodeEquiv
#print axioms rademacherCompatibleChoiceNodeEquiv

#print axioms rademacherCatalanRecursiveOccurrenceEquiv
#print axioms prod_catalanOccurrences_eq_root_inside_outside
#print axioms rademacherAlternatingOccurrenceFactor_eq_extracted

end GraphMatrixReplica
