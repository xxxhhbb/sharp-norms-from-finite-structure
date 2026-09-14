import R6.PaperRademacherCatalanAssignmentEquivRecursive

/-! # Separating Catalan edge labels from path coordinates

The existing typed occurrence decorations mix one edge label at every
Catalan node with row/column path coordinates.  This file removes the edge
labels into the genuine compatible occurrence word.  The resulting mutual
coordinate decorations contain no matching assumptions; all matching and
inside-parity transport is handled by the already proved edge-word node
equivalence.
-/

noncomputable section

namespace GraphMatrixReplica

mutual
  /-- Row-starting coordinate decoration, with no edge labels. -/
  def RademacherRowCoordinateDecoration
      (ι κ : Type) : {n : ℕ} →
        RademacherNoncrossingMatching n → ι → ι → Type
    | 0, .empty, i, j => PLift (i = j)
    | _, .node inside outside, _i, j =>
        Σ mid : ι, Σ c₁ : κ, Σ c₀ : κ,
          RademacherRowCoordinateDecoration ι κ outside mid j ×
            RademacherColumnCoordinateDecoration ι κ inside c₀ c₁

  /-- Column-starting coordinate decoration, with no edge labels. -/
  def RademacherColumnCoordinateDecoration
      (ι κ : Type) : {n : ℕ} →
        RademacherNoncrossingMatching n → κ → κ → Type
    | 0, .empty, i, j => PLift (i = j)
    | _, .node inside outside, _i, j =>
        Σ mid : κ, Σ r₁ : ι, Σ r₀ : ι,
          RademacherColumnCoordinateDecoration ι κ outside mid j ×
            RademacherRowCoordinateDecoration ι κ inside r₀ r₁
end

/-- The compatible occurrence word of the empty matching is unique. -/
def rademacherEmptyCompatibleOccurrenceWord (ε : Type) :
    RademacherCompatibleOccurrenceWord ε (.empty) :=
  ⟨fun s => Fin.elim0 s, by
    intro i j hp
    simp [RademacherNoncrossingMatching.pairList] at hp⟩

theorem rademacherCompatibleOccurrenceWord_empty_unique
    {ε : Type} (w : RademacherCompatibleOccurrenceWord ε (.empty)) :
    w = rademacherEmptyCompatibleOccurrenceWord ε := by
  apply Subtype.ext
  funext s
  exact Fin.elim0 s

mutual
  /-- A row occurrence decoration is exactly its compatible edge word and
  its edge-free coordinate decoration. -/
  noncomputable def rademacherRowOccurrenceCoordinateEquiv
      {ε ι κ : Type} : {n : ℕ} →
      (M : RademacherNoncrossingMatching n) → (i j : ι) →
        RademacherRowOccurrenceDecoration ε ι κ M i j ≃
          RademacherCompatibleOccurrenceWord ε M ×
            RademacherRowCoordinateDecoration ι κ M i j
    | 0, .empty, i, j =>
        { toFun := fun d => (rademacherEmptyCompatibleOccurrenceWord ε, d)
          invFun := fun x => x.2
          left_inv := fun _ => rfl
          right_inv := by
            intro x
            apply Prod.ext
            · exact (rademacherCompatibleOccurrenceWord_empty_unique x.1).symm
            · rfl }
    | _, @RademacherNoncrossingMatching.node a b inside outside, i, j => by
        let Eout := rademacherRowOccurrenceCoordinateEquiv
          (ε := ε) (ι := ι) (κ := κ) outside
        let Ein := rademacherColumnOccurrenceCoordinateEquiv
          (ε := ε) (ι := ι) (κ := κ) inside
        let Eword := rademacherCompatibleOccurrenceWordNodeEquiv
          (ε := ε) inside outside
        exact
          { toFun := fun d =>
              let dout := Eout d.1 j d.2.2.2.2.1
              let din := Ein d.2.2.2.1 d.2.2.1 d.2.2.2.2.2
              (Eword.symm (d.2.1, din.1, dout.1),
                ⟨d.1, d.2.2.1, d.2.2.2.1, dout.2, din.2⟩)
            invFun := fun x =>
              let edgeData := Eword x.1
              ⟨x.2.1, edgeData.1, x.2.2.1, x.2.2.2.1,
                (Eout x.2.1 j).symm (edgeData.2.2, x.2.2.2.2.1),
                (Ein x.2.2.2.1 x.2.2.1).symm
                  (edgeData.2.1, x.2.2.2.2.2)⟩
            left_inv := by
              intro d
              rcases d with ⟨mid, e, c₁, c₀, dout, din⟩
              simp [Eout, Ein, Eword]
              congr
            right_inv := by
              intro x
              rcases x with ⟨word, mid, c₁, c₀, dout, din⟩
              simp [Eout, Ein, Eword] }

  /-- The transpose-typed column analogue. -/
  noncomputable def rademacherColumnOccurrenceCoordinateEquiv
      {ε ι κ : Type} : {n : ℕ} →
      (M : RademacherNoncrossingMatching n) → (i j : κ) →
        RademacherColumnOccurrenceDecoration ε ι κ M i j ≃
          RademacherCompatibleOccurrenceWord ε M ×
            RademacherColumnCoordinateDecoration ι κ M i j
    | 0, .empty, i, j =>
        { toFun := fun d => (rademacherEmptyCompatibleOccurrenceWord ε, d)
          invFun := fun x => x.2
          left_inv := fun _ => rfl
          right_inv := by
            intro x
            apply Prod.ext
            · exact (rademacherCompatibleOccurrenceWord_empty_unique x.1).symm
            · rfl }
    | _, @RademacherNoncrossingMatching.node a b inside outside, i, j => by
        let Eout := rademacherColumnOccurrenceCoordinateEquiv
          (ε := ε) (ι := ι) (κ := κ) outside
        let Ein := rademacherRowOccurrenceCoordinateEquiv
          (ε := ε) (ι := ι) (κ := κ) inside
        let Eword := rademacherCompatibleOccurrenceWordNodeEquiv
          (ε := ε) inside outside
        exact
          { toFun := fun d =>
              let dout := Eout d.1 j d.2.2.2.2.1
              let din := Ein d.2.2.2.1 d.2.2.1 d.2.2.2.2.2
              (Eword.symm (d.2.1, din.1, dout.1),
                ⟨d.1, d.2.2.1, d.2.2.2.1, dout.2, din.2⟩)
            invFun := fun x =>
              let edgeData := Eword x.1
              ⟨x.2.1, edgeData.1, x.2.2.1, x.2.2.2.1,
                (Eout x.2.1 j).symm (edgeData.2.2, x.2.2.2.2.1),
                (Ein x.2.2.2.1 x.2.2.1).symm
                  (edgeData.2.1, x.2.2.2.2.2)⟩
            left_inv := by
              intro d
              rcases d with ⟨mid, e, r₁, r₀, dout, din⟩
              simp [Eout, Ein, Eword]
              congr
            right_inv := by
              intro x
              rcases x with ⟨word, mid, r₁, r₀, dout, din⟩
              simp [Eout, Ein, Eword] }
end

/-- At a positive node, all edge compatibility and all row/column
coordinates have now been separated by a concrete equivalence. -/
def rademacherClosedOccurrenceEdgeCoordinateEquiv
    {ε ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanNodeClosedOccurrence ε ι κ inside outside ≃
      RademacherCompatibleOccurrenceWord ε (.node inside outside) ×
        (Σ i : ι, RademacherRowCoordinateDecoration ι κ
          (.node inside outside) i i) :=
  (Equiv.sigmaCongrRight fun i =>
      rademacherRowOccurrenceCoordinateEquiv (.node inside outside) i i).trans
    { toFun := fun x => (x.2.1, ⟨x.1, x.2.2⟩)
      invFun := fun x => ⟨x.2.1, x.1, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The genuine paper assignment subtype likewise separates into its
compatible occurrence edge word and the two unconstrained cycle-coordinate
functions. -/
def rademacherCompatibleAssignmentEdgeCoordinateEquiv
    {ε ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanNodeCompatibleAssignment ε ι κ inside outside ≃
      RademacherCompatibleOccurrenceWord ε (.node inside outside) ×
        ((Fin (a + b + 1) → ι) × (Fin (a + b + 1) → κ)) where
  toFun x :=
    (rademacherCompatibleChoiceOccurrenceWordEquiv (.node inside outside)
      ⟨x.1.2.2,
        (rademacherNoncrossingCompatible_node_iff
          inside outside x.1.2.2).mpr x.2⟩,
      (x.1.1, x.1.2.1))
  invFun x :=
    let choiceData :=
      (rademacherCompatibleChoiceOccurrenceWordEquiv
        (.node inside outside)).symm x.1
    ⟨(x.2.1, x.2.2, choiceData.1),
      (rademacherNoncrossingCompatible_node_iff
        inside outside choiceData.1).mp choiceData.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    rcases x with ⟨word, rows, cols⟩
    apply Prod.ext
    · simp
    · rfl

/-- The remaining node problem after the edge recursion is a pure coordinate
equivalence plus its pointwise scalar compatibility.  The statement has no
hidden matching hypothesis: `word` ranges over the genuine compatible edge
words already proved equivalent to the original choices. -/
structure RademacherCatalanCoordinateWeightEquiv
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
      rademacherRowOccurrenceWeight A
        ((rademacherClosedOccurrenceEdgeCoordinateEquiv inside outside).symm
          (word, toEquiv coordinates)).2

/-- A solution of the now-pure coordinate reindexing constructs the exact
`RademacherCatalanAssignmentOccurrenceEquiv` requested by the trace bridge. -/
def rademacherCatalanAssignmentOccurrenceEquiv_of_coordinate
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (C : RademacherCatalanCoordinateWeightEquiv A inside outside) :
    RademacherCatalanAssignmentOccurrenceEquiv A inside outside where
  toEquiv :=
    (rademacherCompatibleAssignmentEdgeCoordinateEquiv inside outside).trans
      ((Equiv.prodCongr (Equiv.refl _ ) C.toEquiv).trans
        (rademacherClosedOccurrenceEdgeCoordinateEquiv inside outside).symm)
  weight_eq x := by
    let E := rademacherCompatibleAssignmentEdgeCoordinateEquiv
      (ε := ε) (ι := ι) (κ := κ) inside outside
    let y := E x
    have hrows : y.2.1 = x.1.1 := by rfl
    have hcols : y.2.2 = x.1.2.1 := by rfl
    have hchoice :
        ((rademacherCompatibleChoiceOccurrenceWordEquiv
          (.node inside outside)).symm y.1).1 = x.1.2.2 := by
      let choiceData :
          {choice : Fin (a + b + 1) → ε × ε //
            RademacherNoncrossingCompatible
              (.node inside outside) choice} :=
        ⟨x.1.2.2,
          (rademacherNoncrossingCompatible_node_iff
            inside outside x.1.2.2).mpr x.2⟩
      have hinv :=
        (rademacherCompatibleChoiceOccurrenceWordEquiv
          (.node inside outside)).symm_apply_apply choiceData
      exact congrArg Subtype.val hinv
    have h := C.weight_eq y.1 y.2
    dsimp only at h
    rw [hrows, hcols, hchoice] at h
    have hprod :
        ((Equiv.refl
          (RademacherCompatibleOccurrenceWord ε (.node inside outside))).prodCongr
            C.toEquiv) (E x) = (y.1, C.toEquiv y.2) := by
      rfl
    change rademacherGramCycleCoefficient A x.1.1 x.1.2.1 x.1.2.2 =
      rademacherRowOccurrenceWeight A
        ((rademacherClosedOccurrenceEdgeCoordinateEquiv inside outside).symm
          (((Equiv.refl _).prodCongr C.toEquiv) (E x))).2
    rw [hprod]
    exact h

#print axioms rademacherCompatibleOccurrenceWord_empty_unique
#print axioms rademacherRowOccurrenceCoordinateEquiv
#print axioms rademacherColumnOccurrenceCoordinateEquiv
#print axioms rademacherClosedOccurrenceEdgeCoordinateEquiv
#print axioms rademacherCompatibleAssignmentEdgeCoordinateEquiv
#print axioms rademacherCatalanAssignmentOccurrenceEquiv_of_coordinate

end GraphMatrixReplica
