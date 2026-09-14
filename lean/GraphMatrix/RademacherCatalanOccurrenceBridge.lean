import GraphMatrix.RademacherCatalanScalarIdentityProof

/-! # Typed occurrence decorations for Catalan open words

The two alternating endpoint types are modeled mutually.  A row node stores
the common root edge, its two column endpoints, the intermediate row, an
inside column decoration, and an outside row decoration.  The column version
is the transpose-typed analogue.  Thus each constructor adds exactly the two
root occurrences of a Catalan node.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Rewrite a sum carried by an arbitrary `Fintype` enumeration of a sigma
type into the canonical iterated sum.  Recursive occurrence types have a
structurally generated enumeration, so making this harmless transport
explicit keeps subsequent Fubini steps independent of typeclass reduction. -/
theorem fintypeSum_sigma_explicit
    {I : Type} {D : I → Type} {R : Type}
    [Fintype I] [(i : I) → Fintype (D i)] [AddCommMonoid R]
    (sigmaFintype : Fintype (Sigma D)) (f : Sigma D → R) :
    @Finset.sum _ _ _ (@Finset.univ _ sigmaFintype) f =
      ∑ i, ∑ d, f ⟨i, d⟩ := by
  calc
    _ = @Finset.sum _ _ _ (@Finset.univ _ Sigma.instFintype) f := by
      exact @Fintype.sum_equiv _ _ _ sigmaFintype Sigma.instFintype _
        (Equiv.refl _) f f (fun _ => rfl)
    _ = _ := Fintype.sum_sigma f

/-- Turn the two matrix entries at every Gram-cycle coordinate into a genuine
word of `2*n` typed occurrences. -/
def rademacherAlternatingOccurrenceIndexEquiv (n : ℕ) :
    Fin n × Bool ≃ Fin (2 * n) :=
  (rademacherCanonicalMatching n).trans (finCongr (by omega))

/-- The matrix-entry factor at an occurrence.  `false` is the first entry of
the Gram factor, while `true` is its transposed/rotated second entry. -/
def rademacherAlternatingOccurrenceFactor
    {ε ι κ : Type} {n : ℕ} (A : ε → Matrix ι κ ℝ)
    (rows : Fin n → ι) (cols : Fin n → κ)
    (choice : Fin n → ε × ε) (s : Fin (2 * n)) : ℝ :=
  let p := (rademacherAlternatingOccurrenceIndexEquiv n).symm s
  if p.2 then
    A (choice p.1).2 (rows (finRotate n p.1)) (cols p.1)
  else
    A (choice p.1).1 (rows p.1) (cols p.1)

/-- The occurrence-word product is definitionally the alternating Gram-cycle
coefficient after the `Fin n × Bool`/`Fin (2*n)` reindexing. -/
theorem prod_rademacherAlternatingOccurrenceFactor
    {ε ι κ : Type} [Fintype ε] {n : ℕ}
    (A : ε → Matrix ι κ ℝ) (rows : Fin n → ι)
    (cols : Fin n → κ) (choice : Fin n → ε × ε) :
    (∏ s : Fin (2 * n),
      rademacherAlternatingOccurrenceFactor A rows cols choice s) =
      rademacherGramCycleCoefficient A rows cols choice := by
  rw [← (rademacherAlternatingOccurrenceIndexEquiv n).prod_comp]
  rw [Fintype.prod_prod_type]
  unfold rademacherGramCycleCoefficient
  apply Finset.prod_congr rfl
  intro t _
  simp [rademacherAlternatingOccurrenceFactor,
    rademacherAlternatingOccurrenceIndexEquiv]
  ring

/-- Occurrence positions of a Catalan node split into its two root
occurrences, the `2*a` inside occurrences, and the `2*b` outside ones. -/
def rademacherCatalanNodeOccurrenceSegmentEquiv (a b : ℕ) :
    Fin 2 ⊕ (Fin (2 * a) ⊕ Fin (2 * b)) ≃ Fin (2 * (a + b + 1)) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] theorem rademacherCatalanNodeOccurrenceSegmentEquiv_root
    (a b : ℕ) (s : Fin 2) :
    rademacherCatalanNodeOccurrenceSegmentEquiv a b (Sum.inl s) =
      ⟨s.1, by omega⟩ := by
  apply Fin.ext
  simp [rademacherCatalanNodeOccurrenceSegmentEquiv, finSumFinEquiv]

@[simp] theorem rademacherCatalanNodeOccurrenceSegmentEquiv_inside
    (a b : ℕ) (s : Fin (2 * a)) :
    rademacherCatalanNodeOccurrenceSegmentEquiv a b
        (Sum.inr (Sum.inl s)) = ⟨s.1 + 2, by omega⟩ := by
  apply Fin.ext
  simp [rademacherCatalanNodeOccurrenceSegmentEquiv, finSumFinEquiv]
  omega

@[simp] theorem rademacherCatalanNodeOccurrenceSegmentEquiv_outside
    (a b : ℕ) (s : Fin (2 * b)) :
    rademacherCatalanNodeOccurrenceSegmentEquiv a b
        (Sum.inr (Sum.inr s)) = ⟨s.1 + (2 * a + 2), by omega⟩ := by
  apply Fin.ext
  simp [rademacherCatalanNodeOccurrenceSegmentEquiv, finSumFinEquiv]
  omega

mutual
  /-- Row-starting occurrence decorations with fixed row endpoints. -/
  def RademacherRowOccurrenceDecoration
      (ε ι κ : Type) : {n : ℕ} →
        RademacherNoncrossingMatching n → ι → ι → Type
    | 0, .empty, i, j => PLift (i = j)
    | _, .node inside outside, _i, j =>
        Σ mid : ι, Σ _e : ε, Σ c₁ : κ, Σ c₀ : κ,
          RademacherRowOccurrenceDecoration ε ι κ outside mid j ×
            RademacherColumnOccurrenceDecoration ε ι κ inside c₀ c₁

  /-- Column-starting occurrence decorations with fixed column endpoints. -/
  def RademacherColumnOccurrenceDecoration
      (ε ι κ : Type) : {n : ℕ} →
        RademacherNoncrossingMatching n → κ → κ → Type
    | 0, .empty, i, j => PLift (i = j)
    | _, .node inside outside, _i, j =>
        Σ mid : κ, Σ _e : ε, Σ r₁ : ι, Σ r₀ : ι,
          RademacherColumnOccurrenceDecoration ε ι κ outside mid j ×
            RademacherRowOccurrenceDecoration ε ι κ inside r₀ r₁
end

mutual
  @[instance_reducible] noncomputable def rademacherRowOccurrenceDecorationFintype
      {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ] :
      {n : ℕ} → (M : RademacherNoncrossingMatching n) →
        (i j : ι) →
          Fintype (RademacherRowOccurrenceDecoration ε ι κ M i j)
    | 0, .empty, i, j => by
        classical
        unfold RademacherRowOccurrenceDecoration
        change Fintype (PLift (i = j))
        infer_instance
    | _, .node inside outside, i, j => by
        classical
        unfold RademacherRowOccurrenceDecoration
        letI (c₀ c₁ : κ) : Fintype
            (RademacherColumnOccurrenceDecoration ε ι κ inside c₀ c₁) :=
          rademacherColumnOccurrenceDecorationFintype inside c₀ c₁
        letI (mid : ι) : Fintype
            (RademacherRowOccurrenceDecoration ε ι κ outside mid j) :=
          rademacherRowOccurrenceDecorationFintype outside mid j
        change Fintype
          (Σ mid : ι, Σ _e : ε, Σ c₁ : κ, Σ c₀ : κ,
            RademacherRowOccurrenceDecoration ε ι κ outside mid j ×
              RademacherColumnOccurrenceDecoration ε ι κ inside c₀ c₁)
        infer_instance

  @[instance_reducible] noncomputable def rademacherColumnOccurrenceDecorationFintype
      {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ] :
      {n : ℕ} → (M : RademacherNoncrossingMatching n) →
        (i j : κ) →
          Fintype (RademacherColumnOccurrenceDecoration ε ι κ M i j)
    | 0, .empty, i, j => by
        classical
        unfold RademacherColumnOccurrenceDecoration
        change Fintype (PLift (i = j))
        infer_instance
    | _, .node inside outside, i, j => by
        classical
        unfold RademacherColumnOccurrenceDecoration
        letI (r₀ r₁ : ι) : Fintype
            (RademacherRowOccurrenceDecoration ε ι κ inside r₀ r₁) :=
          rademacherRowOccurrenceDecorationFintype inside r₀ r₁
        letI (mid : κ) : Fintype
            (RademacherColumnOccurrenceDecoration ε ι κ outside mid j) :=
          rademacherColumnOccurrenceDecorationFintype outside mid j
        change Fintype
          (Σ mid : κ, Σ _e : ε, Σ r₁ : ι, Σ r₀ : ι,
            RademacherColumnOccurrenceDecoration ε ι κ outside mid j ×
              RademacherRowOccurrenceDecoration ε ι κ inside r₀ r₁)
        infer_instance
end

@[instance_reducible] noncomputable instance instFintypeRademacherRowOccurrenceDecoration
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    {n : ℕ} {M : RademacherNoncrossingMatching n} {i j : ι} :
    Fintype (RademacherRowOccurrenceDecoration ε ι κ M i j) :=
  rademacherRowOccurrenceDecorationFintype M i j

@[instance_reducible] noncomputable instance instFintypeRademacherColumnOccurrenceDecoration
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    {n : ℕ} {M : RademacherNoncrossingMatching n} {i j : κ} :
    Fintype (RademacherColumnOccurrenceDecoration ε ι κ M i j) :=
  rademacherColumnOccurrenceDecorationFintype M i j

mutual
  /-- Product of matrix-entry factors attached to a row decoration. -/
  def rademacherRowOccurrenceWeight
      {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) :
      {n : ℕ} → {M : RademacherNoncrossingMatching n} →
      {i j : ι} → RademacherRowOccurrenceDecoration ε ι κ M i j → ℝ
    | 0, .empty, _, _, _ => 1
    | _, .node inside outside, i, _, d =>
        A d.2.1 i d.2.2.2.1 *
          rademacherColumnOccurrenceWeight A d.2.2.2.2.2 *
          A d.2.1 d.1 d.2.2.1 *
          rademacherRowOccurrenceWeight A d.2.2.2.2.1

  /-- Product of matrix-entry factors attached to a column decoration. -/
  def rademacherColumnOccurrenceWeight
      {ε ι κ : Type} (A : ε → Matrix ι κ ℝ) :
      {n : ℕ} → {M : RademacherNoncrossingMatching n} →
      {i j : κ} → RademacherColumnOccurrenceDecoration ε ι κ M i j → ℝ
    | 0, .empty, _, _, _ => 1
    | _, .node inside outside, i, _, d =>
        A d.2.1 d.2.2.2.1 i *
          rademacherRowOccurrenceWeight A d.2.2.2.2.2 *
          A d.2.1 d.2.2.1 d.1 *
          rademacherColumnOccurrenceWeight A d.2.2.2.2.1
end

@[simp] theorem rademacherRowOccurrenceWeight_node_apply
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ)
    {a b : ℕ} (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : ι) (e : ε) (c₁ c₀ : κ)
    (dout : RademacherRowOccurrenceDecoration ε ι κ outside mid j)
    (din : RademacherColumnOccurrenceDecoration ε ι κ inside c₀ c₁) :
    @rademacherRowOccurrenceWeight ε ι κ A _ (.node inside outside) i j
        ⟨mid, e, c₁, c₀, dout, din⟩ =
      A e i c₀ * rademacherColumnOccurrenceWeight A din *
        A e mid c₁ * rademacherRowOccurrenceWeight A dout := rfl

@[simp] theorem rademacherColumnOccurrenceWeight_node_apply
    {ε ι κ : Type} (A : ε → Matrix ι κ ℝ)
    {a b : ℕ} (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (i j mid : κ) (e : ε) (r₁ r₀ : ι)
    (dout : RademacherColumnOccurrenceDecoration ε ι κ outside mid j)
    (din : RademacherRowOccurrenceDecoration ε ι κ inside r₀ r₁) :
    @rademacherColumnOccurrenceWeight ε ι κ A _ (.node inside outside) i j
        ⟨mid, e, r₁, r₀, dout, din⟩ =
      A e r₀ i * rademacherRowOccurrenceWeight A din *
        A e r₁ mid * rademacherColumnOccurrenceWeight A dout := rfl

/-- The recursively typed occurrence-decoration sums are exactly the row and
column open-word entries.  This closes both child-entry identifications on
the recursive occurrence side. -/
theorem rademacherOpenWords_apply_eq_occurrenceDecorationSums
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    (∀ i j : ι,
      rademacherRowOpenWord A M i j =
        ∑ d : RademacherRowOccurrenceDecoration ε ι κ M i j,
          rademacherRowOccurrenceWeight A d) ∧
    (∀ i j : κ,
      rademacherColumnOpenWord A M i j =
        ∑ d : RademacherColumnOccurrenceDecoration ε ι κ M i j,
          rademacherColumnOccurrenceWeight A d) := by
  induction M with
  | empty =>
      constructor
      · intro i j
        classical
        by_cases h : i = j
        · subst j
          simp [rademacherRowOpenWord,
            RademacherRowOccurrenceDecoration,
            rademacherRowOccurrenceWeight, Matrix.one_apply]
        · simp [rademacherRowOpenWord,
            RademacherRowOccurrenceDecoration,
            rademacherRowOccurrenceWeight, Matrix.one_apply, h]
      · intro i j
        classical
        by_cases h : i = j
        · subst j
          simp [rademacherColumnOpenWord,
            RademacherColumnOccurrenceDecoration,
            rademacherColumnOccurrenceWeight, Matrix.one_apply]
        · simp [rademacherColumnOpenWord,
            RademacherColumnOccurrenceDecoration,
            rademacherColumnOccurrenceWeight, Matrix.one_apply, h]
  | @node a b inside outside ihInside ihOutside =>
      constructor
      · intro i j
        classical
        simp only [rademacherRowOpenWord, rademacherRowSandwich,
          Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]
        simp_rw [ihInside.2]
        simp_rw [ihOutside.1]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        change _ = ∑ d :
          (Σ mid : ι, Σ _e : ε, Σ c₁ : κ, Σ c₀ : κ,
            RademacherRowOccurrenceDecoration ε ι κ outside mid j ×
              RademacherColumnOccurrenceDecoration ε ι κ inside c₀ c₁),
            @rademacherRowOccurrenceWeight ε ι κ A _ (.node inside outside) i j d
        conv_rhs => rw [fintypeSum_sigma_explicit]
        simp [RademacherRowOccurrenceDecoration,
          rademacherRowOccurrenceWeight, Fintype.sum_sigma,
          Fintype.sum_prod_type, Finset.sum_mul]
      · intro i j
        classical
        simp only [rademacherColumnOpenWord, rademacherColumnSandwich,
          Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]
        simp_rw [ihInside.1]
        simp_rw [ihOutside.2]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        change _ = ∑ d :
          (Σ mid : κ, Σ _e : ε, Σ r₁ : ι, Σ r₀ : ι,
            RademacherColumnOccurrenceDecoration ε ι κ outside mid j ×
              RademacherRowOccurrenceDecoration ε ι κ inside r₀ r₁),
            @rademacherColumnOccurrenceWeight ε ι κ A _ (.node inside outside) i j d
        conv_rhs => rw [fintypeSum_sigma_explicit]
        simp [RademacherColumnOccurrenceDecoration,
          rademacherColumnOccurrenceWeight, Fintype.sum_sigma,
          Fintype.sum_prod_type, Finset.sum_mul]

theorem rademacherRowOpenWord_apply_eq_occurrenceDecorationSum
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) (i j : ι) :
    rademacherRowOpenWord A M i j =
      ∑ d : RademacherRowOccurrenceDecoration ε ι κ M i j,
        rademacherRowOccurrenceWeight A d :=
  (rademacherOpenWords_apply_eq_occurrenceDecorationSums A M).1 i j

theorem rademacherColumnOpenWord_apply_eq_occurrenceDecorationSum
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) (i j : κ) :
    rademacherColumnOpenWord A M i j =
      ∑ d : RademacherColumnOccurrenceDecoration ε ι κ M i j,
        rademacherColumnOccurrenceWeight A d :=
  (rademacherOpenWords_apply_eq_occurrenceDecorationSums A M).2 i j

/-- Closing the row endpoints turns the typed open occurrence sum into the
trace of the corresponding Catalan open word. -/
theorem trace_rademacherRowOpenWord_eq_occurrenceDecorationSum
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {n : ℕ}
    (M : RademacherNoncrossingMatching n) :
    Matrix.trace (rademacherRowOpenWord A M) =
      ∑ i : ι,
        ∑ d : RademacherRowOccurrenceDecoration ε ι κ M i i,
          rademacherRowOccurrenceWeight A d := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  exact rademacherRowOpenWord_apply_eq_occurrenceDecorationSum A M i i

/-- At a node, the closed occurrence word has exactly the five boundary
indices and the common root edge appearing in the row-sandwich expansion. -/
theorem sum_nodeOccurrenceDecorations_eq_boundaryOpenWords
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    (∑ i : ι,
      ∑ d : RademacherRowOccurrenceDecoration ε ι κ
          (.node inside outside) i i,
        rademacherRowOccurrenceWeight A d) =
      ∑ rowStart : ι, ∑ rowEnd : ι,
      ∑ colStart : κ, ∑ colEnd : κ, ∑ e : ε,
        A e rowStart colStart *
          rademacherColumnOpenWord A inside colStart colEnd *
          A e rowEnd colEnd *
          rademacherRowOpenWord A outside rowEnd rowStart := by
  rw [← trace_rademacherRowOpenWord_eq_occurrenceDecorationSum
    A (.node inside outside)]
  exact trace_catalanNodeOpenWord_eq_boundary_sum A inside outside

/-- The single remaining combinatorial statement: the original compatible
cycle assignments enumerate precisely the closed typed occurrence
decorations.  Unlike an abstract trace bridge, both sides here are explicit
finite sums. -/
def RademacherCatalanNodeAssignmentsToOccurrenceIdentity
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) : Prop := by
  classical
  exact
    (∑ rowRoot : ι, ∑ rowInside : Fin a → ι,
      ∑ rowOutside : Fin b → ι,
      ∑ colRoot : κ, ∑ colInside : Fin a → κ,
      ∑ colOutside : Fin b → κ,
      ∑ choiceRoot : ε × ε, ∑ choiceInside : Fin a → ε × ε,
      ∑ choiceOutside : Fin b → ε × ε,
        let rows := (rademacherCatalanNodeRowsEquiv ι a b).symm
          (rowRoot, rowInside, rowOutside)
        let cols := (rademacherCatalanNodeColsEquiv κ a b).symm
          (colRoot, colInside, colOutside)
        let choice := (rademacherCatalanNodeChoicesEquiv ε a b).symm
          (choiceRoot, choiceInside, choiceOutside)
        if RademacherCatalanNodeCompatible inside outside choice then
          rademacherGramCycleCoefficient A rows cols choice else 0) =
      ∑ i : ι,
        ∑ d : RademacherRowOccurrenceDecoration ε ι κ
            (.node inside outside) i i,
          rademacherRowOccurrenceWeight A d

/-- All analytic and typed child-word work is complete: the former boundary
residual is equivalent exactly to the assignments-to-occurrences reindexing
above. -/
theorem rademacherCatalanNodeAssignmentsToOccurrence_iff_boundary
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanNodeAssignmentsToOccurrenceIdentity A inside outside ↔
      RademacherCatalanNodeBoundaryScalarIdentity A inside outside := by
  classical
  unfold RademacherCatalanNodeAssignmentsToOccurrenceIdentity
  unfold RademacherCatalanNodeBoundaryScalarIdentity
  rw [sum_nodeOccurrenceDecorations_eq_boundaryOpenWords A inside outside]

/-- Thus the previously isolated `NodeFinsetReindex` is neither more nor less
than the explicit assignment/occurrence enumeration statement. -/
theorem rademacherCatalanNodeFinsetReindex_iff_assignmentsToOccurrence
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    RademacherCatalanNodeFinsetReindex A inside outside ↔
      RademacherCatalanNodeAssignmentsToOccurrenceIdentity A inside outside :=
  (rademacherCatalanNodeFinsetReindex_iff_scalarProductIdentity
      A inside outside).trans
    ((rademacherCatalanNodeScalarProductIdentity_iff_boundary
      A inside outside).trans
      (rademacherCatalanNodeAssignmentsToOccurrence_iff_boundary
        A inside outside).symm)

/-- An explicit assignment-to-occurrence reindexing immediately supplies the
genuine coefficient-cycle trace bridge for that positive node. -/
theorem rademacherCatalanContributionTraceBridge_of_assignmentsToOccurrence
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    {a b : ℕ} (A : ε → Matrix ι κ ℝ)
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b)
    (h : RademacherCatalanNodeAssignmentsToOccurrenceIdentity
      A inside outside) :
    RademacherCatalanContributionTraceBridge A (.node inside outside) :=
  (rademacherCatalanNodeFinsetReindex_iff_traceBridge
      A inside outside).mp
    ((rademacherCatalanNodeFinsetReindex_iff_assignmentsToOccurrence
      A inside outside).mpr h)


end GraphMatrixReplica
