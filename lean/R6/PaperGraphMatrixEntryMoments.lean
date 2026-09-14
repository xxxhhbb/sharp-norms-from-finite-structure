import R6.JointEdgeRademacherExpectation

/-! # Exact original graph-matrix entry moments

This module follows the graph-matrix convention in BLNvH v2, Definition 4.5:
all shape roles are embedded injectively into one ambient finite label set, and a
single unordered ambient edge carries one shared Rademacher coordinate.
It is intentionally separate from the fully-partite joint edge sample
surrogate used by the preceding R6 state-polynomial modules.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A paper-level shape with ordered boundary embeddings and a simple
undirected edge list stored in increasing endpoint order. -/
structure PaperShape where
  roles : ℕ
  edges : ℕ
  source : Fin edges → Fin roles
  target : Fin edges → Fin roles
  edge_order : ∀ e, source e < target e
  edge_injective : Function.Injective (fun e => (source e, target e))
  leftSize : ℕ
  rightSize : ℕ
  left : Fin leftSize ↪ Fin roles
  right : Fin rightSize ↪ Fin roles

abbrev PaperRow (G : PaperShape) (n : ℕ) := Fin G.leftSize → Fin n
abbrev PaperCol (G : PaperShape) (n : ℕ) := Fin G.rightSize → Fin n
abbrev PaperRealization (G : PaperShape) (n : ℕ) := Fin G.roles ↪ Fin n
abbrev PaperNoise (n : ℕ) := Fin n → Fin n → Bool

/-- One unordered ambient edge, represented by its ordered endpoint pair. -/
def paperUnorderedPair {n : ℕ} (i j : Fin n) : Fin n × Fin n :=
  (min i j, max i j)

/-- The shared sign attached to an unordered edge of the complete graph. -/
def paperEdgeSign {n : ℕ} (w : PaperNoise n) (i j : Fin n) : ℝ :=
  if w (min i j) (max i j) then 1 else -1

theorem paperEdgeSign_symmetric {n : ℕ} (w : PaperNoise n)
    (i j : Fin n) : paperEdgeSign w i j = paperEdgeSign w j i := by
  simp [paperEdgeSign, min_comm, max_comm]

/-- A realization's edge word, with one entry for each shape edge. -/
def paperEmbeddingEdgeWord (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) : List (Fin n × Fin n) :=
  List.ofFn (fun e : Fin G.edges =>
    (phi (G.source e), phi (G.target e)))

/-- The edge word of a finite family of realizations. -/
def paperJointEdgeWord (G : PaperShape) {n q : ℕ}
    (phis : Fin q → PaperRealization G n) : List (Fin n × Fin n) :=
  (List.ofFn (fun i => paperEmbeddingEdgeWord G (phis i))).flatten

theorem paperEmbeddingEdgeWord_product (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) (phi : PaperRealization G n) :
    ((paperEmbeddingEdgeWord G phi).map
        (fun e => paperEdgeSign w e.1 e.2)).prod =
      ∏ e : Fin G.edges, paperEdgeSign w (phi (G.source e))
        (phi (G.target e)) := by
  simp [paperEmbeddingEdgeWord, Function.comp_def, List.prod_ofFn]

theorem paperJointEdgeWord_product (G : PaperShape) (n q : ℕ)
    (w : PaperNoise n) (phis : Fin q → PaperRealization G n) :
    ((paperJointEdgeWord G phis).map
        (fun e => paperEdgeSign w e.1 e.2)).prod =
      ∏ i : Fin q,
        ((paperEmbeddingEdgeWord G (phis i)).map
          (fun e => paperEdgeSign w e.1 e.2)).prod := by
  simp [paperJointEdgeWord, List.map_flatten, List.prod_flatten,
    List.map_ofFn, List.prod_ofFn]

/-- Compatibility of a global realization with a matrix entry. -/
def paperEntryCompatible (G : PaperShape)
    {n : ℕ} (phi : PaperRealization G n)
    (row : PaperRow G n) (col : PaperCol G n) : Prop :=
  (∀ i, phi (G.left i) = row i) ∧
    (∀ j, phi (G.right j) = col j)

instance paperEntryCompatibleDecidable (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) (row : PaperRow G n)
    (col : PaperCol G n) :
    Decidable (paperEntryCompatible G phi row col) :=
  inferInstanceAs (Decidable ((∀ i, phi (G.left i) = row i) ∧
    (∀ j, phi (G.right j) = col j)))

theorem paperProdConditional {ι : Type} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (f : ι → ℝ) :
    (∏ i, if P i then f i else 0) =
      if ∀ i, P i then ∏ i, f i else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The original globally-injective graph matrix. -/
def paperGraphMatrix (G : PaperShape) (n : ℕ) (w : PaperNoise n) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ := by
  classical
  exact fun row col =>
    ∑ phi : PaperRealization G n,
      if paperEntryCompatible G phi row col then
        ∏ e : Fin G.edges, paperEdgeSign w
          (phi (G.source e)) (phi (G.target e))
      else 0

theorem paperGraphMatrix_as_words (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) (row : PaperRow G n) (col : PaperCol G n) :
    paperGraphMatrix G n w row col =
      ∑ phi : PaperRealization G n,
        if paperEntryCompatible G phi row col then
          ((paperEmbeddingEdgeWord G phi).map
            (fun e => paperEdgeSign w e.1 e.2)).prod
        else 0 := by
  classical
  simp [paperGraphMatrix, paperEmbeddingEdgeWord_product]

/-- Product expansion before taking the ambient sign expectation. -/
theorem paperEntryProductExpansion (G : PaperShape) (n q : ℕ)
    (w : PaperNoise n) (rows : Fin q → PaperRow G n)
    (cols : Fin q → PaperCol G n) :
    (∏ i : Fin q, paperGraphMatrix G n w (rows i) (cols i)) =
      ∑ phis : Fin q → PaperRealization G n,
        if ∀ i, paperEntryCompatible G (phis i) (rows i) (cols i) then
          ((paperJointEdgeWord G phis).map
            (fun e => paperEdgeSign w e.1 e.2)).prod
        else 0 := by
  classical
  simp_rw [paperGraphMatrix_as_words]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro phis _
  rw [paperProdConditional, paperJointEdgeWord_product]
  by_cases h : ∀ i, paperEntryCompatible G (phis i) (rows i) (cols i) <;>
    simp only [h, ite_false]

/-- Uniform average over the finite product of all ordered ambient bits. -/
def paperMean {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ a, f a

theorem paperMean_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) :
    paperMean (fun a => f (e a)) = paperMean f := by
  unfold paperMean
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

theorem paperMean_sum {α β : Type} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    paperMean (fun a => ∑ b, f a b) = ∑ b, paperMean (fun a => f a b) := by
  unfold paperMean
  rw [Finset.sum_comm, Finset.mul_sum]

theorem paperMean_zero {α : Type} [Fintype α] :
    paperMean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [paperMean]

def paperSign (b : Bool) : ℝ := if b then 1 else -1

theorem paperSign_power_sum (k : ℕ) :
    (∑ b : Bool, paperSign b ^ k) = if Even k then 2 else 0 := by
  simp only [Fintype.sum_bool, paperSign, Bool.false_eq_true, if_false,
    if_true, one_pow]
  by_cases hk : Even k
  · rw [hk.neg_one_pow, if_pos hk]; norm_num
  · have ho : Odd k := Nat.not_even_iff_odd.mp hk
    rw [ho.neg_one_pow, if_neg hk]; norm_num

theorem paperMean_sign_monomial {ι : Type} [Fintype ι]
    [DecidableEq ι] (k : ι → ℕ) :
    paperMean (fun w : ι → Bool => ∏ i, paperSign (w i) ^ k i) =
      if ∀ i, Even (k i) then 1 else 0 := by
  classical
  unfold paperMean
  have heq := Fintype.prod_sum
    (fun (i : ι) (b : Bool) => paperSign b ^ k i)
  dsimp only at heq ⊢
  rw [← heq]
  simp_rw [paperSign_power_sum]
  by_cases h : ∀ i, Even (k i)
  · simp [h]
  · have hz : (∏ i, if Even (k i) then (2 : ℝ) else 0) = 0 := by
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    rw [hz, mul_zero, if_neg h]

theorem paperWordProduct_eq_powers {ι : Type} [Fintype ι]
    [DecidableEq ι] (word : List ι) (f : ι → ℝ) :
    (word.map f).prod = ∏ i, f i ^ word.count i := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp [List.count_eq_zero.mpr (by simpa using hi)]

theorem paperMean_sign_word {ι : Type} [Fintype ι] [DecidableEq ι]
    (word : List ι) :
    paperMean (fun w : ι → Bool =>
      (word.map (fun i => paperSign (w i))).prod) =
      if ∀ i, Even (word.count i) then 1 else 0 := by
  simp_rw [paperWordProduct_eq_powers]
  exact paperMean_sign_monomial (fun i => word.count i)

def paperUnorderedEdgeWord {n : ℕ}
    (edges : List (Fin n × Fin n)) : List (Fin n × Fin n) :=
  edges.map (fun e => paperUnorderedPair e.1 e.2)

theorem paperOriginalEdgeWordMoment (n : ℕ)
    (edges : List (Fin n × Fin n)) :
    paperMean (fun w : PaperNoise n =>
        (edges.map (fun e => paperEdgeSign w e.1 e.2)).prod) =
      if ∀ e, Even ((paperUnorderedEdgeWord edges).count e) then
        1 else 0 := by
  rw [← paperMean_equiv (Equiv.curry (Fin n) (Fin n) Bool)]
  have heq :
      (fun w : (Fin n × Fin n) → Bool =>
        (edges.map (fun e => paperEdgeSign
          ((Equiv.curry (Fin n) (Fin n) Bool) w) e.1 e.2)).prod) =
      (fun w => ((paperUnorderedEdgeWord edges).map
        (fun e => paperSign (w e))).prod) := by
    funext w
    simp only [paperUnorderedEdgeWord, List.map_map]
    rfl
  rw [heq]
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
    paperMean_sign_word (paperUnorderedEdgeWord edges)

theorem paperOriginalEntryJointMoment (G : PaperShape) (n q : ℕ)
    (rows : Fin q → PaperRow G n)
    (cols : Fin q → PaperCol G n) :
    paperMean (fun w : PaperNoise n =>
        ∏ i, paperGraphMatrix G n w (rows i) (cols i)) =
      ∑ phis : Fin q → PaperRealization G n,
        if ∀ i, paperEntryCompatible G (phis i) (rows i) (cols i) then
          if ∀ e, Even ((paperUnorderedEdgeWord
              (paperJointEdgeWord G phis)).count e) then
            (1 : ℝ) else 0
        else 0 := by
  classical
  simp_rw [paperEntryProductExpansion]
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro phis _
  by_cases h : ∀ i, paperEntryCompatible G (phis i) (rows i) (cols i)
  · simp only [if_pos h]
    exact paperOriginalEdgeWordMoment n (paperJointEdgeWord G phis)
  · simp only [if_neg h, paperMean_zero]

#print axioms paperEmbeddingEdgeWord_product
#print axioms paperEntryProductExpansion
#print axioms paperOriginalEdgeWordMoment
#print axioms paperOriginalEntryJointMoment

end GraphMatrixReplica
