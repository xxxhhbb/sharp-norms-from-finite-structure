import GraphMatrix.GlobalEqualityState
import Mathlib.Data.Sym.Sym2.Order

/-! # Shared unordered-edge parity on global equality states

For the original paper model the equality pattern is global on all
role/replica occurrences. Consequently an edge occurrence is recorded by an
unordered pair of blocks of this one quotient, not by independent rolewise
blocks. For an equality state induced by actual globally-injective
realizations, the block pair has an injective ambient unordered-edge label.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The unordered pair of global equality blocks used by one shape-edge in
one replica. -/
def paperGlobalEdgeBlockAt (G : PaperShape) (p : ℕ)
    (S : PaperTraceGlobalEqualityState G p)
    (x : Replica (p + 1)) (e : Fin G.edges) :
    Sym2 (Quotient S.partition) :=
  s((Quotient.mk'' (G.source e, x) : Quotient S.partition),
    (Quotient.mk'' (G.target e, x) : Quotient S.partition))

/-- The quotient-block edge word, enumerated in the same replica/edge order
as `paperJointEdgeWord`. -/
def paperGlobalEdgeBlockWord (G : PaperShape) (p : ℕ)
    (S : PaperTraceGlobalEqualityState G p) :
    List (Sym2 (Quotient S.partition)) :=
  (List.ofFn (fun i : Fin (Fintype.card (Replica (p + 1))) =>
    List.ofFn (fun e : Fin G.edges =>
      paperGlobalEdgeBlockAt G p S ((paperTraceIndexEquiv p).symm i) e))).flatten

/-- Every unordered pair of global blocks occurs an even number of times. -/
def PaperTraceGlobalEqualityState.EveryEdgeBlockPairEven
    {G : PaperShape} {p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) : Prop := by
  classical
  exact ∀ z : Sym2 (Quotient S.partition),
    Even ((paperGlobalEdgeBlockWord G p S).count z)

/-- Quotient blocks of the equality partition inherit their common ambient
label, and distinct blocks have distinct labels. -/
def paperFamilyBlockEmbedding (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    Quotient (paperFamilyEqualityPartition G phis) ↪ Fin n where
  toFun := Quotient.lift (paperFamilyLabel G phis) (by
    intro a b h
    exact h)
  inj' := by
    intro q r h
    refine Quotient.inductionOn₂ q r ?_ h
    intro a b hab
    exact Quotient.sound hab

@[simp] theorem paperFamilyBlockEmbedding_mk
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n)
    (z : PaperOccurrence G p) :
    paperFamilyBlockEmbedding G phis
        (Quotient.mk'' z :
          Quotient (paperFamilyEqualityPartition G phis)) =
      paperFamilyLabel G phis z := by
  rfl

/-- Canonical ordered representative `(min,max)` of an ambient unordered
edge. -/
def paperCanonicalAmbientEdge {n : ℕ} (z : Sym2 (Fin n)) :
    Fin n × Fin n :=
  (Sym2.sortEquiv z).1

@[simp] theorem paperCanonicalAmbientEdge_mk {n : ℕ} (i j : Fin n) :
    paperCanonicalAmbientEdge s(i, j) = (min i j, max i j) := by
  simp [paperCanonicalAmbientEdge, Sym2.sortEquiv]

theorem paperCanonicalAmbientEdge_injective {n : ℕ} :
    Function.Injective (@paperCanonicalAmbientEdge n) := by
  intro z z' h
  apply (Sym2.sortEquiv (α := Fin n)).injective
  apply Subtype.ext
  exact h

/-- Map an unordered pair of equality blocks to its ambient unordered edge. -/
def paperBlockPairAmbientEdge (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    Sym2 (Quotient (paperFamilyEqualityPartition G phis)) →
      Fin n × Fin n :=
  fun z => paperCanonicalAmbientEdge
    (Sym2.map (paperFamilyBlockEmbedding G phis) z)

theorem paperBlockPairAmbientEdge_injective
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    Function.Injective (paperBlockPairAmbientEdge G phis) :=
  paperCanonicalAmbientEdge_injective.comp
    (Sym2.map.injective (paperFamilyBlockEmbedding G phis).injective)

@[simp] theorem paperBlockPairAmbientEdge_mk_mk
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n)
    (a b : PaperOccurrence G p) :
    paperBlockPairAmbientEdge G phis
        s((Quotient.mk'' a :
            Quotient (paperFamilyEqualityPartition G phis)),
          (Quotient.mk'' b :
            Quotient (paperFamilyEqualityPartition G phis))) =
      paperUnorderedPair (paperFamilyLabel G phis a)
        (paperFamilyLabel G phis b) := by
  simp [paperBlockPairAmbientEdge, paperUnorderedPair]

/-- Reindex a realization family by the enumeration used by the entry-moment
theorem. -/
def paperIndexedRealizationFamily (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n :=
  fun i => phis ((paperTraceIndexEquiv p).symm i)

/-- A global equality state is realized by `phis` when its equivalence
relation is exactly equality of the ambient vertex labels.  Stating this
explicitly avoids relying on definitional reduction through a structure
projection and makes the parity transport reusable for any such state. -/
def paperGlobalStateRealizedBy (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n) : Prop :=
  ∀ a b : PaperOccurrence G p,
    S.partition.r a b ↔
      paperFamilyLabel G phis a = paperFamilyLabel G phis b

theorem paperTraceInducedGlobalState_realizedBy
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n)
    (hCompatible : paperTraceCompatible G n p phis rows cols) :
    paperGlobalStateRealizedBy G
      (paperTraceInducedGlobalState G phis rows cols hCompatible) phis := by
  intro a b
  rfl

/-- Ambient labels give an embedding of the blocks of any state whose
partition is exactly realized by those labels. -/
def paperStateBlockEmbedding (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n)
    (hRealized : paperGlobalStateRealizedBy G S phis) :
    Quotient S.partition ↪ Fin n where
  toFun := Quotient.lift (paperFamilyLabel G phis) (by
    intro a b hab
    exact (hRealized a b).1 hab)
  inj' := by
    intro q r h
    refine Quotient.inductionOn₂ q r ?_ h
    intro a b hab
    exact Quotient.sound ((hRealized a b).2 hab)

@[simp] theorem paperStateBlockEmbedding_mk
    (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n)
    (hRealized : paperGlobalStateRealizedBy G S phis)
    (z : PaperOccurrence G p) :
    paperStateBlockEmbedding G S phis hRealized
        (Quotient.mk'' z : Quotient S.partition) =
      paperFamilyLabel G phis z := by
  rfl

/-- Injectively relabel an unordered pair of state blocks by its canonical
ambient unordered edge. -/
def paperStateBlockPairAmbientEdge (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n)
    (hRealized : paperGlobalStateRealizedBy G S phis) :
    Sym2 (Quotient S.partition) → Fin n × Fin n :=
  fun z => paperCanonicalAmbientEdge
    (Sym2.map (paperStateBlockEmbedding G S phis hRealized) z)

theorem paperStateBlockPairAmbientEdge_injective
    (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n)
    (hRealized : paperGlobalStateRealizedBy G S phis) :
    Function.Injective
      (paperStateBlockPairAmbientEdge G S phis hRealized) :=
  paperCanonicalAmbientEdge_injective.comp
    (Sym2.map.injective
      (paperStateBlockEmbedding G S phis hRealized).injective)

@[simp] theorem paperStateGlobalEdgeBlockAt_toAmbient
    (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n)
    (hRealized : paperGlobalStateRealizedBy G S phis)
    (x : Replica (p + 1)) (e : Fin G.edges) :
    paperStateBlockPairAmbientEdge G S phis hRealized
        (paperGlobalEdgeBlockAt G p S x e) =
      paperUnorderedPair (phis x (G.source e)) (phis x (G.target e)) := by
  unfold paperGlobalEdgeBlockAt paperStateBlockPairAmbientEdge
  rw [Sym2.map_mk, paperCanonicalAmbientEdge_mk]
  simp [paperUnorderedPair, paperFamilyLabel]

/-- Mapping the induced quotient-block word to ambient unordered edges gives
exactly the canonicalized ambient edge word from the entry expansion. -/
theorem paperStateBlockWord_map_eq_ambientWord
    (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n)
    (hRealized : paperGlobalStateRealizedBy G S phis) :
    (paperGlobalEdgeBlockWord G p S).map
        (paperStateBlockPairAmbientEdge G S phis hRealized) =
      paperUnorderedEdgeWord
        (paperJointEdgeWord G (paperIndexedRealizationFamily G phis)) := by
  unfold paperGlobalEdgeBlockWord paperUnorderedEdgeWord paperJointEdgeWord
    paperEmbeddingEdgeWord paperIndexedRealizationFamily
  rw [List.map_flatten, List.map_flatten]
  congr 1
  rw [List.map_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  rw [List.map_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext e
  exact paperStateGlobalEdgeBlockAt_toAmbient G S phis hRealized
    ((paperTraceIndexEquiv p).symm i) e

/-- An injective relabeling preserves the assertion that every list count is
even, including labels outside the image (whose count is zero). -/
theorem list_every_count_even_map_iff_of_injective
    {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (word : List α) (f : α → β)
    (hf : Function.Injective f) :
    (∀ y : β, Even ((word.map f).count y)) ↔
      ∀ x : α, Even (word.count x) := by
  classical
  constructor
  · intro h x
    have hx := h (f x)
    rw [List.count_map_of_injective word f hf x] at hx
    exact hx
  · intro h y
    by_cases hy : y ∈ word.map f
    · obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
      subst y
      have hx := h x
      rw [← List.count_map_of_injective word f hf x] at hx
      exact hx
    · have hzero : (word.map f).count y = 0 := by
        exact List.count_eq_zero_of_not_mem hy
      rw [hzero]
      exact Even.zero

/-- For an induced global equality state, quotient-block parity is strictly
equivalent to the original shared ambient unordered-edge parity condition. -/
theorem paperInducedEveryEdgeBlockPairEven_iff_ambientParity
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n)
    (hCompatible : paperTraceCompatible G n p phis rows cols) :
    PaperTraceGlobalEqualityState.EveryEdgeBlockPairEven
        (paperTraceInducedGlobalState G phis rows cols hCompatible) ↔
      ∀ e : Fin n × Fin n,
        Even ((paperUnorderedEdgeWord
          (paperJointEdgeWord G
            (paperIndexedRealizationFamily G phis))).count e) := by
  classical
  let S := paperTraceInducedGlobalState G phis rows cols hCompatible
  have hRealized : paperGlobalStateRealizedBy G S phis := by
    exact paperTraceInducedGlobalState_realizedBy G phis rows cols hCompatible
  let f := paperStateBlockPairAmbientEdge G S phis hRealized
  have hWord := paperStateBlockWord_map_eq_ambientWord G S phis hRealized
  change (∀ z, Even ((paperGlobalEdgeBlockWord G p S).count z)) ↔ _
  rw [← hWord]
  exact (list_every_count_even_map_iff_of_injective
    (paperGlobalEdgeBlockWord G p S) f
    (paperStateBlockPairAmbientEdge_injective G S phis hRealized)).symm


end GraphMatrixReplica
