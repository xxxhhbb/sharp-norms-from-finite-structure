import R6.PaperTraceMomentFormula
import R6.PaperGlobalEdgeParity
import R6.PaperGlobalStateWeight

/-! # The finite global-state polynomial for the original paper model

The state space here is genuinely global: a state is one setoid on all
role/replica occurrences, with same-replica injectivity, trace gluing, and
shared unordered-edge parity.  Its labeling multiplicity is therefore one
falling factorial in the total number of global blocks.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A globally admissible trace state is a trace equality state whose shared
unordered block-edge word has even multiplicity at every block pair. -/
abbrev PaperAdmissibleGlobalTraceState (G : PaperShape) (p : ℕ) :=
  {S : PaperTraceGlobalEqualityState G p // S.EveryEdgeBlockPairEven}

/-- Setoids on the finite global occurrence type form a finite type. -/
noncomputable instance paperOccurrenceSetoidFintype
    (G : PaperShape) (p : ℕ) :
    Fintype (Setoid (PaperOccurrence G p)) := by
  classical
  apply Fintype.ofInjective
    (fun S : Setoid (PaperOccurrence G p) =>
      fun a b => decide (S.r a b))
  intro S T h
  apply Setoid.ext
  intro a b
  exact decide_eq_decide.mp (congrFun (congrFun h a) b)

/-- The proof-carrying global trace states are finite because their only data
field is a setoid on a finite occurrence type. -/
noncomputable instance paperTraceGlobalEqualityStateFintype
    (G : PaperShape) (p : ℕ) :
    Fintype (PaperTraceGlobalEqualityState G p) := by
  classical
  apply Fintype.ofInjective PaperTraceGlobalEqualityState.partition
  intro S T h
  cases S
  cases T
  cases h
  rfl

noncomputable instance paperAdmissibleGlobalTraceStateFintype
    (G : PaperShape) (p : ℕ) :
    Fintype (PaperAdmissibleGlobalTraceState G p) :=
  Fintype.ofFinite _

/-- The polynomial weight contributed by an admissible global state. -/
def paperAdmissibleGlobalTraceStateWeight
    {G : PaperShape} {p : ℕ}
    (S : PaperAdmissibleGlobalTraceState G p) (n : ℕ) : ℕ :=
  S.1.globalLabelingWeight n

/-- The row boundary tuple forced by a realization family. -/
def paperRowsOfRealizationFamily (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    Fin (p + 1) → PaperRow G n :=
  fun i j => phis (i, false) (G.left j)

/-- The column boundary tuple forced by a realization family. -/
def paperColsOfRealizationFamily (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    Fin (p + 1) → PaperCol G n :=
  fun i j => phis (i, false) (G.right j)

/-- The trace-glue fields of a global state make its canonical boundary
tuples compatible with every realization family in that state's fiber. -/
theorem paperTraceCompatible_canonical_of_partition_eq
    (G : PaperShape) {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p)
    (phis : Replica (p + 1) → PaperRealization G n)
    (hPartition : paperFamilyEqualityPartition G phis = S.partition) :
    paperTraceCompatible G n p phis
      (paperRowsOfRealizationFamily G phis)
      (paperColsOfRealizationFamily G phis) := by
  rintro ⟨i, b⟩
  cases b with
  | false =>
      constructor <;> intro j <;> rfl
  | true =>
      constructor
      · intro j
        have h := S.leftCyclicGlue (G.left j) (by simp) i
        rw [← hPartition] at h
        exact h
      · intro j
        have h := S.rightAdjacentGlue (G.right j) (by simp) i
        rw [← hPartition] at h
        exact h.symm

/-- Boundary rows and columns compatible with a fixed realization family are
unique; hence summing them introduces no multiplicity. -/
theorem paperTraceCompatible_boundary_unique
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n)
    (hCompatible : paperTraceCompatible G n p phis rows cols) :
    rows = paperRowsOfRealizationFamily G phis ∧
      cols = paperColsOfRealizationFamily G phis := by
  constructor
  · funext i j
    exact ((hCompatible (i, false)).1 j).symm
  · funext i j
    exact ((hCompatible (i, false)).2 j).symm

/-- Reindex an entry-moment family back to semantic replicas. -/
def paperReplicaRealizationFamily (G : PaperShape) {n p : ℕ}
    (phis : Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n) :
    Replica (p + 1) → PaperRealization G n :=
  fun x => phis (paperTraceIndexEquiv p x)

/-- Fixed enumeration gives an exact equivalence between the indexed and
semantic presentations of a realization family. -/
def paperIndexedReplicaFamilyEquiv (G : PaperShape) (n p : ℕ) :
    (Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n) ≃
      (Replica (p + 1) → PaperRealization G n) where
  toFun := paperReplicaRealizationFamily G
  invFun := paperIndexedRealizationFamily G
  left_inv := by
    intro phis
    funext i
    simp [paperReplicaRealizationFamily, paperIndexedRealizationFamily]
  right_inv := by
    intro phis
    funext x
    apply Function.Embedding.ext
    intro v
    simp [paperReplicaRealizationFamily, paperIndexedRealizationFamily]

@[simp] theorem paperIndexedRealizationFamily_replica
    (G : PaperShape) {n p : ℕ}
    (phis : Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n) :
    paperIndexedRealizationFamily G
        (paperReplicaRealizationFamily G phis) = phis :=
  (paperIndexedReplicaFamilyEquiv G n p).left_inv phis

@[simp] theorem paperReplicaRealizationFamily_indexed
    (G : PaperShape) {n p : ℕ}
    (phis : Replica (p + 1) → PaperRealization G n) :
    paperReplicaRealizationFamily G
        (paperIndexedRealizationFamily G phis) = phis :=
  (paperIndexedReplicaFamilyEquiv G n p).right_inv phis

/-- The indexed compatibility predicate is the semantic compatibility of the
reindexed family. -/
theorem paperIndexedCompatible_iff_replicaCompatible
    (G : PaperShape) (n p : ℕ)
    (phis : Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n)
    (rows : Fin (p + 1) → PaperRow G n)
    (cols : Fin (p + 1) → PaperCol G n) :
    (∀ i, paperEntryCompatible G (phis i)
        (paperTraceIndexedRows G n p rows i)
        (paperTraceIndexedCols G n p cols i)) ↔
      paperTraceCompatible G n p
        (paperReplicaRealizationFamily G phis) rows cols := by
  exact paperTraceIndexedCompatible_iff G n p phis rows cols

/-- For any fixed global state, adding the parity certificate does not change
the exact falling-factorial cardinality of its realization fiber. -/
theorem paperAdmissibleGlobalTraceState_fiber_card
    {G : PaperShape} {p : ℕ}
    (S : PaperAdmissibleGlobalTraceState G p) (n : ℕ) :
    Nat.card (PaperGlobalStateRealizationFamilyFiber S.1 n) =
      paperAdmissibleGlobalTraceStateWeight S n := by
  exact S.1.realizationFamilyFiber_card_eq_globalWeight n

/-- A realization family for which the cyclic boundary tuples exist. -/
abbrev PaperTraceGluableRealizationFamily
    (G : PaperShape) (n p : ℕ) :=
  {phis : Replica (p + 1) → PaperRealization G n //
    ∃ rows : Fin (p + 1) → PaperRow G n,
      ∃ cols : Fin (p + 1) → PaperCol G n,
        paperTraceCompatible G n p phis rows cols}

def paperTraceGluableRows
    {G : PaperShape} {n p : ℕ}
    (x : PaperTraceGluableRealizationFamily G n p) :
    Fin (p + 1) → PaperRow G n :=
  Classical.choose x.2

def paperTraceGluableCols
    {G : PaperShape} {n p : ℕ}
    (x : PaperTraceGluableRealizationFamily G n p) :
    Fin (p + 1) → PaperCol G n :=
  Classical.choose (Classical.choose_spec x.2)

theorem paperTraceGluableCompatible
    {G : PaperShape} {n p : ℕ}
    (x : PaperTraceGluableRealizationFamily G n p) :
    paperTraceCompatible G n p x.1
      (paperTraceGluableRows x) (paperTraceGluableCols x) :=
  Classical.choose_spec (Classical.choose_spec x.2)

/-- The unique global trace state induced by a gluable family.  The chosen
boundary witnesses do not affect this state because its sole data field is
the family's equality partition. -/
def paperTraceGluableFamilyState
    {G : PaperShape} {n p : ℕ}
    (x : PaperTraceGluableRealizationFamily G n p) :
    PaperTraceGlobalEqualityState G p :=
  paperTraceInducedGlobalState G x.1
    (paperTraceGluableRows x) (paperTraceGluableCols x)
    (paperTraceGluableCompatible x)

@[simp] theorem paperTraceGluableFamilyState_partition
    {G : PaperShape} {n p : ℕ}
    (x : PaperTraceGluableRealizationFamily G n p) :
    (paperTraceGluableFamilyState x).partition =
      paperFamilyEqualityPartition G x.1 := by
  rfl

theorem paperTraceGlobalEqualityState_eq_of_partition_eq
    {G : PaperShape} {p : ℕ}
    {S T : PaperTraceGlobalEqualityState G p}
    (h : S.partition = T.partition) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- In a gluable family, state block parity is exactly the original shared
ambient unordered-edge parity. -/
theorem paperTraceGluableFamilyState_even_iff_ambient
    {G : PaperShape} {n p : ℕ}
    (x : PaperTraceGluableRealizationFamily G n p) :
    (paperTraceGluableFamilyState x).EveryEdgeBlockPairEven ↔
      ∀ e : Fin n × Fin n,
        Even ((paperUnorderedEdgeWord
          (paperJointEdgeWord G
            (paperIndexedRealizationFamily G x.1))).count e) := by
  exact paperInducedEveryEdgeBlockPairEven_iff_ambientParity G x.1
    (paperTraceGluableRows x) (paperTraceGluableCols x)
    (paperTraceGluableCompatible x)

/-- The surviving semantic realization families, after the unique boundary
rows and columns have been eliminated. -/
abbrev PaperAdmissibleGluableRealizationFamily
    (G : PaperShape) (n p : ℕ) :=
  {x : PaperTraceGluableRealizationFamily G n p //
    ∀ e : Fin n × Fin n,
      Even ((paperUnorderedEdgeWord
        (paperJointEdgeWord G
          (paperIndexedRealizationFamily G x.1))).count e)}

/-- The fiber of the induced-state map is exactly the previously counted
realization-family fiber; the trace-gluable witness is automatic in the
reverse direction from the state's glue fields. -/
def paperTraceGluableStateFiberEquiv
    {G : PaperShape} {n p : ℕ}
    (S : PaperTraceGlobalEqualityState G p) :
    {x : PaperTraceGluableRealizationFamily G n p //
      paperTraceGluableFamilyState x = S} ≃
      PaperGlobalStateRealizationFamilyFiber S n where
  toFun := fun x =>
    ⟨x.1.1, by
      have h := congrArg PaperTraceGlobalEqualityState.partition x.2
      simpa using h⟩
  invFun := fun phis =>
    let rows := paperRowsOfRealizationFamily G phis.1
    let cols := paperColsOfRealizationFamily G phis.1
    let hCompatible : paperTraceCompatible G n p phis.1 rows cols :=
      paperTraceCompatible_canonical_of_partition_eq G S phis.1 phis.2
    let x : PaperTraceGluableRealizationFamily G n p :=
      ⟨phis.1, ⟨rows, cols, hCompatible⟩⟩
    ⟨x, paperTraceGlobalEqualityState_eq_of_partition_eq (by
      change paperFamilyEqualityPartition G phis.1 = S.partition
      exact phis.2)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro phis
    apply Subtype.ext
    rfl

/-- Exact finite disjoint-fiber decomposition of all surviving semantic
families by their unique admissible global state. -/
def paperAdmissibleGlobalStateFibersEquivFamilies
    (G : PaperShape) (n p : ℕ) :
    (Σ S : PaperAdmissibleGlobalTraceState G p,
      PaperGlobalStateRealizationFamilyFiber S.1 n) ≃
      PaperAdmissibleGluableRealizationFamily G n p :=
  (Equiv.sigmaCongrRight (fun S : PaperAdmissibleGlobalTraceState G p =>
    (paperTraceGluableStateFiberEquiv S.1).symm)).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype paperTraceGluableFamilyState
      (fun x => (paperTraceGluableFamilyState_even_iff_ambient x).symm))

/-- The number of surviving semantic families is the finite global-state
polynomial with one falling factorial per global equality state. -/
theorem paperAdmissibleGluableRealizationFamily_card_eq_statePolynomial
    (G : PaperShape) (n p : ℕ) :
    Nat.card (PaperAdmissibleGluableRealizationFamily G n p) =
      ∑ S : PaperAdmissibleGlobalTraceState G p,
        paperAdmissibleGlobalTraceStateWeight S n := by
  calc
    Nat.card (PaperAdmissibleGluableRealizationFamily G n p) =
        Nat.card (Σ S : PaperAdmissibleGlobalTraceState G p,
          PaperGlobalStateRealizationFamilyFiber S.1 n) :=
      Nat.card_congr
        (paperAdmissibleGlobalStateFibersEquivFamilies G n p).symm
    _ = ∑ S : PaperAdmissibleGlobalTraceState G p,
          Nat.card (PaperGlobalStateRealizationFamilyFiber S.1 n) :=
      Nat.card_sigma
    _ = ∑ S : PaperAdmissibleGlobalTraceState G p,
          paperAdmissibleGlobalTraceStateWeight S n := by
      apply Finset.sum_congr rfl
      intro S _
      exact paperAdmissibleGlobalTraceState_fiber_card S n

/-- Raw row/column/indexed-family data in the exact entry-moment expansion. -/
structure PaperIndexedTraceDatum (G : PaperShape) (n p : ℕ) where
  rows : Fin (p + 1) → PaperRow G n
  cols : Fin (p + 1) → PaperCol G n
  phis : Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n

noncomputable instance paperIndexedTraceDatumFintype
    (G : PaperShape) (n p : ℕ) :
    Fintype (PaperIndexedTraceDatum G n p) := by
  classical
  apply Fintype.ofInjective
    (fun d : PaperIndexedTraceDatum G n p => (d.rows, d.cols, d.phis))
  intro d d' h
  cases d
  cases d'
  cases h
  rfl

def paperIndexedTraceDatumEquiv (G : PaperShape) (n p : ℕ) :
    PaperIndexedTraceDatum G n p ≃
      ((Fin (p + 1) → PaperRow G n) ×
        (Fin (p + 1) → PaperCol G n) ×
        (Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n)) where
  toFun := fun d => (d.rows, d.cols, d.phis)
  invFun := fun d => ⟨d.1, d.2.1, d.2.2⟩
  left_inv := by intro d; cases d; rfl
  right_inv := by intro d; cases d; rfl

/-- The surviving data triples in the actual trace/parity expansion. -/
abbrev PaperIndexedTraceSurvivor (G : PaperShape) (n p : ℕ) :=
  {d : PaperIndexedTraceDatum G n p //
    (∀ i, paperEntryCompatible G (d.phis i)
      (paperTraceIndexedRows G n p d.rows i)
      (paperTraceIndexedCols G n p d.cols i)) ∧
    ∀ e : Fin n × Fin n,
      Even ((paperUnorderedEdgeWord
        (paperJointEdgeWord G d.phis)).count e)}

/-- Reindexing the family and forgetting the uniquely forced boundary tuples
is an equivalence between surviving indexed triples and surviving semantic
families. -/
def paperIndexedTraceSurvivorEquivAdmissibleGluableFamily
    (G : PaperShape) (n p : ℕ) :
    PaperIndexedTraceSurvivor G n p ≃
      PaperAdmissibleGluableRealizationFamily G n p where
  toFun := fun d =>
    let phis := paperReplicaRealizationFamily G d.1.phis
    let x : PaperTraceGluableRealizationFamily G n p :=
      ⟨phis, ⟨d.1.rows, d.1.cols,
        (paperIndexedCompatible_iff_replicaCompatible G n p
          d.1.phis d.1.rows d.1.cols).1 d.2.1⟩⟩
    ⟨x, by
      intro e
      have hIndexed : paperIndexedRealizationFamily G phis = d.1.phis := by
        exact paperIndexedRealizationFamily_replica G d.1.phis
      rw [hIndexed]
      exact d.2.2 e⟩
  invFun := fun x =>
    ⟨{
      rows := paperTraceGluableRows x.1
      cols := paperTraceGluableCols x.1
      phis := paperIndexedRealizationFamily G x.1.1
    }, by
      constructor
      · exact (paperIndexedCompatible_iff_replicaCompatible G n p
          (paperIndexedRealizationFamily G x.1.1)
          (paperTraceGluableRows x.1)
          (paperTraceGluableCols x.1)).2 (by
            simpa using paperTraceGluableCompatible x.1)
      · exact x.2⟩
  left_inv := by
    intro d
    apply Subtype.ext
    cases d with
    | mk d hd =>
      cases d with
      | mk rows cols phis =>
        have hRep : paperTraceCompatible G n p
            (paperReplicaRealizationFamily G phis) rows cols :=
          (paperIndexedCompatible_iff_replicaCompatible G n p
            phis rows cols).1 hd.1
        have hUnique := paperTraceCompatible_boundary_unique G
          (paperReplicaRealizationFamily G phis) rows cols hRep
        have hChosen := paperTraceCompatible_boundary_unique G
            (paperReplicaRealizationFamily G phis)
            (paperTraceGluableRows
              (⟨paperReplicaRealizationFamily G phis,
                ⟨rows, cols, hRep⟩⟩ :
                PaperTraceGluableRealizationFamily G n p))
            (paperTraceGluableCols
              (⟨paperReplicaRealizationFamily G phis,
                ⟨rows, cols, hRep⟩⟩ :
                PaperTraceGluableRealizationFamily G n p))
            (paperTraceGluableCompatible
              (⟨paperReplicaRealizationFamily G phis,
                ⟨rows, cols, hRep⟩⟩ :
                PaperTraceGluableRealizationFamily G n p))
        have hRows : paperTraceGluableRows
              (⟨paperReplicaRealizationFamily G phis,
                ⟨rows, cols, hRep⟩⟩ :
                PaperTraceGluableRealizationFamily G n p) = rows :=
          hChosen.1.trans hUnique.1.symm
        have hCols : paperTraceGluableCols
              (⟨paperReplicaRealizationFamily G phis,
                ⟨rows, cols, hRep⟩⟩ :
                PaperTraceGluableRealizationFamily G n p) = cols :=
          hChosen.2.trans hUnique.2.symm
        have hPhis : paperIndexedRealizationFamily G
            (paperReplicaRealizationFamily G phis) = phis := by simp
        change ({
          rows := paperTraceGluableRows
            (⟨paperReplicaRealizationFamily G phis,
              ⟨rows, cols, hRep⟩⟩ :
              PaperTraceGluableRealizationFamily G n p)
          cols := paperTraceGluableCols
            (⟨paperReplicaRealizationFamily G phis,
              ⟨rows, cols, hRep⟩⟩ :
              PaperTraceGluableRealizationFamily G n p)
          phis := paperIndexedRealizationFamily G
            (paperReplicaRealizationFamily G phis)
        } : PaperIndexedTraceDatum G n p) =
          { rows := rows, cols := cols, phis := phis }
        rw [hRows, hCols, hPhis]
  right_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    funext replica
    simp

/-- The nested `0/1` trace expansion is the cardinality of its finite
survivor subtype. -/
theorem paperIndexedTraceIndicatorSum_eq_survivorCard
    (G : PaperShape) (n p : ℕ) :
    (∑ rows : Fin (p + 1) → PaperRow G n,
      ∑ cols : Fin (p + 1) → PaperCol G n,
        ∑ phis : Fin (Fintype.card (Replica (p + 1))) →
            PaperRealization G n,
          if ∀ i, paperEntryCompatible G (phis i)
              (paperTraceIndexedRows G n p rows i)
              (paperTraceIndexedCols G n p cols i) then
            if ∀ e, Even ((paperUnorderedEdgeWord
                (paperJointEdgeWord G phis)).count e) then
              (1 : ℝ) else 0
          else 0) =
      Nat.card (PaperIndexedTraceSurvivor G n p) := by
  classical
  let P : PaperIndexedTraceDatum G n p → Prop := fun d =>
    (∀ i, paperEntryCompatible G (d.phis i)
      (paperTraceIndexedRows G n p d.rows i)
      (paperTraceIndexedCols G n p d.cols i)) ∧
    ∀ e : Fin n × Fin n,
      Even ((paperUnorderedEdgeWord
        (paperJointEdgeWord G d.phis)).count e)
  calc
    (∑ rows : Fin (p + 1) → PaperRow G n,
      ∑ cols : Fin (p + 1) → PaperCol G n,
        ∑ phis : Fin (Fintype.card (Replica (p + 1))) →
            PaperRealization G n,
          if ∀ i, paperEntryCompatible G (phis i)
              (paperTraceIndexedRows G n p rows i)
              (paperTraceIndexedCols G n p cols i) then
            if ∀ e, Even ((paperUnorderedEdgeWord
                (paperJointEdgeWord G phis)).count e) then
              (1 : ℝ) else 0
          else 0) =
        ∑ t : (Fin (p + 1) → PaperRow G n) ×
            (Fin (p + 1) → PaperCol G n) ×
            (Fin (Fintype.card (Replica (p + 1))) → PaperRealization G n),
          if P ((paperIndexedTraceDatumEquiv G n p).symm t)
          then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro rows _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro cols _
      apply Finset.sum_congr rfl
      intro phis _
      by_cases hCompatible : ∀ i, paperEntryCompatible G (phis i)
          (paperTraceIndexedRows G n p rows i)
          (paperTraceIndexedCols G n p cols i)
      · simp [P, paperIndexedTraceDatumEquiv, hCompatible]
      · simp [P, paperIndexedTraceDatumEquiv, hCompatible]
    _ = ∑ d : PaperIndexedTraceDatum G n p,
          if P d then (1 : ℝ) else 0 := by
      symm
      apply Fintype.sum_equiv (paperIndexedTraceDatumEquiv G n p)
      intro d
      rfl
    _ = Nat.card (PaperIndexedTraceSurvivor G n p) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp [P]

/-- Exact arbitrary-positive-order global-state polynomial for the original
globally-injective graph matrix.  Shared unordered-edge parity and global
same-replica injectivity are retained in every summand. -/
theorem paperGraphMatrixGramTracePowMean_eq_globalStatePolynomial
    (G : PaperShape) (n p : ℕ) :
    paperMean (fun w : PaperNoise n =>
      Matrix.trace ((paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) ^ (p + 1))) =
      ∑ S : PaperAdmissibleGlobalTraceState G p,
        (paperAdmissibleGlobalTraceStateWeight S n : ℝ) := by
  rw [paperGraphMatrixGramTracePowMean]
  rw [paperIndexedTraceIndicatorSum_eq_survivorCard]
  have hEquivCard :
      Nat.card (PaperIndexedTraceSurvivor G n p) =
        Nat.card (PaperAdmissibleGluableRealizationFamily G n p) :=
    Nat.card_congr
      (paperIndexedTraceSurvivorEquivAdmissibleGluableFamily G n p)
  rw [hEquivCard,
    paperAdmissibleGluableRealizationFamily_card_eq_statePolynomial]
  simp

#print axioms paperTraceCompatible_canonical_of_partition_eq
#print axioms paperTraceCompatible_boundary_unique
#print axioms paperIndexedReplicaFamilyEquiv
#print axioms paperAdmissibleGlobalTraceState_fiber_card
#print axioms paperAdmissibleGlobalStateFibersEquivFamilies
#print axioms
  paperAdmissibleGluableRealizationFamily_card_eq_statePolynomial
#print axioms
  paperIndexedTraceSurvivorEquivAdmissibleGluableFamily
#print axioms paperIndexedTraceIndicatorSum_eq_survivorCard
#print axioms paperGraphMatrixGramTracePowMean_eq_globalStatePolynomial

end GraphMatrixReplica
