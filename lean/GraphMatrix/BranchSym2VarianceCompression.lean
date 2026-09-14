import GraphMatrix.BranchTreeDyadicTraceConcrete
import Mathlib.Data.Sym.Sym2.Order

/-! # Symmetric-pair variance compression at branch nodes

The distinguished paper sign is indexed by an unordered ambient edge.  On
one fixed strict orientation piece, however, exactly one of the two ordered
representatives can carry a nonzero coefficient.  This file records that
support fact before comparing the symmetric coefficient flattenings with the
two literal successor stages.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

set_option maxHeartbeats 1600000

/-! ## Pure aggregation and oriented support -/

theorem paperSym2AggregatedCoefficientFamily_mk
    {n : ℕ} {rows cols : Type} [Fintype rows] [Fintype cols]
    (A : Fin n → Fin n → Matrix rows cols ℝ) (a b : Fin n) :
    paperSym2AggregatedCoefficientFamily A s(a, b) =
      if a = b then A a b else A a b + A b a := by
  classical
  ext row col
  unfold paperSym2AggregatedCoefficientFamily
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab, Matrix.add_apply]
    rw [← Finset.sum_filter]
    have hfilter :
        Finset.univ.filter
            (fun x : Fin n × Fin n => s(x.1, x.2) = s(a, b)) =
          {(a, b), (b, a)} := by
      ext x
      simp [Sym2.eq_iff]
    rw [hfilter]
    exact Finset.sum_pair (fun h => hab (congrArg Prod.fst h))

/-- A coefficient on the wrong ordered representative of the fixed
orientation piece vanishes. -/
theorem paperBranchStageOrderedCoefficient_eq_zero_of_orientation_ne
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (a b : Fin n)
    (hwrong : orientation (paperUnconditionalOrderingEdgeAt G stage hstage) ≠
      decide (a < b)) :
    paperBranchStageOrderedCoefficient G n orientation D stage hstage w a b = 0 := by
  classical
  ext row col
  unfold paperBranchStageOrderedCoefficient
  apply Finset.sum_eq_zero
  intro assignment _hassignment
  split_ifs with hEntry
  · have hbad : ¬(Function.Injective assignment ∧
        paperAssignmentOrientationCompatible G orientation assignment) := by
      intro hgood
      apply hwrong
      have he := congrFun hgood.2
        (paperUnconditionalOrderingEdgeAt G stage hstage)
      simpa [paperAssignmentOrientationCompatible, hEntry.2.2.1,
        hEntry.2.2.2] using he
    simp [paperOrientedAssignmentWeight, hbad]
  · rfl

theorem paperBranchStageOrderedCoefficient_diag_eq_zero
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (a : Fin n) :
    paperBranchStageOrderedCoefficient G n orientation D stage hstage w a a = 0 := by
  classical
  ext row col
  unfold paperBranchStageOrderedCoefficient
  apply Finset.sum_eq_zero
  intro assignment _hassignment
  split_ifs with hEntry
  · have hbad : ¬ Function.Injective assignment := by
      intro hinj
      have hroles : G.source (paperUnconditionalOrderingEdgeAt G stage hstage) ≠
          G.target (paperUnconditionalOrderingEdgeAt G stage hstage) :=
        ne_of_lt (G.edge_order _)
      apply hroles
      apply hinj
      simpa [hEntry.2.2.1, hEntry.2.2.2]
    simp [paperOrientedAssignmentWeight, hbad]
  · rfl

/-! ## Canonical oriented representative -/

/-- Choose the unique ordered representative compatible with one strict
orientation bit. -/
def paperOrientedSym2Pair {n : ℕ} (o : Bool) (z : Sym2 (Fin n)) :
    Fin n × Fin n :=
  if o then (Sym2.sortEquiv z).1
  else ((Sym2.sortEquiv z).1.2, (Sym2.sortEquiv z).1.1)

theorem paperOrientedSym2Pair_injective {n : ℕ} (o : Bool) :
    Function.Injective (paperOrientedSym2Pair (n := n) o) := by
  intro z z' h
  unfold paperOrientedSym2Pair at h
  cases o
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    apply Sym2.sortEquiv.injective
    apply Subtype.ext
    exact Prod.swap_injective h
  · simp only [↓reduceIte] at h
    exact Sym2.sortEquiv.injective (Subtype.ext h)

def paperOrientedSym2Embedding {n : ℕ} (o : Bool) :
    Sym2 (Fin n) ↪ Fin n × Fin n :=
  ⟨paperOrientedSym2Pair o, paperOrientedSym2Pair_injective o⟩

theorem paperOrientedSym2Pair_mk_of_matches
    {n : ℕ} (o : Bool) (a b : Fin n) (h : o = decide (a < b)) :
    paperOrientedSym2Pair o s(a, b) = (a, b) := by
  by_cases hab : a ≤ b
  · by_cases heq : a = b
    · subst b
      have ho : o = false := by simpa using h
      simp [paperOrientedSym2Pair, ho]
    · have hlt : a < b := lt_of_le_of_ne hab heq
      have ho : o = true := by simpa [hlt] using h
      simp [paperOrientedSym2Pair, ho, hab]
  · have hba : b ≤ a := le_of_not_ge hab
    have hba' : b < a := lt_of_le_of_ne hba (Ne.symm (by
      intro heq
      subst b
      exact hab le_rfl))
    have ho : o = false := by simpa [hba', not_lt.mpr hba] using h
    simp [paperOrientedSym2Pair, ho, hba]

theorem paperBranchStageOrderedCoefficient_eq_zero_of_not_mem_orientedRange
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (p : Fin n × Fin n)
    (hout : p ∉ Set.range (paperOrientedSym2Embedding
      (orientation (paperUnconditionalOrderingEdgeAt G stage hstage)))) :
    paperBranchStageOrderedCoefficient G n orientation D stage hstage w
        p.1 p.2 = 0 := by
  by_cases hwrong :
      orientation (paperUnconditionalOrderingEdgeAt G stage hstage) ≠
        decide (p.1 < p.2)
  · exact paperBranchStageOrderedCoefficient_eq_zero_of_orientation_ne
      G n orientation D stage hstage w p.1 p.2 hwrong
  · exfalso
    apply hout
    refine ⟨s(p.1, p.2), ?_⟩
    exact paperOrientedSym2Pair_mk_of_matches _ _ _ (not_ne_iff.mp hwrong)

/-- On a fixed orientation piece, aggregation over the unordered sign fiber
selects exactly the unique oriented representative.  Diagonal fibers vanish
because a paper assignment is globally injective. -/
theorem paperBranchStageSym2Coefficient_eq_orientedRepresentative
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) (z : Sym2 (Fin n)) :
    paperBranchStageSym2Coefficient G n orientation D stage hstage w z =
      paperBranchStageOrderedCoefficient G n orientation D stage hstage w
        (paperOrientedSym2Pair
          (orientation (paperUnconditionalOrderingEdgeAt G stage hstage)) z).1
        (paperOrientedSym2Pair
          (orientation (paperUnconditionalOrderingEdgeAt G stage hstage)) z).2 := by
  induction z using Sym2.inductionOn with
  | _ a b =>
      unfold paperBranchStageSym2Coefficient
      rw [paperSym2AggregatedCoefficientFamily_mk]
      by_cases hab : a = b
      · subst b
        rw [if_pos rfl]
        simpa [paperOrientedSym2Pair] using
          (paperBranchStageOrderedCoefficient_diag_eq_zero
            G n orientation D stage hstage w a).symm
      · rw [if_neg hab]
        rcases lt_trichotomy a b with hablt | habeq | hbalt
        · cases ho : orientation
              (paperUnconditionalOrderingEdgeAt G stage hstage)
          · have hzero :
                paperBranchStageOrderedCoefficient G n orientation D stage
                    hstage w a b = 0 :=
              paperBranchStageOrderedCoefficient_eq_zero_of_orientation_ne
                G n orientation D stage hstage w a b (by simp [ho, hablt])
            rw [hzero, zero_add]
            simp [paperOrientedSym2Pair, ho, hablt.le, not_le.mpr hablt]
          · have hzero :
                paperBranchStageOrderedCoefficient G n orientation D stage
                    hstage w b a = 0 :=
              paperBranchStageOrderedCoefficient_eq_zero_of_orientation_ne
                G n orientation D stage hstage w b a (by
                  intro h
                  have hdec : decide (b < a) = true := h.symm.trans ho
                  exact (not_lt.mpr hablt.le) (of_decide_eq_true hdec))
            rw [hzero, add_zero]
            simp [paperOrientedSym2Pair, ho, hablt.le, not_le.mpr hablt]
        · exact (hab habeq).elim
        · cases ho : orientation
              (paperUnconditionalOrderingEdgeAt G stage hstage)
          · have hzero :
                paperBranchStageOrderedCoefficient G n orientation D stage
                    hstage w b a = 0 :=
              paperBranchStageOrderedCoefficient_eq_zero_of_orientation_ne
                G n orientation D stage hstage w b a (by simp [ho, hbalt])
            rw [hzero, add_zero]
            simp [paperOrientedSym2Pair, ho, hbalt.le, not_le.mpr hbalt]
          · have hzero :
                paperBranchStageOrderedCoefficient G n orientation D stage
                    hstage w a b = 0 :=
              paperBranchStageOrderedCoefficient_eq_zero_of_orientation_ne
                G n orientation D stage hstage w a b (by
                  intro h
                  have hdec : decide (a < b) = true := h.symm.trans ho
                  exact (not_lt.mpr hbalt.le) (of_decide_eq_true hdec))
            rw [hzero, zero_add]
            simp [paperOrientedSym2Pair, ho, hbalt.le, not_le.mpr hbalt]

/-! ## Reindexing coefficient sums through the supported representative -/

theorem paperBranch_sum_orderedCoefficient_eq_sum_sym2Coefficient
    {M : Type} [AddCommMonoid M]
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n)
    (F : Matrix
        (PaperYRowIndex G n (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate D stage))
        (PaperYColIndex G n (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate D stage)) ℝ → M)
    (hFzero : F 0 = 0) :
    (∑ p : Fin n × Fin n,
        F (paperBranchStageOrderedCoefficient G n orientation D stage hstage w
          p.1 p.2)) =
      ∑ z : Sym2 (Fin n),
        F (paperBranchStageSym2Coefficient
          G n orientation D stage hstage w z) := by
  classical
  let o := orientation (paperUnconditionalOrderingEdgeAt G stage hstage)
  let emb := paperOrientedSym2Embedding (n := n) o
  calc
    (∑ p : Fin n × Fin n,
        F (paperBranchStageOrderedCoefficient G n orientation D stage hstage w
          p.1 p.2)) =
      (∑ p ∈ Finset.univ.image emb,
        F (paperBranchStageOrderedCoefficient G n orientation D stage hstage w
          p.1 p.2)) := by
        symm
        apply Finset.sum_subset (by simp)
        intro p _hp hnot
        rw [paperBranchStageOrderedCoefficient_eq_zero_of_not_mem_orientedRange,
          hFzero]
        simpa [emb, o, Set.mem_range] using hnot
    _ = ∑ z : Sym2 (Fin n),
        F (paperBranchStageOrderedCoefficient G n orientation D stage hstage w
          (emb z).1 (emb z).2) := by
        rw [Finset.sum_image]
        exact Set.injOn_of_injective emb.injective
    _ = ∑ z : Sym2 (Fin n),
        F (paperBranchStageSym2Coefficient
          G n orientation D stage hstage w z) := by
        apply Finset.sum_congr rfl
        intro z _hz
        rw [paperBranchStageSym2Coefficient_eq_orientedRepresentative]
        rfl

theorem paperBranchStageSym2_rowVariance_eq_ordered
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    rademacherRowVariance
        (paperBranchStageSym2Coefficient G n orientation D stage hstage w) =
      ∑ p : Fin n × Fin n,
        paperBranchStageOrderedCoefficient G n orientation D stage hstage w
            p.1 p.2 *
          (paperBranchStageOrderedCoefficient G n orientation D stage hstage w
            p.1 p.2).transpose := by
  unfold rademacherRowVariance
  symm
  exact paperBranch_sum_orderedCoefficient_eq_sum_sym2Coefficient
    G n orientation D stage hstage w
    (fun A => A * A.transpose) (by simp)

theorem paperBranchStageSym2_columnVariance_eq_ordered
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    rademacherColumnVariance
        (paperBranchStageSym2Coefficient G n orientation D stage hstage w) =
      ∑ p : Fin n × Fin n,
        (paperBranchStageOrderedCoefficient G n orientation D stage hstage w
            p.1 p.2).transpose *
          paperBranchStageOrderedCoefficient G n orientation D stage hstage w
            p.1 p.2 := by
  unfold rademacherColumnVariance
  symm
  exact paperBranch_sum_orderedCoefficient_eq_sum_sym2Coefficient
    G n orientation D stage hstage w
    (fun A => A.transpose * A) (by simp)

theorem paperMatrixRademacherColFlattening_eq_rowBlock
    {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
    {n : ℕ}
    (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ)
    (w : ι → PaperNoise n) :
    paperMatrixRademacherColFlattening A w =
      rademacherRowBlockMatrix
        (fun p : Fin n × Fin n => A
          w p.1 p.2) := by
  rfl

theorem paperMatrixRademacherRowFlattening_eq_transpose_rowBlock
    {ι rows cols : Type} [Fintype ι] [Fintype rows] [Fintype cols]
    {n : ℕ}
    (A : (ι → PaperNoise n) → Fin n → Fin n → Matrix rows cols ℝ)
    (w : ι → PaperNoise n) :
    paperMatrixRademacherRowFlattening A w =
      (rademacherRowBlockMatrix
        (fun p : Fin n × Fin n => (A w p.1 p.2).transpose)).transpose := by
  rfl

/-- The column child is exactly the row-variance norm of the true unordered
coefficient family. -/
theorem paperBranch_colFlattening_norm_mul_self_eq_rowVariance
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    ‖paperMatrixRademacherColFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ *
      ‖paperMatrixRademacherColFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ =
      ‖rademacherRowVariance
        (paperBranchStageSym2Coefficient
          G n orientation D stage hstage w)‖ := by
  let A : Fin n × Fin n → Matrix
      (PaperYRowIndex G n (paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage))
      (PaperYColIndex G n (paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage)) ℝ :=
    fun p => paperBranchStageOrderedCoefficient
      G n orientation D stage hstage w p.1 p.2
  calc
    ‖paperMatrixRademacherColFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ *
      ‖paperMatrixRademacherColFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ =
        ‖rademacherRowVariance A‖ := by
          simpa [A, paperMatrixRademacherColFlattening_eq_rowBlock] using
            (rademacherRowBlock_norm_sq A)
    _ = ‖rademacherRowVariance
        (paperBranchStageSym2Coefficient
          G n orientation D stage hstage w)‖ := by
          congr 1
          unfold rademacherRowVariance
          simpa [A, rademacherRowVariance] using
            (paperBranchStageSym2_rowVariance_eq_ordered
              G n orientation D stage hstage w).symm

/-- The row child is exactly the column-variance norm of the true unordered
coefficient family. -/
theorem paperBranch_rowFlattening_norm_mul_self_eq_columnVariance
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (D : PaperCanonicalNCKSides G) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    ‖paperMatrixRademacherRowFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ *
      ‖paperMatrixRademacherRowFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ =
      ‖rademacherColumnVariance
        (paperBranchStageSym2Coefficient
          G n orientation D stage hstage w)‖ := by
  let A : Fin n × Fin n → Matrix
      (PaperYColIndex G n (paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage))
      (PaperYRowIndex G n (paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate D stage)) ℝ :=
    fun p => (paperBranchStageOrderedCoefficient
      G n orientation D stage hstage w p.1 p.2).transpose
  have htranspose :
      ‖(rademacherRowBlockMatrix A).transpose‖ =
        ‖rademacherRowBlockMatrix A‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose (rademacherRowBlockMatrix A)
  calc
    ‖paperMatrixRademacherRowFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ *
      ‖paperMatrixRademacherRowFlattening
        (paperBranchStageOrderedCoefficient
          G n orientation D stage hstage) w‖ =
        ‖rademacherRowVariance A‖ := by
          rw [paperMatrixRademacherRowFlattening_eq_transpose_rowBlock,
            htranspose]
          exact rademacherRowBlock_norm_sq A
    _ = ‖rademacherColumnVariance
        (paperBranchStageSym2Coefficient
          G n orientation D stage hstage w)‖ := by
          congr 1
          unfold rademacherRowVariance rademacherColumnVariance
          simpa [A, rademacherColumnVariance] using
            (paperBranchStageSym2_columnVariance_eq_ordered
              G n orientation D stage hstage w).symm

/-! ## Identification with the two actual branch children -/

theorem paperNCKBranchColChild_norm_mul_self_eq_rowVariance
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (history : List Bool)
    (hstage : history.length < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    ‖paperNCKBranchStageMatrix G n orientation
        (paperNCKBranchChild true history) w‖ *
      ‖paperNCKBranchStageMatrix G n orientation
        (paperNCKBranchChild true history) w‖ =
      ‖rademacherRowVariance
        (paperBranchStageSym2Coefficient G n orientation
          (paperNCKBranchSides G history) history.length hstage w)‖ := by
  rw [paperNCKBranchColChildMatrix_reindex_orderedCoefficient]
  exact paperBranch_colFlattening_norm_mul_self_eq_rowVariance
    G n orientation (paperNCKBranchSides G history) history.length hstage w

theorem paperNCKBranchRowChild_norm_mul_self_eq_columnVariance
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (history : List Bool)
    (hstage : history.length < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    ‖paperNCKBranchStageMatrix G n orientation
        (paperNCKBranchChild false history) w‖ *
      ‖paperNCKBranchStageMatrix G n orientation
        (paperNCKBranchChild false history) w‖ =
      ‖rademacherColumnVariance
        (paperBranchStageSym2Coefficient G n orientation
          (paperNCKBranchSides G history) history.length hstage w)‖ := by
  rw [paperNCKBranchRowChildMatrix_reindex_orderedCoefficient]
  exact paperBranch_rowFlattening_norm_mul_self_eq_columnVariance
    G n orientation (paperNCKBranchSides G history) history.length hstage w

theorem paperBranch_varianceNormMax_eq_max_childSquares
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (history : List Bool)
    (hstage : history.length < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    rademacherVarianceNormMax
        (paperBranchStageSym2Coefficient G n orientation
          (paperNCKBranchSides G history) history.length hstage w) =
      max
        (‖paperNCKBranchStageMatrix G n orientation
            (paperNCKBranchChild true history) w‖ ^ 2)
        (‖paperNCKBranchStageMatrix G n orientation
            (paperNCKBranchChild false history) w‖ ^ 2) := by
  unfold rademacherVarianceNormMax
  rw [← paperNCKBranchColChild_norm_mul_self_eq_rowVariance,
    ← paperNCKBranchRowChild_norm_mul_self_eq_columnVariance]
  simp only [pow_two]

/-! ## The honest conditional L1 analytic interface

The dyadic trace route is useful for proving a fixed-coefficient NCK bound,
but the branch iteration required by formula (28) is an L1 conditional
statement.  Keeping the other edge copies fixed avoids an invalid exchange
between an outer mean and a high power.
-/

def PaperBranchSym2CoefficientConditionalL1NCK
    (G : PaperShape) (C : ℝ) (p n : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (stage : ℕ)
      (hstage : stage < paperUnconditionalOrderingLength G)
      (D : PaperCanonicalNCKSides G)
      (w : PaperDecoupledNoise G n),
    paperMean (fun eta : Sym2 (Fin n) → Bool =>
      ‖paperRademacherMatrixSum
        (paperBranchStageSym2Coefficient
          G n orientation D stage hstage w) eta‖) ≤
      (C * Real.sqrt p) *
        (‖paperMatrixRademacherRowFlattening
            (paperBranchStageOrderedCoefficient
              G n orientation D stage hstage) w‖ +
          ‖paperMatrixRademacherColFlattening
            (paperBranchStageOrderedCoefficient
              G n orientation D stage hstage) w‖)

theorem paperMean_prod_eq_iterated
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A × B → ℝ) :
    paperMean f =
      paperMean (fun a : A => paperMean (fun b : B => f (a, b))) := by
  unfold paperMean
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  push_cast
  rw [← Finset.mul_sum]
  ring

/-- Resampling one coordinate is a permutation of a product sample together
with the overwritten old coordinate. -/
def paperCoordinateResampleEquiv
    {I B : Type} [DecidableEq I] (e : I) :
    ((I → B) × B) ≃ ((I → B) × B) where
  toFun x := (Function.update x.1 e x.2, x.1 e)
  invFun x := (Function.update x.1 e x.2, x.1 e)
  left_inv := by
    rintro ⟨w, b⟩
    apply Prod.ext
    · funext i
      by_cases hi : i = e
      · subst i
        simp
      · simp [Function.update_of_ne hi]
    · simp
  right_inv := by
    rintro ⟨w, b⟩
    apply Prod.ext
    · funext i
      by_cases hi : i = e
      · subst i
        simp
      · simp [Function.update_of_ne hi]
    · simp

theorem paperMean_resample_coordinate
    {I B : Type} [Fintype I] [Fintype B]
    [DecidableEq I] [Nonempty B] (e : I) (f : (I → B) → ℝ) :
    paperMean (fun w : I → B =>
      paperMean (fun b : B => f (Function.update w e b))) = paperMean f := by
  calc
    paperMean (fun w : I → B =>
        paperMean (fun b : B => f (Function.update w e b))) =
      paperMean (fun x : (I → B) × B =>
        f (Function.update x.1 e x.2)) :=
      (@paperMean_prod_eq_iterated (I → B) B _ _ _ _
        (fun x => f (Function.update x.1 e x.2))).symm
    _ = paperMean (fun x : (I → B) × B => f x.1) := by
      exact paperMean_equiv (paperCoordinateResampleEquiv e) (fun x => f x.1)
    _ = paperMean f := by
      rw [paperMean_prod_eq_iterated]
      simp_rw [paperMean_const_function]

theorem paperMean_add
    {A : Type} [Fintype A] (f g : A → ℝ) :
    paperMean (fun a => f a + g a) = paperMean f + paperMean g := by
  unfold paperMean
  rw [Finset.sum_add_distrib]
  ring

/-- The coefficient-level L1 input is exactly the conditional estimate for
the literal parent when only the distinguished paper-noise copy is
resampled. -/
theorem paperBranch_conditionalParentL1_le_of_sym2CoefficientNCK
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hNCK : PaperBranchSym2CoefficientConditionalL1NCK G C p n)
    (orientation : Fin G.edges → Bool) (stage : ℕ)
    (hstage : stage < paperUnconditionalOrderingLength G)
    (D : PaperCanonicalNCKSides G)
    (w : PaperDecoupledNoise G n) :
    paperMean (fun xi : PaperNoise n =>
      ‖paperPartialNCKStageMatrix G
        G.unconditionalBoundaryCleanMengerCertificate D n orientation stage
        (Function.update w
          (paperUnconditionalOrderingEdgeAt G stage hstage) xi)‖) ≤
      (C * Real.sqrt p) *
        (‖paperMatrixRademacherRowFlattening
            (paperBranchStageOrderedCoefficient
              G n orientation D stage hstage) w‖ +
          ‖paperMatrixRademacherColFlattening
            (paperBranchStageOrderedCoefficient
              G n orientation D stage hstage) w‖) := by
  calc
    paperMean (fun xi : PaperNoise n =>
        ‖paperPartialNCKStageMatrix G
          G.unconditionalBoundaryCleanMengerCertificate D n orientation stage
          (Function.update w
            (paperUnconditionalOrderingEdgeAt G stage hstage) xi)‖) =
      paperMean (fun xi : PaperNoise n =>
        ‖paperRademacherMatrixSum
          (paperBranchStageSym2Coefficient
            G n orientation D stage hstage w)
          (paperNoiseSym2Projection xi)‖) := by
        apply congrArg paperMean
        funext xi
        rw [paperPartialNCKStageMatrix_eq_sym2RademacherSum
          G n orientation D stage hstage]
        unfold paperSym2NoiseMatrixRademacherSum
        rw [paperBranchStageSym2Coefficient_independent]
        simp
    _ = paperMean (fun eta : Sym2 (Fin n) → Bool =>
        ‖paperRademacherMatrixSum
          (paperBranchStageSym2Coefficient
            G n orientation D stage hstage w) eta‖) := by
        simpa using (paperMean_comp_noiseSym2Projection n
          (fun eta : Sym2 (Fin n) → Bool =>
            ‖paperRademacherMatrixSum
              (paperBranchStageSym2Coefficient
                G n orientation D stage hstage w) eta‖))
    _ ≤ _ := hNCK orientation stage hstage D w

theorem paperNCKBranch_conditionalParentL1_le_children
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hNCK : PaperBranchSym2CoefficientConditionalL1NCK G C p n)
    (orientation : Fin G.edges → Bool) (history : List Bool)
    (hstage : history.length < paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    paperMean (fun xi : PaperNoise n =>
      ‖paperNCKBranchStageMatrix G n orientation history
        (Function.update w
          (paperUnconditionalOrderingEdgeAt G history.length hstage) xi)‖) ≤
      (C * Real.sqrt p) *
        (‖paperNCKBranchStageMatrix G n orientation
            (paperNCKBranchChild false history) w‖ +
          ‖paperNCKBranchStageMatrix G n orientation
            (paperNCKBranchChild true history) w‖) := by
  calc
    paperMean (fun xi : PaperNoise n =>
        ‖paperNCKBranchStageMatrix G n orientation history
          (Function.update w
            (paperUnconditionalOrderingEdgeAt G history.length hstage) xi)‖) ≤
      (C * Real.sqrt p) *
        (‖paperMatrixRademacherRowFlattening
            (paperBranchStageOrderedCoefficient G n orientation
              (paperNCKBranchSides G history) history.length hstage) w‖ +
          ‖paperMatrixRademacherColFlattening
            (paperBranchStageOrderedCoefficient G n orientation
              (paperNCKBranchSides G history) history.length hstage) w‖) := by
        exact paperBranch_conditionalParentL1_le_of_sym2CoefficientNCK
          G C p n hNCK orientation history.length hstage
            (paperNCKBranchSides G history) w
    _ = (C * Real.sqrt p) *
        (‖paperNCKBranchStageMatrix G n orientation
            (paperNCKBranchChild false history) w‖ +
          ‖paperNCKBranchStageMatrix G n orientation
            (paperNCKBranchChild true history) w‖) := by
        rw [paperNCKBranchRowChildMatrix_reindex_orderedCoefficient,
          paperNCKBranchColChildMatrix_reindex_orderedCoefficient]

/-- Averaging the conditional estimate over all remaining noise copies gives
the exact L1 two-child recurrence needed by the branch ledger. -/
theorem paperNCKBranch_parentMeanL1_le_children
    (G : PaperShape) (C : ℝ) (p n : ℕ)
    (hNCK : PaperBranchSym2CoefficientConditionalL1NCK G C p n)
    (orientation : Fin G.edges → Bool) (history : List Bool)
    (hstage : history.length < paperUnconditionalOrderingLength G) :
    paperMean (fun w : PaperDecoupledNoise G n =>
      ‖paperNCKBranchStageMatrix G n orientation history w‖) ≤
      (C * Real.sqrt p) *
        (paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperNCKBranchStageMatrix G n orientation
              (paperNCKBranchChild false history) w‖) +
          paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperNCKBranchStageMatrix G n orientation
              (paperNCKBranchChild true history) w‖)) := by
  let e := paperUnconditionalOrderingEdgeAt G history.length hstage
  calc
    paperMean (fun w : PaperDecoupledNoise G n =>
        ‖paperNCKBranchStageMatrix G n orientation history w‖) =
      paperMean (fun w : PaperDecoupledNoise G n =>
        paperMean (fun xi : PaperNoise n =>
          ‖paperNCKBranchStageMatrix G n orientation history
            (Function.update w e xi)‖)) := by
        symm
        exact paperMean_resample_coordinate e
          (fun w : PaperDecoupledNoise G n =>
            ‖paperNCKBranchStageMatrix G n orientation history w‖)
    _ ≤ paperMean (fun w : PaperDecoupledNoise G n =>
        (C * Real.sqrt p) *
          (‖paperNCKBranchStageMatrix G n orientation
              (paperNCKBranchChild false history) w‖ +
            ‖paperNCKBranchStageMatrix G n orientation
              (paperNCKBranchChild true history) w‖)) := by
        apply paperMean_mono
        intro w
        exact paperNCKBranch_conditionalParentL1_le_children
          G C p n hNCK orientation history hstage w
    _ = (C * Real.sqrt p) *
        (paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperNCKBranchStageMatrix G n orientation
              (paperNCKBranchChild false history) w‖) +
          paperMean (fun w : PaperDecoupledNoise G n =>
            ‖paperNCKBranchStageMatrix G n orientation
              (paperNCKBranchChild true history) w‖)) := by
        rw [paperMean_const_mul, paperMean_add]


end GraphMatrixReplica
