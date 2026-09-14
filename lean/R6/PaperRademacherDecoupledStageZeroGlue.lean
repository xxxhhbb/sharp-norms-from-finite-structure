import R6.PaperRademacherWalshProjection
import R6.PaperPartialNCKStageReindexIsometry

/-! # Walsh decoupling at the literal stage-zero matrix

This file contains only finite reindexing and exact matrix identities.  It
transports the Walsh bound from unordered ambient-pair noise to the paper's
redundant ordered noise tables, identifies the fully decoupled chaos with the
literal partial-NCK stage zero, and does not assert a higher-moment estimate.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

abbrev PaperLowerAmbientPair (n : ℕ) :=
  {p : Fin n × Fin n // ¬ p.1 ≤ p.2}

def paperSym2LowerPairEquiv (n : ℕ) :
    Sym2 (Fin n) ⊕ PaperLowerAmbientPair n ≃ Fin n × Fin n :=
  (Equiv.sumCongr
      (Sym2.sortEquiv : Sym2 (Fin n) ≃ {p : Fin n × Fin n // p.1 ≤ p.2})
      (Equiv.refl _)).trans
    (Equiv.sumCompl (fun p : Fin n × Fin n => p.1 ≤ p.2))

def paperNoiseSym2Projection {n : ℕ} (w : PaperNoise n) :
    Sym2 (Fin n) → Bool :=
  fun z =>
    w (paperCanonicalAmbientEdge z).1 (paperCanonicalAmbientEdge z).2

@[simp] theorem paperNoiseSym2Projection_mk {n : ℕ}
    (w : PaperNoise n) (i j : Fin n) :
    paperNoiseSym2Projection w s(i, j) = w (min i j) (max i j) := by
  simp [paperNoiseSym2Projection, paperCanonicalAmbientEdge_mk]

def paperNoiseSplitEquiv (n : ℕ) :
    PaperNoise n ≃
      ((Sym2 (Fin n) → Bool) × (PaperLowerAmbientPair n → Bool)) :=
  (Equiv.curry (Fin n) (Fin n) Bool).symm |>.trans
    ((Equiv.arrowCongr (paperSym2LowerPairEquiv n).symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ Bool))

theorem paperNoiseSplitEquiv_fst (n : ℕ) (w : PaperNoise n) :
    (paperNoiseSplitEquiv n w).1 = paperNoiseSym2Projection w := by
  rfl

theorem paperMean_comp_noiseSym2Projection (n : ℕ)
    (f : (Sym2 (Fin n) → Bool) → ℝ) :
    paperMean (fun w : PaperNoise n => f (paperNoiseSym2Projection w)) =
      paperMean f := by
  calc
    paperMean (fun w : PaperNoise n => f (paperNoiseSym2Projection w)) =
        paperMean (fun w : PaperNoise n => f (paperNoiseSplitEquiv n w).1) := by
      rfl
    _ = paperMean (fun x :
          (Sym2 (Fin n) → Bool) × (PaperLowerAmbientPair n → Bool) =>
          f x.1) :=
      paperMean_equiv (paperNoiseSplitEquiv n)
        (fun x : (Sym2 (Fin n) → Bool) ×
          (PaperLowerAmbientPair n → Bool) => f x.1)
    _ = paperMean f := paperMean_prod_fst f

def paperDecoupledNoiseSplitEquiv (G : PaperShape) (n : ℕ) :
    PaperDecoupledNoise G n ≃
      ((Fin G.edges → Sym2 (Fin n) → Bool) ×
        (Fin G.edges → PaperLowerAmbientPair n → Bool)) :=
  (Equiv.piCongrRight (fun _ : Fin G.edges => paperNoiseSplitEquiv n)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

def paperDecoupledNoiseSym2Projection (G : PaperShape) {n : ℕ}
    (w : PaperDecoupledNoise G n) : Fin G.edges → Sym2 (Fin n) → Bool :=
  fun e => paperNoiseSym2Projection (w e)

theorem paperDecoupledNoiseSplitEquiv_fst
    (G : PaperShape) (n : ℕ) (w : PaperDecoupledNoise G n) :
    (paperDecoupledNoiseSplitEquiv G n w).1 =
      paperDecoupledNoiseSym2Projection G w := by
  funext e
  exact paperNoiseSplitEquiv_fst n (w e)

theorem paperMean_comp_decoupledNoiseSym2Projection
    (G : PaperShape) (n : ℕ)
    (f : (Fin G.edges → Sym2 (Fin n) → Bool) → ℝ) :
    paperMean (fun w : PaperDecoupledNoise G n =>
        f (paperDecoupledNoiseSym2Projection G w)) =
      paperMean f := by
  calc
    paperMean (fun w : PaperDecoupledNoise G n =>
        f (paperDecoupledNoiseSym2Projection G w)) =
        paperMean (fun w : PaperDecoupledNoise G n =>
          f (paperDecoupledNoiseSplitEquiv G n w).1) := by
      rfl
    _ = paperMean (fun x :
          (Fin G.edges → Sym2 (Fin n) → Bool) ×
            (Fin G.edges → PaperLowerAmbientPair n → Bool) => f x.1) :=
      paperMean_equiv (paperDecoupledNoiseSplitEquiv G n)
        (fun x : (Fin G.edges → Sym2 (Fin n) → Bool) ×
          (Fin G.edges → PaperLowerAmbientPair n → Bool) => f x.1)
    _ = paperMean f := paperMean_prod_fst f

/-! ## Exact chaos and matrix identifications -/

@[simp] theorem paperDecoupledNoiseProductOn_sym2
    (G : PaperShape) {n : ℕ}
    (eta : Fin G.edges → Sym2 (Fin n) → Bool)
    (assignment : PaperAssignment G n) :
    paperDecoupledNoiseProductOn G Finset.univ
        (fun e => paperSym2NoiseToPaper (eta e)) assignment =
      ∏ e : Fin G.edges,
        paperSign (eta e s(assignment (G.source e), assignment (G.target e))) := by
  simp [paperDecoupledNoiseProductOn, paperEdgeSign_sym2Noise]

/-- The abstract fully decoupled square-free chaos is exactly the concrete
order-zero paper matrix, after converting each unordered-pair noise copy to
the paper's redundant ordered table. -/
theorem paperFullyDecoupledOrientedChaos_eq_decoupledMatrix
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (eta : Fin G.edges → Sym2 (Fin n) → Bool) :
    paperFullyDecoupledRademacherChaos
        (paperOrientedSquareFreeChaosData G n orientation) eta =
      paperDecoupledOrientedGraphMatrix G n orientation
        (fun e => paperSym2NoiseToPaper (eta e)) := by
  classical
  ext row col
  unfold paperFullyDecoupledRademacherChaos
    paperOrientedSquareFreeChaosData paperOrientedChaosCoefficient
    paperDecoupledOrientedGraphMatrix paperYThroughCoordinates
  simp only [Matrix.sum_apply]
  calc
    (∑ phi : PaperRealization G n,
        (∏ e : Fin G.edges,
          paperSign (eta e s(phi (G.source e), phi (G.target e)))) *
          (if paperEntryCompatible G phi row col ∧
              paperOrientationCompatible G orientation phi then 1 else 0)) =
        ∑ phi : PaperRealization G n,
          if paperAssignmentEntryCompatible G phi row col ∧
              paperAssignmentOrientationCompatible G orientation phi then
            paperDecoupledNoiseProductOn G Finset.univ
              (fun e => paperSym2NoiseToPaper (eta e)) phi
          else 0 := by
      apply Finset.sum_congr rfl
      intro phi _
      by_cases hEntry : paperEntryCompatible G phi row col <;>
        by_cases hOrientation : paperOrientationCompatible G orientation phi <;>
        simp [hEntry, hOrientation,
          paperAssignmentEntryCompatible_realization_iff,
          paperAssignmentOrientationCompatible_realization_iff,
          paperDecoupledNoiseProductOn_sym2]
    _ = ∑ assignment : PaperAssignment G n,
          if Function.Injective assignment then
            (if paperAssignmentEntryCompatible G assignment row col ∧
                paperAssignmentOrientationCompatible G orientation assignment then
              paperDecoupledNoiseProductOn G Finset.univ
                (fun e => paperSym2NoiseToPaper (eta e)) assignment
            else 0)
          else 0 := by
      simpa only using
        (sum_paperRealization_eq_sum_assignment_if_injective G n
          (fun assignment =>
            if paperAssignmentEntryCompatible G assignment row col ∧
                paperAssignmentOrientationCompatible G orientation assignment then
              paperDecoupledNoiseProductOn G Finset.univ
                (fun e => paperSym2NoiseToPaper (eta e)) assignment
            else 0))
    _ = ∑ assignment : PaperAssignment G n,
          if paperAssignmentLeftTuple G assignment = row ∧
              paperAssignmentRightTuple G assignment = col then
            paperOrientedAssignmentWeight G orientation assignment *
              paperDecoupledNoiseProductOn G Finset.univ
                (fun e => paperSym2NoiseToPaper (eta e)) assignment
          else 0 := by
      apply Finset.sum_congr rfl
      intro assignment _
      by_cases hInjective : Function.Injective assignment <;>
        by_cases hOrientation :
          paperAssignmentOrientationCompatible G orientation assignment <;>
        by_cases hEntry :
          paperAssignmentEntryCompatible G assignment row col <;>
        simp [hInjective, hOrientation,
          paperOrientedAssignmentWeight, paperAssignmentEntryCompatible]
  apply Finset.sum_congr rfl
  intro assignment _
  by_cases hEntry : paperAssignmentLeftTuple G assignment = row ∧
      paperAssignmentRightTuple G assignment = col <;> simp [hEntry]

@[simp] theorem paperEdgeSign_sym2Projection
    {n : ℕ} (w : PaperNoise n) (i j : Fin n) :
    paperEdgeSign
        (paperSym2NoiseToPaper (paperNoiseSym2Projection w)) i j =
      paperEdgeSign w i j := by
  rw [paperEdgeSign_sym2Noise]
  simp [paperEdgeSign, paperSign]

theorem paperOrientedGraphMatrix_sym2Projection_eq
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperNoise n) :
    paperOrientedGraphMatrix G n orientation
        (paperSym2NoiseToPaper (paperNoiseSym2Projection w)) =
      paperOrientedGraphMatrix G n orientation w := by
  classical
  ext row col
  unfold paperOrientedGraphMatrix
  apply Finset.sum_congr rfl
  intro phi _
  by_cases hCompatible : paperEntryCompatible G phi row col ∧
      paperOrientationCompatible G orientation phi
  · simp only [if_pos hCompatible]
    apply Finset.prod_congr rfl
    intro e _
    exact paperEdgeSign_sym2Projection w _ _
  · simp [hCompatible]

theorem paperDecoupledOrientedGraphMatrix_sym2Projection_eq
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    paperDecoupledOrientedGraphMatrix G n orientation
        (fun e => paperSym2NoiseToPaper
          (paperNoiseSym2Projection (w e))) =
      paperDecoupledOrientedGraphMatrix G n orientation w := by
  classical
  ext row col
  unfold paperDecoupledOrientedGraphMatrix paperYThroughCoordinates
  apply Finset.sum_congr rfl
  intro assignment _
  by_cases hEntry : paperAssignmentLeftTuple G assignment = row ∧
      paperAssignmentRightTuple G assignment = col
  · simp only [if_pos hEntry]
    congr 1
    unfold paperDecoupledNoiseProductOn
    apply Finset.prod_congr rfl
    intro e _
    exact paperEdgeSign_sym2Projection (w e) _ _
  · simp [hEntry]

theorem paperMean_norm_orientedGraphMatrix_eq_sym2
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖) =
      paperMean (fun epsilon : Sym2 (Fin n) → Bool =>
        ‖paperOrientedGraphMatrix G n orientation
          (paperSym2NoiseToPaper epsilon)‖) := by
  calc
    paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖) =
        paperMean (fun w : PaperNoise n =>
          ‖paperOrientedGraphMatrix G n orientation
            (paperSym2NoiseToPaper (paperNoiseSym2Projection w))‖) := by
      apply congrArg paperMean
      funext w
      exact congrArg norm
        (paperOrientedGraphMatrix_sym2Projection_eq G n orientation w).symm
    _ = paperMean (fun epsilon : Sym2 (Fin n) → Bool =>
          ‖paperOrientedGraphMatrix G n orientation
            (paperSym2NoiseToPaper epsilon)‖) :=
      paperMean_comp_noiseSym2Projection n
        (fun epsilon : Sym2 (Fin n) → Bool =>
          ‖paperOrientedGraphMatrix G n orientation
            (paperSym2NoiseToPaper epsilon)‖)

theorem paperMean_norm_fullyDecoupledOrientedChaos_eq_decoupledMatrix
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperMean (fun eta : Fin G.edges → Sym2 (Fin n) → Bool =>
        ‖paperFullyDecoupledRademacherChaos
          (paperOrientedSquareFreeChaosData G n orientation) eta‖) =
      paperMean (fun w : PaperDecoupledNoise G n =>
        ‖paperDecoupledOrientedGraphMatrix G n orientation w‖) := by
  symm
  calc
    paperMean (fun w : PaperDecoupledNoise G n =>
        ‖paperDecoupledOrientedGraphMatrix G n orientation w‖) =
        paperMean (fun w : PaperDecoupledNoise G n =>
          ‖paperFullyDecoupledRademacherChaos
            (paperOrientedSquareFreeChaosData G n orientation)
              (paperDecoupledNoiseSym2Projection G w)‖) := by
      apply congrArg paperMean
      funext w
      exact congrArg norm <|
        ((paperFullyDecoupledOrientedChaos_eq_decoupledMatrix
          G n orientation (paperDecoupledNoiseSym2Projection G w)).trans
          (paperDecoupledOrientedGraphMatrix_sym2Projection_eq
            G n orientation w)).symm
    _ = paperMean (fun eta : Fin G.edges → Sym2 (Fin n) → Bool =>
          ‖paperFullyDecoupledRademacherChaos
            (paperOrientedSquareFreeChaosData G n orientation) eta‖) :=
      paperMean_comp_decoupledNoiseSym2Projection G n
        (fun eta : Fin G.edges → Sym2 (Fin n) → Bool =>
          ‖paperFullyDecoupledRademacherChaos
            (paperOrientedSquareFreeChaosData G n orientation) eta‖)

/-! ## Literal stage zero -/

theorem paperUnconditionalRawStageNorm_zero_eq_decoupledMatrix
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    paperUnconditionalPartialNCKRawStageNorm G n orientation w 0 =
      ‖paperDecoupledOrientedGraphMatrix G n orientation w‖ := by
  classical
  unfold paperUnconditionalPartialNCKRawStageNorm
    paperPartialNCKRawStageNorm paperPartialNCKStageMatrix
  rw [paperPartialNCKStageRowEdges_zero,
    paperPartialNCKStageColEdges_zero]
  calc
    ‖paperYMatrix G n orientation ∅ ∅ w‖ =
        ‖Matrix.reindex (paperYEmptyRowEquiv G n)
          (paperYEmptyColEquiv G n)
          (paperYMatrix G n orientation ∅ ∅ w)‖ := by
      symm
      exact paper_l2_opNorm_reindex
        (paperYEmptyRowEquiv G n) (paperYEmptyColEquiv G n) _
    _ = ‖paperDecoupledOrientedGraphMatrix G n orientation w‖ := by
      rw [paperYMatrix_empty_reindex_eq_decoupled]

theorem paperMean_norm_decoupledMatrix_eq_rawStageZero
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperMean (fun w : PaperDecoupledNoise G n =>
        ‖paperDecoupledOrientedGraphMatrix G n orientation w‖) =
      paperMean (fun w : PaperDecoupledNoise G n =>
        paperUnconditionalPartialNCKRawStageNorm G n orientation w 0) := by
  apply congrArg paperMean
  funext w
  exact (paperUnconditionalRawStageNorm_zero_eq_decoupledMatrix
    G n orientation w).symm

/-- Honest first-moment handoff from one coupled oriented piece to the
literal fully decoupled stage zero.  The only loss is the explicit Walsh
factor `edges^edges`; no higher moment is claimed. -/
theorem paperMean_norm_orientedMatrix_le_edges_pow_edges_mul_rawStageZero
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    paperMean (fun w : PaperNoise n =>
        ‖paperOrientedGraphMatrix G n orientation w‖) ≤
      (G.edges : ℝ) ^ G.edges *
        paperMean (fun w : PaperDecoupledNoise G n =>
          paperUnconditionalPartialNCKRawStageNorm G n orientation w 0) := by
  rw [paperMean_norm_orientedGraphMatrix_eq_sym2,
    ← paperMean_norm_decoupledMatrix_eq_rawStageZero,
    ← paperMean_norm_fullyDecoupledOrientedChaos_eq_decoupledMatrix]
  exact paperMean_norm_orientedMatrix_le_edges_pow_edges_mul_fullyDecoupled
    G n orientation

#print axioms paperNoiseSplitEquiv_fst
#print axioms paperMean_comp_noiseSym2Projection
#print axioms paperMean_comp_decoupledNoiseSym2Projection
#print axioms paperFullyDecoupledOrientedChaos_eq_decoupledMatrix
#print axioms paperMean_norm_orientedGraphMatrix_eq_sym2
#print axioms paperMean_norm_fullyDecoupledOrientedChaos_eq_decoupledMatrix
#print axioms paperUnconditionalRawStageNorm_zero_eq_decoupledMatrix
#print axioms paperMean_norm_orientedMatrix_le_edges_pow_edges_mul_rawStageZero

end GraphMatrixReplica
