import R6.PaperR16ColorCompressionNorm
import R6.PaperR16ColorLowerProjectedMatrix

/-! Compressing a finite matrix to selected row and column coordinates is
contractive for the Euclidean operator norm. -/

noncomputable section
open scoped Matrix.Norms.L2Operator

namespace GraphMatrixReplica

theorem paper_l2_opNorm_le_fromBlocks
    {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    (A : Matrix m n ℝ) (B : Matrix m n' ℝ)
    (C : Matrix m' n ℝ) (D : Matrix m' n' ℝ) :
    ‖A‖ ≤ ‖Matrix.fromBlocks A B C D‖ := by
  classical
  rw [Matrix.l2_opNorm_def (A := A)]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
  intro x
  let xExtend : EuclideanSpace ℝ (n ⊕ n') :=
    WithLp.toLp 2 (Sum.elim (fun j => x j) (fun _ => 0))
  have hxExtend : ‖xExtend‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [xExtend, Fintype.sum_sum_type]
  have hTop :
      ‖(EuclideanSpace.equiv m ℝ).symm <| A.mulVec x‖ ≤
        ‖(EuclideanSpace.equiv (m ⊕ m') ℝ).symm <|
          (Matrix.fromBlocks A B C D).mulVec xExtend‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    gcongr
    simp only [Fintype.sum_sum_type]
    have hTopEntry : ∀ i : m,
        (Matrix.fromBlocks A B C D).mulVec xExtend (Sum.inl i) =
          A.mulVec x i := by
      intro i
      simp [Matrix.mulVec, Matrix.fromBlocks, dotProduct, xExtend,
        Fintype.sum_sum_type]
    change (∑ i : m, ‖A.mulVec x i‖ ^ 2) ≤
      (∑ i : m, ‖(Matrix.fromBlocks A B C D).mulVec xExtend (Sum.inl i)‖ ^ 2) +
      (∑ i : m', ‖(Matrix.fromBlocks A B C D).mulVec xExtend (Sum.inr i)‖ ^ 2)
    simp only [hTopEntry]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hFull := Matrix.l2_opNorm_mulVec (Matrix.fromBlocks A B C D) xExtend
  change ‖(EuclideanSpace.equiv m ℝ).symm <| A.mulVec x‖ ≤
    ‖Matrix.fromBlocks A B C D‖ * ‖x‖
  rw [← hxExtend]
  exact hTop.trans hFull

theorem paper_l2_opNorm_submatrix_le
    {m n m' n' : Type*}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    (er : m ↪ m') (ec : n ↪ n') (A : Matrix m' n' ℝ) :
    ‖A.submatrix er ec‖ ≤ ‖A‖ := by
  classical
  let rowEquiv := paperEmbeddingSumComplEquiv er
  let colEquiv := paperEmbeddingSumComplEquiv ec
  let R := Matrix.reindex rowEquiv.symm colEquiv.symm A
  have hTop : R.submatrix Sum.inl Sum.inl = A.submatrix er ec := by
    ext i j
    simp [R, rowEquiv, colEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply]
  have hBlock : R =
      Matrix.fromBlocks
        (R.submatrix Sum.inl Sum.inl)
        (R.submatrix Sum.inl Sum.inr)
        (R.submatrix Sum.inr Sum.inl)
        (R.submatrix Sum.inr Sum.inr) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.submatrix]
  calc
    ‖A.submatrix er ec‖ = ‖R.submatrix Sum.inl Sum.inl‖ := by rw [hTop]
    _ ≤ ‖R‖ := by
      conv_rhs => rw [hBlock]
      exact paper_l2_opNorm_le_fromBlocks _ _ _ _
    _ = ‖A‖ := paper_l2_opNorm_reindex rowEquiv.symm colEquiv.symm A

theorem paperFiniteUniformLq_le_of_norm_le
    {Ω E F : Type} [Fintype Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : Ω → E) (g : Ω → F)
    (h : ∀ ω, ‖f ω‖ ≤ ‖g ω‖) (q : ℝ) :
    paperFiniteUniformLq f q ≤ paperFiniteUniformLq g q := by
  letI : MeasurableSpace Ω := ⊤
  let μ : MeasureTheory.Measure Ω :=
    (Fintype.card Ω : NNReal)⁻¹ • MeasureTheory.Measure.count
  let p : ENNReal := ENNReal.ofReal q
  have hg : MeasureTheory.MemLp g p μ := MeasureTheory.MemLp.of_discrete
  have hnorm : MeasureTheory.MemLp (fun ω => ‖g ω‖) p μ :=
    MeasureTheory.MemLp.of_discrete
  have hmono := MeasureTheory.lpNorm_mono_real hnorm h
  rw [MeasureTheory.lpNorm_norm hg.aestronglyMeasurable p] at hmono
  exact hmono

theorem PaperRoleColoring.projectedCompressed_lq_le_original
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n =>
        (paperR16ProjectedGraphMatrix G n tag w).submatrix
          C.paperRowEmbedding C.paperColEmbedding) q ≤
      paperFiniteUniformLq (paperGraphMatrix G n) q := by
  have hCompression := paperFiniteUniformLq_le_of_norm_le
    (fun w : PaperNoise n =>
      (paperR16ProjectedGraphMatrix G n tag w).submatrix
        C.paperRowEmbedding C.paperColEmbedding)
    (paperR16ProjectedGraphMatrix G n tag)
    (fun w => paper_l2_opNorm_submatrix_le
      C.paperRowEmbedding C.paperColEmbedding
      (paperR16ProjectedGraphMatrix G n tag w)) q
  exact hCompression.trans
    (paperR16ProjectedGraphMatrix_lq_le G n tag q hq)

/-- The exact scalar-multiple identity is the remaining combinatorial
survivor-sum obligation; this theorem closes the analytic lower transfer
once that identity has been established. -/
theorem PaperRoleColoring.projectedCompressed_lower_of_identity
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (H : PaperNoise n →
      Matrix (PartiteBoundaryRow (G := G.toPartiteShape) dimension)
        (PartiteBoundaryCol (G := G.toPartiteShape) dimension) ℝ)
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (hIdentity : ∀ w : PaperNoise n,
      (paperR16ProjectedGraphMatrix G n tag w).submatrix
        C.paperRowEmbedding C.paperColEmbedding = coefficient • H w)
    (q : ℝ) (hq : 1 ≤ q) :
    coefficient * paperFiniteUniformLq H q ≤
      paperFiniteUniformLq (paperGraphMatrix G n) q := by
  have hFunction :
      (fun w : PaperNoise n =>
        (paperR16ProjectedGraphMatrix G n tag w).submatrix
          C.paperRowEmbedding C.paperColEmbedding) =
        coefficient • H := by
    funext w
    exact hIdentity w
  have hNorm :
      paperFiniteUniformLq
        (fun w : PaperNoise n =>
          (paperR16ProjectedGraphMatrix G n tag w).submatrix
            C.paperRowEmbedding C.paperColEmbedding) q =
        coefficient * paperFiniteUniformLq H q := by
    letI : MeasurableSpace (PaperNoise n) := ⊤
    let μ : MeasureTheory.Measure (PaperNoise n) :=
      (Fintype.card (PaperNoise n) : NNReal)⁻¹ •
        MeasureTheory.Measure.count
    change MeasureTheory.lpNorm _ (ENNReal.ofReal q) μ =
      coefficient * MeasureTheory.lpNorm H (ENNReal.ofReal q) μ
    rw [hFunction, MeasureTheory.lpNorm_const_smul]
    have hc : (‖coefficient‖₊ : ℝ) = coefficient := by
      simp [nnnorm, Real.norm_eq_abs, abs_of_nonneg hcoefficient]
    rw [hc]
  rw [← hNorm]
  exact C.projectedCompressed_lq_le_original tag q hq

#print axioms paper_l2_opNorm_le_fromBlocks
#print axioms paper_l2_opNorm_submatrix_le
#print axioms paperFiniteUniformLq_le_of_norm_le
#print axioms PaperRoleColoring.projectedCompressed_lq_le_original
#print axioms PaperRoleColoring.projectedCompressed_lower_of_identity

end GraphMatrixReplica
