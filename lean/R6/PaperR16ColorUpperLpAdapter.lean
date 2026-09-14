import R6.PaperR16ColorUpperNormAdapter
import R6.PaperR16FiniteColorLpTransfer
import R6.PaperR16ZeroRole

/-! # Real-q color upper transfer

The finite-color Minkowski bound holds for every real `q ≥ 1`.  The first
theorem below applies it to the exact R16 random-color matrix identity.  The
second theorem compresses each fixed-color matrix at the same `Lq` level.
Identifying the resulting readout norm with the independent typed Lq norm
requires the finite-uniform pushforward law at the Lq level.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

private theorem paperR16_matrix_eq_color_sum
    (G : PaperShape) (n : ℕ) (hroles : 0 < G.roles)
    (w : PaperNoise n) :
    paperGraphMatrix G n w =
      (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) •
        ∑ color : Fin n → Fin G.roles,
          paperR16ColoredGraphMatrix G n w color := by
  have hMultiplicity :
      ((G.roles ^ (n - G.roles) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (n - G.roles) (Nat.ne_of_gt hroles)
  ext row col
  have hSum := paperR16_sum_coloredGraphMatrix G n w row col
  simp only [Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Nat.cast_pow, nsmul_eq_mul] at *
  rw [hSum]
  field_simp [hMultiplicity]

/-- The global paper matrix has the finite-color Minkowski bound for every
real `q ≥ 1`, with no q-dependent coefficient. -/
theorem paperR16_globalLq_le_sum_coloredLq
    (G : PaperShape) (n : ℕ) (hroles : 0 < G.roles)
    (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperGraphMatrix G n w) q ≤
      (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
        ∑ color : Fin n → Fin G.roles,
          paperFiniteUniformLq
            (fun w : PaperNoise n =>
              paperR16ColoredGraphMatrix G n w color) q := by
  apply paperFiniteUniformLq_le_of_finiteColorSum
    (target := fun w : PaperNoise n => paperGraphMatrix G n w)
    (colored := fun color w => paperR16ColoredGraphMatrix G n w color)
    (coefficient := (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹))
  · positivity
  · exact paperR16_matrix_eq_color_sum G n hroles
  · exact hq

/-- At each coloring, zero padding and fixed-color entry identification
compare the real-q norm to the typed matrix read from the ambient signs. -/
theorem paperR16_coloredLq_le_readFiberPartiteLq
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles)
    (q : ℝ) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperR16ColoredGraphMatrix G n w color) q ≤
      paperFiniteUniformLq
        (fun w : PaperNoise n =>
          c027PartiteBoundaryMatrixReal G
            (paperR16ColorClassDimension G n color)
            ((paperR16ColorClassRoleColoring G n color).readJointEdgeSignSample w)) q := by
  classical
  letI : MeasurableSpace (PaperNoise n) := ⊤
  let μ : MeasureTheory.Measure (PaperNoise n) :=
    (Fintype.card (PaperNoise n) : NNReal)⁻¹ • MeasureTheory.Measure.count
  let p : ENNReal := ENNReal.ofReal q
  let typedRead := fun w : PaperNoise n =>
    c027PartiteBoundaryMatrixReal G
      (paperR16ColorClassDimension G n color)
      ((paperR16ColorClassRoleColoring G n color).readJointEdgeSignSample w)
  have hMem : MeasureTheory.MemLp (fun w => ‖typedRead w‖) p μ :=
    MeasureTheory.MemLp.of_discrete
  have hTypedMem : MeasureTheory.MemLp typedRead p μ :=
    MeasureTheory.MemLp.of_discrete
  change MeasureTheory.lpNorm
      (fun w : PaperNoise n => paperR16ColoredGraphMatrix G n w color) p μ ≤
    MeasureTheory.lpNorm typedRead p μ
  calc
    MeasureTheory.lpNorm
        (fun w : PaperNoise n => paperR16ColoredGraphMatrix G n w color) p μ ≤
        MeasureTheory.lpNorm (fun w => ‖typedRead w‖) p μ := by
      apply MeasureTheory.lpNorm_mono_real hMem
      intro w
      exact paperR16_coloredNorm_le_fiberPartite G n w color
    _ = MeasureTheory.lpNorm typedRead p μ := by
      exact MeasureTheory.lpNorm_norm hTypedMem.aestronglyMeasurable p

/-- On a finite discrete space, integrating against normalized counting
measure is exactly `paperMean`, including the empty-space convention. -/
private theorem paperR16_uniformIntegral_eq_paperMean
    {Ω : Type} [Fintype Ω] (f : Ω → ℝ) :
    (letI : MeasurableSpace Ω := ⊤
     ∫ ω, f ω ∂
       ((Fintype.card Ω : NNReal)⁻¹ • MeasureTheory.Measure.count)) =
      paperMean f := by
  letI : MeasurableSpace Ω := ⊤
  rw [MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_count]
  simp [paperMean, NNReal.smul_def, smul_eq_mul]

/-- Finite-uniform real-q norm is the qth root of the finite-uniform
qth absolute moment.  This formula is used only for positive q. -/
private theorem paperR16_finiteUniformLq_eq_moment
    {Ω E : Type} [Fintype Ω] [NormedAddCommGroup E]
    (f : Ω → E) (q : ℝ) (hq : 0 < q) :
    paperFiniteUniformLq f q =
      (paperMean (fun ω => ‖f ω‖ ^ q)) ^ q⁻¹ := by
  letI : MeasurableSpace Ω := ⊤
  let μ : MeasureTheory.Measure Ω :=
    (Fintype.card Ω : NNReal)⁻¹ • MeasureTheory.Measure.count
  have hMem : MeasureTheory.MemLp f (ENNReal.ofReal q) μ :=
    MeasureTheory.MemLp.of_discrete
  have hp0 : ENNReal.ofReal q ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hq
  have hpTop : ENNReal.ofReal q ≠ ⊤ := by simp
  change MeasureTheory.lpNorm f (ENNReal.ofReal q) μ = _
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    hp0 hpTop hMem.aestronglyMeasurable]
  rw [ENNReal.toReal_ofReal (le_of_lt hq)]
  exact congrArg (fun x : ℝ => x ^ q⁻¹)
    (paperR16_uniformIntegral_eq_paperMean (fun ω => ‖f ω‖ ^ q))

/-- A fixed color's readout has the same real-q norm as the independent
typed model.  The equality follows from the full joint finite-uniform law,
not merely matching individual edge marginals. -/
theorem paperR16_readFiberPartiteLq_eq_independent
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles)
    (q : ℝ) (hq : 0 < q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n =>
        c027PartiteBoundaryMatrixReal G
          (paperR16ColorClassDimension G n color)
          ((paperR16ColorClassRoleColoring G n color).readJointEdgeSignSample w)) q =
      paperFiniteUniformLq
        (fun epsilon : JointEdgeSignSample
            (G := G.toPartiteShape)
            (paperR16ColorClassDimension G n color) =>
          c027PartiteBoundaryMatrixReal G
            (paperR16ColorClassDimension G n color) epsilon) q := by
  let C := paperR16ColorClassRoleColoring G n color
  let dimension := paperR16ColorClassDimension G n color
  rw [paperR16_finiteUniformLq_eq_moment _ q hq,
    paperR16_finiteUniformLq_eq_moment _ q hq]
  congr 1
  exact C.paperMean_readJointEdgeSignSample
    (fun epsilon => ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ ^ q)

/-- The actual colored paper matrix has no larger real-q norm than the
independent typed fiber model for every q ≥ 1. -/
theorem paperR16_coloredLq_le_independentFiberPartiteLq
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles)
    (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperR16ColoredGraphMatrix G n w color) q ≤
      paperFiniteUniformLq
        (fun epsilon : JointEdgeSignSample
            (G := G.toPartiteShape)
            (paperR16ColorClassDimension G n color) =>
          c027PartiteBoundaryMatrixReal G
            (paperR16ColorClassDimension G n color) epsilon) q := by
  exact (paperR16_coloredLq_le_readFiberPartiteLq G n color q).trans_eq
    (paperR16_readFiberPartiteLq_eq_independent G n color q (by linarith))

/-- Complete deterministic random-color upper reduction at real q ≥ 1:
the paper-global matrix is controlled by the sum of independent-edge
fully-partite norms at the exact, possibly unbalanced, color-fiber sizes. -/
theorem paperR16_globalLq_le_sum_independentFiberPartiteLq
    (G : PaperShape) (n : ℕ) (hroles : 0 < G.roles)
    (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperGraphMatrix G n w) q ≤
      (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
        ∑ color : Fin n → Fin G.roles,
          paperFiniteUniformLq
            (fun epsilon : JointEdgeSignSample
                (G := G.toPartiteShape)
                (paperR16ColorClassDimension G n color) =>
              c027PartiteBoundaryMatrixReal G
                (paperR16ColorClassDimension G n color) epsilon) q := by
  calc
    paperFiniteUniformLq
        (fun w : PaperNoise n => paperGraphMatrix G n w) q ≤
        (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
          ∑ color : Fin n → Fin G.roles,
            paperFiniteUniformLq
              (fun w : PaperNoise n =>
                paperR16ColoredGraphMatrix G n w color) q :=
      paperR16_globalLq_le_sum_coloredLq G n hroles q hq
    _ ≤ (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
          ∑ color : Fin n → Fin G.roles,
            paperFiniteUniformLq
              (fun epsilon : JointEdgeSignSample
                  (G := G.toPartiteShape)
                  (paperR16ColorClassDimension G n color) =>
                c027PartiteBoundaryMatrixReal G
                  (paperR16ColorClassDimension G n color) epsilon) q := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro color _
        exact paperR16_coloredLq_le_independentFiberPartiteLq
          G n color q hq
      · positivity

/-- Each actual color class has at most the ambient number of labels. -/
theorem paperR16_colorClassDimension_le
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles)
    (v : Fin G.roles) :
    paperR16ColorClassDimension G n color v ≤ n := by
  unfold paperR16ColorClassDimension
  simpa using Fintype.card_subtype_le (fun i : Fin n => color i = v)

/-- A uniform typed real-q estimate for all labelled size vectors bounded
by n transfers to the globally injective sign matrix.  The constant is
exactly `roles^roles`, independent of q, including n < roles. -/
theorem paperR16_globalLq_le_of_uniformTypedBound
    (G : PaperShape) (n : ℕ) (hroles : 0 < G.roles)
    (q : ℝ) (hq : 1 ≤ q) (B : ℝ) (hB : 0 ≤ B)
    (hTyped : ∀ dimension : Fin G.roles → ℕ,
      (∀ v, dimension v ≤ n) →
      paperFiniteUniformLq
        (fun epsilon : JointEdgeSignSample
            (G := G.toPartiteShape) dimension =>
          c027PartiteBoundaryMatrixReal G dimension epsilon) q ≤ B) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperGraphMatrix G n w) q ≤
      (G.roles : ℝ) ^ G.roles * B := by
  have hColorSum :
      (∑ color : Fin n → Fin G.roles,
        paperFiniteUniformLq
          (fun epsilon : JointEdgeSignSample
              (G := G.toPartiteShape)
              (paperR16ColorClassDimension G n color) =>
            c027PartiteBoundaryMatrixReal G
              (paperR16ColorClassDimension G n color) epsilon) q) ≤
        (G.roles : ℝ) ^ n * B := by
    calc
      _ ≤ ∑ _color : Fin n → Fin G.roles, B := by
        apply Finset.sum_le_sum
        intro color _
        exact hTyped (paperR16ColorClassDimension G n color)
          (paperR16_colorClassDimension_le G n color)
      _ = (G.roles : ℝ) ^ n * B := by
        simp [Fintype.card_fun, nsmul_eq_mul]
  have hExponent :
      G.roles ^ n ≤ G.roles ^ (n - G.roles) * G.roles ^ G.roles := by
    by_cases hn : G.roles ≤ n
    · rw [← pow_add, Nat.sub_add_cancel hn]
    · have hnv : n ≤ G.roles := Nat.le_of_lt (Nat.lt_of_not_ge hn)
      simpa [Nat.sub_eq_zero_of_le hnv] using
        (Nat.pow_le_pow_right hroles hnv)
  have hFactor :
      (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
          (G.roles : ℝ) ^ n ≤ (G.roles : ℝ) ^ G.roles := by
    have hExponentReal :
        (G.roles : ℝ) ^ n ≤
          (G.roles : ℝ) ^ (n - G.roles) *
            (G.roles : ℝ) ^ G.roles := by
      exact_mod_cast hExponent
    calc
      (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
          (G.roles : ℝ) ^ n ≤
          (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
            ((G.roles : ℝ) ^ (n - G.roles) *
              (G.roles : ℝ) ^ G.roles) := by
        exact mul_le_mul_of_nonneg_left hExponentReal (by positivity)
      _ = (G.roles : ℝ) ^ G.roles := by
        simp only [Nat.cast_pow]
        have hv : (G.roles : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt hroles
        field_simp [hv]
  calc
    paperFiniteUniformLq
        (fun w : PaperNoise n => paperGraphMatrix G n w) q ≤
        (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
          ∑ color : Fin n → Fin G.roles,
            paperFiniteUniformLq
              (fun epsilon : JointEdgeSignSample
                  (G := G.toPartiteShape)
                  (paperR16ColorClassDimension G n color) =>
                c027PartiteBoundaryMatrixReal G
                  (paperR16ColorClassDimension G n color) epsilon) q :=
      paperR16_globalLq_le_sum_independentFiberPartiteLq
        G n hroles q hq
    _ ≤ (((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹) *
          ((G.roles : ℝ) ^ n * B) := by
      exact mul_le_mul_of_nonneg_left hColorSum (by positivity)
    _ ≤ (G.roles : ℝ) ^ G.roles * B := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hFactor hB

/-- Every entry of a real matrix is bounded by its Euclidean operator norm. -/
private theorem paperR16_abs_entry_le_opNorm
    {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (i : ι) (j : κ) :
    |A i j| ≤ ‖A‖ := by
  let x : EuclideanSpace ℝ κ := EuclideanSpace.single j 1
  let y : EuclideanSpace ℝ ι :=
    (EuclideanSpace.equiv ι ℝ).symm (Matrix.mulVec A x.ofLp)
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ ‖A‖ * ‖x‖ :=
    Matrix.l2_opNorm_mulVec A x
  calc
    |A i j| = ‖y.ofLp i‖ := by
      simp [x, y, Real.norm_eq_abs]
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖A‖ * ‖x‖ := hop
    _ = ‖A‖ := by simp [x]

/-- For a zero-role paper shape, the sole entry is one and the Euclidean
operator norm of that singleton matrix is one for every sign sample. -/
theorem paperR16_zeroRole_graphMatrix_norm_eq_one
    (G : PaperShape) (hroles : G.roles = 0) (n : ℕ)
    (w : PaperNoise n) : ‖paperGraphMatrix G n w‖ = 1 := by
  classical
  letI : IsEmpty (Fin G.roles) := by rw [hroles]; infer_instance
  letI : IsEmpty (Fin G.leftSize) :=
    ⟨fun i => isEmptyElim (G.left i)⟩
  letI : IsEmpty (Fin G.rightSize) :=
    ⟨fun i => isEmptyElim (G.right i)⟩
  letI : Unique (PaperRow G n) := inferInstance
  letI : Unique (PaperCol G n) := inferInstance
  let M := paperGraphMatrix G n w
  have hLower : 1 ≤ ‖M‖ := by
    have hEntry := paperR16_abs_entry_le_opNorm M
      (default : PaperRow G n) (default : PaperCol G n)
    simpa [M, paperR16_zeroRole_graphMatrix_eq_one G hroles n w] using hEntry
  have hUpperSq : ‖M‖ ^ 2 ≤ 1 := by
    have hFrob := matrix_l2_opNorm_sq_le_sum_entry_sq M
    simpa [M, paperR16_zeroRole_graphMatrix_eq_one G hroles n w]
      using hFrob
  have hUpper : ‖M‖ ≤ 1 := by
    nlinarith [norm_nonneg M]
  exact le_antisymm hUpper hLower

/-- The zero-role branch of `lem:color-upper`: the global matrix is the
scalar-one matrix, so every real-q norm (q ≥ 1) equals one. -/
theorem paperR16_zeroRole_globalLq_eq_one
    (G : PaperShape) (hroles : G.roles = 0) (n : ℕ)
    (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperGraphMatrix G n w) q = 1 := by
  rw [paperR16_finiteUniformLq_eq_moment _ q (by linarith)]
  have hConst :
      (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖ ^ q) =
        fun _ => (1 : ℝ) := by
    funext w
    rw [paperR16_zeroRole_graphMatrix_norm_eq_one G hroles n w]
    simp
  rw [hConst]
  have hCard : Fintype.card (PaperNoise n) ≠ 0 := Fintype.card_ne_zero
  simp [paperMean, hCard]

#print axioms paperR16_globalLq_le_sum_coloredLq
#print axioms paperR16_coloredLq_le_readFiberPartiteLq
#print axioms paperR16_readFiberPartiteLq_eq_independent
#print axioms paperR16_coloredLq_le_independentFiberPartiteLq
#print axioms paperR16_globalLq_le_sum_independentFiberPartiteLq
#print axioms paperR16_colorClassDimension_le
#print axioms paperR16_globalLq_le_of_uniformTypedBound
#print axioms paperR16_zeroRole_graphMatrix_norm_eq_one
#print axioms paperR16_zeroRole_globalLq_eq_one

end GraphMatrixReplica
