import R6.PaperR16ColorUpperLpAdapter
import R6.PaperR16RealLpTraceEndpoint
import R6.PaperR16AnyOrderTraceDomination
import R6.PartiteBoundaryMatrixMengerBound
import R6.C079PartiteRealTransfer

/-! # A non-circular uniform typed input for R16 color upper transfer

The existing unconditional finite-Menger trace estimate gives a coarse,
explicitly finite uniform bound for all role dimensions at most `n`.  This
module converts it to the real-q `paperFiniteUniformLq` used by the color
transfer, then applies that transfer.  The bound is deliberately not claimed
to have the sharp constants of R16's `prop:core-upper`: those require the
still-open all-defect count.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The real-cast typed matrix in the color transfer and the real-cast
C079 typed matrix are definitionally the same entrywise. -/
theorem paperR16_c027PartiteReal_eq_c079PartiteReal
    (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    c027PartiteBoundaryMatrixReal G dimension epsilon =
      c079PartiteBoundaryMatrixReal G.toPartiteShape dimension epsilon := by
  ext row col
  rfl

/-- Uniform finite counting measure integrates exactly as `paperMean`. -/
private theorem paperR16_uniformTyped_integral_eq_mean
    {Ω : Type} [Fintype Ω] (f : Ω → ℝ) :
    (letI : MeasurableSpace Ω := ⊤
     ∫ ω, f ω ∂
       ((Fintype.card Ω : NNReal)⁻¹ • MeasureTheory.Measure.count)) =
      paperMean f := by
  letI : MeasurableSpace Ω := ⊤
  rw [MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_count]
  simp [paperMean, NNReal.smul_def, smul_eq_mul]

/-- Public finite-uniform Lq-to-moment interface, for the concrete
normalized counting convention used in the R16 color transfer. -/
theorem paperFiniteUniformLq_eq_paperMean_norm_rpow
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
    (paperR16_uniformTyped_integral_eq_mean
      (fun ω => ‖f ω‖ ^ q))

/-- The unconditional finite-Menger trace budget, with no defect-count
premise.  Its state-cardinality factor may be large as the trace order grows. -/
def paperR16MengerUniformTraceBudget
    (G : PaperShape) (p n : ℕ) : ℝ :=
  (Fintype.card (AdmissiblePartitionState G.toPartiteShape p) : ℝ) *
    (n : ℝ) ^ ((p + 1) *
      (G.roles - G.toPartiteShape.rightLeftSeparatorNumber +
        G.toPartiteShape.isolatedMiddleCount) +
      G.toPartiteShape.rightLeftSeparatorNumber)

/-- The corresponding positive moment scale, with a harmless `+1` to
avoid a zero-budget case in real exponent arithmetic. -/
def paperR16MengerUniformLpScale
    (G : PaperShape) (p n : ℕ) : ℝ :=
  Real.rpow (paperR16MengerUniformTraceBudget G p n + 1)
    ((((2 * (p + 1) : ℕ) : ℝ))⁻¹)

theorem paperR16MengerUniformTraceBudget_nonneg
    (G : PaperShape) (p n : ℕ) :
    0 ≤ paperR16MengerUniformTraceBudget G p n := by
  unfold paperR16MengerUniformTraceBudget
  positivity

theorem paperR16MengerUniformLpScale_nonneg
    (G : PaperShape) (p n : ℕ) :
    0 ≤ paperR16MengerUniformLpScale G p n := by
  unfold paperR16MengerUniformLpScale
  exact Real.rpow_nonneg
    (add_nonneg (paperR16MengerUniformTraceBudget_nonneg G p n) zero_le_one) _

theorem paperR16MengerUniformLpScale_pow
    (G : PaperShape) (p n : ℕ) :
    paperR16MengerUniformLpScale G p n ^ (2 * (p + 1)) =
      paperR16MengerUniformTraceBudget G p n + 1 := by
  unfold paperR16MengerUniformLpScale
  apply Real.rpow_inv_natCast_pow
  · exact add_nonneg (paperR16MengerUniformTraceBudget_nonneg G p n) zero_le_one
  · positivity

/-- Existing unconditional Menger counting gives one real Gram-trace
budget uniformly over every labelled dimension vector below `n`. -/
theorem paperR16_typedGramTrace_le_mengerUniformBudget
    (G : PaperShape) (p n : ℕ) (hn : 1 ≤ n)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v, dimension v ≤ n) :
    paperMean (fun epsilon : JointEdgeSignSample
        (G := G.toPartiteShape) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G.toPartiteShape dimension epsilon *
          (c079PartiteBoundaryMatrixReal G.toPartiteShape dimension epsilon).transpose) ^
          (p + 1))) ≤
      paperR16MengerUniformTraceBudget G p n := by
  rw [paperMean_c079PartiteBoundaryMatrixReal_gramTracePow_eq_castAverage
    G.toPartiteShape (p + 1) dimension]
  unfold paperR16MengerUniformTraceBudget
  exact_mod_cast
    (partiteBoundaryMatrixGramTracePowAverage_le_separatorNumber
      G.toPartiteShape dimension hn hDimension)

/-- A genuinely derived uniform typed Lq input, albeit with the coarse
finite-Menger state-cardinality factor.  No uniformTypedBound proposition
or exact-defect count is assumed. -/
theorem paperR16_uniformTypedLq_le_mengerScale
    (G : PaperShape) (p n : ℕ) (hn : 1 ≤ n)
    (q : ℝ) (hq : 0 < q)
    (hOrder : q ≤ ((2 * (p + 1) : ℕ) : ℝ))
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v, dimension v ≤ n) :
    paperFiniteUniformLq
      (fun epsilon : JointEdgeSignSample
          (G := G.toPartiteShape) dimension =>
        c027PartiteBoundaryMatrixReal G dimension epsilon) q ≤
      paperR16MengerUniformLpScale G p n := by
  rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ q hq]
  simp_rw [paperR16_c027PartiteReal_eq_c079PartiteReal]
  apply paperR16_realLpRoot_le_of_traceBudget
    (fun epsilon : JointEdgeSignSample
        (G := G.toPartiteShape) dimension =>
      c079PartiteBoundaryMatrixReal G.toPartiteShape dimension epsilon)
    q (p + 1) (paperR16MengerUniformLpScale G p n)
    hq (by simpa only [Nat.mul_assoc] using hOrder)
    (paperR16MengerUniformLpScale_nonneg G p n)
  · intro epsilon
    exact paperR16_matrix_l2_opNorm_pow_le_gramTrace
      (c079PartiteBoundaryMatrixReal G.toPartiteShape dimension epsilon)
      (p + 1) (by omega)
  · exact (paperR16_typedGramTrace_le_mengerUniformBudget
      G p n hn dimension hDimension).trans
        ((le_add_of_nonneg_right zero_le_one).trans_eq
          (paperR16MengerUniformLpScale_pow G p n).symm)

/-- The color upper transfer now has a non-circular typed input: one may
use the unconditional finite-Menger moment estimate at any selected order
covering `q`.  This is a coarse bound and is not the sharp R16 core theorem. -/
theorem paperR16_globalLq_le_mengerUniformScale
    (G : PaperShape) (p n : ℕ) (hroles : 0 < G.roles)
    (hn : 1 ≤ n) (q : ℝ) (hq : 1 ≤ q)
    (hOrder : q ≤ ((2 * (p + 1) : ℕ) : ℝ)) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperGraphMatrix G n w) q ≤
      (G.roles : ℝ) ^ G.roles *
        paperR16MengerUniformLpScale G p n := by
  apply paperR16_globalLq_le_of_uniformTypedBound
    G n hroles q hq
    (paperR16MengerUniformLpScale G p n)
    (paperR16MengerUniformLpScale_nonneg G p n)
  intro dimension hDimension
  exact paperR16_uniformTypedLq_le_mengerScale
    G p n hn q (by linarith) hOrder dimension hDimension

/-- Choosing the finite trace order by the requested real q removes the
last order side condition.  This gives an unconditional, coarse global Lq
bound for every q ≥ 1 and every positive ambient size. -/
theorem paperR16_globalLq_le_mengerSelectedScale
    (G : PaperShape) (n : ℕ) (hroles : 0 < G.roles)
    (hn : 1 ≤ n) (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq
      (fun w : PaperNoise n => paperGraphMatrix G n w) q ≤
      (G.roles : ℝ) ^ G.roles *
        paperR16MengerUniformLpScale G ⌈q / 2⌉₊ n := by
  have hCeil : q / 2 ≤ (⌈q / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hOrder : q ≤ ((2 * (⌈q / 2⌉₊ + 1) : ℕ) : ℝ) := by
    push_cast
    linarith
  exact paperR16_globalLq_le_mengerUniformScale
    G ⌈q / 2⌉₊ n hroles hn q hq hOrder

#print axioms paperR16_c027PartiteReal_eq_c079PartiteReal
#print axioms paperFiniteUniformLq_eq_paperMean_norm_rpow
#print axioms paperR16MengerUniformLpScale_pow
#print axioms paperR16_typedGramTrace_le_mengerUniformBudget
#print axioms paperR16_uniformTypedLq_le_mengerScale
#print axioms paperR16_globalLq_le_mengerUniformScale
#print axioms paperR16_globalLq_le_mengerSelectedScale

end GraphMatrixReplica
