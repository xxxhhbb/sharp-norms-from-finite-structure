import R6.PaperR16FiniteColorNormTransfer
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Finite-color uniform Lq transfer

This is only the generic Minkowski step in the R16 color upper reduction.
It assumes the exact pointwise color identity; it does not construct it or
identify the laws of different colored matrices. The finite uniform measure
is normalized counting measure, with zero measure on an empty sample space.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The finite uniform `L^q` norm, including the zero-measure convention for
an empty sample space. -/
def paperFiniteUniformLq {Ω E : Type} [Fintype Ω] [NormedAddCommGroup E]
    (f : Ω → E) (q : ℝ) : ℝ := by
  letI : MeasurableSpace Ω := ⊤
  exact MeasureTheory.lpNorm f (ENNReal.ofReal q)
    ((Fintype.card Ω : NNReal)⁻¹ • MeasureTheory.Measure.count)

/-- A pointwise finite color sum transfers to every real `L^q`, `q ≥ 1`,
without any additional factor depending on `q`. -/
theorem paperFiniteUniformLq_le_of_finiteColorSum
    {Ω Color E : Type} [Fintype Ω] [Fintype Color]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : Ω → E) (colored : Color → Ω → E)
    (coefficient : ℝ) (hCoefficient : 0 ≤ coefficient)
    (hIdentity : ∀ ω, target ω =
      coefficient • ∑ c : Color, colored c ω)
    (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq target q ≤
      coefficient * ∑ c : Color, paperFiniteUniformLq (colored c) q := by
  classical
  letI : MeasurableSpace Ω := ⊤
  let μ : MeasureTheory.Measure Ω :=
    (Fintype.card Ω : NNReal)⁻¹ • MeasureTheory.Measure.count
  let p : ENNReal := ENNReal.ofReal q
  have hp : (1 : ENNReal) ≤ p := by
    simpa [p] using (ENNReal.ofReal_le_ofReal hq)
  have hmem : ∀ c : Color, MeasureTheory.MemLp (colored c) p μ := by
    intro c
    exact MeasureTheory.MemLp.of_discrete
  have hfun : target = coefficient • (∑ c : Color, colored c) := by
    funext ω
    simpa [Finset.sum_apply] using hIdentity ω
  have hsum : MeasureTheory.lpNorm (∑ c : Color, colored c) p μ ≤
      ∑ c : Color, MeasureTheory.lpNorm (colored c) p μ := by
    exact MeasureTheory.lpNorm_sum_le (fun c _ => hmem c) hp
  change MeasureTheory.lpNorm target p μ ≤
    coefficient * ∑ c : Color, MeasureTheory.lpNorm (colored c) p μ
  rw [hfun, MeasureTheory.lpNorm_const_smul]
  have hc : (‖coefficient‖₊ : ℝ) = coefficient := by
    simp [nnnorm, Real.norm_eq_abs, abs_of_nonneg hCoefficient]
  rw [hc]
  exact mul_le_mul_of_nonneg_left hsum hCoefficient

#print axioms paperFiniteUniformLq_le_of_finiteColorSum

end GraphMatrixReplica
