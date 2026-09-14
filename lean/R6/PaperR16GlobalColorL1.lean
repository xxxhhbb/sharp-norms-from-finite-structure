import R6.PaperR16ColorUpperTransfer
import R6.PaperR16FiniteColorNormTransfer

/-! # R16 global-to-colored expected operator norm inequality

This module composes the exact finite random-color matrix sum with the
finite-color norm triangle/Fubini lemma.  The coefficient is the reciprocal
of the exact retention multiplicity.  It has not yet replaced the colored
zero-padded matrices by typed matrices; that requires the fixed-color
compression and noise-law adapters.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The paper-global matrix's expected operator norm is controlled by the
sum of expected norms of its zero-padded role-colored pieces. -/
theorem paperR16_globalExpectedNorm_le_sum_colored
    (G : PaperShape) (n : ℕ) (hroles : 0 < G.roles) :
    paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖) ≤
      ((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹ *
        ∑ color : Fin n → Fin G.roles,
          paperMean (fun w : PaperNoise n =>
            ‖paperR16ColoredGraphMatrix G n w color‖) := by
  have hMultiplicity :
      ((G.roles ^ (n - G.roles) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (n - G.roles) (Nat.ne_of_gt hroles)
  apply paperMean_norm_le_of_finiteColorSum
    (target := fun w : PaperNoise n => paperGraphMatrix G n w)
    (colored := fun color w => paperR16ColoredGraphMatrix G n w color)
    (coefficient := ((G.roles ^ (n - G.roles) : ℕ) : ℝ)⁻¹)
  · positivity
  · intro w
    ext row col
    have hSum := paperR16_sum_coloredGraphMatrix G n w row col
    simp only [Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul, Nat.cast_pow, nsmul_eq_mul] at *
    rw [hSum]
    field_simp [hMultiplicity]

#print axioms paperR16_globalExpectedNorm_le_sum_colored

end GraphMatrixReplica
