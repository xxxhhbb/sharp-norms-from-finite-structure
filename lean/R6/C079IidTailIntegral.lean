import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Gamma integral for a Gaussian-type tail

This analytic identity supplies the Gamma kernel needed after substituting
`u=t²/2` in a Rayleigh tail integral. It does not itself establish a
finite-sample tail bound, layer-cake identity, or change of variables.
-/

noncomputable section
namespace GraphMatrixReplica

/-- Exponential tail kernel at an arbitrary integer moment. -/
theorem c079_exponentialTail_gamma_kernel (q : ℕ) :
    (∫ t : ℝ in Set.Ioi 0, t ^ q * Real.exp (-t)) =
      (q.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (q + 1 : ℕ)) (r := 1)
    (by exact_mod_cast Nat.succ_pos q) (by norm_num)
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h

#print axioms c079_exponentialTail_gamma_kernel

end GraphMatrixReplica
