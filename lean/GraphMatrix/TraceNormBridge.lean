import GraphMatrix.GlobalStatePolynomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef

/-! # From exact trace moments to operator-norm moments

All matrix norms in this file are the Euclidean (`L2`) operator norm supplied
by Mathlib's scoped matrix instance.  The probabilistic part uses only the
finite uniform average `paperMean`, so no measure-theoretic assumptions are
hidden.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- A positive semidefinite real matrix has operator norm at most its trace. -/
theorem matrix_l2_opNorm_le_trace_of_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    ‖A‖ ≤ Matrix.trace A := by
  let U := hA.isHermitian.eigenvectorUnitary
  let eigen := hA.isHermitian.eigenvalues
  have hdiag : A = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
      (Matrix.diagonal eigen) := by
    simpa [U, eigen] using hA.isHermitian.spectral_theorem
  calc
    ‖A‖ = ‖Matrix.diagonal eigen‖ := by
      rw [hdiag, Unitary.conjStarAlgAut_apply]
      simp only [← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary,
        CStarRing.norm_coe_unitary_mul]
    _ = ‖eigen‖ := Matrix.l2_opNorm_diagonal eigen
    _ ≤ ∑ i, eigen i := by
      apply (pi_norm_le_iff_of_nonneg (by
        exact Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i)).2
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
      exact Finset.single_le_sum
        (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = Matrix.trace A := by
      simpa [eigen] using hA.isHermitian.trace_eq_sum_eigenvalues.symm

/-- Dyadic powers of a positive semidefinite matrix remain positive
semidefinite.  This is the exact power family for which Mathlib's C⋆-ring
API supplies norm-power equality without an extra normality interface. -/
theorem matrix_posSemidef_pow_two_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (q : ℕ) :
    (A ^ (2 ^ q)).PosSemidef := by
  induction q with
  | zero => simpa using hA
  | succ q ih =>
      have hsquare := Matrix.posSemidef_conjTranspose_mul_self
        (A ^ (2 ^ q))
      rw [ih.isHermitian.eq] at hsquare
      simpa [pow_succ, pow_two, pow_mul] using hsquare

/-- The Euclidean operator norm of a real matrix, raised to the dyadic even
moment `2 * 2^q`, is bounded by the matching Gram trace moment. -/
theorem matrix_l2_opNorm_pow_dyadic_le_gramTrace
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ ℝ) (q : ℕ) :
    ‖M‖ ^ (2 * 2 ^ q) ≤
      Matrix.trace ((M * M.transpose) ^ (2 ^ q)) := by
  let A : Matrix ι ι ℝ := M * M.transpose
  have hA : A.PosSemidef := by
    simpa [A] using Matrix.posSemidef_self_mul_conjTranspose M
  have hTranspose : ‖M.transpose‖ = ‖M‖ := by
    simpa using (Matrix.l2_opNorm_conjTranspose M)
  have hNormA : ‖A‖ = ‖M‖ * ‖M‖ := by
    simpa [A, hTranspose] using
      (Matrix.l2_opNorm_conjTranspose_mul_self (A := M.transpose))
  have hSelf : IsSelfAdjoint A :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp hA.isHermitian
  calc
    ‖M‖ ^ (2 * 2 ^ q) = (‖M‖ * ‖M‖) ^ (2 ^ q) := by
      rw [pow_mul, pow_two]
    _ = ‖A‖ ^ (2 ^ q) := by rw [hNormA]
    _ = ‖A ^ (2 ^ q)‖ := (hSelf.norm_pow_two_pow q).symm
    _ ≤ Matrix.trace (A ^ (2 ^ q)) :=
      matrix_l2_opNorm_le_trace_of_posSemidef
        (A ^ (2 ^ q)) (matrix_posSemidef_pow_two_pow A hA q)
    _ = Matrix.trace ((M * M.transpose) ^ (2 ^ q)) := rfl

/-- Finite uniform averaging preserves pointwise inequalities.  This remains
true for an empty indexing type, where `paperMean` is defined to be zero. -/
theorem paperMean_mono
    {α : Type} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ a, f a ≤ g a) :
    paperMean f ≤ paperMean g := by
  unfold paperMean
  gcongr with a
  exact hfg a

/-- The dyadic operator-norm moment of the paper matrix is bounded by its
exact Gram trace moment, after averaging over the finite noise space. -/
theorem paperGraphMatrix_l2_opNorm_dyadicMoment_mean_le_traceMean
    (G : PaperShape) (n q : ℕ) :
    paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix G n w‖ ^ (2 * 2 ^ q)) ≤
      paperMean (fun w : PaperNoise n =>
        Matrix.trace ((paperGraphMatrix G n w *
          (paperGraphMatrix G n w).transpose) ^ (2 ^ q))) := by
  apply paperMean_mono
  intro w
  exact matrix_l2_opNorm_pow_dyadic_le_gramTrace
    (paperGraphMatrix G n w) q

/-- Combining the deterministic norm-to-trace inequality with the exact
global-state expansion gives a finite, fully explicit operator-norm moment
bound.  Every summand retains global same-replica injectivity and shared
unordered-edge parity through `PaperAdmissibleGlobalTraceState`. -/
theorem paperGraphMatrix_l2_opNorm_dyadicMoment_mean_le_globalStatePolynomial
    (G : PaperShape) (n q : ℕ) :
    paperMean (fun w : PaperNoise n =>
      ‖paperGraphMatrix G n w‖ ^ (2 * 2 ^ q)) ≤
      ∑ S : PaperAdmissibleGlobalTraceState G (2 ^ q - 1),
        (paperAdmissibleGlobalTraceStateWeight S n : ℝ) := by
  have hpow : 2 ^ q - 1 + 1 = 2 ^ q := by
    have hpos : 0 < 2 ^ q := pow_pos (by omega) q
    omega
  calc
    paperMean (fun w : PaperNoise n =>
        ‖paperGraphMatrix G n w‖ ^ (2 * 2 ^ q)) ≤
        paperMean (fun w : PaperNoise n =>
          Matrix.trace ((paperGraphMatrix G n w *
            (paperGraphMatrix G n w).transpose) ^ (2 ^ q))) :=
      paperGraphMatrix_l2_opNorm_dyadicMoment_mean_le_traceMean G n q
    _ = ∑ S : PaperAdmissibleGlobalTraceState G (2 ^ q - 1),
          (paperAdmissibleGlobalTraceStateWeight S n : ℝ) := by
      simpa [hpow] using
        (paperGraphMatrixGramTracePowMean_eq_globalStatePolynomial
          G n (2 ^ q - 1))


end GraphMatrixReplica
