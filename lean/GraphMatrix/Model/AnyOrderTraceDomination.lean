import GraphMatrix.TraceNormBridge

/-! # integer-order norm-to-Gram-trace domination

The core upper bound in uses arbitrary integer trace order, not only the
dyadic orders supported by `matrix_l2_opNorm_pow_dyadic_le_gramTrace`.
This file proves the deterministic pointwise comparison at every positive
integer order for a rectangular real matrix.  It uses only the spectral
theorem for the positive semidefinite row Gram matrix.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

private theorem paperR16_trace_pow_eq_sum_eigenvalues_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (p : ℕ) :
    Matrix.trace (S ^ p) =
      ∑ i : ι, (hS.isHermitian.eigenvalues i) ^ p := by
  let U := hS.isHermitian.eigenvectorUnitary
  let eigen := hS.isHermitian.eigenvalues
  have hdiag : S = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
      (Matrix.diagonal eigen) := by
    simpa [U, eigen] using hS.isHermitian.spectral_theorem
  calc
    Matrix.trace (S ^ p) = Matrix.trace
        ((Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
          (Matrix.diagonal eigen)) ^ p) := by rw [hdiag]
    _ = Matrix.trace (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
          ((Matrix.diagonal eigen) ^ p)) := by rw [map_pow]
    _ = Matrix.trace ((Matrix.diagonal eigen) ^ p) := by
      rw [Unitary.conjStarAlgAut_apply, ← Matrix.trace_mul_cycle]
      simp only [mul_assoc, Unitary.coe_star_mul_self, mul_one]
    _ = ∑ i : ι, eigen i ^ p := by
      rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
      simp only [Pi.pow_apply]
    _ = ∑ i : ι, (hS.isHermitian.eigenvalues i) ^ p := by rfl

private theorem paperR16_norm_pow_le_sum_eigenvalues_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef)
    (p : ℕ) (hp : 1 ≤ p) :
    ‖S‖ ^ p ≤ ∑ i : ι, (hS.isHermitian.eigenvalues i) ^ p := by
  let U := hS.isHermitian.eigenvectorUnitary
  let eigen := hS.isHermitian.eigenvalues
  have hdiag : S = Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
      (Matrix.diagonal eigen) := by
    simpa [U, eigen] using hS.isHermitian.spectral_theorem
  have hNorm : ‖S‖ = ‖eigen‖ := by
    calc
      ‖S‖ = ‖Matrix.diagonal eigen‖ := by
        rw [hdiag, Unitary.conjStarAlgAut_apply]
        simp only [← Unitary.coe_star,
          CStarRing.norm_mul_coe_unitary,
          CStarRing.norm_coe_unitary_mul]
      _ = ‖eigen‖ := Matrix.l2_opNorm_diagonal eigen
  rw [hNorm]
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
      letI := hEmpty
      simp [Pi.norm_def, pow_eq_zero_of_le hp]
  | inr hNonempty =>
      letI := hNonempty
      obtain ⟨i, hi⟩ := (IsGreatest.pi_norm eigen).1
      have hei : eigen i = ‖eigen‖ := by
        have hNonneg : 0 ≤ eigen i := hS.eigenvalues_nonneg i
        simpa [Real.norm_of_nonneg hNonneg] using hi
      rw [← hei]
      exact Finset.single_le_sum
        (fun j _ => pow_nonneg (hS.eigenvalues_nonneg j) p)
        (Finset.mem_univ i)

/-- The pointwise norm-to-trace bridge for the arbitrary integer order used
by `prop:core-upper`.  The matrices may be rectangular, and `p ≥ 1` is
essential when the row index type is empty. -/
theorem paperR16_matrix_l2_opNorm_pow_le_gramTrace
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ ℝ) (p : ℕ) (hp : 1 ≤ p) :
    ‖M‖ ^ (2 * p) ≤
      Matrix.trace ((M * M.transpose) ^ p) := by
  let S : Matrix ι ι ℝ := M * M.transpose
  have hS : S.PosSemidef := by
    simpa [S] using Matrix.posSemidef_self_mul_conjTranspose M
  have hTranspose : ‖M.transpose‖ = ‖M‖ := by
    simpa using (Matrix.l2_opNorm_conjTranspose M)
  have hNormS : ‖S‖ = ‖M‖ * ‖M‖ := by
    simpa [S, hTranspose] using
      (Matrix.l2_opNorm_conjTranspose_mul_self (A := M.transpose))
  calc
    ‖M‖ ^ (2 * p) = ‖S‖ ^ p := by
      rw [pow_mul, pow_two, hNormS]
    _ ≤ ∑ i : ι, (hS.isHermitian.eigenvalues i) ^ p :=
      paperR16_norm_pow_le_sum_eigenvalues_pow S hS p hp
    _ = Matrix.trace (S ^ p) :=
      (paperR16_trace_pow_eq_sum_eigenvalues_pow S hS p).symm
    _ = Matrix.trace ((M * M.transpose) ^ p) := rfl


end GraphMatrixReplica
