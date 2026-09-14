import GraphMatrix.OperatorNormEndpoint

/-! # Real-exponent Lyapunov step for the core upper bound

The trace estimate in is at an even integer order.  The requested
`L^q` order may be real.  This file supplies the finite-uniform probability
space conversion without assuming that `q` is an integer.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A high integer moment budget controls every smaller positive real moment
on a finite uniform probability space.  The empty sample space is included. -/
theorem paperMean_realRpow_le_of_higherMoment_budget
    {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (q : ℝ) (m : ℕ) (B : ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hq : 0 < q) (hqm : q ≤ (m : ℝ))
    (hB : 0 ≤ B)
    (hMoment : paperMean (fun ω => f ω ^ m) ≤ B ^ m) :
    paperMean (fun ω => f ω ^ q) ≤ B ^ q := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl hEmpty =>
      letI := hEmpty
      simpa [paperMean] using (Real.rpow_nonneg hB q)
  | inr hNonempty =>
      letI := hNonempty
      let t : ℝ := (m : ℝ) / q
      have ht : 1 ≤ t := by
        dsimp [t]
        exact (one_le_div hq).2 hqm
      have htPos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have hWeightNonneg :
          ∀ ω ∈ (Finset.univ : Finset Ω),
            0 ≤ (Fintype.card Ω : ℝ)⁻¹ := by
        intro _ _
        positivity
      have hWeightSum :
          ∑ _ω : Ω, (Fintype.card Ω : ℝ)⁻¹ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      have hJensen :=
        Real.rpow_arith_mean_le_arith_mean_rpow
          (s := (Finset.univ : Finset Ω))
          (fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹)
          (fun ω => f ω ^ q)
          hWeightNonneg hWeightSum
          (fun ω _ => Real.rpow_nonneg (hf ω) q) ht
      have hJ :
          (paperMean (fun ω => f ω ^ q)) ^ t ≤
            paperMean (fun ω =>
              (f ω ^ q) ^ t) := by
        simpa only [Finset.mul_sum, paperMean] using hJensen
      have hqt : q * t = (m : ℝ) := by
        dsimp [t]
        field_simp
      have hPow : ∀ ω, (f ω ^ q) ^ t = f ω ^ m := by
        intro ω
        rw [← Real.rpow_mul (hf ω), hqt, Real.rpow_natCast]
      simp_rw [hPow] at hJ
      have hMeanNonneg :
          0 ≤ paperMean (fun ω => f ω ^ q) := by
        have h0 : paperMean (fun _ω : Ω => (0 : ℝ)) ≤
            paperMean (fun ω => f ω ^ q) :=
          paperMean_mono (fun ω => Real.rpow_nonneg (hf ω) q)
        simpa only [paperMean_zero] using h0
      have hBq : 0 ≤ B ^ q := Real.rpow_nonneg hB q
      apply (Real.rpow_le_rpow_iff hMeanNonneg hBq htPos).mp
      have hBpow : (B ^ q) ^ t = B ^ m := by
        rw [← Real.rpow_mul hB, hqt, Real.rpow_natCast]
      rw [hBpow]
      exact hJ.trans hMoment

/-- The same conversion written as an `L^q` root estimate.  In one
specializes `m = 2 * p` and obtains the moment budget from the Gram trace. -/
theorem paperMean_realLpRoot_le_of_higherMoment_budget
    {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (q : ℝ) (m : ℕ) (B : ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hq : 0 < q) (hqm : q ≤ (m : ℝ))
    (hB : 0 ≤ B)
    (hMoment : paperMean (fun ω => f ω ^ m) ≤ B ^ m) :
    (paperMean (fun ω => f ω ^ q)) ^ q⁻¹ ≤ B := by
  have hBudget := paperMean_realRpow_le_of_higherMoment_budget
    f q m B hf hq hqm hB hMoment
  have hMeanNonneg : 0 ≤ paperMean (fun ω => f ω ^ q) := by
    have h0 : paperMean (fun _ω : Ω => (0 : ℝ)) ≤
        paperMean (fun ω => f ω ^ q) :=
      paperMean_mono (fun ω => Real.rpow_nonneg (hf ω) q)
    simpa only [paperMean_zero] using h0
  have hBq : 0 ≤ B ^ q := Real.rpow_nonneg hB q
  have hRoot := (Real.rpow_le_rpow_iff hMeanNonneg hBq
    (inv_pos.mpr hq)).mpr hBudget
  have hqInverse : q * q⁻¹ = 1 := by
    field_simp
  have hBRoot : (B ^ q) ^ q⁻¹ = B := by
    rw [← Real.rpow_mul hB, hqInverse, Real.rpow_one]
  simpa only [hBRoot] using hRoot


end GraphMatrixReplica
