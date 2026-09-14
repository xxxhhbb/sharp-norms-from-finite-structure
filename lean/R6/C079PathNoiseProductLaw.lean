import R6.C079PathAuxMomentShape
import R6.PaperGraphMatrixEntryMoments

/-! # Finite uniform product law for canonical path edge noise -/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Uniform averaging of a product of independent coordinate functions.
The statement includes empty index and empty coordinate types. -/
theorem paperMean_coordinateProduct
    {I Ω : Type} [Fintype I] [Fintype Ω] [DecidableEq I]
    (F : I → Ω → ℝ) :
    paperMean (fun w : I → Ω => ∏ i : I, F i (w i)) =
      ∏ i : I, paperMean (F i) := by
  classical
  unfold paperMean
  rw [Fintype.card_fun]
  push_cast
  rw [← Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [inv_pow]

/-- Each edge of a canonical path is an independent uniform sign array.
Real edge observables include operator-norm powers of the edge matrices. -/
theorem c079PathNoiseProductLaw (ell m : ℕ)
    (F : Fin ell → (Fin m × Fin m → Bool) → ℝ) :
    paperMean (fun ε : JointEdgeSignSample
        (c079CanonicalPathDimension ell m) =>
      ∏ e : Fin ell, F e (ε e)) =
        ∏ e : Fin ell,
          paperMean (F e) := by
  let g : (Fin ell → (Fin m × Fin m → Bool)) → ℝ :=
    fun ε => ∏ e : Fin ell, F e (ε e)
  calc
    _ = paperMean g := by
      simpa [g, c079PathSampleEquiv] using
        (paperMean_equiv (c079PathSampleEquiv ell m) g)
    _ = _ := paperMean_coordinateProduct F

/-- The rational-observable version is a direct specialization through the
canonical inclusion into the reals. -/
theorem c079PathNoiseProductLaw_rat (ell m : ℕ)
    (F : Fin ell → (Fin m × Fin m → Bool) → ℚ) :
    paperMean (fun ε : JointEdgeSignSample
        (c079CanonicalPathDimension ell m) =>
      ∏ e : Fin ell, (F e (ε e) : ℝ)) =
        ∏ e : Fin ell,
          paperMean (fun σ : Fin m × Fin m → Bool => (F e σ : ℝ)) := by
  exact c079PathNoiseProductLaw ell m (fun e σ => (F e σ : ℝ))

/-- With no path edges, both the random product and its expectation are one. -/
theorem c079PathNoiseProductLaw_zero_edges (m : ℕ)
    (F : Fin 0 → (Fin m × Fin m → Bool) → ℝ) :
    paperMean (fun ε : JointEdgeSignSample
        (c079CanonicalPathDimension 0 m) =>
      ∏ e : Fin 0, F e (ε e)) = 1 := by
  rw [c079PathNoiseProductLaw 0 m F]
  simp

/-- At auxiliary dimension zero the edge-sign sample has one possible value,
so the mean of the path product is that deterministic product. -/
theorem c079PathNoiseProductLaw_zero_dimension (ell : ℕ)
    (F : Fin ell → (Fin 0 × Fin 0 → Bool) → ℝ) :
    paperMean (fun ε : JointEdgeSignSample
        (c079CanonicalPathDimension ell 0) =>
      ∏ e : Fin ell, F e (ε e)) =
        ∏ e : Fin ell,
          F e (fun ab => Fin.elim0 ab.1) := by
  letI : Unique (Fin 0 × Fin 0 → Bool) :=
    { default := fun ab => Fin.elim0 ab.1
      uniq := by
        intro σ
        funext ab
        exact Fin.elim0 ab.1 }
  rw [c079PathNoiseProductLaw ell 0 F]
  apply Finset.prod_congr rfl
  intro e _
  simp [paperMean]
  congr 1

#print axioms paperMean_coordinateProduct
#print axioms c079PathNoiseProductLaw
#print axioms c079PathNoiseProductLaw_rat
#print axioms c079PathNoiseProductLaw_zero_edges
#print axioms c079PathNoiseProductLaw_zero_dimension

end GraphMatrixReplica
