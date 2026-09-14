import GraphMatrix.Main.GraphRawProbabilityBridge
import GraphMatrix.Probability.MomentComparison.ScalarMomentProof

/-! Exact L2 orthogonality for the genuine detached-component scalar. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace GraphMatrixReplica.Model.RawFactorShape

variable {W E : Type} [Fintype W] [Fintype E] [DecidableEq W] [DecidableEq E]
variable (S : RawFactorShape W E)

/-- Primitive coordinate read by detached assignment `a` at occurrence `e`. -/
def detachedAssignmentCoord
    (j : S.DetachedComponent)
    (a : S.canonicalPreprocessedShape.DetachedTuple j)
    (e : S.CanonicalDetachedOccurrence j) : S.DetachedPrimitiveCoord j :=
  ⟨⟨e.1, fun w => a ⟨w.1, e.2 w.1 w.2⟩⟩, e.2⟩

theorem detachedAssignmentCoord_occurrence_eq
    {j : S.DetachedComponent}
    {a b : S.canonicalPreprocessedShape.DetachedTuple j}
    {e e' : S.CanonicalDetachedOccurrence j}
    (h : S.detachedAssignmentCoord j a e =
      S.detachedAssignmentCoord j b e') : e = e' := by
  apply Subtype.ext
  exact congrArg (fun p : S.DetachedPrimitiveCoord j => p.1.1) h

theorem detachedAssignmentCoord_injective
    (j : S.DetachedComponent)
    (a : S.canonicalPreprocessedShape.DetachedTuple j) :
    Function.Injective (S.detachedAssignmentCoord j a) := by
  intro e e' h
  exact S.detachedAssignmentCoord_occurrence_eq h

/-- The squarefree Walsh support of one detached assignment. -/
def detachedAssignmentSupport
    (j : S.DetachedComponent)
    (a : S.canonicalPreprocessedShape.DetachedTuple j) :
    Finset (S.DetachedPrimitiveCoord j) := by
  classical
  exact Finset.univ.image (S.detachedAssignmentCoord j a)

theorem detachedAssignmentSupport_injective (j : S.DetachedComponent) :
    Function.Injective (S.detachedAssignmentSupport j) := by
  classical
  intro a b hab
  funext d
  have hdmem := S.mem_detachedComponentRoles.mp d.2
  rcases hdmem.1.1 with ⟨e, he⟩
  have hocc : S.DetachedOccurrence j e := by
    intro w hw
    apply S.mem_detachedComponentRoles.mpr
    refine ⟨S.scope_detached_closed e he hw hdmem.1, ?_⟩
    exact (S.component_scope_eq e hw he).trans hdmem.2
  let ed : S.CanonicalDetachedOccurrence j := ⟨e, hocc⟩
  have hmem : S.detachedAssignmentCoord j a ed ∈
      S.detachedAssignmentSupport j a := by
    unfold detachedAssignmentSupport
    exact Finset.mem_image.mpr ⟨ed, Finset.mem_univ _, rfl⟩
  rw [hab] at hmem
  unfold detachedAssignmentSupport at hmem
  rcases Finset.mem_image.mp hmem with ⟨ed', _hed', heq⟩
  have hedeq : ed' = ed :=
    S.detachedAssignmentCoord_occurrence_eq heq
  subst ed'
  have hfun :
      (fun w : {w : W // w ∈ S.scope e} =>
        b ⟨w.1, hocc w.1 w.2⟩) =
      (fun w : {w : W // w ∈ S.scope e} =>
        a ⟨w.1, hocc w.1 w.2⟩) := by
    change
      (⟨⟨e, fun w => b ⟨w.1, hocc w.1 w.2⟩⟩, hocc⟩ :
        S.DetachedPrimitiveCoord j) =
      ⟨⟨e, fun w => a ⟨w.1, hocc w.1 w.2⟩⟩, hocc⟩ at heq
    have hraw := congrArg Subtype.val heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp hraw).2
  have hv := congrFun hfun ⟨d.1, he⟩
  simpa using hv.symm

theorem detachedAmplitude_sign_eq_support_prod
    (j : S.DetachedComponent)
    (a : S.canonicalPreprocessedShape.DetachedTuple j)
    (epsilon : S.DetachedPrimitiveCoord j → Bool) :
    S.detachedAmplitudeFromBlock j
        (fun p => (GraphMatrixReplica.rademacherSign (epsilon p) : ℝ)) a =
      ∏ p ∈ S.detachedAssignmentSupport j a,
        (GraphMatrixReplica.rademacherSign (epsilon p) : ℝ) := by
  classical
  unfold detachedAmplitudeFromBlock detachedAssignmentSupport
  rw [Finset.prod_image]
  · rfl
  · exact fun e _ e' _ h => S.detachedAssignmentCoord_injective j a h

/-- One-coordinate finite Rademacher power sum. -/
theorem main_rademacherSign_power_sum (m : ℕ) :
    (∑ b : Bool, (GraphMatrixReplica.rademacherSign b : ℝ) ^ m) =
      if Even m then 2 else 0 := by
  by_cases h : Even m
  · rw [if_pos h]
    simp [GraphMatrixReplica.rademacherSign, h.neg_one_pow]
    norm_num
  · rw [if_neg h]
    have hm : Odd m := Nat.not_even_iff_odd.mp h
    simp [GraphMatrixReplica.rademacherSign, hm.neg_one_pow]

/-- Product Rademacher characters have expectation one exactly at even
multiplicity vectors. -/
theorem paperMean_rademacherSign_monomial
    {K : Type} [Fintype K] [DecidableEq K] (count : K → ℕ) :
    paperMean (fun epsilon : K → Bool => ∏ k : K,
      (GraphMatrixReplica.rademacherSign (epsilon k) : ℝ) ^ count k) =
      if ∀ k, Even (count k) then 1 else 0 := by
  classical
  unfold paperMean
  have heq := Fintype.prod_sum
    (fun (k : K) (b : Bool) =>
      (GraphMatrixReplica.rademacherSign b : ℝ) ^ count k)
  dsimp only at heq ⊢
  rw [← heq]
  simp_rw [main_rademacherSign_power_sum]
  by_cases h : ∀ k, Even (count k)
  · simp [h]
  · have hz : (∏ k, if Even (count k) then (2 : ℝ) else 0) = 0 := by
      obtain ⟨k, hk⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
    rw [hz, mul_zero, if_neg h]

/-- Uniform Walsh characters indexed by two finite supports are orthogonal. -/
theorem paperMean_supportCharacter_mul
    {K : Type} [Fintype K] [DecidableEq K] (s t : Finset K) :
    paperMean (fun epsilon : K → Bool =>
      (∏ k ∈ s, (GraphMatrixReplica.rademacherSign (epsilon k) : ℝ)) *
      (∏ k ∈ t, (GraphMatrixReplica.rademacherSign (epsilon k) : ℝ))) =
      if s = t then 1 else 0 := by
  classical
  let count : K → ℕ := fun k =>
    (if k ∈ s then 1 else 0) + (if k ∈ t then 1 else 0)
  have hpoint : (fun epsilon : K → Bool =>
      (∏ k ∈ s, (GraphMatrixReplica.rademacherSign (epsilon k) : ℝ)) *
      (∏ k ∈ t, (GraphMatrixReplica.rademacherSign (epsilon k) : ℝ))) =
      (fun epsilon => ∏ k : K,
        (GraphMatrixReplica.rademacherSign (epsilon k) : ℝ) ^ count k) := by
    funext epsilon
    simp only [count, pow_add, Finset.prod_mul_distrib]
    congr 1 <;> simp
  have heven : (∀ k : K, Even (count k)) ↔ s = t := by
    constructor
    · intro h
      ext k
      have hk := h k
      by_cases hs : k ∈ s <;> by_cases ht : k ∈ t <;>
        simp [count, hs, ht] at hk ⊢
    · intro h
      subst t
      intro k
      by_cases hk : k ∈ s <;> simp [count, hk]
  rw [hpoint]
  rw [paperMean_rademacherSign_monomial]
  exact if_congr heven rfl rfl

theorem paperMean_detachedAmplitude_pair
    (j : S.DetachedComponent)
    (a b : S.canonicalPreprocessedShape.DetachedTuple j) :
    paperMean (fun epsilon : S.DetachedPrimitiveCoord j → Bool =>
      S.detachedAmplitudeFromBlock j
          (fun p => (GraphMatrixReplica.rademacherSign (epsilon p) : ℝ)) a *
      S.detachedAmplitudeFromBlock j
          (fun p => (GraphMatrixReplica.rademacherSign (epsilon p) : ℝ)) b) =
      if a = b then 1 else 0 := by
  simp_rw [S.detachedAmplitude_sign_eq_support_prod j a,
    S.detachedAmplitude_sign_eq_support_prod j b]
  rw [paperMean_supportCharacter_mul]
  simpa only [(S.detachedAssignmentSupport_injective j).eq_iff]

/-- Exact second moment: all off-diagonal assignment pairs cancel. -/
theorem paperMean_detachedScalar_sq
    (j : S.DetachedComponent) :
    paperMean (fun epsilon : S.DetachedPrimitiveCoord j → Bool =>
      S.detachedScalarFromBlock j
        (fun p => (GraphMatrixReplica.rademacherSign (epsilon p) : ℝ)) ^ 2) =
      Fintype.card (S.canonicalPreprocessedShape.DetachedTuple j) := by
  classical
  unfold detachedScalarFromBlock
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [paperMean_sum]
  simp_rw [paperMean_sum, S.paperMean_detachedAmplitude_pair]
  simp [Fintype.card_pi]

/-- The coordinatewise sign map carries the finite Boolean cube to the actual
product law used by the raw-factor model. -/
theorem main_map_bool_sign_eq_pi_rootScalarSignLaw
    (K : Type) [Fintype K] [DecidableEq K] :
    Measure.map
        (fun epsilon : K → Bool => fun k =>
          (GraphMatrixReplica.rademacherSign (epsilon k) : ℝ))
        (GraphMatrixReplica.mainFiniteUniformLaw (K → Bool)) =
      Measure.infinitePi (fun _ : K => GraphMatrixReplica.mainScalarSignLaw) := by
  rw [GraphMatrixReplica.main_uniform_bool_function_law]
  exact Measure.infinitePi_map_pi
    (fun _ : K => GraphMatrixReplica.mainFiniteUniformLaw Bool)
    (fun _ => measurable_of_finite
      (fun b : Bool => (GraphMatrixReplica.rademacherSign b : ℝ)))

/-- Exact detached second moment under the genuine block law. -/
theorem integral_abs_detachedScalar_sq_rootScalarSignLaw
    (j : S.DetachedComponent) :
    (∫ x, |S.detachedScalarFromBlock j x| ^ 2
      ∂S.oneBlockLaw (fun _ => GraphMatrixReplica.mainScalarSignLaw)
        (Sum.inr j)) =
      Fintype.card (S.canonicalPreprocessedShape.DetachedTuple j) := by
  change
    (∫ x : S.DetachedPrimitiveCoord j → ℝ,
      |S.detachedScalarFromBlock j x| ^ 2
      ∂Measure.infinitePi
        (fun _ : S.DetachedPrimitiveCoord j =>
          GraphMatrixReplica.mainScalarSignLaw)) = _
  rw [← main_map_bool_sign_eq_pi_rootScalarSignLaw
    (S.DetachedPrimitiveCoord j)]
  rw [integral_map (measurable_of_finite _).aemeasurable
    ((S.measurable_detachedScalarFromBlock j).abs.pow_const 2).aestronglyMeasurable]
  rw [GraphMatrixReplica.main_integral_finiteUniformLaw_eq_paperMean]
  simpa only [sq_abs] using S.paperMean_detachedScalar_sq j

/-- Cardinal form of the same identity: one factor for every detached role. -/
theorem integral_abs_detachedScalar_sq_eq_roleDimensionProduct
    (j : S.DetachedComponent) :
    (∫ x, |S.detachedScalarFromBlock j x| ^ 2
      ∂S.oneBlockLaw (fun _ => GraphMatrixReplica.mainScalarSignLaw)
        (Sum.inr j)) =
      ∏ d : S.CanonicalDetached j, S.size d.1 := by
  rw [S.integral_abs_detachedScalar_sq_rootScalarSignLaw j]
  rw [Fintype.card_pi]
  norm_cast
  apply Finset.prod_congr rfl
  intro d _hd
  change Fintype.card (Fin (S.size d.1)) = S.size d.1
  exact Fintype.card_fin _

/-- With a common ambient dimension `n`, the exact second moment is the
expected power of `n` indexed by the roles of the detached component. -/
theorem integral_abs_detachedScalar_sq_eq_pow_of_constantSize
    (j : S.DetachedComponent) (n : ℕ)
    (hsize : ∀ w : W, S.size w = n) :
    (∫ x, |S.detachedScalarFromBlock j x| ^ 2
      ∂S.oneBlockLaw (fun _ => GraphMatrixReplica.mainScalarSignLaw)
        (Sum.inr j)) =
      (n : ℝ) ^ Fintype.card (S.CanonicalDetached j) := by
  rw [S.integral_abs_detachedScalar_sq_eq_roleDimensionProduct j]
  simp [hsize]

/-- The componentwise power bound needed when every role dimension is at most
the common ambient size `n`. -/
theorem integral_abs_detachedScalar_sq_le_pow_of_size_le
    (j : S.DetachedComponent) (n : ℕ)
    (hsize : ∀ w : W, S.size w ≤ n) :
    (∫ x, |S.detachedScalarFromBlock j x| ^ 2
      ∂S.oneBlockLaw (fun _ => GraphMatrixReplica.mainScalarSignLaw)
        (Sum.inr j)) ≤
      (n : ℝ) ^ Fintype.card (S.CanonicalDetached j) := by
  rw [S.integral_abs_detachedScalar_sq_eq_roleDimensionProduct j]
  norm_cast
  simpa using Finset.prod_le_prod (s := Finset.univ)
    (fun (d : S.CanonicalDetached j) _hd => Nat.zero_le (S.size d.1))
    (fun (d : S.CanonicalDetached j) _hd => hsize d.1)

/-- Multiplying the exact component laws costs one half-power per detached
role after the final square root.  This theorem records the squared bound. -/
theorem prod_integral_abs_detachedScalar_sq_le_pow_sum
    (n : ℕ) (hsize : ∀ w : W, S.size w ≤ n) :
    (∏ j : S.DetachedComponent,
      ∫ x, |S.detachedScalarFromBlock j x| ^ 2
        ∂S.oneBlockLaw (fun _ => GraphMatrixReplica.mainScalarSignLaw)
          (Sum.inr j)) ≤
      (n : ℝ) ^
        (∑ j : S.DetachedComponent,
          Fintype.card (S.CanonicalDetached j)) := by
  calc
    (∏ j : S.DetachedComponent,
      ∫ x, |S.detachedScalarFromBlock j x| ^ 2
        ∂S.oneBlockLaw (fun _ => GraphMatrixReplica.mainScalarSignLaw)
          (Sum.inr j)) ≤
        ∏ j : S.DetachedComponent,
          (n : ℝ) ^ Fintype.card (S.CanonicalDetached j) := by
      apply Finset.prod_le_prod
      · intro j _hj
        exact integral_nonneg (fun _ => sq_nonneg _)
      · intro j _hj
        exact S.integral_abs_detachedScalar_sq_le_pow_of_size_le j n hsize
    _ = (n : ℝ) ^
        (∑ j : S.DetachedComponent,
          Fintype.card (S.CanonicalDetached j)) := by
      exact Finset.prod_pow_eq_pow_sum Finset.univ
        (fun j : S.DetachedComponent =>
          Fintype.card (S.CanonicalDetached j)) (n : ℝ)


end GraphMatrixReplica.Model.RawFactorShape
