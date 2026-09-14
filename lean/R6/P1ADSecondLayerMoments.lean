import R6.P1ADInternalMoments

/-!
# C: moments for every fixed complete internal realization

`eps` is an arbitrary value of `P1InternalSample`, not a random sample averaged
under an internal event. No good-event or moment hypothesis appears below.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
open GraphMatrixReplica.PaperR16
set_option maxHeartbeats 6000000

theorem fintype_sum_irrel {Omega : Type} (i j : Fintype Omega)
    (f : Omega → ℝ) :
    (@Finset.univ Omega i).sum f = (@Finset.univ Omega j).sum f := by
  classical
  have huniv : @Finset.univ Omega i = @Finset.univ Omega j := by
    ext x
    simp
  rw [huniv]

theorem energy_fintype_irrel {T U : Type} [Fintype T]
    (i j : Fintype U) (a : T → U → ℝ) :
    @energy T U inferInstance i a = @energy T U inferInstance j a := by
  unfold energy
  apply Finset.sum_congr rfl
  intro t _
  exact fintype_sum_irrel i j (fun u => a t u ^ 2)

abbrev p1StructuralBoundaryRestLabelFintype
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (z0 : Fin P.roles) :
    Fintype (P1BoundaryRestLabel P dimension cut c z0) := inferInstance

abbrev p1ClassicalBoundaryRestLabelFintype
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (z0 : Fin P.roles) :
    Fintype (P1BoundaryRestLabel P dimension cut c z0) :=
  @Pi.instFintype
    (P1BoundaryRestRole P cut c z0)
    (fun v => Fin (dimension v.1))
    (fun a b => Classical.propDecidable (a = b))
    inferInstance
    (fun v => Fin.fintype (dimension v.1))

abbrev p1ClassicalSecondFintype
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (z0 : Fin P.roles) :
    Fintype (P1SecondSample P dimension cut c z0) :=
  @Pi.instFintype
    (P1BoundaryRestRole P cut c z0)
    (fun v => Fin (dimension v.1) → Bool)
    (fun a b => Classical.propDecidable (a = b))
    inferInstance
    (fun v =>
      @Pi.instFintype
        (Fin (dimension v.1))
        (fun _ => Bool)
        (fun a b => Classical.propDecidable (a = b))
        (Fin.fintype (dimension v.1))
        (fun _ => inferInstance))

/-- Exact deterministic coefficients obtained from the original gamma. -/
def secondCoefficient
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c)
    (j : Fin (dimension z0)) (r : P1BoundaryRestLabel P dimension cut c z0) : ℝ :=
  p1Gamma P dimension cut c (p1InsertBoundary P dimension cut c z0 hz0 j r) eps

theorem secondCharacter_eq
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (r : P1BoundaryRestLabel P dimension cut c z0)
    (eta : P1SecondSample P dimension cut c z0) :
    (p1SecondCharacterZ P dimension cut c z0 r eta : ℝ) = character r eta := by
  simp [p1SecondCharacterZ, character, sign]

theorem Z_eq_chaos
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c)
    (eta : P1SecondSample P dimension cut c z0) (j : Fin (dimension z0)) :
    p1Z P dimension cut c z0 hz0 eps eta j =
      chaos (secondCoefficient P dimension cut c z0 hz0 eps) eta j := by
  simp only [p1Z, chaos, secondCoefficient, secondCharacter_eq]
  exact fintype_sum_irrel
    (p1StructuralBoundaryRestLabelFintype P dimension cut c z0)
    (p1ClassicalBoundaryRestLabelFintype P dimension cut c z0) _

theorem secondCoefficient_energy
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c) :
    energy (secondCoefficient P dimension cut c z0 hz0 eps) =
      p1Q P dimension cut c eps := by
  exact (Q_eq_sum_R P dimension cut c z0 hz0 eps).symm

/-- Exact conditional-on-the-complete-array coefficient variance. -/
theorem Z_second
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c) (j : Fin (dimension z0)) :
    p1SecondMean P dimension cut c z0
      (fun eta => p1Z P dimension cut c z0 hz0 eps eta j ^ 2) =
      p1R P dimension cut c z0 hz0 eps j := by
  have h := sparse_second
    (fun r : P1BoundaryRestLabel P dimension cut c z0 => r)
    (by intro x y hxy; exact hxy)
    (secondCoefficient P dimension cut c z0 hz0 eps j)
  have h' :
      @paperMean (P1SecondSample P dimension cut c z0)
          (p1ClassicalSecondFintype P dimension cut c z0)
          (fun eta => p1Z P dimension cut c z0 hz0 eps eta j ^ 2) =
        (@Finset.univ (P1BoundaryRestLabel P dimension cut c z0)
            (p1StructuralBoundaryRestLabelFintype P dimension cut c z0)).sum
          (fun r => secondCoefficient P dimension cut c z0 hz0 eps j r ^ 2) := by
    simpa [p1ClassicalSecondFintype, p1Z, secondCoefficient,
      secondCharacter_eq] using h
  have hsum :
      (@Finset.univ (P1BoundaryRestLabel P dimension cut c z0)
          (p1StructuralBoundaryRestLabelFintype P dimension cut c z0)).sum
        (fun r => secondCoefficient P dimension cut c z0 hz0 eps j r ^ 2) =
        p1R P dimension cut c z0 hz0 eps j := by
    unfold secondCoefficient p1R
    exact fintype_sum_irrel _ _ _
  unfold p1SecondMean
  calc
    _ = @paperMean (P1SecondSample P dimension cut c z0)
          (p1ClassicalSecondFintype P dimension cut c z0)
          (fun eta => p1Z P dimension cut c z0 hz0 eps eta j ^ 2) :=
      paperMean_fintype_irrel _ _ _
    _ = _ := h'.trans hsum

/-- C.1: for every fixed eps, the second-layer mean of sigmaSq is its actual Q. -/
theorem sigmaSq_mean
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c) :
    p1SecondMean P dimension cut c z0
      (p1SigmaSq P dimension cut c z0 hz0 eps) = p1Q P dimension cut c eps := by
  have hZ (j : Fin (dimension z0)) :
      paperMean (fun eta => p1Z P dimension cut c z0 hz0 eps eta j ^ 2) =
        p1R P dimension cut c z0 hz0 eps j :=
    Z_second P dimension cut c z0 hz0 eps j
  unfold p1SecondMean p1SigmaSq
  rw [paperMean_sum]
  simp_rw [hZ]
  exact (Q_eq_sum_R P dimension cut c z0 hz0 eps).symm

/-- C.2: the mixed square-sum moment, before specializing q to two. -/
theorem sigmaSq_moment
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c) (q : ℕ) (hq : q ≤ 16) :
    p1SecondMean P dimension cut c z0
      (fun eta => p1SigmaSq P dimension cut c z0 hz0 eps eta ^ q) ≤
      (32 : ℝ) ^ (q * secondDegree P cut c z0) * p1Q P dimension cut c eps ^ q := by
  have h := grouped_moment (secondCoefficient P dimension cut c z0 hz0 eps) q hq
  have h' :
      @paperMean (P1SecondSample P dimension cut c z0)
          (p1ClassicalSecondFintype P dimension cut c z0)
          (fun eta => p1SigmaSq P dimension cut c z0 hz0 eps eta ^ q) ≤
        (32 : ℝ) ^ (q * secondDegree P cut c z0) *
          (@energy (Fin (dimension z0))
            (P1BoundaryRestLabel P dimension cut c z0)
            inferInstance
            (p1ClassicalBoundaryRestLabelFintype P dimension cut c z0)
            (secondCoefficient P dimension cut c z0 hz0 eps)) ^ q := by
    simpa [p1ClassicalSecondFintype, p1SigmaSq, Z_eq_chaos, euclideanSq,
      secondDegree] using h
  have hEnergy :
      @energy (Fin (dimension z0))
          (P1BoundaryRestLabel P dimension cut c z0)
          inferInstance
          (p1ClassicalBoundaryRestLabelFintype P dimension cut c z0)
          (secondCoefficient P dimension cut c z0 hz0 eps) =
        p1Q P dimension cut c eps := by
    calc
      _ = @energy (Fin (dimension z0))
            (P1BoundaryRestLabel P dimension cut c z0)
            inferInstance
            (p1StructuralBoundaryRestLabelFintype P dimension cut c z0)
            (secondCoefficient P dimension cut c z0 hz0 eps) :=
        energy_fintype_irrel _ _ _
      _ = _ := secondCoefficient_energy P dimension cut c z0 hz0 eps
  unfold p1SecondMean
  calc
    _ = @paperMean (P1SecondSample P dimension cut c z0)
          (p1ClassicalSecondFintype P dimension cut c z0)
          (fun eta => p1SigmaSq P dimension cut c z0 hz0 eps eta ^ q) :=
      paperMean_fintype_irrel _ _ _
    _ ≤ (32 : ℝ) ^ (q * secondDegree P cut c z0) *
          (@energy (Fin (dimension z0))
            (P1BoundaryRestLabel P dimension cut c z0)
            inferInstance
            (p1ClassicalBoundaryRestLabelFintype P dimension cut c z0)
            (secondCoefficient P dimension cut c z0 hz0 eps)) ^ q := h'
    _ = _ := by rw [hEnergy]

/-- C.3: each actual z_j, for arbitrary fixed eps, including the zero case. -/
theorem Z_even_moment
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c) (j : Fin (dimension z0))
    (q : ℕ) (hq : q ≤ 16) :
    p1SecondMean P dimension cut c z0
      (fun eta => |p1Z P dimension cut c z0 hz0 eps eta j| ^ (2 * q)) ≤
      (32 : ℝ) ^ (q * secondDegree P cut c z0) *
        p1R P dimension cut c z0 hz0 eps j ^ q := by
  have h := sparse_scalar_moment
    (fun r : P1BoundaryRestLabel P dimension cut c z0 => r)
    (by intro x y hxy; exact hxy)
    (secondCoefficient P dimension cut c z0 hz0 eps j) q hq
  have h' :
      @paperMean (P1SecondSample P dimension cut c z0)
          (p1ClassicalSecondFintype P dimension cut c z0)
          (fun eta => |p1Z P dimension cut c z0 hz0 eps eta j| ^ (2 * q)) ≤
        (32 : ℝ) ^ (q * secondDegree P cut c z0) *
          ((@Finset.univ (P1BoundaryRestLabel P dimension cut c z0)
              (p1StructuralBoundaryRestLabelFintype P dimension cut c z0)).sum
            (fun r => secondCoefficient P dimension cut c z0 hz0 eps j r ^ 2)) ^ q := by
    simpa [p1ClassicalSecondFintype, p1Z, secondCoefficient,
      secondCharacter_eq, secondDegree] using h
  have hsum :
      (@Finset.univ (P1BoundaryRestLabel P dimension cut c z0)
          (p1StructuralBoundaryRestLabelFintype P dimension cut c z0)).sum
        (fun r => secondCoefficient P dimension cut c z0 hz0 eps j r ^ 2) =
        p1R P dimension cut c z0 hz0 eps j := by
    unfold secondCoefficient p1R
    exact fintype_sum_irrel _ _ _
  unfold p1SecondMean
  calc
    _ = @paperMean (P1SecondSample P dimension cut c z0)
          (p1ClassicalSecondFintype P dimension cut c z0)
          (fun eta => |p1Z P dimension cut c z0 hz0 eps eta j| ^ (2 * q)) :=
      paperMean_fintype_irrel _ _ _
    _ ≤ (32 : ℝ) ^ (q * secondDegree P cut c z0) *
          ((@Finset.univ (P1BoundaryRestLabel P dimension cut c z0)
              (p1StructuralBoundaryRestLabelFintype P dimension cut c z0)).sum
            (fun r => secondCoefficient P dimension cut c z0 hz0 eps j r ^ 2)) ^ q := h'
    _ = _ := by rw [hsum]

/-- All three C obligations in one actual, pointwise-in-eps theorem. -/
theorem second_layer_endpoints
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c) :
    p1SecondMean P dimension cut c z0 (p1SigmaSq P dimension cut c z0 hz0 eps) =
        p1Q P dimension cut c eps ∧
    p1SecondMean P dimension cut c z0
        (fun eta => p1SigmaSq P dimension cut c z0 hz0 eps eta ^ 2) ≤
        (32 : ℝ) ^ (2 * secondDegree P cut c z0) * p1Q P dimension cut c eps ^ 2 ∧
    ∀ j : Fin (dimension z0),
      p1SecondMean P dimension cut c z0
        (fun eta => |p1Z P dimension cut c z0 hz0 eps eta j| ^ 32) ≤
        (32 : ℝ) ^ (16 * secondDegree P cut c z0) *
          p1R P dimension cut c z0 hz0 eps j ^ 16 := by
  refine ⟨sigmaSq_mean P dimension cut c z0 hz0 eps,
    sigmaSq_moment P dimension cut c z0 hz0 eps 2 (by norm_num), ?_⟩
  intro j
  simpa only [show 2 * 16 = 32 by norm_num] using
    Z_even_moment P dimension cut c z0 hz0 eps j 16 (by norm_num)

/-- When B = {z0}, the variance identity is deterministic, not merely in mean. -/
theorem sigmaSq_eq_Q_of_boundary_singleton
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (hB : p1BoundaryRoles P cut c = {z0})
    (eps : P1InternalSample P dimension cut c)
    (eta : P1SecondSample P dimension cut c z0) :
    p1SigmaSq P dimension cut c z0 hz0 eps eta = p1Q P dimension cut c eps := by
  classical
  letI : IsEmpty (P1BoundaryRestRole P cut c z0) :=
    p1BoundaryRestRole_isEmpty_of_boundary_singleton P cut c z0 hB
  letI : Unique (P1BoundaryRestLabel P dimension cut c z0) :=
    { default := fun v => isEmptyElim v
      uniq := fun r => funext fun v => isEmptyElim v }
  rw [Q_eq_sum_R P dimension cut c z0 hz0 eps]
  unfold p1SigmaSq
  apply Finset.sum_congr rfl
  intro j _
  simp [p1Z, p1R, p1SecondCharacterZ]

#print axioms sigmaSq_mean
#print axioms sigmaSq_moment
#print axioms Z_even_moment
#print axioms second_layer_endpoints
#print axioms sigmaSq_eq_Q_of_boundary_singleton
end GraphMatrixReplica.P1AD
