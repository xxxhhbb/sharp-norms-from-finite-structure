import GraphMatrix.Probability.Internal.Structure

/-! # A and B: actual internal coefficients, exact means, and moment bounds -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
set_option maxHeartbeats 6000000

/-- `paperMean` is independent of the concrete lawful enumeration stored in a
`Fintype` instance.  This is needed because the grouped-moment theorem uses a
classical equality decision on its dependent function space, whereas the P1
sample abbreviation inherits the structural subtype equality decision. -/
theorem paperMean_fintype_irrel {Omega : Type}
    (i j : Fintype Omega) (f : Omega → ℝ) :
    @paperMean Omega i f = @paperMean Omega j f := by
  classical
  have hcard : @Fintype.card Omega i = @Fintype.card Omega j :=
    @Fintype.card_congr Omega Omega i j (Equiv.refl Omega)
  have huniv : @Finset.univ Omega i = @Finset.univ Omega j := by
    ext x
    simp
  simp only [paperMean]
  rw [hcard, huniv]

/-- The exact `Fintype` instance hard-wired into the generic grouped-moment
theorems after their local classical elaboration. -/
abbrev p1ClassicalInternalFintype
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :
    Fintype (P1InternalSample P dimension cut c) :=
  @Pi.instFintype
    (P1InternalEdge P cut c)
    (fun e => P1InternalCoordinate P dimension cut c e → Bool)
    (fun a b => Classical.propDecidable (a = b))
    inferInstance
    (fun e =>
      @Pi.instFintype
        (P1InternalCoordinate P dimension cut c e)
        (fun _ => Bool)
        (fun a b => Classical.propDecidable (a = b))
        inferInstance
        (fun _ => inferInstance))

/-- A.1: the actual gamma second moment, with no dimension-positivity restriction. -/
theorem gamma_second
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (b : P1BoundaryLabel P dimension cut c) :
    p1InternalMean P dimension cut c (fun eps => p1Gamma P dimension cut c b eps ^ 2) =
      (interiorCount P dimension cut c : ℝ) := by
  have h := sparse_second (internalKey P dimension cut c b)
    (internalKey_injective P dimension cut c hActive b) (fun _ => (1 : ℝ))
  have h' :
      @paperMean (P1InternalSample P dimension cut c)
          (p1ClassicalInternalFintype P dimension cut c)
          (fun eps => p1Gamma P dimension cut c b eps ^ 2) =
        (Fintype.card (P1InteriorLabel P dimension cut c) : ℝ) := by
    simpa [p1ClassicalInternalFintype, gamma_eq_character_sum] using h
  unfold p1InternalMean
  calc
    _ = @paperMean (P1InternalSample P dimension cut c)
          (p1ClassicalInternalFintype P dimension cut c)
          (fun eps => p1Gamma P dimension cut c b eps ^ 2) :=
      paperMean_fintype_irrel _ _ _
    _ = (Fintype.card (P1InteriorLabel P dimension cut c) : ℝ) := h'
    _ = _ := by exact_mod_cast card_interiorLabel P dimension cut c

/-- A.2: all boundary-square terms are retained in the actual Q. -/
theorem Q_mean
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) :
    p1InternalMean P dimension cut c (p1Q P dimension cut c) =
      (componentCount P dimension cut c : ℝ) := by
  classical
  have hγ (b : P1BoundaryLabel P dimension cut c) :
      paperMean (fun eps => p1Gamma P dimension cut c b eps ^ 2) =
        (interiorCount P dimension cut c : ℝ) :=
    gamma_second P dimension cut c hActive b
  unfold p1InternalMean p1Q
  rw [paperMean_sum]
  simp_rw [hγ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← card_interiorLabel]
  exact_mod_cast boundary_interior_count P dimension cut c

/-- A.3: the exact punctured-volume mean of every actual R_j. -/
theorem R_mean
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (z0 : Fin P.roles)
    (hz0 : z0 ∈ p1BoundaryRoles P cut c) (j : Fin (dimension z0)) :
    p1InternalMean P dimension cut c (fun eps => p1R P dimension cut c z0 hz0 eps j) =
      (puncturedCount P dimension cut c z0 : ℝ) := by
  classical
  have hγ (b : P1BoundaryLabel P dimension cut c) :
      paperMean (fun eps => p1Gamma P dimension cut c b eps ^ 2) =
        (interiorCount P dimension cut c : ℝ) :=
    gamma_second P dimension cut c hActive b
  unfold p1InternalMean p1R
  rw [paperMean_sum]
  simp_rw [hγ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← card_interiorLabel]
  exact_mod_cast rest_interior_count P dimension cut c z0 hz0

/-- B.1: a finite exact sign argument for every required even order. The
constant 32^(q*d) is deliberately coarse, graph-dependent, and dimension-free. -/
theorem gamma_even_moment
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (b : P1BoundaryLabel P dimension cut c)
    (q : ℕ) (hq : q ≤ 16) :
    p1InternalMean P dimension cut c
      (fun eps => |p1Gamma P dimension cut c b eps| ^ (2 * q)) ≤
      (32 : ℝ) ^ (q * internalDegree P cut c) *
        (interiorCount P dimension cut c : ℝ) ^ q := by
  have h := sparse_scalar_moment (internalKey P dimension cut c b)
    (internalKey_injective P dimension cut c hActive b) (fun _ => (1 : ℝ)) q hq
  have h' :
      @paperMean (P1InternalSample P dimension cut c)
          (p1ClassicalInternalFintype P dimension cut c)
          (fun eps => |p1Gamma P dimension cut c b eps| ^ (2 * q)) ≤
        (32 : ℝ) ^ (q * internalDegree P cut c) *
          (Fintype.card (P1InteriorLabel P dimension cut c) : ℝ) ^ q := by
    simpa [p1ClassicalInternalFintype, gamma_eq_character_sum,
      internalDegree] using h
  unfold p1InternalMean
  calc
    _ = @paperMean (P1InternalSample P dimension cut c)
          (p1ClassicalInternalFintype P dimension cut c)
          (fun eps => |p1Gamma P dimension cut c b eps| ^ (2 * q)) :=
      paperMean_fintype_irrel _ _ _
    _ ≤ (32 : ℝ) ^ (q * internalDegree P cut c) *
          (Fintype.card (P1InteriorLabel P dimension cut c) : ℝ) ^ q := h'
    _ = _ := by rw [card_interiorLabel]

/-- A Hilbert-valued family of actual coefficients; repeated boundary outputs
are allowed. This statement includes all cross terms after the q-th power. -/
theorem gamma_family_moment {T : Type} [Fintype T]
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (select : T → P1BoundaryLabel P dimension cut c)
    (q : ℕ) (hq : q ≤ 16) :
    p1InternalMean P dimension cut c
      (fun eps => (∑ t, p1Gamma P dimension cut c (select t) eps ^ 2) ^ q) ≤
      (32 : ℝ) ^ (q * internalDegree P cut c) *
        ((Fintype.card T : ℝ) * (interiorCount P dimension cut c : ℝ)) ^ q := by
  have h := sparse_vector_moment
    (fun t => internalKey P dimension cut c (select t))
    (fun t => internalKey_injective P dimension cut c hActive (select t))
    (fun (_ : T) (_ : P1InteriorLabel P dimension cut c) => (1 : ℝ)) q hq
  have h' :
      @paperMean (P1InternalSample P dimension cut c)
          (p1ClassicalInternalFintype P dimension cut c)
          (fun eps => (∑ t, p1Gamma P dimension cut c (select t) eps ^ 2) ^ q) ≤
        (32 : ℝ) ^ (q * internalDegree P cut c) *
          ((Fintype.card T : ℝ) *
            (Fintype.card (P1InteriorLabel P dimension cut c) : ℝ)) ^ q := by
    simpa [p1ClassicalInternalFintype, gamma_eq_character_sum, energy,
      internalDegree] using h
  unfold p1InternalMean
  calc
    _ = @paperMean (P1InternalSample P dimension cut c)
          (p1ClassicalInternalFintype P dimension cut c)
          (fun eps => (∑ t, p1Gamma P dimension cut c (select t) eps ^ 2) ^ q) :=
      paperMean_fintype_irrel _ _ _
    _ ≤ (32 : ℝ) ^ (q * internalDegree P cut c) *
          ((Fintype.card T : ℝ) *
            (Fintype.card (P1InteriorLabel P dimension cut c) : ℝ)) ^ q := h'
    _ = _ := by rw [card_interiorLabel]

/-- B.2: the actual Q, not a sum of individual fourth moments. -/
theorem Q_moment
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (q : ℕ) (hq : q ≤ 16) :
    p1InternalMean P dimension cut c (fun eps => p1Q P dimension cut c eps ^ q) ≤
      (32 : ℝ) ^ (q * internalDegree P cut c) *
        (componentCount P dimension cut c : ℝ) ^ q := by
  have hCount :
      (Fintype.card (P1BoundaryLabel P dimension cut c) : ℝ) *
        (interiorCount P dimension cut c : ℝ) = (componentCount P dimension cut c : ℝ) := by
    rw [← card_interiorLabel]
    exact_mod_cast boundary_interior_count P dimension cut c
  have h := gamma_family_moment P dimension cut c hActive
    (fun b : P1BoundaryLabel P dimension cut c => b) q hq
  simpa only [p1Q, hCount] using h

/-- B.3: the actual R_j sixteenth moment follows from its vector square sum. -/
theorem R_moment
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (z0 : Fin P.roles)
    (hz0 : z0 ∈ p1BoundaryRoles P cut c) (j : Fin (dimension z0))
    (q : ℕ) (hq : q ≤ 16) :
    p1InternalMean P dimension cut c
      (fun eps => p1R P dimension cut c z0 hz0 eps j ^ q) ≤
      (32 : ℝ) ^ (q * internalDegree P cut c) *
        (puncturedCount P dimension cut c z0 : ℝ) ^ q := by
  have hCount :
      (Fintype.card (P1BoundaryRestLabel P dimension cut c z0) : ℝ) *
        (interiorCount P dimension cut c : ℝ) =
          (puncturedCount P dimension cut c z0 : ℝ) := by
    rw [← card_interiorLabel]
    exact_mod_cast rest_interior_count P dimension cut c z0 hz0
  have h := gamma_family_moment P dimension cut c hActive
    (fun r => p1InsertBoundary P dimension cut c z0 hz0 j r) q hq
  simpa only [p1R, hCount] using h

/-- The two internal moment bounds used by the good-event assembly are actual
specializations, with no moment assumptions in their public signature. -/
theorem internal_moment_endpoints
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (z0 : Fin P.roles)
    (hz0 : z0 ∈ p1BoundaryRoles P cut c) :
    p1InternalMean P dimension cut c (fun eps => p1Q P dimension cut c eps ^ 2) ≤
        (32 : ℝ) ^ (2 * internalDegree P cut c) *
          (componentCount P dimension cut c : ℝ) ^ 2 ∧
    ∀ j : Fin (dimension z0),
      p1InternalMean P dimension cut c
        (fun eps => p1R P dimension cut c z0 hz0 eps j ^ 16) ≤
        (32 : ℝ) ^ (16 * internalDegree P cut c) *
          (puncturedCount P dimension cut c z0 : ℝ) ^ 16 := by
  exact ⟨Q_moment P dimension cut c hActive 2 (by norm_num),
    fun j => R_moment P dimension cut c hActive z0 hz0 j 16 (by norm_num)⟩

end GraphMatrixReplica.P1AD
