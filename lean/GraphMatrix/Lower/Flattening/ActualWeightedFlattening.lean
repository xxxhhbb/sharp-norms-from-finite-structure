import GraphMatrix.Lower.Flattening.ActualMixedFlattening

/-!
# actual weighted-flattening lower bound

This module removes the old external `hReindexNorm`, instantiates C1's actual
cover/intersection theorems, and rewrites the recursive heterogeneous mean as
the finite uniform average over the genuine fresh original edge arrays.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model.C2Actual

open GraphMatrixReplica
open GraphMatrixReplica.Model
open GraphMatrixReplica.Model.ActualPrimitiveObservations

attribute [local instance] Classical.propDecidable

/-! ## 1. The recursive heterogeneous mean is the ordinary finite uniform mean -/

/-- Cardinal mean on the complete heterogeneous Boolean group sample. -/
theorem lowerHeteroMean_eq_card_mean :
    ∀ q (size : Fin q → ℕ) (f : lowerHeteroNoise q size → ℝ),
      lowerHeteroMean q size f =
        (∑ w : lowerHeteroNoise q size, f w) /
          (Fintype.card (lowerHeteroNoise q size) : ℝ) := by
  intro q
  induction q with
  | zero =>
      intro size f
      have hcard : Fintype.card (lowerHeteroNoise 0 size) = 1 := by
        rw [Fintype.card_eq_one_iff]
        refine ⟨fun g => Fin.elim0 g, ?_⟩
        intro a
        funext g
        exact Fin.elim0 g
      simp [lowerHeteroMean, hcard]
      exact congrArg f (Subsingleton.elim _ _)
  | succ q ih =>
      intro size f
      let tailSize : Fin q → ℕ := fun g => size g.succ
      let Head := Fin (size 0) → Bool
      let Tail := lowerHeteroNoise q tailSize
      have hHeadPos : (Fintype.card Head : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Head).ne'
      have hTailPos : (Fintype.card Tail : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Tail).ne'
      have hCard : Fintype.card (lowerHeteroNoise (q + 1) size) =
          Fintype.card Head * Fintype.card Tail := by
        have hc := Fintype.card_congr
          (Fin.consEquiv (fun g : Fin (q + 1) => Fin (size g) → Bool))
        simpa [Head, Tail, tailSize, Fintype.card_prod] using hc.symm
      have hSum :
          (∑ w : lowerHeteroNoise (q + 1) size, f w) =
            ∑ tail : Tail, ∑ head : Head, f (Fin.cons head tail) := by
        calc
          (∑ w : lowerHeteroNoise (q + 1) size, f w) =
              ∑ z : Head × Tail, f (Fin.cons z.1 z.2) := by
                symm
                apply Fintype.sum_equiv
                  (Fin.consEquiv (fun g : Fin (q + 1) => Fin (size g) → Bool))
                intro z
                rfl
          _ = ∑ tail : Tail, ∑ head : Head, f (Fin.cons head tail) := by
                rw [Fintype.sum_prod_type, Finset.sum_comm]
      change lowerHeteroMean q tailSize
          (fun tail => allSignsMean (size 0)
            (fun head => f (Fin.cons head tail))) = _
      rw [ih]
      simp_rw [allSignsMean_eq_card_mean]
      simp_rw [← Finset.sum_div]
      rw [hSum, hCard]
      field_simp [hHeadPos, hTailPos]
      simp only [Nat.cast_mul, Head, Tail]
      ring

/-- Genuine finite uniform mean on the original fresh arrays. -/
def actualFreshMean
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (f : FreshSample (G := P.toPartiteShape) S dimension → ℝ) : ℝ :=
  (∑ ξ : FreshSample (G := P.toPartiteShape) S dimension, f ξ) /
    (Fintype.card (FreshSample (G := P.toPartiteShape) S dimension) : ℝ)

/-- The concrete fresh-array/noise equivalence preserves the complete uniform
mean exactly, not merely in distribution. -/
theorem lowerHeteroMean_eq_actualFreshMean
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (f : FreshSample (G := P.toPartiteShape) S dimension → ℝ) :
    lowerHeteroMean (freshCount P S) (freshSize P S dimension)
      (fun w => f ((freshSampleNoiseEquiv P S dimension).symm w)) =
      actualFreshMean P S dimension f := by
  rw [lowerHeteroMean_eq_card_mean]
  unfold actualFreshMean
  have hSum :
      (∑ w : lowerHeteroNoise (freshCount P S) (freshSize P S dimension),
          f ((freshSampleNoiseEquiv P S dimension).symm w)) =
        ∑ ξ : FreshSample (G := P.toPartiteShape) S dimension, f ξ := by
    apply Fintype.sum_equiv (freshSampleNoiseEquiv P S dimension).symm
    intro w
    rfl
  have hCard :
      Fintype.card (lowerHeteroNoise (freshCount P S) (freshSize P S dimension)) =
        Fintype.card (FreshSample (G := P.toPartiteShape) S dimension) := by
    exact (Fintype.card_congr (freshSampleNoiseEquiv P S dimension)).symm
  rw [hSum, hCard]

/-- The actual matrix norm average is exactly the coefficient chaos norm average. -/
theorem actualFreshMean_norm_eq_lowerHeteroMean
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    actualFreshMean P S dimension
      (fun ξ => (@norm (Matrix (PartiteBoundaryRow (G := P.toPartiteShape) dimension) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm (partiteBoundaryMatrixReal P dimension
        (assembleSample (G := P.toPartiteShape) S dimension ω ξ)))) =
    lowerHeteroMean (freshCount P S) (freshSize P S dimension)
      (fun noise => (@norm (Matrix (PartiteBoundaryRow (G := P.toPartiteShape) dimension) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm (lowerHeteroChaos (freshCount P S) (freshSize P S dimension)
        (actualCoefficientFamily P S dimension ω) noise))) := by
  rw [← lowerHeteroMean_eq_actualFreshMean]
  apply congrArg (lowerHeteroMean (freshCount P S) (freshSize P S dimension))
  funext noise
  have hm := lowerHeteroChaos_actual_eq_partiteBoundaryMatrixReal P S dimension ω
    ((freshSampleNoiseEquiv P S dimension).symm noise)
  simpa only [Equiv.apply_symm_apply] using congrArg (fun M : Matrix (PartiteBoundaryRow (G := P.toPartiteShape) dimension) (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ℝ => @norm _ Matrix.instL2OpNormedAddCommGroup.toNorm M) hm.symm

/-- Positive role dimensions provide an explicit all-zero separator assignment. -/
theorem separatorAssignments_univ_nonempty
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hdim : ∀ v, 0 < dimension v) :
    (Finset.univ : Finset (C1C2.SeparatorAssignment P S (X dimension))).Nonempty := by
  refine ⟨(fun v => ⟨0, hdim v.1.1⟩), Finset.mem_univ _⟩

/-- The concrete coefficient scale appearing on the left side of C2. -/
def actualC2ExplicitScale
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ) (hdim : ∀ v, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) : ℝ :=
  Real.sqrt
      ((Fintype.card (C2.RoleAssign (C1C2.retainedLabel P S (X dimension))
          (C1C2.rows P S \ C1C2.separator P S)) : ℝ) *
       (Fintype.card (C2.RoleAssign (C1C2.retainedLabel P S (X dimension))
          (C1C2.cols P S \ C1C2.separator P S)) : ℝ)) *
    Finset.univ.sup' (separatorAssignments_univ_nonempty P S dimension hdim)
      (fun s : C1C2.SeparatorAssignment P S (X dimension) =>
        |actualWeight (G := P.toPartiteShape) S dimension ω
          (c1c2ToCutAssignment P S dimension s)|)

/-- The native L2 operator norm of the actual retained-address coefficient. -/
def actualC2CoefficientScale
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) : ℝ :=
  @norm (Matrix (RowAddress P S (X dimension))
      (ColAddress P S (X dimension)) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (C1C2.retainedAddressCoefficient P S (X dimension)
      (c1c2ActualWeight P S dimension ω))

/-- The recursive heterogeneous-chaos L2-operator-norm mean on the right side. -/
def actualC2ChaosMean
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) : ℝ :=
  lowerHeteroMean (freshCount P S) (freshSize P S dimension)
    (fun noise =>
      @norm (Matrix (PartiteBoundaryRow (G := P.toPartiteShape) dimension)
          (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm
        (lowerHeteroChaos (freshCount P S) (freshSize P S dimension)
          (actualCoefficientFamily P S dimension ω) noise))

/-- The finite uniform mean of the actual assembled original typed matrices. -/
def actualC2FreshMean
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) : ℝ :=
  actualFreshMean P S dimension
    (fun ξ =>
      @norm (Matrix (PartiteBoundaryRow (G := P.toPartiteShape) dimension)
          (PartiteBoundaryCol (G := P.toPartiteShape) dimension) ℝ)
        Matrix.instL2OpNormedAddCommGroup.toNorm
        (partiteBoundaryMatrixReal P dimension
          (assembleSample (G := P.toPartiteShape) S dimension ω ξ)))

/-- The existing exact coefficient norm, specialized with an inferred result
type so the two definitionally equal retained-role Fintype presentations are
never compared against a separately handwritten matrix type. -/
def actualCoefficientNormProof
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v : Fin P.roles, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :=
  letI : ∀ v : Fin P.roles, Nonempty (Fin (dimension v)) :=
    fun v => ⟨⟨0, hdim v⟩⟩
  C1C2.coefficient_norm P S (X dimension) hNoIsolated hMin
    (c1c2ActualWeight P S dimension ω)

/-- The actual retained-address coefficient has the same native L2 operator
norm as the role-fibre coefficient.  Its result type is inferred for the same
instance-stability reason as `actualCoefficientNormProof`. -/
def actualRetainedCoefficientNormProof
    (P : PaperShape) (S : Finset (Fin P.roles))
    (dimension : Fin P.roles → ℕ)
    (hdim : ∀ v : Fin P.roles, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :=
  letI : ∀ v : Fin P.roles, Nonempty (Fin (dimension v)) :=
    fun v => ⟨⟨0, hdim v⟩⟩
  C1C2.retainedAddressCoefficient_norm P S (X dimension)
    (c1c2ActualWeight P S dimension ω)

/-! ## 2. No-external-hypothesis actual theorem -/

set_option backward.isDefEq.respectTransparency true

variable (P : PaperShape) (S : Finset (Fin P.roles))
variable (dimension : Fin P.roles → ℕ)

/-- The old `weightedFlattening_of_mixed_reindex` with all three graph-specific
premises discharged internally: supplies cover/intersection and C supplies
the actual norm reindex. -/
theorem actual_weightedFlattening_lower
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v : Fin P.roles, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    actualC2CoefficientScale P S dimension ω ≤
      Real.sqrt 3 ^ freshCount P S * actualC2ChaosMean P S dimension ω := by
  letI : ∀ v : Fin P.roles, Nonempty (Fin (dimension v)) :=
    fun v => ⟨⟨0, hdim v⟩⟩
  have hStack := lowerMixedFlatten_norm_le
    (freshCount P S) (freshSize P S dimension) (freshDir P S)
    (actualCoefficientFamily P S dimension ω)
  rw [actual_mixed_reindex_norm P dimension S ω] at hStack
  simpa [actualC2CoefficientScale, actualC2ChaosMean] using hStack

/-- D: final deterministic lower bound with the RHS written as the finite
uniform average over the ACTUAL fresh original edge arrays and with the matrix
inside that average equal to the original typed `partiteBoundaryMatrix` after
assembly with the fixed nonfresh realization.  No `hCover`, `hInter`, or
`hReindexNorm` is an argument. -/
theorem actual_C2_lower_bound
    (hNoIsolated : P.HasNoIsolatedMiddleRoles)
    (hMin : P.toPartiteShape.IsMinimumRightLeftSeparator S)
    (hdim : ∀ v : Fin P.roles, 0 < dimension v)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension) :
    actualC2CoefficientScale P S dimension ω ≤
      Real.sqrt 3 ^ freshCount P S * actualC2FreshMean P S dimension ω := by
  letI : ∀ v : Fin P.roles, Nonempty (Fin (dimension v)) :=
    fun v => ⟨⟨0, hdim v⟩⟩
  have h := actual_weightedFlattening_lower P S dimension
    hNoIsolated hMin hdim ω
  have hMean : actualC2ChaosMean P S dimension ω =
      actualC2FreshMean P S dimension ω := by
    simpa [actualC2ChaosMean, actualC2FreshMean] using
      (actualFreshMean_norm_eq_lowerHeteroMean P S dimension ω).symm
  exact h.trans_eq
    (congrArg (fun z : ℝ => Real.sqrt 3 ^ freshCount P S * z) hMean)


end GraphMatrixReplica.Model.C2Actual
