import GraphMatrix.IsolatedAmplitudeFactorization

/-! # Formula (21) after exact isolated-role marginalization

The ambient role type for the core matrix is the subtype of non-isolated
roles.  Intermediate row and column role sets are transported to that
subtype, where they cover the whole ambient type.  This makes the covered
core a genuine nearly-combinatorial flattening and permits an unconditional
application of the Schur/formula-(21) support estimate.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The role type remaining after isolated middle coordinates are removed. -/
abbrev PaperCoveredRole (G : PaperShape) :=
  {v : Fin G.roles // v ∈ coveredRoles G.isolatedMiddleRoles}

namespace PartiteShape.IntermediateFlatteningRoleSides

variable {G : PaperShape}
    {certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate}

/-- Intermediate row roles contain no isolated middle role. -/
theorem rowRoles_subset_coveredRoles
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    D.rowRoles ⊆ coveredRoles G.isolatedMiddleRoles := by
  classical
  intro v hv
  apply Finset.mem_sdiff.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hIso
  have hIsolated := (G.mem_isolatedMiddleRoles_iff v).1 hIso
  simp only [rowRoles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with hLeft | ⟨e, _he, _hSide, hIncident⟩
  · exact hIsolated.1 hLeft
  · rcases hIncident with hSource | hTarget
    · exact (hIsolated.2.2 e).1 hSource
    · exact (hIsolated.2.2 e).2 hTarget

/-- Intermediate column roles contain no isolated middle role. -/
theorem colRoles_subset_coveredRoles
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    D.colRoles ⊆ coveredRoles G.isolatedMiddleRoles := by
  classical
  intro v hv
  apply Finset.mem_sdiff.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hIso
  have hIsolated := (G.mem_isolatedMiddleRoles_iff v).1 hIso
  simp only [colRoles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with hRight | ⟨e, _he, _hSide, hIncident⟩
  · exact hIsolated.2.1 hRight
  · rcases hIncident with hSource | hTarget
    · exact (hIsolated.2.2 e).1 hSource
    · exact (hIsolated.2.2 e).2 hTarget

/-- Inclusion of a row role into the covered-role subtype. -/
def rowRoleCoveredEmbedding
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    ({v : Fin G.roles // v ∈ D.rowRoles}) ↪ PaperCoveredRole G where
  toFun v := ⟨v.1, D.rowRoles_subset_coveredRoles v.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : PaperCoveredRole G => z.1) h

/-- Inclusion of a column role into the covered-role subtype. -/
def colRoleCoveredEmbedding
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    ({v : Fin G.roles // v ∈ D.colRoles}) ↪ PaperCoveredRole G where
  toFun v := ⟨v.1, D.colRoles_subset_coveredRoles v.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : PaperCoveredRole G => z.1) h

/-- Row roles transported to the covered-role ambient type. -/
def coveredRowRoles
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) : Finset (PaperCoveredRole G) :=
  D.rowRoles.attach.map D.rowRoleCoveredEmbedding

/-- Column roles transported to the covered-role ambient type. -/
def coveredColRoles
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) : Finset (PaperCoveredRole G) :=
  D.colRoles.attach.map D.colRoleCoveredEmbedding

@[simp] theorem card_coveredRowRoles
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    D.coveredRowRoles.card = D.rowRoles.card := by
  calc
    D.coveredRowRoles.card = D.rowRoles.attach.card :=
      Finset.card_map D.rowRoleCoveredEmbedding
    _ = D.rowRoles.card := Finset.card_attach

@[simp] theorem card_coveredColRoles
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    D.coveredColRoles.card = D.colRoles.card := by
  calc
    D.coveredColRoles.card = D.colRoles.attach.card :=
      Finset.card_map D.colRoleCoveredEmbedding
    _ = D.colRoles.card := Finset.card_attach

/-- After deleting the isolated roles, intermediate row and column sides
cover the entire remaining ambient role type. -/
theorem coveredRowRoles_union_coveredColRoles_eq_univ
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    D.coveredRowRoles ∪ D.coveredColRoles = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  have hUnion : v.1 ∈ D.rowRoles ∪ D.colRoles :=
    D.univ_sdiff_isolatedMiddleRoles_subset_rowRoles_union_colRoles v.2
  rcases Finset.mem_union.mp hUnion with hRow | hCol
  · apply Finset.mem_union_left
    apply Finset.mem_map.mpr
    exact ⟨⟨v.1, hRow⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  · apply Finset.mem_union_right
    apply Finset.mem_map.mpr
    exact ⟨⟨v.1, hCol⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- The covered-role ambient cardinality is the total role count minus the
isolated-middle count. -/
theorem card_paperCoveredRole (G : PaperShape) :
    Fintype.card (PaperCoveredRole G) =
      G.roles - G.isolatedMiddleRoles.card := by
  rw [Fintype.card_coe]
  simpa [coveredRoles] using
    (Finset.card_sdiff_of_subset
      (Finset.subset_univ G.isolatedMiddleRoles))

/-- The covered complement exponent plus the two powers paid by squaring
the isolated scalar is exactly the original intermediate exponent. -/
theorem coveredComplementExponent_add_twice_isolated
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides
      certificate.paths) :
    flatteningComplementExponent D.coveredRowRoles D.coveredColRoles +
        2 * G.isolatedMiddleRoles.card =
      D.exponentNumerator := by
  change flatteningComplementExponent D.coveredRowRoles D.coveredColRoles +
      2 * G.isolatedMiddleRoles.card =
    2 * G.roles - (D.rowRoles.card + D.colRoles.card)
  have hRow : D.rowRoles.card ≤ G.roles := by
    have h := Finset.card_le_card (Finset.subset_univ D.rowRoles)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have hRoles : G.toPartiteShape.roles = G.roles :=
      G.toPartiteShape_roles
    omega
  have hCol : D.colRoles.card ≤ G.roles := by
    have h := Finset.card_le_card (Finset.subset_univ D.colRoles)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have hRoles : G.toPartiteShape.roles = G.roles :=
      G.toPartiteShape_roles
    omega
  have hIso : G.isolatedMiddleRoles.card ≤ G.roles := by
    simpa using Finset.card_le_card
      (Finset.subset_univ G.isolatedMiddleRoles)
  have hRowCovered :
      D.rowRoles.card ≤ G.roles - G.isolatedMiddleRoles.card := by
    rw [← D.card_coveredRowRoles, ← card_paperCoveredRole G]
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ D.coveredRowRoles)
  have hColCovered :
      D.colRoles.card ≤ G.roles - G.isolatedMiddleRoles.card := by
    rw [← D.card_coveredColRoles, ← card_paperCoveredRole G]
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ D.coveredColRoles)
  unfold flatteningComplementExponent
  rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ D.coveredRowRoles),
    Finset.card_sdiff_of_subset
      (Finset.subset_univ D.coveredColRoles)]
  simp only [Finset.card_univ, card_paperCoveredRole,
    card_coveredRowRoles, card_coveredColRoles]
  omega

end PartiteShape.IntermediateFlatteningRoleSides

/-! ## The covered nearly-combinatorial core -/

/-- The covered shared-noise product still has absolute value one. -/
theorem abs_paperCoveredNoiseProduct_eq_one
    (G : PaperShape) {n : ℕ} (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    |paperCoveredNoiseProduct G w covered| = 1 := by
  classical
  rw [paperCoveredNoiseProduct, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro e _
  unfold paperEdgeSign
  split <;> norm_num

/-- The covered injective/oriented core retains the unit entry bound. -/
theorem abs_paperCoveredInjectiveOrientedCoreAmplitude_le_one
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n)
    (covered : PaperVisibleTuple n
      (coveredRoles G.isolatedMiddleRoles)) :
    |paperCoveredInjectiveOrientedCoreAmplitude
        G n orientation w covered| ≤ 1 := by
  classical
  unfold paperCoveredInjectiveOrientedCoreAmplitude
    paperCoveredOrientedCoreAmplitude
  by_cases hInjective : Function.Injective covered <;>
    by_cases hOrientation :
      paperCoveredOrientationCompatible G orientation covered <;>
    simp [hInjective, hOrientation, abs_paperCoveredNoiseProduct_eq_one]

/-- The faithful nearly-combinatorial data of the covered intermediate
flattening. -/
def paperIntermediateCoveredCoreData
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    PaperNearlyCombinatorialFlatteningData
      (PaperCoveredRole G) n D.coveredRowRoles D.coveredColRoles where
  weight := paperCoveredInjectiveOrientedCoreAmplitude
    G n orientation w
  weight_abs_le_one :=
    abs_paperCoveredInjectiveOrientedCoreAmplitude_le_one
      G n orientation w
  active_jointly_injective := by
    intro a b _ _ hRow hCol
    apply paperAssignmentRestriction_pair_injective_of_union_eq_univ
      D.coveredRowRoles D.coveredColRoles
        D.coveredRowRoles_union_coveredColRoles_eq_univ
    exact Prod.ext hRow hCol

/-- The matrix obtained from the full oriented assignment sum after its row
and column maps have been transported to covered-role coordinates. -/
def paperIntermediateMarginalizedOrientedMatrix
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    Matrix (PaperVisibleTuple n D.coveredRowRoles)
      (PaperVisibleTuple n D.coveredColRoles) ℝ :=
  paperOrientedMatrixThroughCoveredCoordinates G n orientation w
    (paperAssignmentRestriction D.coveredRowRoles)
    (paperAssignmentRestriction D.coveredColRoles)

/-- Exact matrix factorization into the isolated falling-factorial scalar
and the covered nearly-combinatorial core matrix. -/
theorem paperIntermediateMarginalizedOrientedMatrix_eq_smul_core
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w =
      (((n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
          G.isolatedMiddleRoles.card : ℕ) : ℝ) •
        (paperIntermediateCoveredCoreData
          G certificate D n orientation w).matrix := by
  classical
  rw [paperIntermediateMarginalizedOrientedMatrix,
    paperOrientedMatrixThroughCoveredCoordinates_eq_smul]
  congr 1
  ext row col
  simp only [paperCoveredInjectiveOrientedCoreMatrix,
    PaperNearlyCombinatorialFlatteningData.matrix,
    paperIntermediateCoveredCoreData]
  apply Fintype.sum_equiv (Equiv.refl _)
  intro covered
  by_cases h :
      paperAssignmentRestriction D.coveredRowRoles covered = row ∧
        paperAssignmentRestriction D.coveredColRoles covered = col
  · simp [h]
  · simp [h]

/-- Formula (21) applies unconditionally to the covered core. -/
theorem paperIntermediateCoveredCore_formula21_squaredNorm_le
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖(paperIntermediateCoveredCoreData
        G certificate D n orientation w).matrix‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent
        D.coveredRowRoles D.coveredColRoles := by
  classical
  exact (paperIntermediateCoveredCoreData
    G certificate D n orientation w).formula21_squaredNorm_le

/-- The exact isolated extension scalar is bounded by the crude
`n ^ |W_iso|` factor used in the final exponent. -/
theorem isolatedExtensionDescFactorial_le_pow
    (G : PaperShape) (n : ℕ) :
    (n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
        G.isolatedMiddleRoles.card ≤
      n ^ G.isolatedMiddleRoles.card := by
  calc
    (n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
        G.isolatedMiddleRoles.card ≤
        (n - (coveredRoles G.isolatedMiddleRoles).card) ^
          G.isolatedMiddleRoles.card :=
      Nat.descFactorial_le_pow _ _
    _ ≤ n ^ G.isolatedMiddleRoles.card :=
      Nat.pow_le_pow_left (Nat.sub_le _ _) _

/-- Squaring the isolated scalar costs two isolated-role powers on top of
the covered-core complement exponent. -/
theorem paperIntermediateMarginalizedOriented_squaredNorm_le_coreExponent
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w‖ ^ 2 ≤
      (n : ℝ) ^
        (flatteningComplementExponent
            D.coveredRowRoles D.coveredColRoles +
          2 * G.isolatedMiddleRoles.card) := by
  classical
  let scalarNat :=
    (n - (coveredRoles G.isolatedMiddleRoles).card).descFactorial
      G.isolatedMiddleRoles.card
  let coreMatrix :=
    (paperIntermediateCoveredCoreData
      G certificate D n orientation w).matrix
  have hScalarNat : scalarNat ≤ n ^ G.isolatedMiddleRoles.card :=
    isolatedExtensionDescFactorial_le_pow G n
  have hScalar : (scalarNat : ℝ) ≤
      (n : ℝ) ^ G.isolatedMiddleRoles.card := by
    exact_mod_cast hScalarNat
  have hScalarNonneg : 0 ≤ (scalarNat : ℝ) := by positivity
  have hPowNonneg :
      0 ≤ (n : ℝ) ^ G.isolatedMiddleRoles.card := by positivity
  have hScalarSq : (scalarNat : ℝ) ^ 2 ≤
      ((n : ℝ) ^ G.isolatedMiddleRoles.card) ^ 2 := by
    nlinarith
  have hCore : ‖coreMatrix‖ ^ 2 ≤
      (n : ℝ) ^ flatteningComplementExponent
        D.coveredRowRoles D.coveredColRoles :=
    paperIntermediateCoveredCore_formula21_squaredNorm_le
      G certificate D n orientation w
  calc
    ‖paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w‖ ^ 2 =
        (scalarNat : ℝ) ^ 2 * ‖coreMatrix‖ ^ 2 := by
      rw [paperIntermediateMarginalizedOrientedMatrix_eq_smul_core]
      simp only [scalarNat, coreMatrix, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hScalarNonneg, mul_pow]
    _ ≤ ((n : ℝ) ^ G.isolatedMiddleRoles.card) ^ 2 *
          ((n : ℝ) ^ flatteningComplementExponent
            D.coveredRowRoles D.coveredColRoles) := by
      exact mul_le_mul hScalarSq hCore (sq_nonneg _) (by positivity)
    _ = (n : ℝ) ^
          (flatteningComplementExponent
              D.coveredRowRoles D.coveredColRoles +
            2 * G.isolatedMiddleRoles.card) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

/-- General-`W_iso` concrete formula-(21) endpoint.  The raw formula-(21)
estimate is discharged on the covered core rather than assumed. -/
theorem paperIntermediateMarginalizedOriented_squaredNorm_le_minSeparatorPower
    (G : PaperShape)
    (certificate :
      G.toPartiteShape.BoundaryCleanRightLeftMengerCertificate)
    (D : G.toPartiteShape.IntermediateFlatteningRoleSides certificate.paths)
    (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) (w : PaperNoise n) :
    ‖paperIntermediateMarginalizedOrientedMatrix
        G certificate D n orientation w‖ ^ 2 ≤
      (n : ℝ) ^
        (G.roles - certificate.cut.card +
          G.isolatedMiddleRoles.card) := by
  refine (paperIntermediateMarginalizedOriented_squaredNorm_le_coreExponent
    G certificate D n orientation w).trans ?_
  apply pow_le_pow_right₀
  · exact_mod_cast hn
  · rw [D.coveredComplementExponent_add_twice_isolated]
    have hBound :=
      D.exponentNumerator_le_roles_sub_cut_add_isolated certificate
    simpa [G.isolatedMiddleRoles_eq_toPartiteShape] using hBound


end GraphMatrixReplica
