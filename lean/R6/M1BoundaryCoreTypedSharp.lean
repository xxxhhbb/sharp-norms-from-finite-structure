import R6.M1TraceScaleBounds
import R6.U3IntegrationAcceptance
import R6.PaperR16UniformTypedInputBridge
import R6.PaperMomentToMean
import R6.FiniteMengerResidualPathProjection
import R6.PaperR16ColorUpperLpAdapter
import R6.PaperRademacherWalshProjection

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica

def rootTypedGraphScale (G : PaperShape) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (((G.roles : ℝ) - G.toPartiteShape.rightLeftSeparatorNumber) / 2) *
    Real.log (n : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2)

def rootTypedCoreConstant (G : PaperShape) : ℝ :=
  max 1 (2 * (c079C G.roles : ℝ) * Real.exp ((G.toPartiteShape.rightLeftSeparatorNumber : ℝ) / 2) *
    (8 : ℝ) ^ ((G.toPartiteShape.c079ActiveMaximum : ℝ) / 2))

theorem rootTypedCoreConstant_pos (G : PaperShape) : 0 < rootTypedCoreConstant G :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem root_typedGraphScale_nonneg (G : PaperShape) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ rootTypedGraphScale G n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  unfold rootTypedGraphScale
  positivity

theorem root_zeroRole_typed_entry (G : PaperShape) (hroles : G.roles = 0)
    (dimension : Fin G.roles → ℕ) (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension) :
    c027PartiteBoundaryMatrixReal G dimension epsilon row col = 1 := by
  classical
  letI : IsEmpty (Fin G.roles) := by rw [hroles]; infer_instance
  letI : IsEmpty (Fin G.toPartiteShape.roles) := inferInstanceAs (IsEmpty (Fin G.roles))
  letI : IsEmpty (Fin G.edges) := ⟨fun e => isEmptyElim (G.source e)⟩
  letI : IsEmpty (Fin G.toPartiteShape.edges) := inferInstanceAs (IsEmpty (Fin G.edges))
  simp [c027PartiteBoundaryMatrixReal, partiteBoundaryMatrix,
    partiteBoundaryEntryCompatible, partiteAssignmentEdgeMonomial]

theorem root_zeroRole_typed_norm (G : PaperShape) (hroles : G.roles = 0)
    (dimension : Fin G.roles → ℕ) (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖ = 1 := by
  classical
  letI : IsEmpty (Fin G.roles) := by rw [hroles]; infer_instance
  letI : IsEmpty (Fin G.toPartiteShape.roles) := inferInstanceAs (IsEmpty (Fin G.roles))
  letI : Unique (PartiteBoundaryRow (G := G.toPartiteShape) dimension) := inferInstance
  letI : Unique (PartiteBoundaryCol (G := G.toPartiteShape) dimension) := inferInstance
  let M := c027PartiteBoundaryMatrixReal G dimension epsilon
  have hLower : 1 ≤ ‖M‖ := by
    let x : EuclideanSpace ℝ (PartiteBoundaryCol (G := G.toPartiteShape) dimension) :=
      EuclideanSpace.single default 1
    let y : EuclideanSpace ℝ (PartiteBoundaryRow (G := G.toPartiteShape) dimension) :=
      (EuclideanSpace.equiv _ ℝ).symm (Matrix.mulVec M x.ofLp)
    have hcoord : ‖y.ofLp default‖ ≤ ‖y‖ := PiLp.norm_apply_le y default
    have hop : ‖y‖ ≤ ‖M‖ * ‖x‖ := Matrix.l2_opNorm_mulVec M x
    have h : |M default default| ≤ ‖M‖ := by
      calc
        |M default default| = ‖y.ofLp default‖ := by simp [x, y, Real.norm_eq_abs]
        _ ≤ ‖y‖ := hcoord
        _ ≤ ‖M‖ * ‖x‖ := hop
        _ = ‖M‖ := by simp [x]
    simpa [M, root_zeroRole_typed_entry G hroles dimension epsilon] using h
  have hSq : ‖M‖ ^ 2 ≤ 1 := by
    have h := matrix_l2_opNorm_sq_le_sum_entry_sq M
    simpa [M, root_zeroRole_typed_entry G hroles dimension epsilon] using h
  exact le_antisymm (by nlinarith [norm_nonneg M]) hLower

theorem root_finiteUniformL2_sq_eq_mean_sq {Ω E : Type} [Fintype Ω] [NormedAddCommGroup E]
    (f : Ω → E) : (paperFiniteUniformLq f 2) ^ 2 = paperMean (fun w => ‖f w‖ ^ 2) := by
  rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ 2 (by norm_num)]
  simp only [Real.rpow_two, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  apply Real.sq_sqrt
  unfold paperMean
  positivity

/-- Sharp typed L2 bound, including zero-role boundary cores. The independently
proved U3 count is an explicit integration input for this assembly helper. -/
theorem root_boundaryCore_typedL2_sharp_of_exactCount (hCount : C079U3.U3ExactStratumAcceptance)
    (G : PaperShape) (hCore : G.toPartiteShape.IsBoundaryCore) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ dimension : Fin G.roles → ℕ, (∀ v, dimension v ≤ n) →
      paperFiniteUniformLq (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
        c027PartiteBoundaryMatrixReal G dimension epsilon) 2 ≤
          rootTypedCoreConstant G * rootTypedGraphScale G n := by
  by_cases hzero : G.roles = 0
  · refine ⟨2, ?_⟩
    intro n hn dimension hDim
    have hs : G.toPartiteShape.rightLeftSeparatorNumber = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [PartiteShape.rightLeftSeparatorNumber, G.toPartiteShape_roles, hzero] using
        Finset.card_le_univ G.toPartiteShape.minimumRightLeftSeparator
    have ha : G.toPartiteShape.c079ActiveMaximum = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [G.toPartiteShape_roles, hzero] using G.toPartiteShape.c079ActiveMaximum_le_roles
    have hL2 : paperFiniteUniformLq (fun epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension =>
        c027PartiteBoundaryMatrixReal G dimension epsilon) 2 = 1 := by
      rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ 2 (by norm_num)]
      simp only [root_zeroRole_typed_norm G hzero dimension, Real.one_rpow, paperMean_const_function]
    rw [hL2]
    have hscale : rootTypedGraphScale G n = 1 := by simp [rootTypedGraphScale, hzero, hs, ha]
    rw [hscale, mul_one]
    exact le_max_left _ _
  · have hr : 0 < G.roles := Nat.pos_of_ne_zero hzero
    let H := G.toPartiteShape
    let s := H.rightLeftSeparatorNumber
    let a := H.c079ActiveMaximum
    let family : H.VertexDisjointRightToLeftPaths s := by
      dsimp [s]
      rw [← H.rightLeftOptima_eq]
      exact H.maximumRightLeftPathPacking
    have hs : s ≤ H.roles := family.pathCount_le_roles
    obtain ⟨N, hN⟩ := paperR16_typedCore_realLpRoot_le_finiteScale_eventually H s a 2 (by norm_num)
    refine ⟨max N 2, ?_⟩
    intro n hn dimension hDim
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnTwo : 2 ≤ n := (le_max_right _ _).trans hn
    have hWindow : (2 : ℝ) ≤ 2 * Real.log (2 * (n : ℝ)) := by
      have hh := one_le_log_two_mul_nat_of_two_le n hnTwo
      linarith
    have hc := hCount H (paperR16ReplicaParameter n 2) (paperR16ReplicaParameter_pos n 2)
      hr hCore H.rightLeftMengerCertificate
    have ht := hN n hnN 2 (by norm_num) hWindow dimension hDim
      (H.roleCovered_of_isBoundaryCore hCore) family hc
    have hL2 : paperFiniteUniformLq (fun epsilon : JointEdgeSignSample (G := H) dimension =>
        c027PartiteBoundaryMatrixReal G dimension epsilon) 2 ≤
        paperR16TypedCoreFiniteLpScale H (paperR16ReplicaParameter n 2) s a n := by
      rw [paperFiniteUniformLq_eq_paperMean_norm_rpow _ 2 (by norm_num)]
      simp_rw [paperR16_c027PartiteReal_eq_c079PartiteReal]
      exact ht
    apply hL2.trans
    have hScale := root_paper_finiteScale_le_original_log_scale H s a n 2 2 hs hnTwo
      (by norm_num) (by norm_num) hWindow
    apply hScale.trans
    change (2 * (c079C G.roles : ℝ) * Real.exp ((s : ℝ) / 2) *
      (2 * (2 + 2)) ^ ((a : ℝ) / 2)) * (n : ℝ) ^ (((G.roles : ℝ) - s) / 2) *
        Real.log (n : ℝ) ^ ((a : ℝ) / 2) ≤ _
    norm_num only [show (2 : ℝ) * (2 + 2) = 8 by norm_num]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (root_typedGraphScale_nonneg G n (by omega))

#print axioms root_zeroRole_typed_norm
#print axioms root_finiteUniformL2_sq_eq_mean_sq
#print axioms root_boundaryCore_typedL2_sharp_of_exactCount
end GraphMatrixReplica
