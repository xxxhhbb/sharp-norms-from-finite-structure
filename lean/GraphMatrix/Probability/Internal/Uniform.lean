import GraphMatrix.Probability.Internal.GoodEvents

/-!
# Constants uniform over every local choice in a fixed finite paper graph

This is a family of individual probability bounds with shared constants.
It is NOT a simultaneous-good-event statement across different trials.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

/-- All legitimate local choices, without any moment or probability fields. -/
abbrev ActiveChoice (P : PaperShape) :=
  Σ cut : Finset (Fin P.roles),
    Σ c : {c : P.toPartiteShape.C079CutComponent cut // c.IsActive},
      {z0 : Fin P.roles // z0 ∈ p1BoundaryRoles P cut c.1}

noncomputable instance activeChoiceFintype (P : PaperShape) : Fintype (ActiveChoice P) :=
  by
    classical
    letI (cut : Finset (Fin P.roles)) :
        Fintype {c : P.toPartiteShape.C079CutComponent cut // c.IsActive} := by
      infer_instance
    letI (cut : Finset (Fin P.roles))
        (c : {c : P.toPartiteShape.C079CutComponent cut // c.IsActive}) :
        Fintype {z0 : Fin P.roles // z0 ∈ p1BoundaryRoles P cut c.1} := by
      infer_instance
    exact Sigma.instFintype

/-- A positive common lower bound, valid even for an empty family. -/
def commonLower {I : Type} [Fintype I] (p : I → ℝ) : ℝ :=
  1 / (1 + ∑ i, (p i)⁻¹)

def commonUpper {I : Type} [Fintype I] (C : I → ℝ) : ℝ := 1 + ∑ i, C i

def commonCutoff {I : Type} [Fintype I] (N : I → ℕ) : ℕ := 1 + ∑ i, N i

theorem commonLower_pos {I : Type} [Fintype I]
    (p : I → ℝ) (hp : ∀ i, 0 < p i) : 0 < commonLower p := by
  have hS : 0 ≤ ∑ i, (p i)⁻¹ :=
    Finset.sum_nonneg fun i _ => (inv_pos.mpr (hp i)).le
  unfold commonLower
  positivity

theorem commonLower_le {I : Type} [Fintype I]
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (i : I) : commonLower p ≤ p i := by
  have hS : 0 ≤ ∑ j, (p j)⁻¹ :=
    Finset.sum_nonneg fun j _ => (inv_pos.mpr (hp j)).le
  have hi : (p i)⁻¹ ≤ ∑ j, (p j)⁻¹ :=
    Finset.single_le_sum (fun j _ => (inv_pos.mpr (hp j)).le) (Finset.mem_univ i)
  have hMul := mul_le_mul_of_nonneg_left hi (hp i).le
  rw [mul_inv_cancel₀ (hp i).ne'] at hMul
  unfold commonLower
  apply (div_le_iff₀ (by positivity : 0 < 1 + ∑ j, (p j)⁻¹)).mpr
  nlinarith [hp i]

theorem commonUpper_pos {I : Type} [Fintype I]
    (C : I → ℝ) (hC : ∀ i, 0 < C i) : 0 < commonUpper C := by
  have hS : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  unfold commonUpper
  linarith

theorem le_commonUpper {I : Type} [Fintype I]
    (C : I → ℝ) (hC : ∀ i, 0 < C i) (i : I) : C i ≤ commonUpper C := by
  have hi : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  unfold commonUpper
  linarith

theorem commonCutoff_pos {I : Type} [Fintype I] (N : I → ℕ) : 1 ≤ commonCutoff N := by
  unfold commonCutoff
  omega

theorem le_commonCutoff {I : Type} [Fintype I] (N : I → ℕ) (i : I) : N i ≤ commonCutoff N := by
  have hi : N i ≤ ∑ j, N j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold commonCutoff
  omega

/-- Strong graph-only uniformity: the graph, a and b are fixed before ALL
cut/component/distinguished-role choices, dimensions, n and complete samples.
The proof chooses witnesses from the actual proved local theorem; it does not
assume a family of target probability estimates. -/
theorem exists_uniform_graph_good_events
    (P : PaperShape) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ p_int p_ext cQ CQ cS CS : ℝ, ∃ n0 : ℕ,
      0 < p_int ∧ 0 < p_ext ∧ 0 < cQ ∧ 0 < CQ ∧ 0 < cS ∧ 0 < CS ∧ 1 ≤ n0 ∧
      ∀ (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut),
        c.IsActive → ∀ (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
          (dimension : Fin P.roles → ℕ) (n : ℕ), n0 ≤ n →
        Balanced P dimension cut c a b n →
        (p_int ≤ finiteUniformProbability (InternalGood P dimension cut c z0 hz0 n)) ∧
        (∀ eps : P1InternalSample P dimension cut c,
          InternalGood P dimension cut c z0 hz0 n eps →
            cQ * (n : ℝ) ^ roleCount P cut c ≤ p1Q P dimension cut c eps ∧
            p1Q P dimension cut c eps ≤ CQ * (n : ℝ) ^ roleCount P cut c ∧
            ∀ j : Fin (dimension z0), p1R P dimension cut c z0 hz0 eps j ≤
              (n : ℝ) ^ ((roleCount P cut c : ℝ) - (3 : ℝ) / 4)) ∧
        (∀ eps : P1InternalSample P dimension cut c,
          InternalGood P dimension cut c z0 hz0 n eps →
            p_ext ≤ finiteUniformProbability (SecondGood P dimension cut c z0 hz0 n eps)) ∧
        (∀ (eps : P1InternalSample P dimension cut c) (eta : P1SecondSample P dimension cut c z0),
          SecondGood P dimension cut c z0 hz0 n eps eta →
            cS * (n : ℝ) ^ roleCount P cut c ≤ p1SigmaSq P dimension cut c z0 hz0 eps eta ∧
            p1SigmaSq P dimension cut c z0 hz0 eps eta ≤ CS * (n : ℝ) ^ roleCount P cut c ∧
            ∀ j : Fin (dimension z0), |p1Z P dimension cut c z0 hz0 eps eta j| ≤
              (n : ℝ) ^ ((roleCount P cut c : ℝ) / 2 - (1 : ℝ) / 4)) := by
  classical
  have hExists := fun i : ActiveChoice P =>
    exists_two_layer_good_events P i.1 i.2.1.1 i.2.1.2 i.2.2.1 i.2.2.2 a b ha hab
  choose pi pe lQ uQ lS uS N hLoc using hExists
  have hpi : ∀ i, 0 < pi i := fun i => (hLoc i).1
  have hpe : ∀ i, 0 < pe i := fun i => (hLoc i).2.1
  have hlQ : ∀ i, 0 < lQ i := fun i => (hLoc i).2.2.1
  have huQ : ∀ i, 0 < uQ i := fun i => (hLoc i).2.2.2.1
  have hlS : ∀ i, 0 < lS i := fun i => (hLoc i).2.2.2.2.1
  have huS : ∀ i, 0 < uS i := fun i => (hLoc i).2.2.2.2.2.1
  refine ⟨commonLower pi, commonLower pe, commonLower lQ, commonUpper uQ,
    commonLower lS, commonUpper uS, commonCutoff N,
    commonLower_pos pi hpi, commonLower_pos pe hpe, commonLower_pos lQ hlQ,
    commonUpper_pos uQ huQ, commonLower_pos lS hlS, commonUpper_pos uS huS,
    commonCutoff_pos N, ?_⟩
  intro cut c hActive z0 hz0 dimension n hn hsize
  let i : ActiveChoice P := ⟨cut, ⟨c, hActive⟩, ⟨z0, hz0⟩⟩
  have hnLocal : N i ≤ n := (le_commonCutoff N i).trans hn
  have H := (hLoc i).2.2.2.2.2.2.2 dimension n hnLocal hsize
  refine ⟨(commonLower_le pi hpi i).trans H.1, ?_, ?_, ?_⟩
  · intro eps hgood
    obtain ⟨hL, hU, hR⟩ := H.2.1 eps hgood
    refine ⟨?_, ?_, hR⟩
    · exact (mul_le_mul_of_nonneg_right (commonLower_le lQ hlQ i)
        (by positivity)).trans hL
    · exact hU.trans (mul_le_mul_of_nonneg_right (le_commonUpper uQ huQ i)
        (by positivity))
  · intro eps hgood
    exact (commonLower_le pe hpe i).trans (H.2.2.1 eps hgood)
  · intro eps eta hgood
    obtain ⟨hL, hU, hZ⟩ := H.2.2.2 eps eta hgood
    refine ⟨?_, ?_, hZ⟩
    · exact (mul_le_mul_of_nonneg_right (commonLower_le lS hlS i)
        (by positivity)).trans hL
    · exact hU.trans (mul_le_mul_of_nonneg_right (le_commonUpper uS huS i)
        (by positivity))

end GraphMatrixReplica.P1AD
