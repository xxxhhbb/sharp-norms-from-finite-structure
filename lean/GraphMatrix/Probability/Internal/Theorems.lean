import GraphMatrix.Probability.Internal.Uniform

/-!
# Uniform internal and conditional moment bounds

The component bounds are assembled with constants uniform over the finite graph.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.P1AD
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

/-- A, B, C in the supplied actual coefficient model, on all heterogeneous
dimensions. Only the legitimate active-component hypothesis is used. -/
theorem p1_A_B_C
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles)) (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) (z0 : Fin P.roles)
    (hz0 : z0 ∈ p1BoundaryRoles P cut c) :
    (∀ b : P1BoundaryLabel P dimension cut c,
      p1InternalMean P dimension cut c (fun eps => p1Gamma P dimension cut c b eps ^ 2) =
        (p1DimensionProduct P dimension
          (p1ComponentRoles P cut c \ p1BoundaryRoles P cut c) : ℝ)) ∧
    p1InternalMean P dimension cut c (p1Q P dimension cut c) =
      (p1DimensionProduct P dimension (p1ComponentRoles P cut c) : ℝ) ∧
    (∀ j : Fin (dimension z0),
      p1InternalMean P dimension cut c (fun eps => p1R P dimension cut c z0 hz0 eps j) =
        (p1DimensionProduct P dimension (p1ComponentRoles P cut c \ {z0}) : ℝ)) ∧
    (∀ (b : P1BoundaryLabel P dimension cut c) (q : ℕ),
      q ∈ ({2, 8, 16} : Finset ℕ) →
      p1InternalMean P dimension cut c (fun eps => |p1Gamma P dimension cut c b eps| ^ (2 * q)) ≤
        (32 : ℝ) ^ (q * Fintype.card (P1InternalEdge P cut c)) *
          (p1DimensionProduct P dimension
            (p1ComponentRoles P cut c \ p1BoundaryRoles P cut c) : ℝ) ^ q) ∧
    (p1InternalMean P dimension cut c (fun eps => p1Q P dimension cut c eps ^ 2) ≤
      (32 : ℝ) ^ (2 * Fintype.card (P1InternalEdge P cut c)) *
        (p1DimensionProduct P dimension (p1ComponentRoles P cut c) : ℝ) ^ 2) ∧
    (∀ j : Fin (dimension z0),
      p1InternalMean P dimension cut c (fun eps => p1R P dimension cut c z0 hz0 eps j ^ 16) ≤
        (32 : ℝ) ^ (16 * Fintype.card (P1InternalEdge P cut c)) *
          (p1DimensionProduct P dimension (p1ComponentRoles P cut c \ {z0}) : ℝ) ^ 16) ∧
    (∀ eps : P1InternalSample P dimension cut c,
      p1SecondMean P dimension cut c z0 (p1SigmaSq P dimension cut c z0 hz0 eps) =
        p1Q P dimension cut c eps ∧
      p1SecondMean P dimension cut c z0
        (fun eta => p1SigmaSq P dimension cut c z0 hz0 eps eta ^ 2) ≤
        (32 : ℝ) ^ (2 * Fintype.card (P1BoundaryRestRole P cut c z0)) *
          p1Q P dimension cut c eps ^ 2 ∧
      ∀ j : Fin (dimension z0),
        p1SecondMean P dimension cut c z0
          (fun eta => |p1Z P dimension cut c z0 hz0 eps eta j| ^ 32) ≤
          (32 : ℝ) ^ (16 * Fintype.card (P1BoundaryRestRole P cut c z0)) *
            p1R P dimension cut c z0 hz0 eps j ^ 16) := by
  refine ⟨?_, Q_mean P dimension cut c hActive, ?_, ?_,
    Q_moment P dimension cut c hActive 2 (by norm_num), ?_, ?_⟩
  · intro b
    exact gamma_second P dimension cut c hActive b
  · intro j
    exact R_mean P dimension cut c hActive z0 hz0 j
  · intro b q hq
    have hq16 : q ≤ 16 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> norm_num
    exact gamma_even_moment P dimension cut c hActive b q hq16
  · intro j
    exact R_moment P dimension cut c hActive z0 hz0 j 16 (by norm_num)
  · intro eps
    exact second_layer_endpoints P dimension cut c z0 hz0 eps

/-- D, with actual event definitions and all four original conclusions.
Constants and n0 precede the dimensions and the complete internal realization. -/
theorem p1_D
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (hActive : c.IsActive)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ p_int p_ext cQ CQ cS CS : ℝ, ∃ n0 : ℕ,
      0 < p_int ∧ 0 < p_ext ∧ 0 < cQ ∧ 0 < CQ ∧ 0 < cS ∧ 0 < CS ∧ 1 ≤ n0 ∧
      ∀ (dimension : Fin P.roles → ℕ) (n : ℕ), n0 ≤ n →
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
  exact exists_two_layer_good_events P cut c hActive z0 hz0 a b ha hab

/-- Uniform graph-level bound: one set of constants for the whole graph. -/
theorem p1_D_uniform_graph
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
  exact exists_uniform_graph_good_events P a b ha hab


end GraphMatrixReplica.P1AD
