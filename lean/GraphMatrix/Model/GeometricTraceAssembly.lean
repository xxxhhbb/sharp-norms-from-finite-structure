import GraphMatrix.Counting.PartiteRealTransfer

/-! # equation `geometric-trace` for the typed sign core

The manuscript obtains its core upper bound from an exact positive
replica-state expansion and an all-defect count.  It does not invoke
noncommutative Khintchine.  This file assembles those two already-defined
interfaces for the fully-partite finite sign matrix.  The all-defect
cardinality estimate remains an explicit hypothesis; no estimate for the
globally-injective, shared-edge paper matrix is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Exact real-valued typed-core trace expansion from R16's
`lem:exact-trace`, with Lean's order `p + 1`. -/
theorem paperR16_partiteMeanGramTrace_eq_statePolynomial
    (G : PartiteShape) (p : ℕ)
    (dimension : Fin G.roles → ℕ) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^
            (p + 1))) =
      ∑ T : AdmissiblePartitionState G p,
        (T.toReplicaState.labelingWeight dimension : ℝ) := by
  rw [paperMean_c079PartiteBoundaryMatrixReal_gramTracePow_eq_castAverage]
  rw [partiteBoundaryMatrixGramTracePowAverage_eq_statePolynomial]
  push_cast
  rfl

/-- Finite, unnormalized form of equation `geometric-trace`.
The manuscript's coefficient bound is visible as `hCount` and is not
conjured from the formal defect stratification. -/
theorem paperR16_partiteMeanGramTrace_le_finiteGeometric
    (G : PartiteShape) (p s a K C n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        C ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1) + K * delta.1)) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^
            (p + 1))) ≤
      (((C ^ (2 * (p + 1)) * (p + 1) ^ (a * (p + 1))) *
        ∑ delta : Fin (c079BlockTarget G p s + 1),
          (p + 1) ^ (K * delta.1) *
            n ^ (c079BlockTarget G p s - delta.1) : ℕ) : ℝ) := by
  rw [paperR16_partiteMeanGramTrace_eq_statePolynomial]
  have hNat :
      (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) ≤
      (C ^ (2 * (p + 1)) * (p + 1) ^ (a * (p + 1))) *
        ∑ delta : Fin (c079BlockTarget G p s + 1),
          (p + 1) ^ (K * delta.1) *
            n ^ (c079BlockTarget G p s - delta.1) := by
    rw [c079_statePolynomial_eq_sum_defectWeightSum G p s dimension hBlocks]
    calc
      (∑ delta : Fin (c079BlockTarget G p s + 1),
          c079DefectWeightSum G p s dimension delta) ≤
          ∑ delta : Fin (c079BlockTarget G p s + 1),
            c079DefectCoefficient G p s delta *
              n ^ (c079BlockTarget G p s - delta.1) := by
        exact Finset.sum_le_sum fun delta _ =>
          c079_defectWeightSum_le_coefficient_mul_degreePower
            G p s n dimension hDimension delta
      _ ≤ ∑ delta : Fin (c079BlockTarget G p s + 1),
            (C ^ (2 * (p + 1)) * (p + 1) ^ (a * (p + 1))) *
              ((p + 1) ^ (K * delta.1) *
                n ^ (c079BlockTarget G p s - delta.1)) := by
        apply Finset.sum_le_sum
        intro delta _
        calc
          c079DefectCoefficient G p s delta *
              n ^ (c079BlockTarget G p s - delta.1) ≤
            (C ^ (2 * (p + 1)) *
              (p + 1) ^ (a * (p + 1) + K * delta.1)) *
                n ^ (c079BlockTarget G p s - delta.1) :=
                  Nat.mul_le_mul_right _ (hCount delta)
          _ = (C ^ (2 * (p + 1)) * (p + 1) ^ (a * (p + 1))) *
                ((p + 1) ^ (K * delta.1) *
                  n ^ (c079BlockTarget G p s - delta.1)) := by
            rw [pow_add]
            ring
      _ = (C ^ (2 * (p + 1)) * (p + 1) ^ (a * (p + 1))) *
            ∑ delta : Fin (c079BlockTarget G p s + 1),
              (p + 1) ^ (K * delta.1) *
                n ^ (c079BlockTarget G p s - delta.1) := by
        rw [Finset.mul_sum]
  exact_mod_cast hNat

/-- R16's explicit `K_r` and `C_r` specialization of the finite geometric
trace estimate.  The all-defect bound is still exactly the visible `hCount`
premise, not a derived consequence of defect stratification. -/
theorem paperR16_partiteMeanGramTrace_le_explicitFiniteGeometric
    (G : PartiteShape) (p s a n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta.1)) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^
            (p + 1))) ≤
      (((c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1))) *
        ∑ delta : Fin (c079BlockTarget G p s + 1),
          (p + 1) ^ (c079K G.roles * delta.1) *
            n ^ (c079BlockTarget G p s - delta.1) : ℕ) : ℝ) := by
  exact paperR16_partiteMeanGramTrace_le_finiteGeometric
    G p s a (c079K G.roles) (c079C G.roles) n dimension
    hDimension (fun T => c079_blockTarget_cap_of_disjointPaths
      hCovered family T) hCount

/-- A finite weighted geometric series has at most twice its zeroth-order
scale when its successive ratio is at most one half. -/
theorem paperR16_finiteWeightedGeometric_le_two
    (b n target : ℕ) (hRatio : 2 * b ≤ n) :
    (∑ delta : Fin (target + 1),
      b ^ delta.1 * n ^ (target - delta.1)) ≤
      2 * n ^ target := by
  induction target with
  | zero => simp
  | succ target ih =>
      have hRec :
          (∑ delta : Fin (target + 1 + 1),
            b ^ delta.1 * n ^ (target + 1 - delta.1)) =
            n ^ (target + 1) +
              b * (∑ delta : Fin (target + 1),
                b ^ delta.1 * n ^ (target - delta.1)) := by
        calc
          (∑ delta : Fin (target + 1 + 1),
              b ^ delta.1 * n ^ (target + 1 - delta.1)) =
              n ^ (target + 1) +
                ∑ delta : Fin (target + 1),
                  b ^ (delta.1 + 1) *
                    n ^ (target + 1 - (delta.1 + 1)) := by
            rw [Fin.sum_univ_succ]
            simp
          _ = n ^ (target + 1) +
                b * (∑ delta : Fin (target + 1),
                  b ^ delta.1 * n ^ (target - delta.1)) := by
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro delta _
            have hSub : target + 1 - (delta.1 + 1) =
                target - delta.1 := by omega
            rw [hSub, pow_succ]
            ring
      rw [hRec]
      calc
        n ^ (target + 1) +
            b * (∑ delta : Fin (target + 1),
              b ^ delta.1 * n ^ (target - delta.1)) ≤
            n ^ (target + 1) + b * (2 * n ^ target) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left b ih) _
        _ = (n + 2 * b) * n ^ target := by
          rw [pow_succ]
          ring
        _ ≤ (n + n) * n ^ target := by
          exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hRatio n)
        _ = 2 * n ^ (target + 1) := by
          rw [pow_succ]
          ring

/-- The `2`-times-leading-scale form of equation `geometric-trace`.
The ratio hypothesis is an explicit finite-size version of the manuscript's
eventual condition `p^K/n ≤ 1/2`. -/
theorem paperR16_partiteMeanGramTrace_le_twiceLeadingScale
    (G : PartiteShape) (p s a n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hRatio : 2 * (p + 1) ^ c079K G.roles ≤ n)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta.1)) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^
            (p + 1))) ≤
      ((2 * c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s : ℕ) : ℝ) := by
  have hFinite := paperR16_partiteMeanGramTrace_le_explicitFiniteGeometric
    G p s a n dimension hDimension hCovered family hCount
  have hSum :
      (∑ delta : Fin (c079BlockTarget G p s + 1),
        (p + 1) ^ (c079K G.roles * delta.1) *
          n ^ (c079BlockTarget G p s - delta.1)) ≤
        2 * n ^ c079BlockTarget G p s := by
    simpa only [pow_mul] using
      paperR16_finiteWeightedGeometric_le_two
        ((p + 1) ^ c079K G.roles) n
        (c079BlockTarget G p s) hRatio
  have hScale := Nat.mul_le_mul_left
    (c079C G.roles ^ (2 * (p + 1)) *
      (p + 1) ^ (a * (p + 1))) hSum
  have hScaleReal :
      (((c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1))) *
        ∑ delta : Fin (c079BlockTarget G p s + 1),
          (p + 1) ^ (c079K G.roles * delta.1) *
            n ^ (c079BlockTarget G p s - delta.1) : ℕ) : ℝ) ≤
      ((2 * c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s : ℕ) : ℝ) := by
    exact_mod_cast (hScale.trans_eq (by ring))
  exact hFinite.trans hScaleReal


end GraphMatrixReplica
