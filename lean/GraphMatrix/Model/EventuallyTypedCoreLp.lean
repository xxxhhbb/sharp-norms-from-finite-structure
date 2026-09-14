import GraphMatrix.Model.GeometricRatioEventually
import GraphMatrix.Model.TypedCoreLpUpperAssembly

/-! # eventual typed-core `L^q` assembly

The exact trace order in `prop:core-upper` is selected from the requested
real exponent `q`.  Lean's replica-state parameter is one less than that
trace order.  This file combines the finite-size typed-core result with the
proved eventual half-ratio window.  The all-defect count remains a visible
per-instance hypothesis, and no transfer to the globally-injective paper
matrix is claimed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Lean's replica parameter corresponding to the integer trace order
selected in R16. -/
def paperR16ReplicaParameter (n : ℕ) (q : ℝ) : ℕ :=
  paperR16RealTraceOrder n q - 1

theorem paperR16ReplicaParameter_add_one (n : ℕ) (q : ℝ) :
    paperR16ReplicaParameter n q + 1 =
      paperR16RealTraceOrder n q := by
  unfold paperR16ReplicaParameter
  have hOrder := paperR16RealTraceOrder_ge_two n q
  omega

theorem paperR16ReplicaParameter_pos (n : ℕ) (q : ℝ) :
    1 ≤ paperR16ReplicaParameter n q := by
  have hOrder := paperR16RealTraceOrder_ge_two n q
  unfold paperR16ReplicaParameter
  omega

/-- The typed-core finite-scale bound on the entire fixed logarithmic
`q` window, once the manuscript's all-defect cardinality estimate is given
for the selected trace order.  The threshold depends only on the fixed
defect exponent (hence `G`) and on `C₀`. -/
theorem paperR16_typedCore_realLpRoot_le_finiteScale_eventually
    (G : PartiteShape) (s a : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ q : ℝ, 2 ≤ q →
        q ≤ C₀ * Real.log (2 * (n : ℝ)) →
      ∀ (dimension : Fin G.roles → ℕ),
        (∀ v : Fin G.roles, dimension v ≤ n) →
        (∀ v : Fin G.roles, G.RoleCovered v) →
        (family : G.VertexDisjointRightToLeftPaths s) →
        (∀ delta : Fin
          (c079BlockTarget G (paperR16ReplicaParameter n q) s + 1),
          c079DefectCoefficient G (paperR16ReplicaParameter n q) s delta ≤
            c079C G.roles ^
              (2 * (paperR16ReplicaParameter n q + 1)) *
              (paperR16ReplicaParameter n q + 1) ^
                (a * (paperR16ReplicaParameter n q + 1) +
                  c079K G.roles * delta.1)) →
        (paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
          ‖c079PartiteBoundaryMatrixReal G dimension epsilon‖ ^ q)) ^ q⁻¹ ≤
          paperR16TypedCoreFiniteLpScale G
            (paperR16ReplicaParameter n q) s a n := by
  obtain ⟨N, hN⟩ :=
    paperR16RealTraceOrder_geometricRatio_eventually
      (c079K G.roles) C₀ hC₀
  refine ⟨N, ?_⟩
  intro n hn q hqTwo hqWindow dimension hDimension hCovered family hCount
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hqTwo
  have hqNonneg : 0 ≤ q := le_trans (by norm_num) hqTwo
  have hRatio :
      2 * (paperR16ReplicaParameter n q + 1) ^ c079K G.roles ≤ n := by
    simpa only [paperR16ReplicaParameter_add_one] using
      hN n hn q hqNonneg hqWindow
  have hqOrder :
      q ≤ ((2 * (paperR16ReplicaParameter n q + 1) : ℕ) : ℝ) := by
    simpa only [paperR16ReplicaParameter_add_one,
      Nat.cast_mul, Nat.cast_ofNat] using
        paperR16RealTraceOrder_covers_q n q
  exact paperR16_typedCore_realLpRoot_le_finiteScale
    G (paperR16ReplicaParameter n q) s a n q dimension
    hDimension hCovered family hqPos hqOrder hRatio hCount


end GraphMatrixReplica
