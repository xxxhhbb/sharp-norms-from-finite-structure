import GraphMatrix.Main.UniformLowerEndpoint

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open Model Model.C2Actual
attribute [local instance] Classical.propDecidable

/-- Product of the actual component thresholds has exactly the endpoint's
active-role power and genuine active-component logarithmic power. -/
theorem main_active_threshold_product (P : PaperShape) (S : Finset (Fin P.roles))
    (eps : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∏ K : P2a.ActiveComponent P.toPartiteShape S,
      eps * (n : ℝ) ^ ((Fintype.card (P2a.ComponentRole K) : ℝ) / 2) *
        Real.sqrt (Real.log (n : ℝ))) =
      mainLowerWitnessThreshold P S (eps ^ P.toPartiteShape.c079ActiveComponentCount S) n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hpower :
      (∏ K : P2a.ActiveComponent P.toPartiteShape S,
        (n : ℝ) ^ ((Fintype.card (P2a.ComponentRole K) : ℝ) / 2)) =
      (n : ℝ) ^ ((mainC2ActiveRoleCount P S : ℝ) / 2) := by
    rw [← Real.rpow_sum_of_pos hn0]
    congr 1
    simp [mainC2ActiveRoleCount, Nat.cast_sum, Finset.sum_div]
  have hsqrt :
      (Real.sqrt (Real.log (n : ℝ))) ^
          Fintype.card (P2a.ActiveComponent P.toPartiteShape S) =
      (Real.log (n : ℝ)) ^ ((P.toPartiteShape.c079ActiveComponentCount S : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hlog, main_activeComponent_card_eq_count]
    congr 1
    ring
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [hpower, hsqrt, main_activeComponent_card_eq_count]
  rfl

/-- Simultaneous lower bounds must use one and the same actual separator tuple.
Their product gives the actual witness threshold without separate maxima. -/
theorem main_actualWeight_lower_of_component_thresholds
    (P : PaperShape) (S : Finset (Fin P.roles)) (dimension : Fin P.roles → ℕ)
    (eps : ℝ) (heps : 0 ≤ eps) (n : ℕ) (hn : 1 ≤ n)
    (ω : FrozenSample (G := P.toPartiteShape) S dimension)
    (s : CutAssignment (G := P.toPartiteShape) S dimension)
    (hEach : ∀ K : P2a.ActiveComponent P.toPartiteShape S,
      eps * (n : ℝ) ^ ((Fintype.card (P2a.ComponentRole K) : ℝ) / 2) *
        Real.sqrt (Real.log (n : ℝ)) ≤
        |actualComponentContraction (G := P.toPartiteShape) S dimension ω s K|) :
    mainLowerWitnessThreshold P S (eps ^ P.toPartiteShape.c079ActiveComponentCount S) n ≤
      |actualWeight (G := P.toPartiteShape) S dimension ω s| := by
  rw [← main_active_threshold_product P S eps n hn, actualWeight, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro K _
    positivity
  · intro K _
    exact hEach K

/-- A simultaneous component event for a legal actual tuple implies the exact
uniform witness event used by the lower endpoint. -/
theorem main_uniform_witness_of_simultaneous_components
    (P : PaperShape) (S : Finset (Fin P.roles))
    (eps : ℝ) (heps : 0 ≤ eps) (n : ℕ) (hn : 1 ≤ n)
    (ω : FrozenSample (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles))
    (hEvent : ∃ s : CutAssignment (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles),
      ∀ K : P2a.ActiveComponent P.toPartiteShape S,
        eps * (n : ℝ) ^ ((Fintype.card (P2a.ComponentRole K) : ℝ) / 2) *
          Real.sqrt (Real.log (n : ℝ)) ≤
          |actualComponentContraction (G := P.toPartiteShape) S (fun _ => n / P.roles) ω s K|) :
    ∃ s : CutAssignment (G := P.toPartiteShape) S (fun _ : Fin P.roles => n / P.roles),
      mainLowerWitnessThreshold P S (eps ^ P.toPartiteShape.c079ActiveComponentCount S) n ≤
        |actualWeight (G := P.toPartiteShape) S (fun _ => n / P.roles) ω s| := by
  obtain ⟨s, hs⟩ := hEvent
  exact ⟨s, main_actualWeight_lower_of_component_thresholds P S _ eps heps n hn ω s hs⟩

end GraphMatrixReplica
