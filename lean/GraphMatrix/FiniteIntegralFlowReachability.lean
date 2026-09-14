import GraphMatrix.FiniteMengerResidualFlowSkeleton

/-! # Reachability in a finite nonnegative integral flow -/

noncomputable section

open scoped BigOperators

namespace FiniteIntegralFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def Out (flow : V → V → ℕ) (v : V) : ℕ := ∑ w, flow v w

def In (flow : V → V → ℕ) (v : V) : ℕ := ∑ u, flow u v

def PositiveArc (flow : V → V → ℕ) (u v : V) : Prop := 0 < flow u v

def ReachableFrom (flow : V → V → ℕ) (source : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    Relation.ReflTransGen (PositiveArc flow) source v

@[simp] theorem source_mem_reachableFrom
    (flow : V → V → ℕ) (source : V) :
  source ∈ ReachableFrom flow source := by
  simp [ReachableFrom]
  exact .refl

theorem reachableFrom_closed
    (flow : V → V → ℕ) (source u v : V)
    (hu : u ∈ ReachableFrom flow source) (hPos : 0 < flow u v) :
    v ∈ ReachableFrom flow source := by
  simp [ReachableFrom] at hu ⊢
  exact hu.tail hPos

theorem flow_eq_zero_of_reachable_not_reachable
    (flow : V → V → ℕ) (source u v : V)
    (hu : u ∈ ReachableFrom flow source)
    (hv : v ∉ ReachableFrom flow source) :
    flow u v = 0 := by
  by_contra hNe
  have hPos : 0 < flow u v := Nat.pos_of_ne_zero hNe
  exact hv (reachableFrom_closed flow source u v hu hPos)

/-- No positive arc exits a reachability-closed set, so its total outgoing
flow is at most its total incoming flow. -/
theorem sum_out_le_sum_in_reachable
    (flow : V → V → ℕ) (source : V) :
    (ReachableFrom flow source).sum (Out flow) ≤
      (ReachableFrom flow source).sum (In flow) := by
  let R := ReachableFrom flow source
  calc
    R.sum (Out flow) =
        ∑ u ∈ R, ∑ v ∈ R, flow u v := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Out]
      symm
      apply Finset.sum_subset (Finset.subset_univ R)
      intro v _ hv
      exact flow_eq_zero_of_reachable_not_reachable
        flow source u v hu hv
    _ = ∑ v ∈ R, ∑ u ∈ R, flow u v := by
      rw [Finset.sum_comm]
    _ ≤ R.sum (In flow) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [In]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ R)

/-- If source has positive excess and every reachable nonterminal vertex is
balanced, then the designated sink is reachable along positive-flow arcs. -/
theorem sink_reachable_of_source_excess
    (flow : V → V → ℕ) (source sink : V)
    (hExcess : In flow source < Out flow source)
    (hConserve : ∀ v, v ≠ source → v ≠ sink → In flow v = Out flow v) :
    Relation.ReflTransGen (PositiveArc flow) source sink := by
  by_contra hNotReachable
  have hSinkNotMem : sink ∉ ReachableFrom flow source := by
    simpa [ReachableFrom] using hNotReachable
  have hStrict :
      (ReachableFrom flow source).sum (In flow) <
        (ReachableFrom flow source).sum (Out flow) := by
    apply Finset.sum_lt_sum
    · intro v hv
      by_cases hSource : v = source
      · subst v
        exact Nat.le_of_lt hExcess
      · exact (hConserve v hSource (fun h => hSinkNotMem (h ▸ hv))).le
    · exact ⟨source, source_mem_reachableFrom flow source, hExcess⟩
  exact (not_lt_of_ge (sum_out_le_sum_in_reachable flow source)) hStrict

end FiniteIntegralFlow
