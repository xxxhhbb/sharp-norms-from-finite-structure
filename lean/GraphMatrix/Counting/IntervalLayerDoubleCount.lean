import Mathlib

/-! # C079 interval-layer double counting

This module formalizes the finite Fubini calculation behind equation (6) of
C079.  Each role `v` carries an integer interval `(ell v, upper v]`; the sum
of the cardinalities of all horizontal layers equals the sum of the interval
widths.  If every layer has size at least `s`, the total layer excess is the
total width minus `s * q`.

The separate graph/partition obligation is to construct these endpoints and
prove that every horizontal layer is a separator.  No such obligation is
assumed or hidden in the first identity.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Roles active in the integer layer `k` of half-open intervals
`(ell v, upper v]`. -/
def c079IntervalLayer {α : Type*} [Fintype α] [DecidableEq α]
    (ell upper : α → ℕ) (k : ℕ) : Finset α :=
  Finset.univ.filter fun v => ell v < k ∧ k ≤ upper v

/-- Indicator-sum presentation of a horizontal layer cardinality. -/
def c079IntervalLayerCard {α : Type*} [Fintype α]
    (ell upper : α → ℕ) (k : ℕ) : ℕ :=
  ∑ v : α, if ell v < k ∧ k ≤ upper v then 1 else 0

theorem c079IntervalLayer_card_eq_layerCard
    {α : Type*} [Fintype α] [DecidableEq α]
    (ell upper : α → ℕ) (k : ℕ) :
    (c079IntervalLayer ell upper k).card =
      c079IntervalLayerCard ell upper k := by
  classical
  simp [c079IntervalLayer, c079IntervalLayerCard]

/-- For one interval contained in `{1,...,q}`, summing its layer indicator
recovers its exact width. -/
theorem c079_sum_one_interval_indicators
    (ell upper q : ℕ) (hupper : upper ≤ q) :
    (∑ k ∈ Finset.Icc 1 q,
      if ell < k ∧ k ≤ upper then 1 else 0) = upper - ell := by
  classical
  calc
    (∑ k ∈ Finset.Icc 1 q,
        if ell < k ∧ k ≤ upper then 1 else 0) =
        ((Finset.Icc 1 q).filter fun k => ell < k ∧ k ≤ upper).card := by
      simp
    _ = (Finset.Ioc ell upper).card := by
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    _ = upper - ell := by simp

/-- Exact C079 horizontal-layer double count. -/
theorem c079_sum_intervalLayerCards_eq_sum_widths
    {α : Type*} [Fintype α] [DecidableEq α]
    (ell upper : α → ℕ) (q : ℕ)
    (hupper : ∀ v : α, upper v ≤ q) :
    (∑ k ∈ Finset.Icc 1 q,
      (c079IntervalLayer ell upper k).card) =
      ∑ v : α, (upper v - ell v) := by
  classical
  simp_rw [c079IntervalLayer_card_eq_layerCard]
  unfold c079IntervalLayerCard
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  exact c079_sum_one_interval_indicators (ell v) (upper v) q (hupper v)

/-- If every horizontal layer has at least `s` roles, the sum of layer
excesses is exactly total interval width minus `s*q`. -/
theorem c079_sum_intervalLayer_excess_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (ell upper : α → ℕ) (q s : ℕ)
    (hupper : ∀ v : α, upper v ≤ q)
    (hLayer : ∀ k ∈ Finset.Icc 1 q,
      s ≤ (c079IntervalLayer ell upper k).card) :
    (∑ k ∈ Finset.Icc 1 q,
      ((c079IntervalLayer ell upper k).card - s)) =
      (∑ v : α, (upper v - ell v)) - s * q := by
  rw [Finset.sum_tsub_distrib (Finset.Icc 1 q) hLayer]
  rw [c079_sum_intervalLayerCards_eq_sum_widths ell upper q hupper]
  simp [Nat.mul_comm]


end GraphMatrixReplica
