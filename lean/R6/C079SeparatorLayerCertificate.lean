import R6.StateBoundaryPathDefect
import R6.C079IntervalLayerDoubleCount

/-! # C079 horizontal layers hit every boundary path

This module isolates the graph-theoretic half of C079 Lemma 2.  An interval
certificate records only the properties proved from the replica partitions:
left endpoints start at zero, right endpoints finish at `q`, and intervals on
the endpoints of every graph edge intersect.  These facts force every
right-to-left path to meet every horizontal layer `1,...,q`.

Constructing the certificate from actual equality partitions is intentionally
left as a separate obligation; the theorem below does not assume that the
layer is a separator by definition.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A graph path hits a set of roles if at least one of its explicitly stored
vertex occurrences lies in that set. -/
def PartiteShape.EdgePathToLeft.Hits
    {G : PartiteShape} {v : Fin G.roles}
    (A : Finset (Fin G.roles)) : G.EdgePathToLeft v → Prop
  | .finish v _ => v ∈ A
  | .step (v := v) _ _ _ _ tail => v ∈ A ∨ tail.Hits A

theorem PartiteShape.EdgePathToLeft.hits_of_head_mem
    {G : PartiteShape} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (A : Finset (Fin G.roles))
    (hv : v ∈ A) : path.Hits A := by
  cases path with
  | finish => exact hv
  | step => exact Or.inl hv

/-- Abstract interval data sufficient for C079's separator-layer argument. -/
structure C079IntervalCertificate (G : PartiteShape) (q : ℕ) where
  ell : Fin G.roles → ℕ
  upper : Fin G.roles → ℕ
  upper_le : ∀ v, upper v ≤ q
  left_ell_zero : ∀ v, v ∈ G.leftBoundary → ell v = 0
  right_upper_eq : ∀ v, v ∈ G.rightBoundary → upper v = q
  edge_intersects : ∀ (e : Fin G.edges) (v w : Fin G.roles),
    G.EdgeIncident e v → G.EdgeIncident e w →
      ell v ≤ upper w ∧ ell w ≤ upper v

/-- If the current path vertex lies weakly above layer `k`, interval
intersection propagates the path until it either enters the layer or reaches
an impossible left endpoint. -/
theorem C079IntervalCertificate.path_hits_layer_of_above
    {G : PartiteShape} {q k : ℕ} (C : C079IntervalCertificate G q)
    (hk : 1 ≤ k) {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (habove : k ≤ C.ell v) :
    path.Hits (c079IntervalLayer C.ell C.upper k) := by
  induction path with
  | finish v hLeft =>
      have hzero := C.left_ell_zero v hLeft
      simp only [PartiteShape.EdgePathToLeft.Hits]
      exfalso
      omega
  | @step v e w hAtStart hAtEnd tail ih =>
      by_cases hHead : v ∈ c079IntervalLayer C.ell C.upper k
      · exact Or.inl hHead
      · apply Or.inr
        have hCross := C.edge_intersects e v w hAtStart hAtEnd
        have hUpperW : k ≤ C.upper w := habove.trans hCross.1
        by_cases hEllW : C.ell w < k
        · exact tail.hits_of_head_mem _ (by
            simp [c079IntervalLayer, hEllW, hUpperW])
        · exact ih (Nat.le_of_not_gt hEllW)

/-- Every right-to-left path meets every certified horizontal layer. -/
theorem C079IntervalCertificate.rightToLeftPath_hits_layer
    {G : PartiteShape} {q k : ℕ} (C : C079IntervalCertificate G q)
    (hk : k ∈ Finset.Icc 1 q)
    (v : Fin G.roles) (hRight : v ∈ G.rightBoundary)
    (path : G.EdgePathToLeft v) :
    path.Hits (c079IntervalLayer C.ell C.upper k) := by
  have hkBounds : 1 ≤ k ∧ k ≤ q := by simpa using hk
  by_cases hHead : v ∈ c079IntervalLayer C.ell C.upper k
  · exact path.hits_of_head_mem _ hHead
  · have hUpper : k ≤ C.upper v := by
      rw [C.right_upper_eq v hRight]
      exact hkBounds.2
    have hNotBelow : ¬ C.ell v < k := by
      intro hBelow
      apply hHead
      simp [c079IntervalLayer, hBelow, hUpper]
    exact C.path_hits_layer_of_above hkBounds.1 path
      (Nat.le_of_not_gt hNotBelow)

#print axioms PartiteShape.EdgePathToLeft.hits_of_head_mem
#print axioms C079IntervalCertificate.path_hits_layer_of_above
#print axioms C079IntervalCertificate.rightToLeftPath_hits_layer

end GraphMatrixReplica
