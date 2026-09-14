import R6.C079PartiteTraceBudget
import R6.PaperGraphMatrixEntryMoments

/-! # Real-cast transfer for the fully-partite C079 trace budget

`C079PartiteTraceBudget` proves its exact matrix-facing estimate over `Rat`.
This module performs only the entrywise cast to `Real`, proves that the cast
commutes with the Gram power and trace, and rewrites the finite rational
average as `paperMean`.  It does not compare the fully-partite matrix with
`paperGraphMatrix`, and the exact C079 counting input remains explicit.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The fully-partite rational boundary matrix cast entry by entry to `Real`.
The matrix indices and edge-sign sample are unchanged. -/
def c079PartiteBoundaryMatrixReal
    (G : PartiteShape) (dimension : Fin G.roles -> Nat)
    (epsilon : JointEdgeSignSample (G := G) dimension) :
    Matrix (PartiteBoundaryRow (G := G) dimension)
      (PartiteBoundaryCol (G := G) dimension) Real :=
  (partiteBoundaryMatrix G dimension epsilon).map (Rat.castHom Real)

@[simp] theorem c079PartiteBoundaryMatrixReal_apply
    (G : PartiteShape) (dimension : Fin G.roles -> Nat)
    (epsilon : JointEdgeSignSample (G := G) dimension)
    (row : PartiteBoundaryRow (G := G) dimension)
    (col : PartiteBoundaryCol (G := G) dimension) :
    c079PartiteBoundaryMatrixReal G dimension epsilon row col =
      ((partiteBoundaryMatrix G dimension epsilon row col : Rat) : Real) := by
  rfl

/-- Entrywise rational casting commutes exactly with every Gram power and its
trace.  No parity or model-transfer statement is involved. -/
theorem c079PartiteBoundaryMatrixReal_gramTracePow_eq_cast
    (G : PartiteShape) (m : Nat) (dimension : Fin G.roles -> Nat)
    (epsilon : JointEdgeSignSample (G := G) dimension) :
    Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^ m) =
      ((Matrix.trace
        ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ m) : Rat) :
        Real) := by
  classical
  let M := partiteBoundaryMatrix G dimension epsilon
  change Matrix.trace
      (((M.map (Rat.castHom Real)) *
        (M.map (Rat.castHom Real)).transpose) ^ m) =
    (Rat.castHom Real) (Matrix.trace ((M * M.transpose) ^ m))
  rw [<- Matrix.transpose_map, <- Matrix.map_mul]
  have hMapPow : forall k : Nat,
      ((M * M.transpose) ^ k).map (Rat.castHom Real) =
        ((M * M.transpose).map (Rat.castHom Real)) ^ k := by
    intro k
    induction k with
    | zero =>
        ext i j
        by_cases hij : i = j <;> simp [hij]
    | succ k ih =>
        rw [pow_succ, pow_succ, Matrix.map_mul, ih]
  rw [<- hMapPow m]
  exact (AddMonoidHom.map_trace (Rat.castHom Real)
    ((M * M.transpose) ^ m)).symm

/-- The `paperMean` of the real-cast Gram trace is exactly the real cast of
the rational sum divided by the sample-space cardinality. -/
theorem paperMean_c079PartiteBoundaryMatrixReal_gramTracePow_eq_castAverage
    (G : PartiteShape) (m : Nat) (dimension : Fin G.roles -> Nat) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^ m)) =
      ((((∑ epsilon : JointEdgeSignSample (G := G) dimension,
          Matrix.trace
            ((partiteBoundaryMatrix G dimension epsilon *
              (partiteBoundaryMatrix G dimension epsilon).transpose) ^ m)) /
        Fintype.card (JointEdgeSignSample (G := G) dimension)) : Rat) : Real) := by
  classical
  unfold paperMean
  rw [show (∑ epsilon : JointEdgeSignSample (G := G) dimension,
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^ m)) =
      ∑ epsilon : JointEdgeSignSample (G := G) dimension,
        ((Matrix.trace
          ((partiteBoundaryMatrix G dimension epsilon *
            (partiteBoundaryMatrix G dimension epsilon).transpose) ^ m) : Rat) :
          Real) by
    apply Finset.sum_congr rfl
    intro epsilon _
    exact c079PartiteBoundaryMatrixReal_gramTracePow_eq_cast
      G m dimension epsilon]
  push_cast
  rw [div_eq_mul_inv]
  ring

/-- Real-valued `paperMean` form of the C079 fully-partite trace budget.  The
exact stratum-count hypothesis `hCount` is deliberately still an argument. -/
theorem paperMean_c079PartiteBoundaryGramTrace_le_explicit
    (G : PartiteShape) (p s a n : Nat)
    (dimension : Fin G.roles -> Nat)
    (hDimension : forall v : Fin G.roles, dimension v <= n)
    (hCovered : forall v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hscale : (p + 1) ^ c079K G.roles <= n)
    (hCount : forall delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta <=
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta.1)) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^
            (p + 1))) <=
      (((c079BlockTarget G p s + 1) *
        (c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s) : Nat) : Real) := by
  rw [paperMean_c079PartiteBoundaryMatrixReal_gramTracePow_eq_castAverage]
  exact_mod_cast
    c079_partiteBoundaryGramTraceAverage_le_explicit
      G p s a n dimension hDimension hCovered family hscale hCount

/-- Dyadic C079 real trace budget with `p = 2^q - 1`.  The explicit
assumption `1 <= q` records the positive dyadic-level regime used downstream;
the exact count hypothesis remains visible at this specialized order. -/
theorem paperMean_c079PartiteBoundaryGramTrace_dyadic_le_explicit
    (G : PartiteShape) (q s a n : Nat) (hq : 1 <= q)
    (dimension : Fin G.roles -> Nat)
    (hDimension : forall v : Fin G.roles, dimension v <= n)
    (hCovered : forall v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hscale : (2 ^ q) ^ c079K G.roles <= n)
    (hCount : forall delta : Fin
        (c079BlockTarget G (2 ^ q - 1) s + 1),
      c079DefectCoefficient G (2 ^ q - 1) s delta <=
        c079C G.roles ^ (2 * 2 ^ q) *
          (2 ^ q) ^ (a * 2 ^ q + c079K G.roles * delta.1)) :
    paperMean (fun epsilon : JointEdgeSignSample (G := G) dimension =>
      Matrix.trace
        ((c079PartiteBoundaryMatrixReal G dimension epsilon *
          (c079PartiteBoundaryMatrixReal G dimension epsilon).transpose) ^
            (2 ^ q))) <=
      (((c079BlockTarget G (2 ^ q - 1) s + 1) *
        (c079C G.roles ^ (2 * 2 ^ q) *
          (2 ^ q) ^ (a * 2 ^ q) *
            n ^ c079BlockTarget G (2 ^ q - 1) s) : Nat) : Real) := by
  have hpow : (2 ^ q - 1) + 1 = 2 ^ q := by
    have hpos : 0 < 2 ^ q := pow_pos (by omega) q
    omega
  have _hqUsed : 0 < q := hq
  simpa only [hpow] using
    (paperMean_c079PartiteBoundaryGramTrace_le_explicit
      G (2 ^ q - 1) s a n dimension hDimension hCovered family
        (by simpa only [hpow] using hscale)
        (by simpa only [hpow] using hCount))

#print axioms c079PartiteBoundaryMatrixReal_apply
#print axioms c079PartiteBoundaryMatrixReal_gramTracePow_eq_cast
#print axioms paperMean_c079PartiteBoundaryMatrixReal_gramTracePow_eq_castAverage
#print axioms paperMean_c079PartiteBoundaryGramTrace_le_explicit
#print axioms paperMean_c079PartiteBoundaryGramTrace_dyadic_le_explicit

end GraphMatrixReplica
