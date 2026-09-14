import R6.PaperR16ColorLowerFourier

/-! # Fourier projection of the original global graph-matrix entry

This module moves the exact monomial-wise Walsh identity through the
finite sum over globally injective paper realizations. It does not yet
reindex the surviving realizations by boundary-fixing automorphisms or
identify their sum with the fixed-color typed matrix.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The scalar Fourier coefficient of one original global matrix entry. -/
def paperR16ProjectedGraphEntry
    (G : PaperShape) (n : ℕ)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (w : PaperNoise n) (row : PaperRow G n) (col : PaperCol G n) : ℝ :=
  paperMean (fun α : Fin G.edges → Bool =>
    paperR16FullWalshCharacter α *
      paperGraphMatrix G n (paperR16FlipTaggedNoise tag α w) row col)

/-- The projected original entry is exactly the sum of the surviving
compatible realization monomials. The predicate here is the actual
edge-tag count from the concrete original-model word, not a surrogate. -/
theorem paperR16ProjectedGraphEntry_eq_survivorSum
    (G : PaperShape) (n : ℕ)
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (w : PaperNoise n) (row : PaperRow G n) (col : PaperCol G n) :
    paperR16ProjectedGraphEntry G n tag w row col =
      ∑ phi : PaperRealization G n,
        if paperEntryCompatible G phi row col then
          if ∀ k : Fin G.edges,
              Odd (paperR16TaggedEdgeCount tag
                (paperEmbeddingEdgeWord G phi) k) then
            ((paperEmbeddingEdgeWord G phi).map
              (fun e => paperEdgeSign w e.1 e.2)).prod
          else 0
        else 0 := by
  classical
  unfold paperR16ProjectedGraphEntry
  simp_rw [paperGraphMatrix_as_words]
  have hDistribute : ∀ α : Fin G.edges → Bool,
      paperR16FullWalshCharacter α *
        (∑ phi : PaperRealization G n,
          if paperEntryCompatible G phi row col then
            ((paperEmbeddingEdgeWord G phi).map
              (fun e => paperEdgeSign
                (paperR16FlipTaggedNoise tag α w) e.1 e.2)).prod
          else 0) =
        ∑ phi : PaperRealization G n,
          if paperEntryCompatible G phi row col then
            paperR16FullWalshCharacter α *
              ((paperEmbeddingEdgeWord G phi).map
                (fun e => paperEdgeSign
                  (paperR16FlipTaggedNoise tag α w) e.1 e.2)).prod
          else 0 := by
    intro α
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro phi _
    split_ifs <;> simp
  simp_rw [hDistribute]
  rw [paperMean_sum]
  apply Finset.sum_congr rfl
  intro phi _
  by_cases hCompat : paperEntryCompatible G phi row col
  · simp only [hCompat, if_true]
    have hProjection := paperR16TaggedWord_fullWalshProjection tag
      (paperEmbeddingEdgeWord G phi) w
    by_cases hOdd : ∀ k : Fin G.edges,
        Odd (paperR16TaggedEdgeCount tag (paperEmbeddingEdgeWord G phi) k)
    · simpa only [hOdd, if_true] using hProjection
    · simpa only [hOdd, if_false] using hProjection
  · simp [hCompat, paperMean_zero]

#print axioms paperR16ProjectedGraphEntry_eq_survivorSum

end GraphMatrixReplica
