import R6.PaperTraceCycleIdentity

/-! # Exact arbitrary-order trace moment in the original paper model

This module combines the cyclic finite-matrix reindexing identity with the
shared-unordered-edge expectation formula.  It is the first theorem whose
left-hand side is the actual positive Gram trace moment of the original
globally-injective graph matrix at every order.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Exact finite parity expansion of every positive Gram trace moment. -/
theorem paperGraphMatrixGramTracePowMean (G : PaperShape) (n p : ℕ) :
    paperMean (fun w : PaperNoise n =>
      Matrix.trace ((paperGraphMatrix G n w *
        (paperGraphMatrix G n w).transpose) ^ (p + 1))) =
      ∑ rows : Fin (p + 1) → PaperRow G n,
        ∑ cols : Fin (p + 1) → PaperCol G n,
          ∑ phis : Fin (Fintype.card (Replica (p + 1))) →
              PaperRealization G n,
            if ∀ i, paperEntryCompatible G (phis i)
                (paperTraceIndexedRows G n p rows i)
                (paperTraceIndexedCols G n p cols i) then
              if ∀ e, Even ((paperUnorderedEdgeWord
                  (paperJointEdgeWord G phis)).count e) then
                (1 : ℝ) else 0
            else 0 := by
  simpa only [paperGramTraceWordSum_eq_trace] using
    paperGramTraceWordMean G n p

#print axioms paperGraphMatrixGramTracePowMean

end GraphMatrixReplica
