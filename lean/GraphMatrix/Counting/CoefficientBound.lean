import GraphMatrix.Counting.AllDefectStatement
import GraphMatrix.Counting.ActiveComponents

/-! # Exact formal target for R16's uniform all-defect count

Unlike the earlier generic arithmetic interfaces, this statement uses the
actual minimum separator number `s_G` and the actual active-minimum-separator
maximum `a_G^*`.  A boundary core and a Menger certificate keep the intended
graph scope explicit.  The only counting premise is the same bound on every
exact defect fiber; proving that premise remains the substantive C079 task.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Any Menger certificate has the same cut cardinality as the internally
chosen minimum right-left separator. -/
theorem PartiteShape.mengerCut_card_eq_separatorNumber
    (G : PartiteShape) (menger : G.RightLeftMengerCertificate) :
    menger.cut.card = G.rightLeftSeparatorNumber := by
  apply Nat.le_antisymm
  · exact menger.cut_minimum.2 G.minimumRightLeftSeparator
      G.minimumRightLeftSeparator_isMinimum.1
  · exact G.minimumRightLeftSeparator_isMinimum.2 menger.cut
      menger.cut_minimum.1

/-- Theorem `Uniform all-defect count`, for positive role count and every
natural defect.  The exact-stratum inequality is deliberately visible as
`hCount`: neither the scope predicates nor the arithmetic ledgers prove it.
The Lean moment parameter `p` corresponds to the paper trace order `p+1`. -/
theorem c079_r16_count_of_exactStratumCertificate
    (G : PartiteShape) (p : ℕ)
    (_hp : 1 ≤ p) (_hr : 1 ≤ G.roles)
    (_hCore : G.IsBoundaryCore)
    (_menger : G.RightLeftMengerCertificate)
    (hCount : ∀ d : Fin
        (c079BlockTarget G p G.rightLeftSeparatorNumber + 1),
      c079DefectCoefficient G p G.rightLeftSeparatorNumber d ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (G.activeComponentMaximum * (p + 1) + c079K G.roles * d.1)) :
    ∀ delta : ℕ,
      c079DefectCoefficientNat G p G.rightLeftSeparatorNumber delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (G.activeComponentMaximum * (p + 1) + c079K G.roles * delta) := by
  exact c079_allDefect_bound_of_exactFiberCount
    G p G.rightLeftSeparatorNumber G.activeComponentMaximum
      (c079K G.roles) (c079C G.roles) hCount


end GraphMatrixReplica
