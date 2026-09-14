import R6.PaperPartialNCKBranchingLedger
import R6.PaperPartialNCKFinalCompression

/-! # Concrete partially iterated NCK stages with independent branches

The Bool selecting an increasing/decreasing graph-orientation piece and the
Bool selecting the row/column child of an NCK step have different meanings.
Here the former remains an explicit matrix parameter, while a `List Bool`
records the latter.  Thus every fixed graph orientation carries its own full
binary tree of formula-(10) stages.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- The canonical selected edge, packaged with its membership proof. -/
def paperNCKBranchEdge
    (G : PaperShape) (i : ℕ)
    (hi : i < paperUnconditionalOrderingLength G) :
    {e : Fin G.edges //
      e ∈ paperSelectedOrderingEdges G
        G.unconditionalBoundaryCleanMengerCertificate} :=
  ⟨paperUnconditionalOrderingEdgeAt G i hi,
    paperUnconditionalOrderingEdgeAt_mem_selected G i hi⟩

/-- Change one NCK row/column decision without changing the graph
orientation. -/
def paperNCKUpdateSide
    (G : PaperShape) (D : G.UnconditionalIntermediateRoleSides)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (side : Bool) : G.UnconditionalIntermediateRoleSides where
  edgeSide := Function.update D.edgeSide (paperNCKBranchEdge G i hi) side

@[simp] theorem paperNCKUpdateSide_current
    (G : PaperShape) (D : G.UnconditionalIntermediateRoleSides)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (side : Bool) :
    paperSelectedEdgeSide G G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKUpdateSide G D i hi side) (paperNCKBranchEdge G i hi) =
      side := by
  unfold paperSelectedEdgeSide paperNCKUpdateSide
  exact Function.update_self _ _ _

/-- Default future decisions.  They are irrelevant before their edges enter
the ordering prefix. -/
def paperNCKInitialSides (G : PaperShape) :
    G.UnconditionalIntermediateRoleSides where
  edgeSide := fun _ => false

/-- Turn a newest-first branch history into a total assignment of the
canonical selected edges.  At a valid child step, the new head updates the
edge whose ordering index is the old history length. -/
def paperNCKBranchSides (G : PaperShape) :
    List Bool → G.UnconditionalIntermediateRoleSides
  | [] => paperNCKInitialSides G
  | side :: history =>
      if hi : history.length < paperUnconditionalOrderingLength G then
        paperNCKUpdateSide G (paperNCKBranchSides G history)
          history.length hi side
      else
        paperNCKBranchSides G history

theorem paperNCKBranchSides_child
    (G : PaperShape) (history : List Bool)
    (hi : history.length < paperUnconditionalOrderingLength G)
    (side : Bool) :
    paperNCKBranchSides G (paperNCKBranchChild side history) =
      paperNCKUpdateSide G (paperNCKBranchSides G history)
        history.length hi side := by
  simp [paperNCKBranchChild, paperNCKBranchSides, hi]

theorem paperNCKBranchSides_child_current
    (G : PaperShape) (history : List Bool)
    (hi : history.length < paperUnconditionalOrderingLength G)
    (side : Bool) :
    paperSelectedEdgeSide G G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G (paperNCKBranchChild side history))
        (paperNCKBranchEdge G history.length hi) = side := by
  rw [paperNCKBranchSides_child G history hi side]
  exact paperNCKUpdateSide_current G _ _ _ _

/-! ## Prefix bookkeeping under a current-edge update -/

/-- Away from the current edge, updating a side assignment changes no
selected-edge decision.  Comparing underlying edge values avoids any
dependence on the proof used to package membership in the selected set. -/
theorem paperNCKUpdateSide_apply_of_val_ne
    (G : PaperShape) (D : G.UnconditionalIntermediateRoleSides)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (side : Bool)
    (e : {x : Fin G.edges // x ∈ paperSelectedOrderingEdges G
      G.unconditionalBoundaryCleanMengerCertificate})
    (hne : e.1 ≠ paperUnconditionalOrderingEdgeAt G i hi) :
    paperSelectedEdgeSide G G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKUpdateSide G D i hi side) e =
      paperSelectedEdgeSide G G.unconditionalBoundaryCleanMengerCertificate
        D e := by
  unfold paperSelectedEdgeSide paperNCKUpdateSide
  apply Function.update_of_ne
  intro hEq
  exact hne (congrArg Subtype.val hEq)

theorem paperNCKUpdateSide_rowEdges_before
    (G : PaperShape) (D : G.UnconditionalIntermediateRoleSides)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (side : Bool) :
    paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKUpdateSide G D i hi side) i =
      paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate D i := by
  classical
  ext e
  simp only [paperPartialNCKStageRowEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hePrefix, heSide⟩
    refine ⟨hePrefix, ?_⟩
    rcases heSide with ⟨heSelected, hSide⟩
    refine ⟨heSelected, ?_⟩
    have hne : e ≠ paperUnconditionalOrderingEdgeAt G i hi := by
      intro hEq
      subst e
      exact (paperUnconditionalOrderingEdgeAt_not_mem_prefix G i hi) hePrefix
    rw [paperNCKUpdateSide_apply_of_val_ne G D i hi side
      ⟨e, heSelected⟩ hne] at hSide
    exact hSide
  · rintro ⟨hePrefix, heSide⟩
    refine ⟨hePrefix, ?_⟩
    rcases heSide with ⟨heSelected, hSide⟩
    refine ⟨heSelected, ?_⟩
    have hne : e ≠ paperUnconditionalOrderingEdgeAt G i hi := by
      intro hEq
      subst e
      exact (paperUnconditionalOrderingEdgeAt_not_mem_prefix G i hi) hePrefix
    rw [paperNCKUpdateSide_apply_of_val_ne G D i hi side
      ⟨e, heSelected⟩ hne]
    exact hSide

theorem paperNCKUpdateSide_colEdges_before
    (G : PaperShape) (D : G.UnconditionalIntermediateRoleSides)
    (i : ℕ) (hi : i < paperUnconditionalOrderingLength G)
    (side : Bool) :
    paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKUpdateSide G D i hi side) i =
      paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate D i := by
  classical
  ext e
  simp only [paperPartialNCKStageColEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hePrefix, heSide⟩
    refine ⟨hePrefix, ?_⟩
    rcases heSide with ⟨heSelected, hSide⟩
    refine ⟨heSelected, ?_⟩
    have hne : e ≠ paperUnconditionalOrderingEdgeAt G i hi := by
      intro hEq
      subst e
      exact (paperUnconditionalOrderingEdgeAt_not_mem_prefix G i hi) hePrefix
    rw [paperNCKUpdateSide_apply_of_val_ne G D i hi side
      ⟨e, heSelected⟩ hne] at hSide
    exact hSide
  · rintro ⟨hePrefix, heSide⟩
    refine ⟨hePrefix, ?_⟩
    rcases heSide with ⟨heSelected, hSide⟩
    refine ⟨heSelected, ?_⟩
    have hne : e ≠ paperUnconditionalOrderingEdgeAt G i hi := by
      intro hEq
      subst e
      exact (paperUnconditionalOrderingEdgeAt_not_mem_prefix G i hi) hePrefix
    rw [paperNCKUpdateSide_apply_of_val_ne G D i hi side
      ⟨e, heSelected⟩ hne]
    exact hSide

theorem paperNCKBranch_rowChild_rowEdges
    (G : PaperShape) (history : List Bool)
    (hi : history.length < paperUnconditionalOrderingLength G) :
    paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G (paperNCKBranchChild false history))
        (history.length + 1) =
      insert (paperUnconditionalOrderingEdgeAt G history.length hi)
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G history) history.length) := by
  classical
  rw [paperNCKBranchSides_child G history hi false]
  unfold paperPartialNCKStageRowEdges
  rw [paperUnconditionalOrderingPrefix_succ G history.length hi]
  simp only [Finset.filter_insert]
  rw [if_pos]
  · change insert (paperUnconditionalOrderingEdgeAt G history.length hi)
        (paperPartialNCKStageRowEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKUpdateSide G (paperNCKBranchSides G history)
            history.length hi false) history.length) = _
    rw [paperNCKUpdateSide_rowEdges_before]
    rfl
  · exact ⟨paperUnconditionalOrderingEdgeAt_mem_selected G history.length hi,
      paperNCKUpdateSide_current G _ _ _ false⟩

theorem paperNCKBranch_rowChild_colEdges
    (G : PaperShape) (history : List Bool)
    (hi : history.length < paperUnconditionalOrderingLength G) :
    paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G (paperNCKBranchChild false history))
        (history.length + 1) =
      paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G history) history.length := by
  classical
  rw [paperNCKBranchSides_child G history hi false]
  unfold paperPartialNCKStageColEdges
  rw [paperUnconditionalOrderingPrefix_succ G history.length hi]
  simp only [Finset.filter_insert]
  rw [if_neg]
  · exact paperNCKUpdateSide_colEdges_before G
      (paperNCKBranchSides G history) history.length hi false
  · rintro ⟨_heSelected, hTrue⟩
    have hFalse := paperNCKUpdateSide_current G
      (paperNCKBranchSides G history) history.length hi false
    exact Bool.false_ne_true (hFalse.symm.trans hTrue)

theorem paperNCKBranch_colChild_colEdges
    (G : PaperShape) (history : List Bool)
    (hi : history.length < paperUnconditionalOrderingLength G) :
    paperPartialNCKStageColEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G (paperNCKBranchChild true history))
        (history.length + 1) =
      insert (paperUnconditionalOrderingEdgeAt G history.length hi)
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G history) history.length) := by
  classical
  rw [paperNCKBranchSides_child G history hi true]
  unfold paperPartialNCKStageColEdges
  rw [paperUnconditionalOrderingPrefix_succ G history.length hi]
  simp only [Finset.filter_insert]
  rw [if_pos]
  · change insert (paperUnconditionalOrderingEdgeAt G history.length hi)
        (paperPartialNCKStageColEdges G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKUpdateSide G (paperNCKBranchSides G history)
            history.length hi true) history.length) = _
    rw [paperNCKUpdateSide_colEdges_before]
    rfl
  · exact ⟨paperUnconditionalOrderingEdgeAt_mem_selected G history.length hi,
      paperNCKUpdateSide_current G _ _ _ true⟩

theorem paperNCKBranch_colChild_rowEdges
    (G : PaperShape) (history : List Bool)
    (hi : history.length < paperUnconditionalOrderingLength G) :
    paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G (paperNCKBranchChild true history))
        (history.length + 1) =
      paperPartialNCKStageRowEdges G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G history) history.length := by
  classical
  rw [paperNCKBranchSides_child G history hi true]
  unfold paperPartialNCKStageRowEdges
  rw [paperUnconditionalOrderingPrefix_succ G history.length hi]
  simp only [Finset.filter_insert]
  rw [if_neg]
  · exact paperNCKUpdateSide_rowEdges_before G
      (paperNCKBranchSides G history) history.length hi true
  · rintro ⟨_heSelected, hFalse⟩
    have hTrue := paperNCKUpdateSide_current G
      (paperNCKBranchSides G history) history.length hi true
    have hBad : true = false := hTrue.symm.trans hFalse
    exact Bool.noConfusion hBad

/-! ## Typed branch matrices and the honest analytic premise -/

/-- Concrete raw stage at one NCK branch.  `orientation` and `history` are
separate arguments and can vary independently. -/
def paperNCKBranchStageMatrix
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (history : List Bool)
    (w : PaperDecoupledNoise G n) :=
  paperPartialNCKStageMatrix G
    G.unconditionalBoundaryCleanMengerCertificate
    (paperNCKBranchSides G history) n orientation history.length w

/-- Squared mean attached to a branch node. -/
def paperNCKBranchSquaredStageMean
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (history : List Bool) : ℝ :=
  paperMean (fun w : PaperDecoupledNoise G n =>
    ‖paperNCKBranchStageMatrix G n orientation history w‖ ^ 2)

theorem paperNCKBranchSquaredStageMean_nonneg
    (G : PaperShape) (n : ℕ)
    (orientation : Fin G.edges → Bool) (history : List Bool) :
    0 ≤ paperNCKBranchSquaredStageMean G n orientation history := by
  unfold paperNCKBranchSquaredStageMean paperMean
  positivity

/-- Correct two-child sum premise for the actual stages.  This is the only
analytic assertion in the file; in particular it does not select one child
using the unrelated graph orientation. -/
def PaperPartialNCKBranchingSumSquared
    (G : PaperShape) (C : ℝ) (p n : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (history : List Bool),
    history.length < paperUnconditionalOrderingLength G →
      paperNCKBranchSquaredStageMean G n orientation history ≤
        partialNCKSquaredStepFactor C p *
          (paperNCKBranchSquaredStageMean G n orientation
              (paperNCKBranchChild false history) +
            paperNCKBranchSquaredStageMean G n orientation
              (paperNCKBranchChild true history))

/-- Max-form alternative, with any row-plus-column factor already absorbed
into the stated constant. -/
def PaperPartialNCKBranchingMaxSquared
    (G : PaperShape) (C : ℝ) (p n : ℕ) : Prop :=
  ∀ (orientation : Fin G.edges → Bool) (history : List Bool),
    history.length < paperUnconditionalOrderingLength G →
      paperNCKBranchSquaredStageMean G n orientation history ≤
        partialNCKSquaredStepFactor C p * max
          (paperNCKBranchSquaredStageMean G n orientation
            (paperNCKBranchChild false history))
          (paperNCKBranchSquaredStageMean G n orientation
            (paperNCKBranchChild true history))

/-! ## Every terminal leaf has the same formula-(21) bound -/

theorem paperNCKAnySidesRawTerminal_squaredNorm_le_canonicalPower
    (G : PaperShape) (D : G.UnconditionalIntermediateRoleSides)
    (n : ℕ) (hn : 1 ≤ n) (orientation : Fin G.edges → Bool)
    (w : PaperDecoupledNoise G n) :
    ‖paperPartialNCKRawTerminalMatrix G
        G.unconditionalBoundaryCleanMengerCertificate D
        n orientation w‖ ^ 2 ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
  have h := paperPartialNCKRawTerminal_squaredNorm_le_minSeparatorPower
    G G.unconditionalBoundaryCleanMengerCertificate D n hn orientation w
  have hExponent :
      G.roles - G.unconditionalBoundaryCleanMengerCertificate.cut.card +
          G.isolatedMiddleRoles.card =
        paperTheorem48CanonicalSizeExponent G := by
    unfold paperTheorem48CanonicalSizeExponent
    have hCut := G.unconditionalMengerCut_card_eq_separatorNumber
    omega
  exact h.trans_eq (congrArg (fun e : ℕ => (n : ℝ) ^ e) hExponent)

theorem paperNCKBranchTerminalLeaf_pointwise_le_canonicalPower
    (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) (history : List Bool)
    (hTerminal : history.length = paperUnconditionalOrderingLength G)
    (w : PaperDecoupledNoise G n) :
    ‖paperNCKBranchStageMatrix G n orientation history w‖ ^ 2 ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
  unfold paperNCKBranchStageMatrix
  rw [hTerminal]
  calc
    paperPartialNCKRawStageNorm G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G history) n orientation w
          (paperUnconditionalOrderingLength G) ^ 2 ≤
        ‖paperPartialNCKRawTerminalMatrix G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G history) n orientation w‖ ^ 2 := by
      apply pow_le_pow_left₀
        (paperPartialNCKRawStageNorm_nonneg G
          G.unconditionalBoundaryCleanMengerCertificate
          (paperNCKBranchSides G history) n orientation w _)
      exact paperPartialNCKFinalLiteralNorm_le_rawTerminal G
        G.unconditionalBoundaryCleanMengerCertificate
        (paperNCKBranchSides G history) orientation w
    _ ≤ (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G :=
      paperNCKAnySidesRawTerminal_squaredNorm_le_canonicalPower
        G (paperNCKBranchSides G history) n hn orientation w

theorem paperNCKBranchTerminalLeaf_mean_le_canonicalPower
    (G : PaperShape) (n : ℕ) (hn : 1 ≤ n)
    (orientation : Fin G.edges → Bool) (history : List Bool)
    (hTerminal : history.length = paperUnconditionalOrderingLength G) :
    paperNCKBranchSquaredStageMean G n orientation history ≤
      (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
  unfold paperNCKBranchSquaredStageMean
  calc
    paperMean (fun w : PaperDecoupledNoise G n =>
        ‖paperNCKBranchStageMatrix G n orientation history w‖ ^ 2) ≤
      paperMean (fun _w : PaperDecoupledNoise G n =>
        (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G) := by
      apply paperMean_mono
      intro w
      exact paperNCKBranchTerminalLeaf_pointwise_le_canonicalPower
        G n hn orientation history hTerminal w
    _ = (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G := by
      simp [paperMean]

/-! ## Direct connection to the numerical branching ledger -/

/-- Level-aware form of the sum iteration.  The analytic step is requested
only strictly before the selected terminal depth. -/
theorem paperNCKBranchSum_iteration_before
    (B : List Bool → ℝ) (c : ℝ) (hc : 0 ≤ c) (k : ℕ)
    (hStep : ∀ history, history.length < k →
      B history ≤ c *
        (B (paperNCKBranchChild false history) +
          B (paperNCKBranchChild true history))) :
    ∀ (remaining : ℕ) (history : List Bool),
      history.length + remaining = k →
      B history ≤ c ^ remaining * paperNCKBranchSum B remaining history := by
  intro remaining
  induction remaining with
  | zero =>
      intro history _hLevel
      simp [paperNCKBranchSum]
  | succ remaining ih =>
      intro history hLevel
      have hlt : history.length < k := by omega
      have hFalse := ih (paperNCKBranchChild false history) (by
        simp [paperNCKBranchChild]
        omega)
      have hTrue := ih (paperNCKBranchChild true history) (by
        simp [paperNCKBranchChild]
        omega)
      calc
        B history ≤ c *
            (B (paperNCKBranchChild false history) +
              B (paperNCKBranchChild true history)) := hStep history hlt
        _ ≤ c *
            (c ^ remaining * paperNCKBranchSum B remaining
                (paperNCKBranchChild false history) +
              c ^ remaining * paperNCKBranchSum B remaining
                (paperNCKBranchChild true history)) := by
          gcongr
        _ = c ^ (remaining + 1) *
            paperNCKBranchSum B (remaining + 1) history := by
          simp only [paperNCKBranchSum, pow_succ]
          ring

theorem paperNCKBranchStageZero_le_of_sumSquared
    (G : PaperShape) (C : ℝ) (p n : ℕ) (hn : 1 ≤ n)
    (hNCK : PaperPartialNCKBranchingSumSquared G C p n)
    (orientation : Fin G.edges → Bool) :
    paperNCKBranchSquaredStageMean G n orientation [] ≤
      partialNCKSquaredStepFactor C p ^
          paperUnconditionalOrderingLength G *
        ((2 : ℝ) ^ paperUnconditionalOrderingLength G *
          (n : ℝ) ^ paperTheorem48CanonicalSizeExponent G) := by
  let k := paperUnconditionalOrderingLength G
  have hIter := paperNCKBranchSum_iteration_before
    (paperNCKBranchSquaredStageMean G n orientation)
    (partialNCKSquaredStepFactor C p)
    (partialNCKSquaredStepFactor_nonneg C p) k
    (fun history hhistory =>
      hNCK orientation history (by simpa [k] using hhistory))
    k [] (by simp)
  exact hIter.trans
    (mul_le_mul_of_nonneg_left
      (paperNCKBranchSum_le_of_terminal_bound
        (paperNCKBranchSquaredStageMean G n orientation)
        ((n : ℝ) ^ paperTheorem48CanonicalSizeExponent G)
        k 0 [] (by simp)
        (by
          intro leaf hLeaf
          apply paperNCKBranchTerminalLeaf_mean_le_canonicalPower
            G n hn orientation leaf
          simpa [k] using hLeaf))
      (pow_nonneg (partialNCKSquaredStepFactor_nonneg C p) k))

#print axioms paperNCKUpdateSide_rowEdges_before
#print axioms paperNCKBranch_rowChild_rowEdges
#print axioms paperNCKBranch_colChild_colEdges
#print axioms paperNCKAnySidesRawTerminal_squaredNorm_le_canonicalPower
#print axioms paperNCKBranchTerminalLeaf_mean_le_canonicalPower
#print axioms paperNCKBranchSum_iteration_before
#print axioms paperNCKBranchStageZero_le_of_sumSquared

end GraphMatrixReplica
