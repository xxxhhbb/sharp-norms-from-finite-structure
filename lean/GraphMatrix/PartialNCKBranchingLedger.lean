import GraphMatrix.RpowHalfExponent

/-! # Branching bookkeeping for partially iterated NCK

The row/column choice made by an NCK step is independent of every graph-edge
orientation.  This file records that distinction in a purely numerical binary
tree.  It contains no matrix definitions and assumes only that every leaf at
the terminal depth obeys the same bound.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Add one independent row/column decision to a branch history. -/
def paperNCKBranchChild (side : Bool) (history : List Bool) : List Bool :=
  side :: history

@[simp] theorem paperNCKBranchChild_length
    (side : Bool) (history : List Bool) :
    (paperNCKBranchChild side history).length = history.length + 1 := by
  simp [paperNCKBranchChild]

/-- Sum of the values on the complete binary subtree of a given depth. -/
def paperNCKBranchSum (B : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, history => B history
  | depth + 1, history =>
      paperNCKBranchSum B depth (paperNCKBranchChild false history) +
        paperNCKBranchSum B depth (paperNCKBranchChild true history)

/-- Maximum of the values on the complete binary subtree of a given depth. -/
def paperNCKBranchMax (B : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, history => B history
  | depth + 1, history =>
      max (paperNCKBranchMax B depth (paperNCKBranchChild false history))
        (paperNCKBranchMax B depth (paperNCKBranchChild true history))

theorem paperNCKBranchSum_nonneg
    (B : List Bool → ℝ) (hB : ∀ history, 0 ≤ B history) :
    ∀ depth history, 0 ≤ paperNCKBranchSum B depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history
      exact hB history
  | succ depth ih =>
      intro history
      exact add_nonneg (ih _) (ih _)

theorem paperNCKBranchMax_nonneg
    (B : List Bool → ℝ) (hB : ∀ history, 0 ≤ B history) :
    ∀ depth history, 0 ≤ paperNCKBranchMax B depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history
      exact hB history
  | succ depth ih =>
      intro history
      exact (ih (paperNCKBranchChild false history)).trans
        (le_max_left _ _)

/-- Iterating a row-plus-column step gives a power of the step factor times
the sum over every independent branch. -/
theorem paperNCKBranchSum_iteration
    (B : List Bool → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ history,
      B history ≤ c *
        (B (paperNCKBranchChild false history) +
          B (paperNCKBranchChild true history))) :
    ∀ depth history,
      B history ≤ c ^ depth * paperNCKBranchSum B depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp [paperNCKBranchSum]
  | succ depth ih =>
      intro history
      calc
        B history ≤ c *
            (B (paperNCKBranchChild false history) +
              B (paperNCKBranchChild true history)) := hStep history
        _ ≤ c *
            (c ^ depth * paperNCKBranchSum B depth
                (paperNCKBranchChild false history) +
              c ^ depth * paperNCKBranchSum B depth
                (paperNCKBranchChild true history)) := by
          gcongr
          · exact ih _
          · exact ih _
        _ = c ^ (depth + 1) * paperNCKBranchSum B (depth + 1) history := by
          simp only [paperNCKBranchSum, pow_succ]
          ring

/-- Iterating a max-of-two-children step has no binary-cardinality loss. -/
theorem paperNCKBranchMax_iteration
    (B : List Bool → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ history,
      B history ≤ c * max
        (B (paperNCKBranchChild false history))
        (B (paperNCKBranchChild true history))) :
    ∀ depth history,
      B history ≤ c ^ depth * paperNCKBranchMax B depth history := by
  intro depth
  induction depth with
  | zero =>
      intro history
      simp [paperNCKBranchMax]
  | succ depth ih =>
      intro history
      have hFalse :
          B (paperNCKBranchChild false history) ≤
            c ^ depth * paperNCKBranchMax B depth
              (paperNCKBranchChild false history) := ih _
      have hTrue :
          B (paperNCKBranchChild true history) ≤
            c ^ depth * paperNCKBranchMax B depth
              (paperNCKBranchChild true history) := ih _
      have hChildren :
          max (B (paperNCKBranchChild false history))
              (B (paperNCKBranchChild true history)) ≤
            c ^ depth * max
              (paperNCKBranchMax B depth
                (paperNCKBranchChild false history))
              (paperNCKBranchMax B depth
                (paperNCKBranchChild true history)) := by
        apply max_le
        · exact hFalse.trans
            (mul_le_mul_of_nonneg_left (le_max_left _ _)
              (pow_nonneg hc depth))
        · exact hTrue.trans
            (mul_le_mul_of_nonneg_left (le_max_right _ _)
              (pow_nonneg hc depth))
      calc
        B history ≤ c * max
            (B (paperNCKBranchChild false history))
            (B (paperNCKBranchChild true history)) := hStep history
        _ ≤ c * (c ^ depth * max
            (paperNCKBranchMax B depth
              (paperNCKBranchChild false history))
            (paperNCKBranchMax B depth
              (paperNCKBranchChild true history))) :=
          mul_le_mul_of_nonneg_left hChildren hc
        _ = c ^ (depth + 1) * paperNCKBranchMax B (depth + 1) history := by
          simp only [paperNCKBranchMax, pow_succ]
          ring

/-- A uniform terminal-depth bound controls the entire leaf sum by the exact
number `2^remaining` of binary descendants. -/
theorem paperNCKBranchSum_le_of_terminal_bound
    (B : List Bool → ℝ) (D : ℝ) :
    ∀ (remaining level : ℕ) (history : List Bool),
      history.length = level →
      (∀ leaf, leaf.length = level + remaining → B leaf ≤ D) →
      paperNCKBranchSum B remaining history ≤ (2 : ℝ) ^ remaining * D := by
  intro remaining
  induction remaining with
  | zero =>
      intro level history hLength hLeaf
      simpa [paperNCKBranchSum] using hLeaf history (by omega)
  | succ remaining ih =>
      intro level history hLength hLeaf
      have hFalseLength :
          (paperNCKBranchChild false history).length = level + 1 := by
        simp [hLength]
      have hTrueLength :
          (paperNCKBranchChild true history).length = level + 1 := by
        simp [hLength]
      have hFalse := ih (level + 1)
        (paperNCKBranchChild false history) hFalseLength
        (fun leaf hLeafLength => hLeaf leaf (by omega))
      have hTrue := ih (level + 1)
        (paperNCKBranchChild true history) hTrueLength
        (fun leaf hLeafLength => hLeaf leaf (by omega))
      calc
        paperNCKBranchSum B (remaining + 1) history =
            paperNCKBranchSum B remaining
                (paperNCKBranchChild false history) +
              paperNCKBranchSum B remaining
                (paperNCKBranchChild true history) := rfl
        _ ≤ (2 : ℝ) ^ remaining * D + (2 : ℝ) ^ remaining * D :=
          add_le_add hFalse hTrue
        _ = (2 : ℝ) ^ (remaining + 1) * D := by ring

/-- A uniform terminal-depth bound also controls the maximum over all binary
descendants, with no cardinality loss. -/
theorem paperNCKBranchMax_le_of_terminal_bound
    (B : List Bool → ℝ) (D : ℝ) :
    ∀ (remaining level : ℕ) (history : List Bool),
      history.length = level →
      (∀ leaf, leaf.length = level + remaining → B leaf ≤ D) →
      paperNCKBranchMax B remaining history ≤ D := by
  intro remaining
  induction remaining with
  | zero =>
      intro level history hLength hLeaf
      simpa [paperNCKBranchMax] using hLeaf history (by omega)
  | succ remaining ih =>
      intro level history hLength hLeaf
      apply max_le
      · apply ih (level + 1) (paperNCKBranchChild false history)
        · simp [hLength]
        · intro leaf hLeafLength
          exact hLeaf leaf (by omega)
      · apply ih (level + 1) (paperNCKBranchChild true history)
        · simp [hLength]
        · intro leaf hLeafLength
          exact hLeaf leaf (by omega)

/-- Formula-(28)-style sum ledger from the root: every terminal R/C side
assignment is present, independently of any graph orientation. -/
theorem paperNCKBranchingLedger_sum
    (B : List Bool → ℝ) (c D : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ history,
      B history ≤ c *
        (B (paperNCKBranchChild false history) +
          B (paperNCKBranchChild true history)))
    (k : ℕ) (hTerminal : ∀ leaf, leaf.length = k → B leaf ≤ D) :
    B [] ≤ c ^ k * ((2 : ℝ) ^ k * D) := by
  exact (paperNCKBranchSum_iteration B c hc hStep k []).trans
    (mul_le_mul_of_nonneg_left
      (paperNCKBranchSum_le_of_terminal_bound B D k 0 [] (by simp)
        (by simpa using hTerminal))
      (pow_nonneg hc k))

/-- Formula-(28)-style max ledger from the root. -/
theorem paperNCKBranchingLedger_max
    (B : List Bool → ℝ) (c D : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ history,
      B history ≤ c * max
        (B (paperNCKBranchChild false history))
        (B (paperNCKBranchChild true history)))
    (k : ℕ) (hTerminal : ∀ leaf, leaf.length = k → B leaf ≤ D) :
    B [] ≤ c ^ k * D := by
  exact (paperNCKBranchMax_iteration B c hc hStep k []).trans
    (mul_le_mul_of_nonneg_left
      (paperNCKBranchMax_le_of_terminal_bound B D k 0 [] (by simp)
        (by simpa using hTerminal))
      (pow_nonneg hc k))

/-- A row-plus-column step can be read as a max step at the explicit price
of a factor two. -/
theorem paperNCKBranchingLedger_sum_to_max
    (B : List Bool → ℝ) (c D : ℝ) (hc : 0 ≤ c)
    (hStep : ∀ history,
      B history ≤ c *
        (B (paperNCKBranchChild false history) +
          B (paperNCKBranchChild true history)))
    (k : ℕ) (hTerminal : ∀ leaf, leaf.length = k → B leaf ≤ D) :
    B [] ≤ (2 * c) ^ k * D := by
  apply paperNCKBranchingLedger_max B (2 * c) D (mul_nonneg (by norm_num) hc)
  · intro history
    calc
      B history ≤ c *
          (B (paperNCKBranchChild false history) +
            B (paperNCKBranchChild true history)) := hStep history
      _ ≤ c * (2 * max
          (B (paperNCKBranchChild false history))
          (B (paperNCKBranchChild true history))) := by
        gcongr
        calc
          B (paperNCKBranchChild false history) +
              B (paperNCKBranchChild true history) ≤
            max (B (paperNCKBranchChild false history))
                (B (paperNCKBranchChild true history)) +
              max (B (paperNCKBranchChild false history))
                (B (paperNCKBranchChild true history)) :=
            add_le_add (le_max_left _ _) (le_max_right _ _)
          _ = 2 * max
              (B (paperNCKBranchChild false history))
              (B (paperNCKBranchChild true history)) := by ring
      _ = (2 * c) * max
          (B (paperNCKBranchChild false history))
          (B (paperNCKBranchChild true history)) := by ring
  · exact hTerminal

/-- Exact squared-scale specialization: the binary branching loss and the
NCK loss accumulate as `2^k C^(2k) p^k`. -/
theorem paperNCKBranchingSquaredScale_eq
    (C : ℝ) (p k : ℕ) (D : ℝ) :
    partialNCKSquaredStepFactor C p ^ k * ((2 : ℝ) ^ k * D ^ 2) =
      (2 : ℝ) ^ k * C ^ (2 * k) * (p : ℝ) ^ k * D ^ 2 := by
  unfold partialNCKSquaredStepFactor
  rw [mul_pow, ← pow_mul]
  ring

/-- After taking the square root, the exact loss is
`sqrt(2)^k C^k sqrt(p^k)`, i.e. `p^(k/2)` in real-exponent notation. -/
theorem sqrt_paperNCKBranchingSquaredScale
    (C : ℝ) (p k : ℕ) (D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Real.sqrt
        (partialNCKSquaredStepFactor C p ^ k *
          ((2 : ℝ) ^ k * D ^ 2)) =
      Real.sqrt 2 ^ k * C ^ k * Real.sqrt ((p : ℝ) ^ k) * D := by
  rw [paperNCKBranchingSquaredScale_eq]
  have hRewrite :
      (2 : ℝ) ^ k * C ^ (2 * k) * (p : ℝ) ^ k * D ^ 2 =
        (Real.sqrt 2 ^ k * C ^ k * D) ^ 2 * (p : ℝ) ^ k := by
    have hTwoPow : (Real.sqrt 2 ^ k) ^ 2 = (2 : ℝ) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hCPow : C ^ (2 * k) = (C ^ k) ^ 2 := by
      rw [mul_comm 2 k, pow_mul]
    rw [← hTwoPow, hCPow]
    ring
  rw [hRewrite, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq]
  · ring
  · positivity

/-- The same square-root identity with the `p^(k/2)` loss written using the
real exponent that appears in formula (28). -/
theorem sqrt_paperNCKBranchingSquaredScale_eq_rpow_half
    (C : ℝ) (p k : ℕ) (D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    Real.sqrt
        (partialNCKSquaredStepFactor C p ^ k *
          ((2 : ℝ) ^ k * D ^ 2)) =
      Real.sqrt 2 ^ k * C ^ k *
        Real.rpow (p : ℝ) ((k : ℝ) / 2) * D := by
  rw [sqrt_paperNCKBranchingSquaredScale C p k D hC hD,
    sqrt_natCast_pow_eq_rpow_half]


end GraphMatrixReplica
