import GraphMatrix.Model.LowerStackingThird

/-! Uniform-size all-row stacking for an arbitrary finite number of groups. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model

def lowerAllVerticalRows (n : ℕ) : (q : ℕ) → Type u → Type u
  | 0, ι => ι
  | q + 1, ι => lowerAllVerticalRows n q (Fin n × ι)

instance lowerAllVerticalRowsFintype (n q : ℕ) (ι : Type u)
    [Fintype ι] : Fintype (lowerAllVerticalRows n q ι) := by
  induction q generalizing ι with
  | zero => simpa [lowerAllVerticalRows] using (inferInstance : Fintype ι)
  | succ q ih =>
      change Fintype (lowerAllVerticalRows n q (Fin n × ι))
      exact ih (Fin n × ι)

instance lowerAllVerticalRowsDecidableEq (n q : ℕ) (ι : Type u)
    [DecidableEq ι] : DecidableEq (lowerAllVerticalRows n q ι) := by
  induction q generalizing ι with
  | zero => simpa [lowerAllVerticalRows] using (inferInstance : DecidableEq ι)
  | succ q ih =>
      change DecidableEq (lowerAllVerticalRows n q (Fin n × ι))
      exact ih (Fin n × ι)

def lowerMultiGroupChaos (n q : ℕ) {ι κ : Type*}
    (A : (Fin q → Fin n) → Matrix ι κ ℝ)
    (w : Fin q → (Fin n → Bool)) : Matrix ι κ ℝ :=
  match q with
  | 0 => A Fin.elim0
  | q + 1 =>
      lowerMatrixSignSum n (fun e =>
        lowerMultiGroupChaos n q
          (fun tail => A (Fin.cons e tail))
          (fun g => w g.succ)) (w 0)

def lowerMultiGroupVerticalFlatten (n q : ℕ) {ι κ : Type*}
    (A : (Fin q → Fin n) → Matrix ι κ ℝ) :
    Matrix (lowerAllVerticalRows n q ι) κ ℝ :=
  match q with
  | 0 => A Fin.elim0
  | q + 1 =>
      lowerMultiGroupVerticalFlatten n q (fun tail =>
        lowerVerticallyStackedMatrix n (fun e => A (Fin.cons e tail)))

def lowerMultiGroupMean (n q : ℕ)
    (f : (Fin q → (Fin n → Bool)) → ℝ) : ℝ :=
  match q with
  | 0 => f Fin.elim0
  | q + 1 =>
      lowerMultiGroupMean n q (fun tail =>
        allSignsMean n (fun head => f (Fin.cons head tail)))

theorem lowerMultiGroupMean_mono (n : ℕ) :
    ∀ q (f g : (Fin q → (Fin n → Bool)) → ℝ),
      (∀ w, f w ≤ g w) →
        lowerMultiGroupMean n q f ≤ lowerMultiGroupMean n q g := by
  intro q
  induction q with
  | zero =>
      intro f g h
      exact h Fin.elim0
  | succ q ih =>
      intro f g h
      change lowerMultiGroupMean n q
          (fun tail => allSignsMean n (fun head => f (Fin.cons head tail))) ≤
        lowerMultiGroupMean n q
          (fun tail => allSignsMean n (fun head => g (Fin.cons head tail)))
      apply ih
      intro tail
      apply allSignsMean_mono n
      intro head
      exact h (Fin.cons head tail)

theorem lowerMultiGroupMean_const_mul (n : ℕ) (c : ℝ) :
    ∀ q (f : (Fin q → (Fin n → Bool)) → ℝ),
      lowerMultiGroupMean n q (fun w => c * f w) =
        c * lowerMultiGroupMean n q f := by
  intro q
  induction q with
  | zero =>
      intro f
      rfl
  | succ q ih =>
      intro f
      change lowerMultiGroupMean n q
          (fun tail => allSignsMean n (fun head => c * f (Fin.cons head tail))) =
        c * lowerMultiGroupMean n q
          (fun tail => allSignsMean n (fun head => f (Fin.cons head tail)))
      have hPoint :
          (fun tail => allSignsMean n (fun head => c * f (Fin.cons head tail))) =
            (fun tail => c * allSignsMean n
              (fun head => f (Fin.cons head tail))) := by
        funext tail
        exact lowerAllSignsMean_const_mul n c
          (fun head => f (Fin.cons head tail))
      rw [hPoint]
      exact ih (fun tail => allSignsMean n
        (fun head => f (Fin.cons head tail)))

/-- A new row-side coefficient coordinate can be moved through every
remaining sign-sum group. This is the exact tensor reindexing needed by
the arbitrary-order lower stacking induction. -/
theorem lowerMultiGroupChaos_verticalStack_commute (n : ℕ) :
    ∀ q {ι κ : Type*}
      (A : Fin n → (Fin q → Fin n) → Matrix ι κ ℝ)
      (w : Fin q → (Fin n → Bool)),
      lowerVerticallyStackedMatrix n
          (fun e => lowerMultiGroupChaos n q (A e) w) =
        lowerMultiGroupChaos n q
          (fun tail => lowerVerticallyStackedMatrix n
            (fun e => A e tail)) w := by
  intro q
  induction q with
  | zero =>
      intro ι κ A w
      rfl
  | succ q ih =>
      intro ι κ A w
      let tailW : Fin q → (Fin n → Bool) := fun g => w g.succ
      let C : Fin n → Fin n → (Fin q → Fin n) → Matrix ι κ ℝ :=
        fun e e' tail => A e (Fin.cons e' tail)
      change lowerVerticallyStackedMatrix n
          (fun e => lowerMatrixSignSum n
            (fun e' => lowerMultiGroupChaos n q (C e e') tailW) (w 0)) =
        lowerMatrixSignSum n
          (fun e' => lowerMultiGroupChaos n q
            (fun tail => lowerVerticallyStackedMatrix n
              (fun e => C e e' tail)) tailW) (w 0)
      calc
        _ = lowerMatrixSignSum n (fun e' =>
            lowerVerticallyStackedMatrix n
              (fun e => lowerMultiGroupChaos n q (C e e') tailW))
              (w 0) := by
          exact lowerVerticalStack_signSum_commute n n
            (fun e e' => lowerMultiGroupChaos n q (C e e') tailW) (w 0)
        _ = lowerMatrixSignSum n
            (fun e' => lowerMultiGroupChaos n q
              (fun tail => lowerVerticallyStackedMatrix n
                (fun e => C e e' tail)) tailW) (w 0) := by
          congr 1
          funext e'
          exact ih (fun e tail => C e e' tail) tailW

/-- Arbitrary finite-order all-row lower stacking, for `q` independent
Boolean sign groups of the same finite size `n`. The original column index
is unchanged; each recursive step appends one actual coefficient coordinate
to the row index. No flattening estimate is assumed. -/
theorem lowerMultiGroupVerticalFlatten_norm_le (n : ℕ) :
    ∀ q {ι κ : Type*} [Fintype ι] [Fintype κ]
      [DecidableEq ι] [DecidableEq κ]
      (A : (Fin q → Fin n) → Matrix ι κ ℝ),
      ‖lowerMultiGroupVerticalFlatten n q A‖ ≤
        Real.sqrt 3 ^ q * lowerMultiGroupMean n q
          (fun w => ‖lowerMultiGroupChaos n q A w‖) := by
  intro q
  induction q with
  | zero =>
      intro ι κ _ _ _ _ A
      simp [lowerMultiGroupVerticalFlatten, lowerMultiGroupMean,
        lowerMultiGroupChaos]
      exact le_rfl
  | succ q ih =>
      intro ι κ _ _ _ _ A
      let B : (Fin q → Fin n) → Matrix (Fin n × ι) κ ℝ :=
        fun tail => lowerVerticallyStackedMatrix n
          (fun e => A (Fin.cons e tail))
      have hIH := ih B
      have hPoint : ∀ tailW : Fin q → (Fin n → Bool),
          ‖lowerMultiGroupChaos n q B tailW‖ ≤
            Real.sqrt 3 * allSignsMean n (fun head =>
              ‖lowerMultiGroupChaos n (q + 1) A
                (Fin.cons head tailW)‖) := by
        intro tailW
        have hComm :
            ‖lowerMultiGroupChaos n q B tailW‖ =
              ‖lowerVerticallyStackedMatrix n (fun e =>
                lowerMultiGroupChaos n q
                  (fun tail => A (Fin.cons e tail)) tailW)‖ := by
          exact congrArg norm
            (lowerMultiGroupChaos_verticalStack_commute n q
              (fun e tail => A (Fin.cons e tail)) tailW).symm
        rw [hComm]
        have hOne := lowerVerticalStack_norm_le_sqrtThree_mean n
          (fun e => lowerMultiGroupChaos n q
            (fun tail => A (Fin.cons e tail)) tailW)
        simpa [lowerMultiGroupChaos] using hOne
      have hMean :
          lowerMultiGroupMean n q
            (fun tailW => ‖lowerMultiGroupChaos n q B tailW‖) ≤
          Real.sqrt 3 * lowerMultiGroupMean n (q + 1)
            (fun w => ‖lowerMultiGroupChaos n (q + 1) A w‖) := by
        calc
          _ ≤ lowerMultiGroupMean n q (fun tailW =>
                Real.sqrt 3 * allSignsMean n (fun head =>
                  ‖lowerMultiGroupChaos n (q + 1) A
                    (Fin.cons head tailW)‖)) :=
            lowerMultiGroupMean_mono n q _ _ hPoint
          _ = Real.sqrt 3 * lowerMultiGroupMean n q
                (fun tailW => allSignsMean n (fun head =>
                  ‖lowerMultiGroupChaos n (q + 1) A
                    (Fin.cons head tailW)‖)) :=
            lowerMultiGroupMean_const_mul n (Real.sqrt 3) q _
          _ = Real.sqrt 3 * lowerMultiGroupMean n (q + 1)
                (fun w => ‖lowerMultiGroupChaos n (q + 1) A w‖) := rfl
      change ‖lowerMultiGroupVerticalFlatten n q B‖ ≤
        Real.sqrt 3 ^ (q + 1) * lowerMultiGroupMean n (q + 1)
          (fun w => ‖lowerMultiGroupChaos n (q + 1) A w‖)
      calc
        _ ≤ Real.sqrt 3 ^ q * lowerMultiGroupMean n q
              (fun tailW => ‖lowerMultiGroupChaos n q B tailW‖) := hIH
        _ ≤ Real.sqrt 3 ^ q *
              (Real.sqrt 3 * lowerMultiGroupMean n (q + 1)
                (fun w => ‖lowerMultiGroupChaos n (q + 1) A w‖)) :=
          mul_le_mul_of_nonneg_left hMean
            (pow_nonneg (Real.sqrt_nonneg _) _)
        _ = Real.sqrt 3 ^ (q + 1) * lowerMultiGroupMean n (q + 1)
              (fun w => ‖lowerMultiGroupChaos n (q + 1) A w‖) := by
          rw [pow_succ]
          ring


end GraphMatrixReplica.Model
