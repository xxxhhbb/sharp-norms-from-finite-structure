import GraphMatrix.Model.LowerStackingAllVertical

/-!
# All-row lower stacking with heterogeneous finite sign-group sizes

The size function is part of the coefficient tensor's index type. It is
not a numerical bound or an assumption that the group sizes are equal.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model

abbrev lowerHeteroIndex (q : ℕ) (size : Fin q → ℕ) :=
  ∀ g : Fin q, Fin (size g)

abbrev lowerHeteroNoise (q : ℕ) (size : Fin q → ℕ) :=
  ∀ g : Fin q, Fin (size g) → Bool

def lowerHeteroRows :
    (q : ℕ) → (size : Fin q → ℕ) → Type u → Type u
  | 0, _, ι => ι
  | q + 1, size, ι =>
      lowerHeteroRows q (fun g => size g.succ) (Fin (size 0) × ι)

instance lowerHeteroRowsFintype :
    (q : ℕ) → (size : Fin q → ℕ) → (ι : Type u) →
      [Fintype ι] → Fintype (lowerHeteroRows q size ι)
  | 0, _, ι, _ => by simpa [lowerHeteroRows] using (inferInstance : Fintype ι)
  | q + 1, size, ι, _ => by
      change Fintype (lowerHeteroRows q
        (fun g => size g.succ) (Fin (size 0) × ι))
      exact lowerHeteroRowsFintype q (fun g => size g.succ) (Fin (size 0) × ι)

instance lowerHeteroRowsDecidableEq :
    (q : ℕ) → (size : Fin q → ℕ) → (ι : Type u) →
      [DecidableEq ι] → DecidableEq (lowerHeteroRows q size ι)
  | 0, _, ι, _ => by simpa [lowerHeteroRows] using (inferInstance : DecidableEq ι)
  | q + 1, size, ι, _ => by
      change DecidableEq (lowerHeteroRows q
        (fun g => size g.succ) (Fin (size 0) × ι))
      exact lowerHeteroRowsDecidableEq q
        (fun g => size g.succ) (Fin (size 0) × ι)

def lowerHeteroChaos (q : ℕ) (size : Fin q → ℕ)
    {ι κ : Type*}
    (A : lowerHeteroIndex q size → Matrix ι κ ℝ)
    (w : lowerHeteroNoise q size) : Matrix ι κ ℝ :=
  match q with
  | 0 => A (fun g => Fin.elim0 g)
  | q + 1 =>
      lowerMatrixSignSum (size 0) (fun e =>
        lowerHeteroChaos q (fun g => size g.succ)
          (fun tail => A (Fin.cons e tail))
          (fun g => w g.succ)) (w 0)

def lowerHeteroFlatten (q : ℕ) (size : Fin q → ℕ)
    {ι κ : Type*}
    (A : lowerHeteroIndex q size → Matrix ι κ ℝ) :
    Matrix (lowerHeteroRows q size ι) κ ℝ :=
  match q with
  | 0 => A (fun g => Fin.elim0 g)
  | q + 1 =>
      lowerHeteroFlatten q (fun g => size g.succ)
        (fun tail => lowerVerticallyStackedMatrix (size 0)
          (fun e => A (Fin.cons e tail)))

def lowerHeteroMean (q : ℕ) (size : Fin q → ℕ)
    (f : lowerHeteroNoise q size → ℝ) : ℝ :=
  match q with
  | 0 => f (fun g => Fin.elim0 g)
  | q + 1 =>
      lowerHeteroMean q (fun g => size g.succ)
        (fun tail => allSignsMean (size 0) (fun head =>
          f (Fin.cons head tail)))

theorem lowerHeteroMean_mono :
    ∀ q (size : Fin q → ℕ)
      (f g : lowerHeteroNoise q size → ℝ),
      (∀ w, f w ≤ g w) →
        lowerHeteroMean q size f ≤ lowerHeteroMean q size g := by
  intro q
  induction q with
  | zero =>
      intro size f g h
      exact h (fun x => Fin.elim0 x)
  | succ q ih =>
      intro size f g h
      change lowerHeteroMean q (fun g => size g.succ)
          (fun tail => allSignsMean (size 0)
            (fun head => f (Fin.cons head tail))) ≤
        lowerHeteroMean q (fun g => size g.succ)
          (fun tail => allSignsMean (size 0)
            (fun head => g (Fin.cons head tail)))
      apply ih
      intro tail
      apply allSignsMean_mono
      intro head
      exact h (Fin.cons head tail)

theorem lowerHeteroMean_const_mul (c : ℝ) :
    ∀ q (size : Fin q → ℕ)
      (f : lowerHeteroNoise q size → ℝ),
      lowerHeteroMean q size (fun w => c * f w) =
        c * lowerHeteroMean q size f := by
  intro q
  induction q with
  | zero =>
      intro size f
      rfl
  | succ q ih =>
      intro size f
      change lowerHeteroMean q (fun g => size g.succ)
          (fun tail => allSignsMean (size 0)
            (fun head => c * f (Fin.cons head tail))) =
        c * lowerHeteroMean q (fun g => size g.succ)
          (fun tail => allSignsMean (size 0)
            (fun head => f (Fin.cons head tail)))
      have hPoint :
          (fun tail => allSignsMean (size 0)
            (fun head => c * f (Fin.cons head tail))) =
          (fun tail => c * allSignsMean (size 0)
            (fun head => f (Fin.cons head tail))) := by
        funext tail
        exact lowerAllSignsMean_const_mul (size 0) c
          (fun head => f (Fin.cons head tail))
      rw [hPoint]
      exact ih (fun g => size g.succ)
        (fun tail => allSignsMean (size 0)
          (fun head => f (Fin.cons head tail)))

/-- Exact commutation of an additional row-coordinate stack with every
remaining sign group, regardless of the groups' individual sizes. -/
theorem lowerHeteroChaos_verticalStack_commute (m : ℕ) :
    ∀ q (size : Fin q → ℕ) {ι κ : Type*}
      (A : Fin m → lowerHeteroIndex q size → Matrix ι κ ℝ)
      (w : lowerHeteroNoise q size),
      lowerVerticallyStackedMatrix m
          (fun e => lowerHeteroChaos q size (A e) w) =
        lowerHeteroChaos q size
          (fun tail => lowerVerticallyStackedMatrix m
            (fun e => A e tail)) w := by
  intro q
  induction q with
  | zero =>
      intro size ι κ A w
      rfl
  | succ q ih =>
      intro size ι κ A w
      let tailSize : Fin q → ℕ := fun g => size g.succ
      let tailW : lowerHeteroNoise q tailSize := fun g => w g.succ
      let C : Fin m → Fin (size 0) →
          lowerHeteroIndex q tailSize → Matrix ι κ ℝ :=
        fun e e' tail => A e (Fin.cons e' tail)
      change lowerVerticallyStackedMatrix m
          (fun e => lowerMatrixSignSum (size 0)
            (fun e' => lowerHeteroChaos q tailSize (C e e') tailW)
            (w 0)) =
        lowerMatrixSignSum (size 0)
          (fun e' => lowerHeteroChaos q tailSize
            (fun tail => lowerVerticallyStackedMatrix m
              (fun e => C e e' tail)) tailW) (w 0)
      calc
        _ = lowerMatrixSignSum (size 0) (fun e' =>
            lowerVerticallyStackedMatrix m
              (fun e => lowerHeteroChaos q tailSize (C e e') tailW))
              (w 0) := by
          exact lowerVerticalStack_signSum_commute m (size 0)
            (fun e e' => lowerHeteroChaos q tailSize (C e e') tailW) (w 0)
        _ = lowerMatrixSignSum (size 0)
            (fun e' => lowerHeteroChaos q tailSize
              (fun tail => lowerVerticallyStackedMatrix m
                (fun e => C e e' tail)) tailW) (w 0) := by
          congr 1
          funext e'
          exact ih tailSize (fun e tail => C e e' tail) tailW

/-- Arbitrary-order all-row stacking with a separately specified finite
size for every independent sign group. The only numerical loss is one
`√3` per group; no uniform-size hypothesis remains. -/
theorem lowerHeteroFlatten_norm_le :
    ∀ q (size : Fin q → ℕ) {ι κ : Type*}
      [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (A : lowerHeteroIndex q size → Matrix ι κ ℝ),
      ‖lowerHeteroFlatten q size A‖ ≤
        Real.sqrt 3 ^ q * lowerHeteroMean q size
          (fun w => ‖lowerHeteroChaos q size A w‖) := by
  intro q
  induction q with
  | zero =>
      intro size ι κ _ _ _ _ A
      simp [lowerHeteroFlatten, lowerHeteroMean, lowerHeteroChaos]
      exact le_rfl
  | succ q ih =>
      intro size ι κ _ _ _ _ A
      let tailSize : Fin q → ℕ := fun g => size g.succ
      let B : lowerHeteroIndex q tailSize →
          Matrix (Fin (size 0) × ι) κ ℝ :=
        fun tail => lowerVerticallyStackedMatrix (size 0)
          (fun e => A (Fin.cons e tail))
      have hIH := ih tailSize B
      have hPoint : ∀ tailW : lowerHeteroNoise q tailSize,
          ‖lowerHeteroChaos q tailSize B tailW‖ ≤
            Real.sqrt 3 * allSignsMean (size 0) (fun head =>
              ‖lowerHeteroChaos (q + 1) size A
                (Fin.cons head tailW)‖) := by
        intro tailW
        have hComm :
            ‖lowerHeteroChaos q tailSize B tailW‖ =
              ‖lowerVerticallyStackedMatrix (size 0) (fun e =>
                lowerHeteroChaos q tailSize
                  (fun tail => A (Fin.cons e tail)) tailW)‖ := by
          exact congrArg norm
            (lowerHeteroChaos_verticalStack_commute (size 0) q tailSize
              (fun e tail => A (Fin.cons e tail)) tailW).symm
        rw [hComm]
        have hOne := lowerVerticalStack_norm_le_sqrtThree_mean (size 0)
          (fun e => lowerHeteroChaos q tailSize
            (fun tail => A (Fin.cons e tail)) tailW)
        simpa [lowerHeteroChaos, tailSize] using hOne
      have hMean :
          lowerHeteroMean q tailSize
            (fun tailW => ‖lowerHeteroChaos q tailSize B tailW‖) ≤
          Real.sqrt 3 * lowerHeteroMean (q + 1) size
            (fun w => ‖lowerHeteroChaos (q + 1) size A w‖) := by
        calc
          _ ≤ lowerHeteroMean q tailSize (fun tailW =>
                Real.sqrt 3 * allSignsMean (size 0) (fun head =>
                  ‖lowerHeteroChaos (q + 1) size A
                    (Fin.cons head tailW)‖)) :=
            lowerHeteroMean_mono q tailSize _ _ hPoint
          _ = Real.sqrt 3 * lowerHeteroMean q tailSize
                (fun tailW => allSignsMean (size 0) (fun head =>
                  ‖lowerHeteroChaos (q + 1) size A
                    (Fin.cons head tailW)‖)) :=
            lowerHeteroMean_const_mul (Real.sqrt 3) q tailSize _
          _ = Real.sqrt 3 * lowerHeteroMean (q + 1) size
                (fun w => ‖lowerHeteroChaos (q + 1) size A w‖) := rfl
      change ‖lowerHeteroFlatten q tailSize B‖ ≤
        Real.sqrt 3 ^ (q + 1) * lowerHeteroMean (q + 1) size
          (fun w => ‖lowerHeteroChaos (q + 1) size A w‖)
      calc
        _ ≤ Real.sqrt 3 ^ q * lowerHeteroMean q tailSize
              (fun tailW => ‖lowerHeteroChaos q tailSize B tailW‖) := hIH
        _ ≤ Real.sqrt 3 ^ q *
              (Real.sqrt 3 * lowerHeteroMean (q + 1) size
                (fun w => ‖lowerHeteroChaos (q + 1) size A w‖)) :=
          mul_le_mul_of_nonneg_left hMean
            (pow_nonneg (Real.sqrt_nonneg _) _)
        _ = Real.sqrt 3 ^ (q + 1) * lowerHeteroMean (q + 1) size
              (fun w => ‖lowerHeteroChaos (q + 1) size A w‖) := by
          rw [pow_succ]
          ring


end GraphMatrixReplica.Model
