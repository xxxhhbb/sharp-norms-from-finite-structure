import GraphMatrix.Model.LowerStackingHeterogeneous

/-! A dependent direction vector makes each row/column stacking branch
definitionally visible to Lean. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model

inductive lowerMixDir : ℕ → Type
  | nil : lowerMixDir 0
  | cons {q : ℕ} : Bool → lowerMixDir q → lowerMixDir (q + 1)

def lowerMixDirOfFn : (q : ℕ) → (Fin q → Bool) → lowerMixDir q
  | 0, _ => .nil
  | q + 1, dir => .cons (dir 0)
      (lowerMixDirOfFn q (fun g => dir g.succ))

def lowerMixRowsD :
    (q : ℕ) → (size : Fin q → ℕ) → lowerMixDir q → Type u → Type u
  | 0, _, .nil, ι => ι
  | q + 1, size, .cons true tail, ι =>
      lowerMixRowsD q (fun g => size g.succ) tail (Fin (size 0) × ι)
  | q + 1, size, .cons false tail, ι =>
      lowerMixRowsD q (fun g => size g.succ) tail ι

def lowerMixColsD :
    (q : ℕ) → (size : Fin q → ℕ) → lowerMixDir q → Type u → Type u
  | 0, _, .nil, κ => κ
  | q + 1, size, .cons true tail, κ =>
      lowerMixColsD q (fun g => size g.succ) tail κ
  | q + 1, size, .cons false tail, κ =>
      lowerMixColsD q (fun g => size g.succ) tail (Fin (size 0) × κ)

instance lowerMixRowsDFintype :
    (q : ℕ) → (size : Fin q → ℕ) → (d : lowerMixDir q) →
      (ι : Type u) → [Fintype ι] → Fintype (lowerMixRowsD q size d ι)
  | 0, _, .nil, ι, _ => by simpa [lowerMixRowsD] using (inferInstance : Fintype ι)
  | q + 1, size, .cons true tail, ι, _ => by
      change Fintype (lowerMixRowsD q (fun g => size g.succ) tail (Fin (size 0) × ι))
      exact lowerMixRowsDFintype q (fun g => size g.succ) tail (Fin (size 0) × ι)
  | q + 1, size, .cons false tail, ι, _ => by
      change Fintype (lowerMixRowsD q (fun g => size g.succ) tail ι)
      exact lowerMixRowsDFintype q (fun g => size g.succ) tail ι

instance lowerMixColsDFintype :
    (q : ℕ) → (size : Fin q → ℕ) → (d : lowerMixDir q) →
      (κ : Type u) → [Fintype κ] → Fintype (lowerMixColsD q size d κ)
  | 0, _, .nil, κ, _ => by simpa [lowerMixColsD] using (inferInstance : Fintype κ)
  | q + 1, size, .cons true tail, κ, _ => by
      change Fintype (lowerMixColsD q (fun g => size g.succ) tail κ)
      exact lowerMixColsDFintype q (fun g => size g.succ) tail κ
  | q + 1, size, .cons false tail, κ, _ => by
      change Fintype (lowerMixColsD q (fun g => size g.succ) tail (Fin (size 0) × κ))
      exact lowerMixColsDFintype q (fun g => size g.succ) tail (Fin (size 0) × κ)

instance lowerMixRowsDDecidableEq :
    (q : ℕ) → (size : Fin q → ℕ) → (d : lowerMixDir q) →
      (ι : Type u) → [DecidableEq ι] → DecidableEq (lowerMixRowsD q size d ι)
  | 0, _, .nil, ι, _ => by simpa [lowerMixRowsD] using (inferInstance : DecidableEq ι)
  | q + 1, size, .cons true tail, ι, _ => by
      change DecidableEq (lowerMixRowsD q (fun g => size g.succ) tail (Fin (size 0) × ι))
      exact lowerMixRowsDDecidableEq q (fun g => size g.succ) tail (Fin (size 0) × ι)
  | q + 1, size, .cons false tail, ι, _ => by
      change DecidableEq (lowerMixRowsD q (fun g => size g.succ) tail ι)
      exact lowerMixRowsDDecidableEq q (fun g => size g.succ) tail ι

instance lowerMixColsDDecidableEq :
    (q : ℕ) → (size : Fin q → ℕ) → (d : lowerMixDir q) →
      (κ : Type u) → [DecidableEq κ] → DecidableEq (lowerMixColsD q size d κ)
  | 0, _, .nil, κ, _ => by simpa [lowerMixColsD] using (inferInstance : DecidableEq κ)
  | q + 1, size, .cons true tail, κ, _ => by
      change DecidableEq (lowerMixColsD q (fun g => size g.succ) tail κ)
      exact lowerMixColsDDecidableEq q (fun g => size g.succ) tail κ
  | q + 1, size, .cons false tail, κ, _ => by
      change DecidableEq (lowerMixColsD q (fun g => size g.succ) tail (Fin (size 0) × κ))
      exact lowerMixColsDDecidableEq q (fun g => size g.succ) tail (Fin (size 0) × κ)

def lowerMixFlattenD (q : ℕ) (size : Fin q → ℕ) (d : lowerMixDir q)
    {ι κ : Type*} (A : lowerHeteroIndex q size → Matrix ι κ ℝ) :
    Matrix (lowerMixRowsD q size d ι) (lowerMixColsD q size d κ) ℝ :=
  match q, d with
  | 0, .nil => A (fun g => Fin.elim0 g)
  | q + 1, .cons true tail =>
      lowerMixFlattenD q (fun g => size g.succ) tail
        (fun idx => lowerVerticallyStackedMatrix (size 0)
          (fun e => A (Fin.cons e idx)))
  | q + 1, .cons false tail =>
      lowerMixFlattenD q (fun g => size g.succ) tail
        (fun idx => lowerHorizontallyStackedMatrix (size 0)
          (fun e => A (Fin.cons e idx)))

theorem lowerHorizontalStack_signSum_commuteD
    {ι κ : Type*} (m n : ℕ)
    (A : Fin m → Fin n → Matrix ι κ ℝ)
    (w : Fin n → Bool) :
    lowerHorizontallyStackedMatrix m
        (fun e => lowerMatrixSignSum n (A e) w) =
      lowerMatrixSignSum n (fun e' =>
        lowerHorizontallyStackedMatrix m
          (fun e => A e e')) w := by
  ext i ⟨e, j⟩
  rfl

theorem lowerHorizontalStack_applyD
    {ι κ : Type*} (n : ℕ) (A : Fin n → Matrix ι κ ℝ)
    (i : ι) (e : Fin n) (j : κ) :
    lowerHorizontallyStackedMatrix n A i (e, j) = A e i j := rfl

theorem lowerHorizontalStack_applyPairD
    {ι κ : Type*} (n : ℕ) (A : Fin n → Matrix ι κ ℝ)
    (i : ι) (p : Fin n × κ) :
    lowerHorizontallyStackedMatrix n A i p = A p.1 i p.2 := by
  cases p
  rfl

theorem lowerHeteroChaos_horizontalStack_commuteD (m : ℕ) :
    ∀ q (size : Fin q → ℕ) {ι κ : Type*}
      (A : Fin m → lowerHeteroIndex q size → Matrix ι κ ℝ)
      (w : lowerHeteroNoise q size),
      lowerHorizontallyStackedMatrix m
          (fun e => lowerHeteroChaos q size (A e) w) =
        lowerHeteroChaos q size
          (fun tail => lowerHorizontallyStackedMatrix m
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
      change lowerHorizontallyStackedMatrix m
          (fun e => lowerMatrixSignSum (size 0)
            (fun e' => lowerHeteroChaos q tailSize (C e e') tailW)
            (w 0)) =
        lowerMatrixSignSum (size 0)
          (fun e' => lowerHeteroChaos q tailSize
            (fun tail => lowerHorizontallyStackedMatrix m
              (fun e => C e e' tail)) tailW) (w 0)
      calc
        _ = lowerMatrixSignSum (size 0) (fun e' =>
            lowerHorizontallyStackedMatrix m
              (fun e => lowerHeteroChaos q tailSize (C e e') tailW))
              (w 0) := by
          exact lowerHorizontalStack_signSum_commuteD m (size 0)
            (fun e e' => lowerHeteroChaos q tailSize (C e e') tailW) (w 0)
        _ = lowerMatrixSignSum (size 0)
            (fun e' => lowerHeteroChaos q tailSize
              (fun tail => lowerHorizontallyStackedMatrix m
                (fun e => C e e' tail)) tailW) (w 0) := by
          congr 1
          funext e'
          exact ih tailSize (fun e tail => C e e' tail) tailW

theorem lowerHorizontalStack_norm_le_sqrtThree_meanD
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (n : ℕ) (A : Fin n → Matrix ι κ ℝ) :
    ‖lowerHorizontallyStackedMatrix n A‖ ≤
      Real.sqrt 3 * allSignsMean n
        (fun w => ‖lowerMatrixSignSum n A w‖) :=
  (le_max_right _ _).trans (lowerOneGroupStackMax_le_sqrtThree_mean n A)

/-- Every finite direction vector gives the same one-`√3`-per-group
lower stacking estimate, with separate sizes for all sign groups. -/
theorem lowerMixFlattenD_norm_le :
    ∀ q (size : Fin q → ℕ) (d : lowerMixDir q) {ι κ : Type*}
      [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (A : lowerHeteroIndex q size → Matrix ι κ ℝ),
      ‖lowerMixFlattenD q size d A‖ ≤
        Real.sqrt 3 ^ q * lowerHeteroMean q size
          (fun w => ‖lowerHeteroChaos q size A w‖) := by
  intro q
  induction q with
  | zero =>
      intro size d ι κ _ _ _ _ A
      cases d
      simp [lowerMixFlattenD, lowerHeteroMean, lowerHeteroChaos]
      exact le_rfl
  | succ q ih =>
      intro size d ι κ _ _ _ _ A
      cases d with
      | cons b tail =>
          cases b with
          | true =>
              let tailSize : Fin q → ℕ := fun g => size g.succ
              let B : lowerHeteroIndex q tailSize →
                  Matrix (Fin (size 0) × ι) κ ℝ :=
                fun idx => lowerVerticallyStackedMatrix (size 0)
                  (fun e => A (Fin.cons e idx))
              have hIH := ih tailSize tail B
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
                          (fun idx => A (Fin.cons e idx)) tailW)‖ := by
                  exact congrArg norm
                    (lowerHeteroChaos_verticalStack_commute (size 0) q tailSize
                      (fun e idx => A (Fin.cons e idx)) tailW).symm
                rw [hComm]
                have hOne := lowerVerticalStack_norm_le_sqrtThree_mean (size 0)
                  (fun e => lowerHeteroChaos q tailSize
                    (fun idx => A (Fin.cons e idx)) tailW)
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
              change ‖lowerMixFlattenD q tailSize tail B‖ ≤
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
          | false =>
              let tailSize : Fin q → ℕ := fun g => size g.succ
              let B : lowerHeteroIndex q tailSize →
                  Matrix ι (Fin (size 0) × κ) ℝ :=
                fun idx => lowerHorizontallyStackedMatrix (size 0)
                  (fun e => A (Fin.cons e idx))
              have hIH := ih tailSize tail B
              have hPoint : ∀ tailW : lowerHeteroNoise q tailSize,
                  ‖lowerHeteroChaos q tailSize B tailW‖ ≤
                    Real.sqrt 3 * allSignsMean (size 0) (fun head =>
                      ‖lowerHeteroChaos (q + 1) size A
                        (Fin.cons head tailW)‖) := by
                intro tailW
                have hComm :
                    ‖lowerHeteroChaos q tailSize B tailW‖ =
                      ‖lowerHorizontallyStackedMatrix (size 0) (fun e =>
                        lowerHeteroChaos q tailSize
                          (fun idx => A (Fin.cons e idx)) tailW)‖ := by
                  exact congrArg norm
                    (lowerHeteroChaos_horizontalStack_commuteD (size 0) q tailSize
                      (fun e idx => A (Fin.cons e idx)) tailW).symm
                rw [hComm]
                have hOne := lowerHorizontalStack_norm_le_sqrtThree_meanD (size 0)
                  (fun e => lowerHeteroChaos q tailSize
                    (fun idx => A (Fin.cons e idx)) tailW)
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
              change ‖lowerMixFlattenD q tailSize tail B‖ ≤
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

/-- Decode a final row/column pair into exactly one original tensor entry.
The base row and column remain on opposite sides. -/
def lowerMixDecodeD (q : ℕ) (size : Fin q → ℕ) (d : lowerMixDir q)
    {ι κ : Type*}
    (r : lowerMixRowsD q size d ι)
    (c : lowerMixColsD q size d κ) :
    lowerHeteroIndex q size × ι × κ :=
  match q, d with
  | 0, .nil => ((fun g => Fin.elim0 g), r, c)
  | q + 1, .cons true tail =>
      let x := lowerMixDecodeD q (fun g => size g.succ) tail r c
      (Fin.cons x.2.1.1 x.1, x.2.1.2, x.2.2)
  | q + 1, .cons false tail =>
      let x := lowerMixDecodeD q (fun g => size g.succ) tail r c
      (Fin.cons x.2.2.1 x.1, x.2.1, x.2.2.2)

/-- The mixed flattening has no averaging or summation in its entries:
each entry is exactly its decoded original coefficient. -/
theorem lowerMixFlattenD_apply :
    ∀ q (size : Fin q → ℕ) (d : lowerMixDir q)
      {ι κ : Type*}
      (A : lowerHeteroIndex q size → Matrix ι κ ℝ)
      (r : lowerMixRowsD q size d ι)
      (c : lowerMixColsD q size d κ),
      lowerMixFlattenD q size d A r c =
        A (lowerMixDecodeD q size d r c).1
          (lowerMixDecodeD q size d r c).2.1
          (lowerMixDecodeD q size d r c).2.2 := by
  intro q
  induction q with
  | zero =>
      intro size d ι κ A r c
      cases d
      rfl
  | succ q ih =>
      intro size d ι κ A r c
      cases d with
      | cons b tail =>
          cases b with
          | true =>
              let tailSize : Fin q → ℕ := fun g => size g.succ
              let B : lowerHeteroIndex q tailSize →
                  Matrix (Fin (size 0) × ι) κ ℝ :=
                fun idx => lowerVerticallyStackedMatrix (size 0)
                  (fun e => A (Fin.cons e idx))
              have h := ih tailSize tail B r c
              change lowerMixFlattenD q tailSize tail B r c =
                A (Fin.cons
                  (lowerMixDecodeD q tailSize tail r c).2.1.1
                  (lowerMixDecodeD q tailSize tail r c).1)
                  (lowerMixDecodeD q tailSize tail r c).2.1.2
                  (lowerMixDecodeD q tailSize tail r c).2.2
              simpa only [B, lowerVerticallyStackedMatrix] using h
          | false =>
              let tailSize : Fin q → ℕ := fun g => size g.succ
              let B : lowerHeteroIndex q tailSize →
                  Matrix ι (Fin (size 0) × κ) ℝ :=
                fun idx => lowerHorizontallyStackedMatrix (size 0)
                  (fun e => A (Fin.cons e idx))
              have h := ih tailSize tail B r c
              change lowerMixFlattenD q tailSize tail B r c =
                A (Fin.cons
                  (lowerMixDecodeD q tailSize tail r c).2.2.1
                  (lowerMixDecodeD q tailSize tail r c).1)
                  (lowerMixDecodeD q tailSize tail r c).2.1
                  (lowerMixDecodeD q tailSize tail r c).2.2.2
              simpa only [B, lowerHorizontalStack_applyPairD] using h

/-- Public direction selector: `true` stacks on rows, `false` on columns. -/
abbrev lowerMixedRows (q : ℕ) (size : Fin q → ℕ)
    (dir : Fin q → Bool) (ι : Type u) : Type u :=
  lowerMixRowsD q size (lowerMixDirOfFn q dir) ι

abbrev lowerMixedCols (q : ℕ) (size : Fin q → ℕ)
    (dir : Fin q → Bool) (κ : Type u) : Type u :=
  lowerMixColsD q size (lowerMixDirOfFn q dir) κ

def lowerMixedFlatten (q : ℕ) (size : Fin q → ℕ)
    (dir : Fin q → Bool) {ι κ : Type*}
    (A : lowerHeteroIndex q size → Matrix ι κ ℝ) :
    Matrix (lowerMixedRows q size dir ι)
      (lowerMixedCols q size dir κ) ℝ :=
  lowerMixFlattenD q size (lowerMixDirOfFn q dir) A

theorem lowerMixedFlatten_norm_le
    (q : ℕ) (size : Fin q → ℕ) (dir : Fin q → Bool)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : lowerHeteroIndex q size → Matrix ι κ ℝ) :
    ‖lowerMixedFlatten q size dir A‖ ≤
      Real.sqrt 3 ^ q * lowerHeteroMean q size
        (fun w => ‖lowerHeteroChaos q size A w‖) :=
  lowerMixFlattenD_norm_le q size (lowerMixDirOfFn q dir) A

theorem lowerMixedFlatten_apply
    (q : ℕ) (size : Fin q → ℕ) (dir : Fin q → Bool)
    {ι κ : Type*}
    (A : lowerHeteroIndex q size → Matrix ι κ ℝ)
    (r : lowerMixedRows q size dir ι)
    (c : lowerMixedCols q size dir κ) :
    lowerMixedFlatten q size dir A r c =
      A (lowerMixDecodeD q size (lowerMixDirOfFn q dir) r c).1
        (lowerMixDecodeD q size (lowerMixDirOfFn q dir) r c).2.1
        (lowerMixDecodeD q size (lowerMixDirOfFn q dir) r c).2.2 :=
  lowerMixFlattenD_apply q size (lowerMixDirOfFn q dir) A r c


end GraphMatrixReplica.Model
