import Mathlib
import GraphMatrix.Model.SeparatorBlock
import GraphMatrix.Model.ColorLowerCompressionContractive

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.Model.Separator

variable {S L R : Type*} [Fintype S] [Fintype L] [Fintype R]
  [DecidableEq S] [DecidableEq R]

theorem blockDiagonal_mulVec_apply
    (B : S → Matrix L R ℝ) (x : EuclideanSpace ℝ (R × S))
    (l : L) (s : S) :
    (Matrix.blockDiagonal B).mulVec x (l, s) =
      (B s).mulVec (WithLp.toLp 2 (fun r : R => x (r, s))) l := by
  classical
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type]

theorem blockDiagonal_norm_le
    (B : S → Matrix L R ℝ) (K : ℝ)
    (hK : ∀ s, ‖B s‖ ≤ K) (hK0 : 0 ≤ K) :
    ‖Matrix.blockDiagonal B‖ ≤ K := by
  classical
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 ?_
  intro x
  let xs (s : S) : EuclideanSpace ℝ R :=
    WithLp.toLp 2 (fun r : R => x (r, s))
  let ys (s : S) : EuclideanSpace ℝ L :=
    (EuclideanSpace.equiv L ℝ).symm ((B s).mulVec (xs s))
  have hSlice (s : S) : ‖ys s‖ ≤ K * ‖xs s‖ := by
    exact (Matrix.l2_opNorm_mulVec (B s) (xs s)).trans
      (mul_le_mul_of_nonneg_right (hK s) (norm_nonneg _))
  have hSliceSq (s : S) : ‖ys s‖ ^ 2 ≤ K ^ 2 * ‖xs s‖ ^ 2 := by
    nlinarith [hSlice s, sq_nonneg (K - ‖ys s‖),
      norm_nonneg (ys s), norm_nonneg (xs s)]
  have hOutputSq :
      ‖((EuclideanSpace.equiv (L × S) ℝ).symm
          ((Matrix.blockDiagonal B).mulVec x))‖ ^ 2 =
        ∑ s : S, ‖ys s‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro l _
    exact congrArg (fun z : ℝ => z ^ 2)
      (blockDiagonal_mulVec_apply B x l s)
  have hInputSq : ‖x‖ ^ 2 = ∑ s : S, ‖xs s‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [EuclideanSpace.real_norm_sq_eq]
  change ‖((EuclideanSpace.equiv (L × S) ℝ).symm
      ((Matrix.blockDiagonal B).mulVec x))‖ ≤ K * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK0 (norm_nonneg _))).mp
  rw [hOutputSq, mul_pow, hInputSq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun s _ => hSliceSq s)

theorem block_norm_le_blockDiagonal
    (B : S → Matrix L R ℝ) (s : S) :
    ‖B s‖ ≤ ‖Matrix.blockDiagonal B‖ := by
  classical
  let er : L ↪ L × S :=
    ⟨fun l => (l, s), by intro l l' h; exact congrArg Prod.fst h⟩
  let ec : R ↪ R × S :=
    ⟨fun r => (r, s), by intro r r' h; exact congrArg Prod.fst h⟩
  have hSub : (Matrix.blockDiagonal B).submatrix er ec = B s := by
    ext l r
    change (if s = s then B s l r else 0) = B s l r
    simp
  rw [← hSub]
  exact paper_l2_opNorm_submatrix_le er ec (Matrix.blockDiagonal B)

theorem blockDiagonal_norm_eq_max [Nonempty S]
    (B : S → Matrix L R ℝ) :
    ‖Matrix.blockDiagonal B‖ =
      Finset.univ.sup' Finset.univ_nonempty (fun s : S => ‖B s‖) := by
  classical
  let K := Finset.univ.sup' Finset.univ_nonempty (fun s : S => ‖B s‖)
  apply le_antisymm
  · apply blockDiagonal_norm_le B K
    · intro s
      exact Finset.le_sup' (fun s : S => ‖B s‖) (Finset.mem_univ s)
    · exact (norm_nonneg (B (Classical.choice inferInstance))).trans
        (Finset.le_sup' (fun s : S => ‖B s‖)
          (Finset.mem_univ (Classical.choice inferInstance)))
  · apply Finset.sup'_le
    intro s hs
    exact block_norm_le_blockDiagonal B s

set_option maxHeartbeats 1000000

/-- Exact separator-block formula when the separator assignment type is
nonempty. This is `sqrt(card L * card R) * max |w|` with the two square-root
factors left uncombined in the formal statement. -/
theorem coefficientBlock_norm_eq [Nonempty S] (w : S → ℝ) :
    ‖coefficientBlock (L := L) (R := R) w‖ =
      (Finset.univ.sup' Finset.univ_nonempty (fun s : S => |w s|)) *
        Real.sqrt (Fintype.card L : ℝ) *
        Real.sqrt (Fintype.card R : ℝ) := by
  classical
  let M := Finset.univ.sup' Finset.univ_nonempty (fun s : S => |w s|)
  rw [coefficientBlock_eq_blockDiagonal]
  have hM : ∀ s : S, |w s| ≤ M := by
    intro s
    exact Finset.le_sup' (fun s : S => |w s|) (Finset.mem_univ s)
  have hTop : ‖Matrix.blockDiagonal
      (fun s : S => constantBlock (L := L) (R := R) (w s))‖ ≤
      M * Real.sqrt (Fintype.card L : ℝ) *
        Real.sqrt (Fintype.card R : ℝ) := by
    apply blockDiagonal_norm_le
    · intro s
      rw [norm_constantBlock]
      gcongr
      exact hM s
    · have hs : (0 : ℝ) ≤ M :=
        (abs_nonneg (w (Classical.choice inferInstance))).trans
          (hM (Classical.choice inferInstance))
      positivity
  have hBot : M * Real.sqrt (Fintype.card L : ℝ) *
        Real.sqrt (Fintype.card R : ℝ) ≤
      ‖Matrix.blockDiagonal
        (fun s : S => constantBlock (L := L) (R := R) (w s))‖ := by
    obtain ⟨s, _, hs⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun s : S => |w s|)
    change M = |w s| at hs
    calc
      M * Real.sqrt (Fintype.card L : ℝ) *
          Real.sqrt (Fintype.card R : ℝ) =
          ‖constantBlock (L := L) (R := R) (w s)‖ := by
            rw [norm_constantBlock, hs]
      _ ≤ _ := block_norm_le_blockDiagonal
        (S := S) (L := L) (R := R)
        (fun t : S => constantBlock (L := L) (R := R) (w t)) s
  exact le_antisymm hTop hBot

theorem coefficientBlock_norm_eq_sqrt_product [Nonempty S] (w : S → ℝ) :
    ‖coefficientBlock (L := L) (R := R) w‖ =
      Real.sqrt ((Fintype.card L : ℝ) * (Fintype.card R : ℝ)) *
        Finset.univ.sup' Finset.univ_nonempty (fun s : S => |w s|) := by
  rw [coefficientBlock_norm_eq, Real.sqrt_mul (by positivity)]
  ring

/-- The zero-dimensional separator-assignment case. `max |w|` is not used
because there is no separator assignment to maximize over. -/
theorem coefficientBlock_norm_eq_zero_of_isEmpty [IsEmpty S] (w : S → ℝ) :
    ‖coefficientBlock (L := L) (R := R) w‖ = 0 := by
  have hZero : coefficientBlock (L := L) (R := R) w = 0 := by
    ext i j
    exact isEmptyElim i.2
  rw [hZero, norm_zero]


end GraphMatrixReplica.Model.Separator
