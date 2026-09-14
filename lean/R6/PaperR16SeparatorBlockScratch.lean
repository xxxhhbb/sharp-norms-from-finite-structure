import Mathlib

/-!
Abstract model for the deterministic R16 separator flattening. `S` is the
separator assignment type; `L` and `R` are the independent nonseparator row
and column assignment types.  The concrete graph-to-coordinate bijection is
not asserted here.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica.PaperR16.SeparatorScratch

variable {S L R : Type*} [Fintype S] [Fintype L] [Fintype R]
  [DecidableEq S] [DecidableEq R]

def coefficientBlock (w : S → ℝ) : Matrix (L × S) (R × S) ℝ :=
  fun i j => if i.2 = j.2 then w i.2 else 0

def constantBlock (c : ℝ) : Matrix L R ℝ := fun _ _ => c

def onesVec (I : Type*) [Fintype I] : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

theorem norm_onesVec (I : Type*) [Fintype I] :
    ‖onesVec I‖ = Real.sqrt (Fintype.card I : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (onesVec I))]
  congr 1
  simp [EuclideanSpace.real_norm_sq_eq, onesVec]

theorem constantBlock_eq_vecMulVec (c : ℝ) :
    constantBlock (L := L) (R := R) c =
      Matrix.vecMulVec (c • onesVec L) (star (onesVec R)) := by
  ext l r
  simp [constantBlock, onesVec, Matrix.vecMulVec_apply]

theorem norm_constantBlock (c : ℝ) :
    ‖constantBlock (L := L) (R := R) c‖ =
      |c| * Real.sqrt (Fintype.card L : ℝ) *
        Real.sqrt (Fintype.card R : ℝ) := by
  classical
  rw [constantBlock_eq_vecMulVec,
    ← InnerProductSpace.symm_toEuclideanLin_rankOne (c • onesVec L) (onesVec R)]
  rw [Matrix.l2_opNorm_def]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change ‖InnerProductSpace.rankOne ℝ (c • onesVec L) (onesVec R)‖ = _
  rw [InnerProductSpace.norm_rankOne, norm_smul, norm_onesVec, norm_onesVec]
  simp [Real.norm_eq_abs, mul_assoc]

theorem coefficientBlock_apply (w : S → ℝ) (s t : S) (l : L) (r : R) :
    coefficientBlock w (l, s) (r, t) = if s = t then w s else 0 := rfl

theorem coefficientBlock_eq_blockDiagonal (w : S → ℝ) :
    coefficientBlock (L := L) (R := R) w =
      Matrix.blockDiagonal (fun s : S => constantBlock (L := L) (R := R) (w s)) := by
  classical
  ext ⟨l, s⟩ ⟨r, t⟩
  simp [coefficientBlock, constantBlock, Matrix.blockDiagonal_apply]

/-- The shape of the paper's coefficient after coordinate recovery and
deletion of inconsistent coordinates. The premise is intentionally the
missing R16 combinatorial bridge. -/
theorem concrete_coefficient_eq_blockDiagonal
    (A : Matrix (L × S) (R × S) ℝ) (w : S → ℝ)
    (hRecover : ∀ s t l r, A (l, s) (r, t) =
      if s = t then w s else 0) :
    A = Matrix.blockDiagonal
      (fun s : S => constantBlock (L := L) (R := R) (w s)) := by
  rw [← coefficientBlock_eq_blockDiagonal]
  ext ⟨l, s⟩ ⟨r, t⟩
  exact hRecover s t l r

#print axioms coefficientBlock_eq_blockDiagonal
#print axioms concrete_coefficient_eq_blockDiagonal
#print axioms norm_constantBlock

end GraphMatrixReplica.PaperR16.SeparatorScratch
