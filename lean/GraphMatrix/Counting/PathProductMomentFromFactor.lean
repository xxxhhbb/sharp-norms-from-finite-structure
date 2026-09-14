import GraphMatrix.Counting.PathBoundaryProductProof
import GraphMatrix.Counting.PathNoiseProductLaw
import GraphMatrix.Counting.IidSignMatrixHighMoment
import GraphMatrix.Counting.PartiteRealTransfer
import GraphMatrix.RademacherOpenWordContraction

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

private theorem c079_sign_cast_eq_neg_paperSign (b : Bool) :
    (Rat.castHom ℝ) (rademacherSign b : ℚ) = -paperSign b := by
  cases b <;> norm_num [rademacherSign, paperSign]

private theorem c079PathEdgeMatrix_cast_eq_neg_iid
    (ell m : ℕ)
    (ε : JointEdgeSignSample (c079CanonicalPathDimension ell m))
    (e : Fin ell) :
    (c079PathEdgeMatrix ell m ε e).map (Rat.castHom ℝ) =
      -c079IidSignMatrix m (ε e) := by
  ext i j
  simpa [c079PathEdgeMatrix, c079IidSignMatrix,
    c079CanonicalPathDimension, c079CanonicalPathShape] using
    c079_sign_cast_eq_neg_paperSign (ε e (i, j))

private theorem c079_map_list_prod {m : ℕ}
    (xs : List (Matrix (Fin m) (Fin m) ℚ)) :
    xs.prod.map (Rat.castHom ℝ) =
      (xs.map (fun X => X.map (Rat.castHom ℝ))).prod := by
  classical
  induction xs with
  | nil => simp
  | cons X xs ih =>
      simp only [List.prod_cons, List.map_cons]
      rw [Matrix.map_mul, ih]

private theorem c079_real_matrix_one_norm_le (m : ℕ) :
    ‖(1 : Matrix (Fin m) (Fin m) ℝ)‖ ≤ 1 := by
  calc
    ‖(1 : Matrix (Fin m) (Fin m) ℝ)‖ =
        ‖Matrix.diagonal (fun _ : Fin m => (1 : ℝ))‖ := by simp
    _ = ‖(fun _ : Fin m => (1 : ℝ))‖ :=
      Matrix.l2_opNorm_diagonal _
    _ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).2
      intro i
      simp

private theorem c079_real_list_prod_norm_le {m : ℕ}
    (xs : List (Matrix (Fin m) (Fin m) ℝ)) :
    ‖xs.prod‖ ≤ (xs.map (fun X => ‖X‖)).prod := by
  classical
  induction xs with
  | nil => simpa using c079_real_matrix_one_norm_le m
  | cons X xs ih =>
      simp only [List.prod_cons, List.map_cons]
      exact (Matrix.l2_opNorm_mul X xs.prod).trans
        (mul_le_mul_of_nonneg_left ih (norm_nonneg X))

private theorem c079_real_matrix_pow_norm_le {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (q : ℕ) :
    ‖M ^ q‖ ≤ ‖M‖ ^ q := by
  induction q with
  | zero => simpa using c079_real_matrix_one_norm_le m
  | succ q ih =>
      rw [pow_succ, pow_succ]
      exact (Matrix.l2_opNorm_mul (M ^ q) M).trans
        (mul_le_mul_of_nonneg_right ih (norm_nonneg M))

private theorem c079_real_gramTrace_le_card_norm_pow {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (q : ℕ) :
    Matrix.trace ((M * M.transpose) ^ q) ≤
      (m : ℝ) * ‖M‖ ^ (2 * q) := by
  have hTranspose : ‖M.transpose‖ = ‖M‖ := by
    simpa using Matrix.l2_opNorm_conjTranspose M
  have hGram : ‖M * M.transpose‖ ≤ ‖M‖ * ‖M.transpose‖ :=
    Matrix.l2_opNorm_mul M M.transpose
  have hPower : ‖(M * M.transpose) ^ q‖ ≤ ‖M‖ ^ (2 * q) := by
    calc
      _ ≤ ‖M * M.transpose‖ ^ q := c079_real_matrix_pow_norm_le _ q
      _ ≤ (‖M‖ * ‖M.transpose‖) ^ q :=
        (pow_le_pow_left₀ (norm_nonneg _) hGram) q
      _ = ‖M‖ ^ (2 * q) := by
        rw [hTranspose, mul_pow, ← pow_add]
        congr 1
        omega
  calc
    Matrix.trace ((M * M.transpose) ^ q) ≤
        |Matrix.trace ((M * M.transpose) ^ q)| := le_abs_self _
    _ ≤ (m : ℝ) * ‖(M * M.transpose) ^ q‖ := by
      simpa using abs_matrix_trace_le_card_mul_l2_opNorm
        ((M * M.transpose) ^ q)
    _ ≤ (m : ℝ) * ‖M‖ ^ (2 * q) :=
      mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg _)

/-- The real cast of the canonical rational product is norm-controlled by
the independent edge factors.  It also covers the empty product. -/
theorem c079CanonicalPathProduct_cast_norm_le_factorProduct
    (ell m : ℕ)
    (ε : JointEdgeSignSample (c079CanonicalPathDimension ell m)) :
    ‖(c079CanonicalPathMatrixProduct ell m ε).map (Rat.castHom ℝ)‖ ≤
      ∏ e : Fin ell, ‖c079IidSignMatrix m (ε e)‖ := by
  classical
  unfold c079CanonicalPathMatrixProduct c079OrderedMatrixProduct
  rw [c079_map_list_prod]
  calc
    _ ≤ (((List.ofFn (fun e : Fin ell => c079PathEdgeMatrix ell m ε e)).map
        (fun X => X.map (Rat.castHom ℝ))).map (fun X => ‖X‖)).prod :=
      c079_real_list_prod_norm_le _
    _ = ∏ e : Fin ell, ‖c079IidSignMatrix m (ε e)‖ := by
      simp only [List.map_ofFn, List.prod_ofFn]
      apply Finset.prod_congr rfl
      intro e _
      change ‖(c079PathEdgeMatrix ell m ε e).map (Rat.castHom ℝ)‖ =
        ‖c079IidSignMatrix m (ε e)‖
      rw [c079PathEdgeMatrix_cast_eq_neg_iid]
      simp

private theorem c079_real_pathGramTrace_eq_cast
    (ell m q : ℕ)
    (ε : JointEdgeSignSample (c079CanonicalPathDimension ell m)) :
    Matrix.trace
        (((c079CanonicalPathMatrixProduct ell m ε).map (Rat.castHom ℝ) *
          ((c079CanonicalPathMatrixProduct ell m ε).map
            (Rat.castHom ℝ)).transpose) ^ q) =
      ((Matrix.trace
        ((c079CanonicalPathMatrixProduct ell m ε *
          (c079CanonicalPathMatrixProduct ell m ε).transpose) ^ q) : ℚ) : ℝ) := by
  classical
  let M := c079CanonicalPathMatrixProduct ell m ε
  change Matrix.trace (((M.map (Rat.castHom ℝ)) *
      (M.map (Rat.castHom ℝ)).transpose) ^ q) =
    (Rat.castHom ℝ) (Matrix.trace ((M * M.transpose) ^ q))
  rw [← Matrix.transpose_map, ← Matrix.map_mul]
  have hMapPow : ∀ k : ℕ,
      ((M * M.transpose) ^ k).map (Rat.castHom ℝ) =
        ((M * M.transpose).map (Rat.castHom ℝ)) ^ k := by
    intro k
    induction k with
    | zero =>
        ext i j
        by_cases hij : i = j <;> simp [hij]
    | succ k ih => rw [pow_succ, pow_succ, Matrix.map_mul, ih]
  rw [← hMapPow q]
  exact (AddMonoidHom.map_trace (Rat.castHom ℝ)
    ((M * M.transpose) ^ q)).symm

private theorem c079_pathTraceAverage_cast_eq_paperMean
    (ell m q : ℕ) :
    (((∑ ε : JointEdgeSignSample (c079CanonicalPathDimension ell m),
        Matrix.trace
          ((c079CanonicalPathMatrixProduct ell m ε *
            (c079CanonicalPathMatrixProduct ell m ε).transpose) ^ q)) /
      Fintype.card (JointEdgeSignSample (c079CanonicalPathDimension ell m)) :
        ℚ) : ℝ) =
      paperMean (fun ε : JointEdgeSignSample
          (c079CanonicalPathDimension ell m) =>
        Matrix.trace
          (((c079CanonicalPathMatrixProduct ell m ε).map (Rat.castHom ℝ) *
            ((c079CanonicalPathMatrixProduct ell m ε).map
              (Rat.castHom ℝ)).transpose) ^ q)) := by
  classical
  unfold paperMean
  simp_rw [c079_real_pathGramTrace_eq_cast]
  push_cast
  rw [div_eq_mul_inv]
  ring

/-- The full canonical path trace moment needs only one independent-edge
operator-norm moment.  The bound also holds when there are no path edges. -/
theorem c079CanonicalPath_productMoment_le_of_iidMoment
    (ell m q : ℕ) (B : ℝ)
    (hFactor : paperMean (fun w : Fin m × Fin m → Bool =>
      ‖c079IidSignMatrix m w‖ ^ (2 * q)) ≤ B) :
    (((∑ ε : JointEdgeSignSample (c079CanonicalPathDimension ell m),
        Matrix.trace
          ((c079CanonicalPathMatrixProduct ell m ε *
            (c079CanonicalPathMatrixProduct ell m ε).transpose) ^ q)) /
      Fintype.card (JointEdgeSignSample (c079CanonicalPathDimension ell m)) :
        ℚ) : ℝ) ≤ (m : ℝ) * B ^ ell := by
  classical
  rw [c079_pathTraceAverage_cast_eq_paperMean]
  have hPointwise : ∀ ε : JointEdgeSignSample
      (c079CanonicalPathDimension ell m),
      Matrix.trace
        (((c079CanonicalPathMatrixProduct ell m ε).map (Rat.castHom ℝ) *
          ((c079CanonicalPathMatrixProduct ell m ε).map
            (Rat.castHom ℝ)).transpose) ^ q) ≤
        (m : ℝ) * ∏ e : Fin ell,
          ‖c079IidSignMatrix m (ε e)‖ ^ (2 * q) := by
    intro ε
    let H := (c079CanonicalPathMatrixProduct ell m ε).map (Rat.castHom ℝ)
    have hNorm := c079CanonicalPathProduct_cast_norm_le_factorProduct ell m ε
    have hPow : ‖H‖ ^ (2 * q) ≤
        (∏ e : Fin ell, ‖c079IidSignMatrix m (ε e)‖) ^ (2 * q) :=
      (pow_le_pow_left₀ (norm_nonneg H) hNorm) (2 * q)
    calc
      _ ≤ (m : ℝ) * ‖H‖ ^ (2 * q) :=
        c079_real_gramTrace_le_card_norm_pow H q
      _ ≤ (m : ℝ) *
          (∏ e : Fin ell, ‖c079IidSignMatrix m (ε e)‖) ^ (2 * q) :=
        mul_le_mul_of_nonneg_left hPow (Nat.cast_nonneg _)
      _ = (m : ℝ) * ∏ e : Fin ell,
          ‖c079IidSignMatrix m (ε e)‖ ^ (2 * q) := by
        rw [Finset.prod_pow]
  calc
    paperMean (fun ε : JointEdgeSignSample
        (c079CanonicalPathDimension ell m) =>
      Matrix.trace
        (((c079CanonicalPathMatrixProduct ell m ε).map (Rat.castHom ℝ) *
          ((c079CanonicalPathMatrixProduct ell m ε).map
            (Rat.castHom ℝ)).transpose) ^ q)) ≤
        paperMean (fun ε : JointEdgeSignSample
          (c079CanonicalPathDimension ell m) =>
          (m : ℝ) * ∏ e : Fin ell,
            ‖c079IidSignMatrix m (ε e)‖ ^ (2 * q)) :=
      paperMean_mono hPointwise
    _ = (m : ℝ) * paperMean (fun ε : JointEdgeSignSample
          (c079CanonicalPathDimension ell m) =>
          ∏ e : Fin ell, ‖c079IidSignMatrix m (ε e)‖ ^ (2 * q)) := by
      rw [paperMean_const_mul]
    _ = (m : ℝ) * ∏ e : Fin ell,
          paperMean (fun w : Fin m × Fin m → Bool =>
            ‖c079IidSignMatrix m w‖ ^ (2 * q)) := by
      congr 1
      simpa [c079CanonicalPathDimension, c079CanonicalPathShape] using
        (c079PathNoiseProductLaw ell m
          (fun _e w => ‖c079IidSignMatrix m w‖ ^ (2 * q)))
    _ ≤ (m : ℝ) * B ^ ell := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        (∏ e : Fin ell, paperMean (fun w : Fin m × Fin m → Bool =>
          ‖c079IidSignMatrix m w‖ ^ (2 * q))) ≤
            ∏ _e : Fin ell, B := by
          apply Finset.prod_le_prod
          · intro e _
            have h := paperMean_mono (fun w : Fin m × Fin m → Bool =>
              pow_nonneg (norm_nonneg (c079IidSignMatrix m w)) (2 * q))
            simpa [paperMean] using h
          · intro e _
            exact hFactor
        _ = B ^ ell := by simp

private theorem c079_iidFactorScale_product_power
    (m q ell : ℕ) :
    (m : ℝ) *
        ((12 * Real.sqrt (m : ℝ)) ^ (2 * q)) ^ ell =
      (12 : ℝ) ^ (2 * q * ell) * (m : ℝ) ^ (q * ell + 1) := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  calc
    (m : ℝ) * ((12 * Real.sqrt (m : ℝ)) ^ (2 * q)) ^ ell =
        (m : ℝ) * ((12 * Real.sqrt (m : ℝ)) ^ 2) ^ (q * ell) := by
      rw [← pow_mul, show 2 * q * ell = 2 * (q * ell) by ring, pow_mul]
    _ = (m : ℝ) * ((12 : ℝ) ^ 2 * (m : ℝ)) ^ (q * ell) := by
      rw [mul_pow, Real.sq_sqrt hm]
    _ = (12 : ℝ) ^ (2 * q * ell) * (m : ℝ) ^ (q * ell + 1) := by
      rw [mul_pow, ← pow_mul, show 2 * (q * ell) = 2 * q * ell by ring,
        pow_succ]
      ring

/-- A single iid sign-matrix `2q`-moment estimate supplies the exact rational
auxiliary product-moment input used by the path-state count.  The only
unproved premise is one single-factor inequality, not a path estimate. -/
theorem c079CanonicalPath_productMoment_le_of_iidHighMoment
    (ell q : ℕ)
    (hFactor : paperMean (fun w : Fin (2 * q ^ 2) × Fin (2 * q ^ 2) → Bool =>
      ‖c079IidSignMatrix (2 * q ^ 2) w‖ ^ (2 * q)) ≤
        (12 * Real.sqrt ((2 * q ^ 2 : ℕ) : ℝ)) ^ (2 * q)) :
    ((∑ ε : JointEdgeSignSample
          (c079CanonicalPathDimension ell (2 * q ^ 2)),
        Matrix.trace
          ((c079CanonicalPathMatrixProduct ell (2 * q ^ 2) ε *
            (c079CanonicalPathMatrixProduct ell (2 * q ^ 2) ε).transpose) ^ q)) /
      Fintype.card
        (JointEdgeSignSample (c079CanonicalPathDimension ell (2 * q ^ 2)))) ≤
      (12 : ℚ) ^ (2 * q * ell) *
        ((2 * q ^ 2 : ℕ) : ℚ) ^ (q * ell + 1) := by
  let m : ℕ := 2 * q ^ 2
  have hReal := c079CanonicalPath_productMoment_le_of_iidMoment
    ell m q ((12 * Real.sqrt (m : ℝ)) ^ (2 * q)) hFactor
  have hScale := c079_iidFactorScale_product_power m q ell
  have hCast :
      (((12 : ℚ) ^ (2 * q * ell) *
        (m : ℚ) ^ (q * ell + 1)) : ℝ) =
        (m : ℝ) * ((12 * Real.sqrt (m : ℝ)) ^ (2 * q)) ^ ell := by
    push_cast
    exact hScale.symm
  have hReal' :
      ((((∑ ε : JointEdgeSignSample (c079CanonicalPathDimension ell m),
          Matrix.trace
            ((c079CanonicalPathMatrixProduct ell m ε *
              (c079CanonicalPathMatrixProduct ell m ε).transpose) ^ q)) /
        Fintype.card (JointEdgeSignSample (c079CanonicalPathDimension ell m))) :
          ℚ) : ℝ) ≤
        (((12 : ℚ) ^ (2 * q * ell) * (m : ℚ) ^ (q * ell + 1)) : ℝ) := by
    rw [hCast]
    exact hReal
  exact_mod_cast hReal'

/-- The finite even-walk bound from the iid module, rather than
an assumed full path moment, is sufficient for the path auxiliary upper sum.
The `ell = 0` product is the identity and is included. -/
theorem c079CanonicalPath_auxiliaryUpper_of_iidEvenWalkCount
    (ell p t : ℕ)
    (hCount : c079IidEvenWalkCount (2 * (p + 1) ^ 2) (p + 1) ≤
      (12 * Real.sqrt ((2 * (p + 1) ^ 2 : ℕ) : ℝ)) ^ (2 * (p + 1))) :
    (∑ T : C079PathStateDegreeFiber (c079CanonicalPathShape ell) p ell t,
      c079PathAuxiliaryWeight T) ≤
      12 ^ (2 * (p + 1) * ell) *
        (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1) := by
  have hFactor := c079IidSignMatrix_highMoment_of_evenWalkCount_bound
    (p + 1) (by omega) hCount
  have hMoment := c079CanonicalPath_productMoment_le_of_iidHighMoment
    ell (p + 1) hFactor
  exact c079CanonicalPath_auxiliaryUpper_of_productMoment ell p t hMoment


end GraphMatrixReplica
