import R6.C079PathAuxMomentAlgebra

/-! Exact canonical path boundary/product, Gram-trace reindexing, and finite-state weight transfer. These identities do not establish the auxiliary moment upper estimate or hCount. -/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica

def c079GenericPathTerm {ι : Type*} [Fintype ι] (n : Nat)
    (A : Fin n → Matrix ι ι Rat) (phi : Fin (n + 1) → ι) : Rat :=
  ∏ e : Fin n, A e (phi e.castSucc) (phi e.succ)

theorem c079GenericPathTerm_succ {ι : Type*} [Fintype ι]
    (n : Nat) (A : Fin (n + 1) → Matrix ι ι Rat)
    (phi : Fin (n + 2) → ι) :
    c079GenericPathTerm (n + 1) A phi =
      A 0 (phi 0) (phi 1) *
        c079GenericPathTerm n (fun e => A e.succ) (Fin.tail phi) := by
  classical
  unfold c079GenericPathTerm
  rw [Fin.prod_univ_succ]
  congr 1

def c079PathAssignmentSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Nat) (A : Fin n → Matrix ι ι Rat) (a b : ι) : Rat :=
  ∑ phi : Fin (n + 1) → ι,
    if phi 0 = a ∧ phi (Fin.last n) = b then
      c079GenericPathTerm n A phi else 0

def c079FinOneFunctionEquiv {ι : Type*} : ι ≃ (Fin 1 → ι) where
  toFun a := fun _ => a
  invFun f := f 0
  left_inv := by intro a; rfl
  right_inv := by
    intro f
    funext i
    fin_cases i
    rfl

theorem c079PathAssignmentSum_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin 0 → Matrix ι ι Rat) (a b : ι) :
    c079PathAssignmentSum 0 A a b = (1 : Matrix ι ι Rat) a b := by
  classical
  unfold c079PathAssignmentSum
  calc
    (∑ phi : Fin 1 → ι,
        if phi 0 = a ∧ phi (Fin.last 0) = b then
          c079GenericPathTerm 0 A phi else 0) =
      ∑ x : ι, if x = a ∧ x = b then (1 : Rat) else 0 := by
        symm
        apply Fintype.sum_equiv c079FinOneFunctionEquiv
        intro x
        simp [c079FinOneFunctionEquiv, c079GenericPathTerm]
    _ = (1 : Matrix ι ι Rat) a b := by
      rw [Finset.sum_eq_single a]
      · simp [Matrix.one_apply]
      · intro x _ hxa
        simp [hxa]
      · intro ha
        exact False.elim (ha (Finset.mem_univ a))

theorem c079PathAssignmentSum_succ_reindex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Nat) (A : Fin (n + 1) → Matrix ι ι Rat) (a b : ι) :
    c079PathAssignmentSum (n + 1) A a b =
      ∑ z : ι × (Fin (n + 1) → ι),
        if z.1 = a ∧ z.2 (Fin.last n) = b then
          A 0 z.1 (z.2 0) *
            c079GenericPathTerm n (fun e => A e.succ) z.2
        else 0 := by
  classical
  unfold c079PathAssignmentSum
  symm
  apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 2) => ι))
  intro z
  dsimp only [Fin.consEquiv]
  rw [c079GenericPathTerm_succ]
  rfl

theorem c079PathAssignmentSum_succ_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Nat) (A : Fin (n + 1) → Matrix ι ι Rat) (a b : ι) :
    c079PathAssignmentSum (n + 1) A a b =
      ∑ psi : Fin (n + 1) → ι,
        if psi (Fin.last n) = b then
          A 0 a (psi 0) *
            c079GenericPathTerm n (fun e => A e.succ) psi
        else 0 := by
  classical
  rw [c079PathAssignmentSum_succ_reindex, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  by_cases h : psi (Fin.last n) = b
  · simp [h]
  · simp [h]

theorem c079PathAssignmentSum_succ_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Nat) (A : Fin (n + 1) → Matrix ι ι Rat) (a b : ι) :
    c079PathAssignmentSum (n + 1) A a b =
      ∑ mid : ι, A 0 a mid *
        c079PathAssignmentSum n (fun e => A e.succ) mid b := by
  classical
  rw [c079PathAssignmentSum_succ_tail]
  unfold c079PathAssignmentSum
  calc
    (∑ psi : Fin (n + 1) → ι,
        if psi (Fin.last n) = b then
          A 0 a (psi 0) * c079GenericPathTerm n (fun e => A e.succ) psi
        else 0) =
      ∑ psi : Fin (n + 1) → ι, ∑ mid : ι,
        if psi 0 = mid ∧ psi (Fin.last n) = b then
          A 0 a mid * c079GenericPathTerm n (fun e => A e.succ) psi
        else 0 := by
          apply Finset.sum_congr rfl
          intro psi _
          symm
          rw [Finset.sum_eq_single (psi 0)]
          · by_cases h : psi (Fin.last n) = b <;> simp [h]
          · intro mid _ hmid
            simp [Ne.symm hmid]
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ _))
    _ = ∑ mid : ι, ∑ psi : Fin (n + 1) → ι,
          if psi 0 = mid ∧ psi (Fin.last n) = b then
            A 0 a mid * c079GenericPathTerm n (fun e => A e.succ) psi
          else 0 := by rw [Finset.sum_comm]
    _ = ∑ mid : ι, A 0 a mid *
          (∑ psi : Fin (n + 1) → ι,
            if psi 0 = mid ∧ psi (Fin.last n) = b then
              c079GenericPathTerm n (fun e => A e.succ) psi
            else 0) := by
          apply Finset.sum_congr rfl
          intro mid _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro psi _
          split_ifs <;> simp

theorem c079PathAssignmentSum_eq_matrixProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Nat) (A : Fin n → Matrix ι ι Rat) (a b : ι) :
    c079PathAssignmentSum n A a b = (List.ofFn A).prod a b := by
  classical
  induction n generalizing a with
  | zero =>
      simpa [List.ofFn_zero] using c079PathAssignmentSum_zero A a b
  | succ n ih =>
      rw [c079PathAssignmentSum_succ_matrix]
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro mid _
      rw [ih]

theorem c079CanonicalPathBoundaryProduct_entry
    (ell m : Nat)
    (epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m))
    (row : PartiteBoundaryRow (c079CanonicalPathDimension ell m))
    (col : PartiteBoundaryCol (c079CanonicalPathDimension ell m)) :
    partiteBoundaryMatrix (c079CanonicalPathShape ell)
        (c079CanonicalPathDimension ell m) epsilon row col =
      c079CanonicalPathMatrixProduct ell m epsilon
        (c079CanonicalPathRowEquiv ell m row)
        (c079CanonicalPathColEquiv ell m col) := by
  classical
  rw [c079Path_boundaryMatrix_entry_eq_assignmentSum]
  exact c079PathAssignmentSum_eq_matrixProduct ell
    (fun e => c079PathEdgeMatrix ell m epsilon e)
    (c079CanonicalPathRowEquiv ell m row)
    (c079CanonicalPathColEquiv ell m col)

theorem c079CanonicalPathBoundaryProductBridge
    (ell m : Nat) : C079PathBoundaryProductBridge ell m := by
  refine ⟨c079CanonicalPathRowEquiv ell m,
    c079CanonicalPathColEquiv ell m, ?_⟩
  intro epsilon row col
  exact c079CanonicalPathBoundaryProduct_entry ell m epsilon row col

theorem c079GramTracePower_eq_of_endpointEquiv
    {α β ι κ : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]
    [DecidableEq α] [DecidableEq β] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix α β Rat) (H : Matrix ι κ Rat)
    (er : α ≃ ι) (ec : β ≃ κ)
    (hM : ∀ r c, M r c = H (er r) (ec c))
    (q : Nat) :
    Matrix.trace ((M * M.transpose) ^ q) =
      Matrix.trace ((H * H.transpose) ^ q) := by
  classical
  have hGram (r s : α) :
      (M * M.transpose) r s =
        (H * H.transpose) (er r) (er s) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    calc
      (∑ c : β, M r c * M s c) =
          ∑ c : β, H (er r) (ec c) * H (er s) (ec c) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hM, hM]
      _ = ∑ d : κ, H (er r) d * H (er s) d := by
            apply Fintype.sum_equiv ec
            intro c
            rfl
  have hPow (k : Nat) (r s : α) :
      ((M * M.transpose) ^ k) r s =
        ((H * H.transpose) ^ k) (er r) (er s) := by
    induction k generalizing r s with
    | zero =>
        simp [Matrix.one_apply, er.injective.eq_iff]
    | succ k ih =>
        rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
        calc
          (∑ t : α, ((M * M.transpose) ^ k) r t *
              (M * M.transpose) t s) =
            ∑ t : α, ((H * H.transpose) ^ k) (er r) (er t) *
              (H * H.transpose) (er t) (er s) := by
                apply Finset.sum_congr rfl
                intro t _
                rw [ih r t, hGram]
          _ = ∑ u : ι, ((H * H.transpose) ^ k) (er r) u *
                (H * H.transpose) u (er s) := by
                  apply Fintype.sum_equiv er
                  intro t
                  rfl
  change (∑ r : α, ((M * M.transpose) ^ q) r r) =
    ∑ u : ι, ((H * H.transpose) ^ q) u u
  calc
    (∑ r : α, ((M * M.transpose) ^ q) r r) =
      ∑ r : α, ((H * H.transpose) ^ q) (er r) (er r) := by
        apply Finset.sum_congr rfl
        intro r _
        exact hPow q r r
    _ = ∑ u : ι, ((H * H.transpose) ^ q) u u := by
          apply Fintype.sum_equiv er
          intro r
          rfl

theorem c079CanonicalPath_boundaryGramTrace_eq_product
    (ell m q : Nat)
    (epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m)) :
    let M := partiteBoundaryMatrix (c079CanonicalPathShape ell)
      (c079CanonicalPathDimension ell m) epsilon
    let H := c079CanonicalPathMatrixProduct ell m epsilon
    Matrix.trace ((M * M.transpose) ^ q) =
      Matrix.trace ((H * H.transpose) ^ q) := by
  exact c079GramTracePower_eq_of_endpointEquiv
    (partiteBoundaryMatrix (c079CanonicalPathShape ell)
      (c079CanonicalPathDimension ell m) epsilon)
    (c079CanonicalPathMatrixProduct ell m epsilon)
    (c079CanonicalPathRowEquiv ell m)
    (c079CanonicalPathColEquiv ell m)
    (c079CanonicalPathBoundaryProduct_entry ell m epsilon) q

theorem c079PathAuxiliaryWeight_fiberSum_le_total
    (G : PartiteShape) (p ell t : Nat) :
    (∑ T : C079PathStateDegreeFiber G p ell t,
        (c079PathAuxiliaryWeight T : Rat)) ≤
      ∑ T : AdmissiblePartitionState G p,
        (T.toReplicaState.labelingWeight
          (fun _ : Fin G.roles => 2 * (p + 1) ^ 2) : Rat) := by
  classical
  let P : AdmissiblePartitionState G p → Prop := fun T =>
    T.toReplicaState.totalBlockCount = (p + 1) * ell + 1 - t
  let w : AdmissiblePartitionState G p → Rat := fun T =>
    (T.toReplicaState.labelingWeight
      (fun _ : Fin G.roles => 2 * (p + 1) ^ 2) : Rat)
  change (∑ T : {T // P T}, w T.1) ≤ ∑ T, w T
  have hComplement : (0 : Rat) ≤ ∑ T : {T // ¬ P T}, w T.1 := by
    apply Finset.sum_nonneg
    intro T _
    exact Nat.cast_nonneg _
  have hSplit := Fintype.sum_subtype_add_sum_subtype P w
  linarith

theorem c079CanonicalPath_productGramTraceAverage_eq_statePolynomial
    (ell m p : Nat) :
    ((∑ epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m),
        Matrix.trace
          ((c079CanonicalPathMatrixProduct ell m epsilon *
            (c079CanonicalPathMatrixProduct ell m epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample (c079CanonicalPathDimension ell m))) =
      ∑ T : AdmissiblePartitionState (c079CanonicalPathShape ell) p,
        (T.toReplicaState.labelingWeight
          (c079CanonicalPathDimension ell m) : Rat) := by
  classical
  calc
    _ = ((∑ epsilon : JointEdgeSignSample (c079CanonicalPathDimension ell m),
        Matrix.trace
          ((partiteBoundaryMatrix (c079CanonicalPathShape ell)
              (c079CanonicalPathDimension ell m) epsilon *
            (partiteBoundaryMatrix (c079CanonicalPathShape ell)
              (c079CanonicalPathDimension ell m) epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample (c079CanonicalPathDimension ell m))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro epsilon _
        exact (c079CanonicalPath_boundaryGramTrace_eq_product ell m (p + 1) epsilon).symm
    _ = _ := partiteBoundaryMatrixGramTracePowAverage_eq_statePolynomial
      (dimension := c079CanonicalPathDimension ell m) (p := p)

theorem c079CanonicalPath_auxiliaryUpper_of_productMoment
    (ell p t : Nat)
    (hMoment :
      ((∑ epsilon : JointEdgeSignSample
            (c079CanonicalPathDimension ell (2 * (p + 1) ^ 2)),
          Matrix.trace
            ((c079CanonicalPathMatrixProduct ell (2 * (p + 1) ^ 2) epsilon *
              (c079CanonicalPathMatrixProduct ell (2 * (p + 1) ^ 2)
                epsilon).transpose) ^ (p + 1))) /
        Fintype.card (JointEdgeSignSample
          (c079CanonicalPathDimension ell (2 * (p + 1) ^ 2)))) ≤
        (12 : Rat) ^ (2 * (p + 1) * ell) *
          ((2 * (p + 1) ^ 2 : Nat) : Rat) ^ ((p + 1) * ell + 1)) :
    (∑ T : C079PathStateDegreeFiber (c079CanonicalPathShape ell) p ell t,
        c079PathAuxiliaryWeight T) ≤
      12 ^ (2 * (p + 1) * ell) *
        (2 * (p + 1) ^ 2) ^ ((p + 1) * ell + 1) := by
  have hFiber := c079PathAuxiliaryWeight_fiberSum_le_total
    (c079CanonicalPathShape ell) p ell t
  have hEq := c079CanonicalPath_productGramTraceAverage_eq_statePolynomial
    ell (2 * (p + 1) ^ 2) p
  have hRat :
      (∑ T : C079PathStateDegreeFiber (c079CanonicalPathShape ell) p ell t,
        (c079PathAuxiliaryWeight T : Rat)) ≤
        (12 : Rat) ^ (2 * (p + 1) * ell) *
          ((2 * (p + 1) ^ 2 : Nat) : Rat) ^ ((p + 1) * ell + 1) := by
    calc
      _ ≤ ∑ T : AdmissiblePartitionState (c079CanonicalPathShape ell) p,
          (T.toReplicaState.labelingWeight
            (c079CanonicalPathDimension ell (2 * (p + 1) ^ 2)) : Rat) := by
            exact hFiber
      _ = _ := hEq.symm
      _ ≤ _ := hMoment
  exact_mod_cast hRat

#print axioms c079CanonicalPathBoundaryProductBridge
#print axioms c079GramTracePower_eq_of_endpointEquiv
#print axioms c079CanonicalPath_boundaryGramTrace_eq_product
#print axioms c079PathAuxiliaryWeight_fiberSum_le_total
#print axioms c079CanonicalPath_productGramTraceAverage_eq_statePolynomial
#print axioms c079CanonicalPath_auxiliaryUpper_of_productMoment

end GraphMatrixReplica

