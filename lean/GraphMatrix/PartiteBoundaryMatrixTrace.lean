import GraphMatrix.JointEdgeRademacherExpectation

/-! # Boundary-indexed realization of the fully-partite replica moment

This file gives the fully-partite surrogate an actual finite matrix.  Its
rows and columns are assignments on the left and right boundary roles, while
interior role labels are summed inside each entry.  The edge arrays are the
joint independent Rademacher sample from `JointEdgeRademacherExpectation`.

This is deliberately not identified with the paper's globally-injective
matrix: the latter shares one ambient label set and one unordered-edge noise
array, whereas this surrogate has a separate label set at every role and a
separate rectangular noise array at every shape edge.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Product of conditionals over a finite type. -/
theorem partiteProdConditional {ι R : Type*} [Fintype ι]
    [CommMonoidWithZero R]
    (P : ι → Prop) [DecidablePred P] (f : ι → R) :
    (∏ i, if P i then f i else 0) =
      if ∀ i, P i then ∏ i, f i else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Product of the entries along an open finite matrix-index path. -/
def partiteOpenMatrixPathProduct {ι R : Type*} [Fintype ι]
    [CommSemiring R] (K : Matrix ι ι R) {q : ℕ}
    (a b : ι) (middle : Fin q → ι) : R :=
  ∏ i : Fin (q + 1),
    K (@Fin.cons q (fun _ : Fin (q + 1) => ι) a middle i)
      (@Fin.snoc q (fun _ : Fin (q + 1) => ι) middle b i)

theorem partiteOpenMatrixPathProduct_cons {ι R : Type*} [Fintype ι]
    [CommSemiring R] (K : Matrix ι ι R) {q : ℕ}
    (a b mid : ι) (middle : Fin q → ι) :
    partiteOpenMatrixPathProduct K a b (Fin.cons mid middle) =
      K a mid * partiteOpenMatrixPathProduct K mid b middle := by
  classical
  unfold partiteOpenMatrixPathProduct
  rw [Fin.prod_univ_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.cons_succ, ← Fin.cons_snoc_eq_snoc_cons]

theorem partite_matrix_pow_succ_apply_eq_sum_openPaths
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (K : Matrix ι ι R) (q : ℕ) (a b : ι) :
    (K ^ (q + 1)) a b =
      ∑ middle : Fin q → ι, partiteOpenMatrixPathProduct K a b middle := by
  classical
  induction q generalizing a with
  | zero =>
      simp [partiteOpenMatrixPathProduct, Fin.snoc_zero]
  | succ q ih =>
      rw [show q + 1 + 1 = (q + 1) + 1 by omega, pow_succ',
        Matrix.mul_apply]
      simp_rw [ih]
      simp_rw [Finset.mul_sum]
      calc
        (∑ mid : ι, ∑ middle : Fin q → ι,
            K a mid * partiteOpenMatrixPathProduct K mid b middle) =
            ∑ z : ι × (Fin q → ι),
              K a z.1 * partiteOpenMatrixPathProduct K z.1 b z.2 := by
                rw [Fintype.sum_prod_type]
        _ = ∑ middle : Fin (q + 1) → ι,
              partiteOpenMatrixPathProduct K a b middle := by
                apply Fintype.sum_equiv
                  (Fin.consEquiv (fun _ : Fin (q + 1) => ι))
                intro z
                exact (partiteOpenMatrixPathProduct_cons
                  K a b z.1 z.2).symm

theorem partiteOpenMatrixPathProduct_self_eq_cycleProduct
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (K : Matrix ι ι R) {q : ℕ} (rows : Fin (q + 1) → ι) :
    partiteOpenMatrixPathProduct K (rows 0) (rows 0) (Fin.tail rows) =
      ∏ i : Fin (q + 1), K (rows i) (rows (finRotate (q + 1) i)) := by
  classical
  have hrows : Fin.cons (rows 0) (Fin.tail rows) = rows :=
    Fin.cons_self_tail rows
  unfold partiteOpenMatrixPathProduct
  rw [Fin.snoc_eq_cons_rotate]
  simp only [hrows]

/-- A self-contained positive-power trace expansion, kept here so the
fully-partite module does not depend on the paper-model trace files. -/
theorem partite_matrix_trace_pow_succ_eq_sum_cycleProducts
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (K : Matrix ι ι R) (q : ℕ) :
    Matrix.trace (K ^ (q + 1)) =
      ∑ rows : Fin (q + 1) → ι,
        ∏ i : Fin (q + 1), K (rows i) (rows (finRotate (q + 1) i)) := by
  classical
  calc
    Matrix.trace (K ^ (q + 1)) =
        ∑ a : ι, (K ^ (q + 1)) a a := rfl
    _ = ∑ a : ι, ∑ middle : Fin q → ι,
        partiteOpenMatrixPathProduct K a a middle := by
          apply Finset.sum_congr rfl
          intro a _
          exact partite_matrix_pow_succ_apply_eq_sum_openPaths K q a a
    _ = ∑ z : ι × (Fin q → ι),
          partiteOpenMatrixPathProduct K z.1 z.1 z.2 := by
            rw [Fintype.sum_prod_type]
    _ = ∑ rows : Fin (q + 1) → ι,
          partiteOpenMatrixPathProduct K (rows 0) (rows 0) (Fin.tail rows) := by
            apply Fintype.sum_equiv
              (Fin.consEquiv (fun _ : Fin (q + 1) => ι))
            intro z
            have htail :
                Fin.tail ((Fin.consEquiv
                  (fun _ : Fin (q + 1) => ι)) z) = z.2 := by
              funext i
              rfl
            have hhead :
                (Fin.consEquiv (fun _ : Fin (q + 1) => ι)) z 0 = z.1 := by
              rfl
            simp only [htail, hhead]
    _ = ∑ rows : Fin (q + 1) → ι,
          ∏ i : Fin (q + 1),
            K (rows i) (rows (finRotate (q + 1) i)) := by
            apply Finset.sum_congr rfl
            intro rows _
            exact partiteOpenMatrixPathProduct_self_eq_cycleProduct K rows

/-- Labels assigned to a selected finite set of graph roles. -/
abbrev PartiteBoundaryLabeling {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) (boundary : Finset (Fin G.roles)) :=
  ∀ v : {v : Fin G.roles // v ∈ boundary}, Fin (dimension v.1)

abbrev PartiteBoundaryRow {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) :=
  PartiteBoundaryLabeling dimension G.leftBoundary

abbrev PartiteBoundaryCol {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) :=
  PartiteBoundaryLabeling dimension G.rightBoundary

/-- One copy of a fully-partite role labeling. -/
abbrev PartiteRoleAssignment {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) :=
  ∀ v : Fin G.roles, Fin (dimension v)

/-- A one-copy assignment extends the displayed boundary row and column. -/
def partiteBoundaryEntryCompatible
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    (phi : PartiteRoleAssignment dimension)
    (row : PartiteBoundaryRow dimension)
    (col : PartiteBoundaryCol dimension) : Prop :=
  (∀ v : {v : Fin G.roles // v ∈ G.leftBoundary}, phi v.1 = row v) ∧
  (∀ v : {v : Fin G.roles // v ∈ G.rightBoundary}, phi v.1 = col v)

instance partiteBoundaryEntryCompatibleDecidable
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    (phi : PartiteRoleAssignment dimension)
    (row : PartiteBoundaryRow dimension)
    (col : PartiteBoundaryCol dimension) :
    Decidable (partiteBoundaryEntryCompatible phi row col) :=
  inferInstanceAs (Decidable
    ((∀ v : {v : Fin G.roles // v ∈ G.leftBoundary}, phi v.1 = row v) ∧
     (∀ v : {v : Fin G.roles // v ∈ G.rightBoundary}, phi v.1 = col v)))

/-- The edge-sign monomial of one role assignment. -/
def partiteAssignmentEdgeMonomial
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension)
    (phi : PartiteRoleAssignment dimension) : ℚ :=
  ∏ e : Fin G.edges,
    (rademacherSign
      (epsilon e (phi (G.source e), phi (G.target e))) : ℚ)

/-- The concrete boundary-indexed matrix for a fixed joint edge sample. -/
def partiteBoundaryMatrix (G : PartiteShape)
    (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample dimension) :
    Matrix (PartiteBoundaryRow dimension) (PartiteBoundaryCol dimension) ℚ := by
  classical
  exact fun row col =>
    ∑ phi : PartiteRoleAssignment dimension,
      if partiteBoundaryEntryCompatible phi row col then
        partiteAssignmentEdgeMonomial epsilon phi
      else 0

/-- Rows used by the two entries of each Gram factor. -/
def partiteTraceReplicaRow
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (rows : Fin (p + 1) → PartiteBoundaryRow dimension) :
    Replica (p + 1) → PartiteBoundaryRow dimension :=
  fun x => if x.2 then rows (finRotate (p + 1) x.1) else rows x.1

/-- Both entries of one Gram factor use the same boundary column. -/
def partiteTraceReplicaCol
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (cols : Fin (p + 1) → PartiteBoundaryCol dimension) :
    Replica (p + 1) → PartiteBoundaryCol dimension :=
  fun x => cols x.1

/-- A family of one-copy assignments, transposed into the existing
role-first `RoleLabeling` convention. -/
def roleLabelingOfAssignmentFamily
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension) :
    RoleLabeling G p dimension :=
  fun v x => phis x v

/-- Swapping the role and replica arguments is an exact finite equivalence. -/
def assignmentFamilyEquivRoleLabeling
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ} :
    (Replica (p + 1) → PartiteRoleAssignment dimension) ≃
      RoleLabeling G p dimension where
  toFun := roleLabelingOfAssignmentFamily
  invFun := fun x a v => x v a
  left_inv := by intro phis; rfl
  right_inv := by intro x; rfl

/-- Boundary compatibility for every entry in a cyclic Gram trace word. -/
def partiteTraceCompatible
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension)
    (rows : Fin (p + 1) → PartiteBoundaryRow dimension)
    (cols : Fin (p + 1) → PartiteBoundaryCol dimension) : Prop :=
  ∀ x, partiteBoundaryEntryCompatible (phis x)
    (partiteTraceReplicaRow rows x) (partiteTraceReplicaCol cols x)

instance partiteTraceCompatibleDecidable
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension)
    (rows : Fin (p + 1) → PartiteBoundaryRow dimension)
    (cols : Fin (p + 1) → PartiteBoundaryCol dimension) :
    Decidable (partiteTraceCompatible phis rows cols) :=
  inferInstanceAs (Decidable
    (∀ x, partiteBoundaryEntryCompatible (phis x)
      (partiteTraceReplicaRow rows x) (partiteTraceReplicaCol cols x)))

/-- The row sequence canonically read from the `false` replica labels. -/
def canonicalPartiteTraceRows
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension) :
    Fin (p + 1) → PartiteBoundaryRow dimension :=
  fun i v => phis (i, false) v.1

/-- The column sequence canonically read from the `false` replica labels. -/
def canonicalPartiteTraceCols
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension) :
    Fin (p + 1) → PartiteBoundaryCol dimension :=
  fun i v => phis (i, false) v.1

/-- The original successor/last formulation of left trace gluing is exactly
the cyclic `finRotate` formulation used by a matrix trace word. -/
theorem leftTraceCoarsens_equalityPartition_iff_rotate
    {p : ℕ} {α : Type*} (x : Replica (p + 1) → α) :
    LeftTraceCoarsens (equalityPartition x) ↔
      ∀ i : Fin (p + 1), x (i, true) =
        x (finRotate (p + 1) i, false) := by
  constructor
  · rintro ⟨hSucc, hLast⟩ i
    by_cases hi : i = Fin.last p
    · subst i
      simpa [finRotate_last] using hLast
    · have hlt : (i : ℕ) < p := Fin.val_lt_last hi
      let k : Fin p := ⟨i, hlt⟩
      have hcast : k.castSucc = i := Fin.ext rfl
      have hrotate : finRotate (p + 1) i = k.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last hi]
        rfl
      have hk := hSucc k
      change x (k.castSucc, true) = x (k.succ, false) at hk
      simpa only [hcast, hrotate] using hk
  · intro h
    constructor
    · intro k
      have hne : k.castSucc ≠ Fin.last p := Fin.castSucc_ne_last k
      have hrotate : finRotate (p + 1) k.castSucc = k.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last hne]
        rfl
      change x (k.castSucc, true) = x (k.succ, false)
      simpa only [hrotate] using h k.castSucc
    · simpa [finRotate_last] using h (Fin.last p)

/-- Right trace gluing is equality inside each adjacent replica pair. -/
theorem rightTraceCoarsens_equalityPartition_iff
    {p : ℕ} {α : Type*} (x : Replica (p + 1) → α) :
    RightTraceCoarsens (equalityPartition x) ↔
      ∀ i : Fin (p + 1), x (i, false) = x (i, true) := by
  rfl

/-- A replica family admits exactly one compatible row/column trace word,
and it admits that word precisely when the existing deterministic trace-glue
predicate holds. -/
theorem partiteTraceCompatible_iff_traceGlue_and_eq_canonical
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension)
    (rows : Fin (p + 1) → PartiteBoundaryRow dimension)
    (cols : Fin (p + 1) → PartiteBoundaryCol dimension) :
    partiteTraceCompatible phis rows cols ↔
      TraceGlueForLabeling (roleLabelingOfAssignmentFamily phis) ∧
      rows = canonicalPartiteTraceRows phis ∧
      cols = canonicalPartiteTraceCols phis := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro v hv
        rw [leftTraceCoarsens_equalityPartition_iff_rotate]
        intro i
        let bv : {v : Fin G.roles // v ∈ G.leftBoundary} := ⟨v, hv⟩
        have h₁ := (h (i, true)).1 bv
        have h₂ := (h (finRotate (p + 1) i, false)).1 bv
        exact h₁.trans h₂.symm
      · intro v hv
        rw [rightTraceCoarsens_equalityPartition_iff]
        intro i
        let bv : {v : Fin G.roles // v ∈ G.rightBoundary} := ⟨v, hv⟩
        have h₁ := (h (i, false)).2 bv
        have h₂ := (h (i, true)).2 bv
        exact h₁.trans h₂.symm
    · funext i v
      exact ((h (i, false)).1 v).symm
    · funext i v
      exact ((h (i, false)).2 v).symm
  · rintro ⟨hTrace, rfl, rfl⟩ ⟨i, b⟩
    constructor
    · intro v
      cases b with
      | false => rfl
      | true =>
          have h :=
            (leftTraceCoarsens_equalityPartition_iff_rotate
              (roleLabelingOfAssignmentFamily phis v.1)).1
              (hTrace.1 v.1 v.2) i
          simpa [partiteTraceReplicaRow, canonicalPartiteTraceRows,
            roleLabelingOfAssignmentFamily] using h
    · intro v
      cases b with
      | false => rfl
      | true =>
          have h :=
            (rightTraceCoarsens_equalityPartition_iff
              (roleLabelingOfAssignmentFamily phis v.1)).1
              (hTrace.2 v.1 v.2) i
          simpa [partiteTraceReplicaCol, canonicalPartiteTraceCols,
            roleLabelingOfAssignmentFamily] using h.symm

/-- The edge monomials of a replica family are exactly the existing joint
edge character product after transposing the two dependent arguments. -/
theorem assignmentFamily_edgeMonomialProduct_eq_jointEdgeCharacterProduct
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension)
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension) :
    (∏ x : Replica (p + 1), partiteAssignmentEdgeMonomial epsilon (phis x)) =
      (jointEdgeCharacterProduct
        (roleLabelingOfAssignmentFamily phis) epsilon : ℚ) := by
  classical
  unfold partiteAssignmentEdgeMonomial jointEdgeCharacterProduct
    jointEdgeCharacter rademacherCharacter roleLabelingOfAssignmentFamily
  push_cast
  rw [Finset.prod_comm]

/-- Product of the `2(p+1)` matrix entries in one cyclic trace word. -/
def partiteTraceEntryProduct
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension)
    (rows : Fin (p + 1) → PartiteBoundaryRow dimension)
    (cols : Fin (p + 1) → PartiteBoundaryCol dimension) : ℚ :=
  ∏ x : Replica (p + 1),
    partiteBoundaryMatrix G dimension epsilon
      (partiteTraceReplicaRow rows x) (partiteTraceReplicaCol cols x)

/-- The replica product is the usual product of the two entries contributed
by each positive Gram factor. -/
theorem partiteTraceEntryProduct_eq_pairProduct
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension)
    (rows : Fin (p + 1) → PartiteBoundaryRow dimension)
    (cols : Fin (p + 1) → PartiteBoundaryCol dimension) :
    partiteTraceEntryProduct epsilon rows cols =
      ∏ i : Fin (p + 1),
        partiteBoundaryMatrix G dimension epsilon (rows i) (cols i) *
          partiteBoundaryMatrix G dimension epsilon
            (rows (finRotate (p + 1) i)) (cols i) := by
  classical
  rw [partiteTraceEntryProduct, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp [partiteTraceReplicaRow, partiteTraceReplicaCol, mul_comm]

/-- The full boundary-indexed cyclic trace word. -/
def partiteBoundaryTraceWord
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension) : ℚ :=
  ∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
    ∑ cols : Fin (p + 1) → PartiteBoundaryCol dimension,
      partiteTraceEntryProduct epsilon rows cols

/-- The boundary trace word is the actual positive Gram-matrix trace. -/
theorem partiteBoundaryTraceWord_eq_matrixTrace
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension) :
    partiteBoundaryTraceWord (p := p) epsilon =
      Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
        (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1)) := by
  classical
  let M := partiteBoundaryMatrix G dimension epsilon
  let K := M * M.transpose
  calc
    partiteBoundaryTraceWord (p := p) epsilon =
        ∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
          ∑ cols : Fin (p + 1) → PartiteBoundaryCol dimension,
            ∏ i : Fin (p + 1),
              M (rows i) (cols i) *
                M (rows (finRotate (p + 1) i)) (cols i) := by
                  simp only [partiteBoundaryTraceWord,
                    partiteTraceEntryProduct_eq_pairProduct, M]
    _ = ∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
          ∏ i : Fin (p + 1),
            ∑ col : PartiteBoundaryCol dimension,
              M (rows i) col * M (rows (finRotate (p + 1) i)) col := by
                apply Finset.sum_congr rfl
                intro rows _
                rw [Fintype.prod_sum]
    _ = ∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
          ∏ i : Fin (p + 1),
            K (rows i) (rows (finRotate (p + 1) i)) := by
                apply Finset.sum_congr rfl
                intro rows _
                apply Finset.prod_congr rfl
                intro i _
                simp [K, Matrix.mul_apply, Matrix.transpose_apply]
    _ = Matrix.trace (K ^ (p + 1)) :=
      (partite_matrix_trace_pow_succ_eq_sum_cycleProducts K p).symm
    _ = Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
        (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1)) := by
          rfl

/-- Expanding the product of entry sums exposes exactly one assignment for
each replica, with the cyclic boundary constraints left explicit. -/
theorem partiteTraceEntryProduct_expansion
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension)
    (rows : Fin (p + 1) → PartiteBoundaryRow dimension)
    (cols : Fin (p + 1) → PartiteBoundaryCol dimension) :
    partiteTraceEntryProduct epsilon rows cols =
      ∑ phis : Replica (p + 1) → PartiteRoleAssignment dimension,
        if partiteTraceCompatible phis rows cols then
          (jointEdgeCharacterProduct
            (roleLabelingOfAssignmentFamily phis) epsilon : ℚ)
        else 0 := by
  classical
  unfold partiteTraceEntryProduct partiteBoundaryMatrix
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro phis _
  by_cases h : partiteTraceCompatible phis rows cols
  · rw [if_pos h]
    have hEach : ∀ x : Replica (p + 1),
        partiteBoundaryEntryCompatible (phis x)
          (partiteTraceReplicaRow rows x) (partiteTraceReplicaCol cols x) := h
    simp_rw [if_pos (hEach _)]
    exact assignmentFamily_edgeMonomialProduct_eq_jointEdgeCharacterProduct
      epsilon phis
  · rw [if_neg h]
    unfold partiteTraceCompatible at h
    push Not at h
    obtain ⟨x, hx⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ x) (if_neg hx)

private theorem partite_sum_pair_indicator
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (a₀ : α) (b₀ : β) (c : ℚ) :
    (∑ a, ∑ b, if a = a₀ ∧ b = b₀ then c else 0) = c := by
  classical
  rw [Finset.sum_eq_single a₀]
  · rw [Finset.sum_eq_single b₀]
    · simp
    · intro b _hb hne
      rw [if_neg (fun h => hne h.2)]
    · simp
  · intro a _ha hne
    apply Finset.sum_eq_zero
    intro b _hb
    rw [if_neg (fun h => hne h.1)]
  · simp

/-- Summing over all displayed boundary words counts the unique canonical
row/column word when trace gluing holds, and contributes zero otherwise. -/
theorem sum_partiteTraceCompatible_eq_traceGlueIndicator_mul
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (phis : Replica (p + 1) → PartiteRoleAssignment dimension)
    (c : ℚ) :
    (∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
      ∑ cols : Fin (p + 1) → PartiteBoundaryCol dimension,
        if partiteTraceCompatible phis rows cols then c else 0) =
      traceGlueIndicator (roleLabelingOfAssignmentFamily phis) * c := by
  classical
  simp_rw [partiteTraceCompatible_iff_traceGlue_and_eq_canonical]
  by_cases hTrace :
      TraceGlueForLabeling (roleLabelingOfAssignmentFamily phis)
  · rw [show traceGlueIndicator (roleLabelingOfAssignmentFamily phis) = 1 by
      simp [traceGlueIndicator, hTrace], one_mul]
    simpa [hTrace] using partite_sum_pair_indicator
      (canonicalPartiteTraceRows phis) (canonicalPartiteTraceCols phis) c
  · simp [traceGlueIndicator, hTrace]

/-- For a fixed joint edge sample, the actual matrix trace is the existing
fixed-sample replica-labeling sum. -/
theorem partiteBoundaryTraceWord_eq_jointReplicaIntegrandSum
    {G : PartiteShape} {p : ℕ} {dimension : Fin G.roles → ℕ}
    (epsilon : JointEdgeSignSample dimension) :
    partiteBoundaryTraceWord (p := p) epsilon =
      ∑ x : RoleLabeling G p dimension,
        traceGlueIndicator x * (jointEdgeCharacterProduct x epsilon : ℚ) := by
  classical
  unfold partiteBoundaryTraceWord
  simp_rw [partiteTraceEntryProduct_expansion]
  calc
    (∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
        ∑ cols : Fin (p + 1) → PartiteBoundaryCol dimension,
          ∑ phis : Replica (p + 1) → PartiteRoleAssignment dimension,
            if partiteTraceCompatible phis rows cols then
              (jointEdgeCharacterProduct
                (roleLabelingOfAssignmentFamily phis) epsilon : ℚ)
            else 0) =
        ∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
          ∑ phis : Replica (p + 1) → PartiteRoleAssignment dimension,
            ∑ cols : Fin (p + 1) → PartiteBoundaryCol dimension,
              if partiteTraceCompatible phis rows cols then
                (jointEdgeCharacterProduct
                  (roleLabelingOfAssignmentFamily phis) epsilon : ℚ)
              else 0 := by
                apply Finset.sum_congr rfl
                intro rows _
                rw [Finset.sum_comm]
    _ = ∑ phis : Replica (p + 1) → PartiteRoleAssignment dimension,
          ∑ rows : Fin (p + 1) → PartiteBoundaryRow dimension,
            ∑ cols : Fin (p + 1) → PartiteBoundaryCol dimension,
              if partiteTraceCompatible phis rows cols then
                (jointEdgeCharacterProduct
                  (roleLabelingOfAssignmentFamily phis) epsilon : ℚ)
              else 0 := by
                rw [Finset.sum_comm]
    _ = ∑ x : RoleLabeling G p dimension,
          traceGlueIndicator x *
            (jointEdgeCharacterProduct x epsilon : ℚ) := by
              apply Fintype.sum_equiv assignmentFamilyEquivRoleLabeling
              intro phis
              exact sum_partiteTraceCompatible_eq_traceGlueIndicator_mul
                phis (jointEdgeCharacterProduct
                  (roleLabelingOfAssignmentFamily phis) epsilon : ℚ)

/-- Uniform average of the concrete boundary-matrix trace words. -/
def partiteBoundaryTraceAverage
    {G : PartiteShape} (p : ℕ) (dimension : Fin G.roles → ℕ) : ℚ :=
  (∑ epsilon : JointEdgeSignSample dimension,
      partiteBoundaryTraceWord (p := p) epsilon) /
    Fintype.card (JointEdgeSignSample dimension)

/-- The boundary-matrix trace average is definitionally the earlier joint
replica moment after the finite boundary reindexing theorem. -/
theorem partiteBoundaryTraceAverage_eq_jointReplicaMomentAverage
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    partiteBoundaryTraceAverage p dimension =
      jointReplicaMomentAverage p dimension := by
  classical
  unfold partiteBoundaryTraceAverage jointReplicaMomentAverage
  congr 1
  apply Finset.sum_congr rfl
  intro epsilon _
  exact partiteBoundaryTraceWord_eq_jointReplicaIntegrandSum epsilon

/-- Exact matrix-facing form of the bridge: the normalized expectation of
`trace ((H Hᵀ)^(p+1))` is the existing joint replica moment. -/
theorem partiteBoundaryMatrixGramTracePowAverage_eq_jointReplicaMomentAverage
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) =
        jointReplicaMomentAverage p dimension := by
  classical
  calc
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) =
        partiteBoundaryTraceAverage p dimension := by
          unfold partiteBoundaryTraceAverage
          congr 1
          apply Finset.sum_congr rfl
          intro epsilon _
          exact (partiteBoundaryTraceWord_eq_matrixTrace epsilon).symm
    _ = jointReplicaMomentAverage p dimension :=
      partiteBoundaryTraceAverage_eq_jointReplicaMomentAverage dimension

/-- Consequently the normalized concrete boundary-matrix trace average is
the already-proved admissible replica-state falling-factorial polynomial. -/
theorem partiteBoundaryMatrixGramTracePowAverage_eq_statePolynomial
    {G : PartiteShape} {p : ℕ} (dimension : Fin G.roles → ℕ) :
    ((∑ epsilon : JointEdgeSignSample dimension,
        Matrix.trace ((partiteBoundaryMatrix G dimension epsilon *
          (partiteBoundaryMatrix G dimension epsilon).transpose) ^ (p + 1))) /
      Fintype.card (JointEdgeSignSample dimension)) =
      ∑ T : AdmissiblePartitionState G p,
        (T.toReplicaState.labelingWeight dimension : ℚ) := by
  rw [partiteBoundaryMatrixGramTracePowAverage_eq_jointReplicaMomentAverage]
  exact jointReplicaMomentAverage_eq_statePolynomial dimension


end GraphMatrixReplica
