import R6.SeparatorPathCertificate

/-! # Isolated-middle correction for the sharp replica degree bound

The path argument bounds covered roles at moment order `q = p + 1` by
`q (|V| - |S|) + |S|`.  A role which is neither a boundary role nor incident
to an edge is an isolated middle role.  Its equality partition is completely
unconstrained and can have as many as `2q` blocks, rather than `q` blocks.

This file keeps the existing path and separator modules unchanged and proves
the exact correction: every isolated middle role costs at most one additional
factor `q`.  Under a right-left Menger certificate the resulting exponent is

`q (|V| - |S_min| + |W_iso|) + |S_min|`.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A role is an isolated middle role when it belongs to neither external
boundary and is incident to no shape edge. -/
def PartiteShape.IsIsolatedMiddle (G : PartiteShape)
    (v : Fin G.roles) : Prop :=
  v ∉ G.leftBoundary ∧ v ∉ G.rightBoundary ∧
    ∀ e : Fin G.edges, G.source e ≠ v ∧ G.target e ≠ v

/-- The finite set of isolated middle roles. -/
def PartiteShape.isolatedMiddleRoles (G : PartiteShape) :
    Finset (Fin G.roles) := by
  classical
  exact Finset.univ.filter G.IsIsolatedMiddle

/-- Number of isolated middle roles, corresponding to `|W_iso|`. -/
def PartiteShape.isolatedMiddleCount (G : PartiteShape) : ℕ :=
  G.isolatedMiddleRoles.card

theorem PartiteShape.isIsolatedMiddle_iff_not_roleCovered
    (G : PartiteShape) (v : Fin G.roles) :
    G.IsIsolatedMiddle v ↔ ¬ G.RoleCovered v := by
  constructor
  · rintro ⟨hLeft, hRight, hEdges⟩
    rintro (⟨e, hSource | hTarget⟩ | hLeft' | hRight')
    · exact (hEdges e).1 hSource
    · exact (hEdges e).2 hTarget
    · exact hLeft hLeft'
    · exact hRight hRight'
  · intro hNotCovered
    refine ⟨?_, ?_, ?_⟩
    · intro hLeft
      exact hNotCovered (Or.inr (Or.inl hLeft))
    · intro hRight
      exact hNotCovered (Or.inr (Or.inr hRight))
    · intro e
      constructor
      · intro hSource
        exact hNotCovered (Or.inl ⟨e, Or.inl hSource⟩)
      · intro hTarget
        exact hNotCovered (Or.inl ⟨e, Or.inr hTarget⟩)

theorem PartiteShape.mem_isolatedMiddleRoles_iff
    (G : PartiteShape) (v : Fin G.roles) :
    v ∈ G.isolatedMiddleRoles ↔ G.IsIsolatedMiddle v := by
  classical
  simp [PartiteShape.isolatedMiddleRoles]

theorem PartiteShape.isolatedMiddleCount_le_roles (G : PartiteShape) :
    G.isolatedMiddleCount ≤ G.roles := by
  classical
  simpa [PartiteShape.isolatedMiddleCount] using
    Finset.card_le_card (Finset.subset_univ G.isolatedMiddleRoles)

/-- Any partition of the `2q` replica occurrences has at most `2q` blocks.
Unlike the covered-role bound, this statement uses no parity or trace glue. -/
theorem partitionBlockCount_le_twice_momentOrder
    {p : ℕ} (pi : ReplicaPartition (p + 1)) :
    partitionBlockCount pi ≤ 2 * (p + 1) := by
  classical
  unfold partitionBlockCount
  have hsurj : Function.Surjective
      (fun a : Replica (p + 1) => Quotient.mk'' a :
        Replica (p + 1) → Quotient pi) := by
    intro q
    exact Quotient.inductionOn q (fun a => ⟨a, rfl⟩)
  have hcard := Fintype.card_le_of_surjective
    (fun a : Replica (p + 1) => Quotient.mk'' a) hsurj
  simpa [Replica, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

/-- Pointwise corrected defect balance.  Covered roles contribute exactly at
most `q`; isolated middle roles contribute at most `2q`, hence one extra `q`. -/
theorem ReplicaState.roleDefect_add_blockCount_le_isolatedCorrection
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (v : Fin G.roles) :
    (p + 1) - partitionBlockCount (S.partition v) +
        partitionBlockCount (S.partition v) ≤
      (p + 1) + if v ∈ G.isolatedMiddleRoles then (p + 1) else 0 := by
  classical
  by_cases hIso : v ∈ G.isolatedMiddleRoles
  · rw [if_pos hIso]
    have hBlocks := partitionBlockCount_le_twice_momentOrder (S.partition v)
    omega
  · rw [if_neg hIso]
    have hNotIso : ¬ G.IsIsolatedMiddle v := fun hv =>
      hIso ((G.mem_isolatedMiddleRoles_iff v).2 hv)
    have hCovered : G.RoleCovered v :=
      Classical.byContradiction fun hn =>
        hNotIso ((G.isIsolatedMiddle_iff_not_roleCovered v).2 hn)
    have hBlocks := S.coveredRole_blockCount_le v hCovered
    omega

/-- Globally, isolated middle roles add at most
`q * |W_iso|` to the usual defect/block balance. -/
theorem ReplicaState.totalDefect_add_totalBlockCount_le_with_isolatedMiddle
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p) :
    S.totalDefect + S.totalBlockCount ≤
      (p + 1) * G.roles + (p + 1) * G.isolatedMiddleCount := by
  classical
  rw [ReplicaState.totalDefect, ReplicaState.totalBlockCount,
    ← Finset.sum_add_distrib]
  calc
    (∑ v : Fin G.roles,
        ((p + 1) - partitionBlockCount (S.partition v) +
          partitionBlockCount (S.partition v))) ≤
        ∑ v : Fin G.roles,
          ((p + 1) + if v ∈ G.isolatedMiddleRoles then (p + 1) else 0) := by
      exact Finset.sum_le_sum fun v _ =>
        S.roleDefect_add_blockCount_le_isolatedCorrection v
    _ = (p + 1) * G.roles + (p + 1) * G.isolatedMiddleCount := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      simp [PartiteShape.isolatedMiddleCount, Nat.mul_comm]

/-- Corrected sharp degree bound for an arbitrary shape.  No global
`RoleCovered` hypothesis is needed: its failures are counted exactly by
`isolatedMiddleCount`. -/
theorem ReplicaState.totalBlockCount_le_sharp_with_isolatedMiddle
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) :
    S.totalBlockCount ≤
      (p + 1) * (G.roles - s + G.isolatedMiddleCount) + s := by
  have hDefect := S.disjointPaths_totalDefect_lower_bound family
  have hBalance := S.totalDefect_add_totalBlockCount_le_with_isolatedMiddle
  have hs : s ≤ G.roles := family.pathCount_le_roles
  have hIntermediate :
      S.totalBlockCount ≤
        (p + 1) * G.roles + (p + 1) * G.isolatedMiddleCount - s * p := by
    omega
  calc
    S.totalBlockCount ≤
        (p + 1) * G.roles + (p + 1) * G.isolatedMiddleCount - s * p :=
      hIntermediate
    _ = (p + 1) * (G.roles - s + G.isolatedMiddleCount) + s := by
      have hr : G.roles = (G.roles - s) + s :=
        (Nat.sub_add_cancel hs).symm
      have hExpand :
          (p + 1) * G.roles + (p + 1) * G.isolatedMiddleCount =
            (p + 1) * (G.roles - s + G.isolatedMiddleCount) +
              s * p + s := by
        calc
          (p + 1) * G.roles + (p + 1) * G.isolatedMiddleCount =
              (p + 1) * ((G.roles - s) + s) +
                (p + 1) * G.isolatedMiddleCount :=
            congrArg
              (fun r => (p + 1) * r +
                (p + 1) * G.isolatedMiddleCount) hr
          _ = (p + 1) * (G.roles - s + G.isolatedMiddleCount) +
                s * p + s := by ring
      rw [hExpand]
      omega

/-- The Theorem 4.8 arithmetic form: a strong separator/path certificate
replaces `s` by the genuine minimum-separator cardinality and adds precisely
`|W_iso|` inside the leading `q` exponent. -/
theorem ReplicaState.totalBlockCount_le_minSeparator_with_isolatedMiddle
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (certificate : G.RightLeftMengerCertificate) :
    S.totalBlockCount ≤
      (p + 1) *
          (G.roles - certificate.cut.card + G.isolatedMiddleCount) +
        certificate.cut.card :=
  S.totalBlockCount_le_sharp_with_isolatedMiddle certificate.paths

/-- When there are no isolated middle roles, the corrected statement reduces
definitionally to the pre-existing sharp formula. -/
theorem ReplicaState.totalBlockCount_le_sharp_of_no_isolatedMiddle
    {G : PartiteShape} {p s : ℕ} (S : ReplicaState G p)
    (hNoIso : G.isolatedMiddleCount = 0)
    (family : G.VertexDisjointRightToLeftPaths s) :
    S.totalBlockCount ≤ (p + 1) * (G.roles - s) + s := by
  simpa [hNoIso] using
    S.totalBlockCount_le_sharp_with_isolatedMiddle family

#print axioms partitionBlockCount_le_twice_momentOrder
#print axioms
  ReplicaState.totalDefect_add_totalBlockCount_le_with_isolatedMiddle
#print axioms ReplicaState.totalBlockCount_le_sharp_with_isolatedMiddle
#print axioms
  ReplicaState.totalBlockCount_le_minSeparator_with_isolatedMiddle

end GraphMatrixReplica
