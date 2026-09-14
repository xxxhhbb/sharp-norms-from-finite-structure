import R6.PaperRademacherMatchingReindex

/-! # Dihedral reindexing classes of canonical matchings

Perfect matchings carry an inessential ordering of their pairs.  Rotating or
reversing this pair index gives a dihedral orbit of encodings with the same
compatibility condition and hence the same coefficient contribution.  This
file evaluates the orbits of the row- and column-canonical representatives.

This orbit only changes the ordering of already canonical pairs.  Matchings
whose pair partition crosses those canonical pairs are explicitly outside the
classes below; no bound for such matchings is claimed.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Direct edge label on the natural paired occurrence type. -/
def rademacherDirectEdgeLabel
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) : Replica r → ε
  | (t, false) => (choice t).1
  | (t, true) => (choice t).2

/-- Compatibility of a matching encoding with an edge choice, expressed on
the natural `Fin r × Bool` occurrence coordinates. -/
def RademacherDirectMatchingCompatible
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε)
    (matching : Replica r ≃ Replica r) : Prop :=
  ∀ k : Fin r,
    rademacherDirectEdgeLabel choice (matching (k, false)) =
      rademacherDirectEdgeLabel choice (matching (k, true))

instance instDecidableRademacherDirectMatchingCompatible
    {ε : Type} [DecidableEq ε] {r : ℕ}
    (choice : Fin r → ε × ε) (matching : Replica r ≃ Replica r) :
    Decidable (RademacherDirectMatchingCompatible choice matching) := by
  unfold RademacherDirectMatchingCompatible
  infer_instance

/-- Relabel the ordered pair slots by a permutation.  This cannot change the
underlying pair partition. -/
def rademacherPairSlotRelabel {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Replica r ≃ Replica r :=
  σ.prodCongr (Equiv.refl Bool)

/-- Precomposition by a pair-slot permutation leaves compatibility exactly
unchanged. -/
theorem directMatchingCompatible_pairSlotRelabel_iff
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε)
    (matching : Replica r ≃ Replica r) (σ : Equiv.Perm (Fin r)) :
    RademacherDirectMatchingCompatible choice
        ((rademacherPairSlotRelabel σ).trans matching) ↔
      RademacherDirectMatchingCompatible choice matching := by
  constructor
  · intro h k
    simpa [RademacherDirectMatchingCompatible,
      rademacherPairSlotRelabel] using h (σ.symm k)
  · intro h k
    simpa [RademacherDirectMatchingCompatible,
      rademacherPairSlotRelabel] using h (σ k)

/-- The original nested coefficient contribution attached to a direct
matching encoding. -/
def rademacherDirectMatchingContribution
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) (matching : Replica r ≃ Replica r) : ℝ :=
  ∑ rows : Fin r → ι, ∑ cols : Fin r → κ,
    ∑ choice : Fin r → ε × ε,
      if RademacherDirectMatchingCompatible choice matching then
        rademacherGramCycleCoefficient A rows cols choice else 0

/-- Pair-slot relabeling leaves the full coefficient contribution unchanged. -/
theorem rademacherDirectMatchingContribution_pairSlotRelabel
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) (matching : Replica r ≃ Replica r)
    (σ : Equiv.Perm (Fin r)) :
    rademacherDirectMatchingContribution A
        ((rademacherPairSlotRelabel σ).trans matching) =
      rademacherDirectMatchingContribution A matching := by
  classical
  unfold rademacherDirectMatchingContribution
  simp_rw [directMatchingCompatible_pairSlotRelabel_iff]

/-- A concrete rotation/reflection of the pair index. -/
def rademacherDihedralPairPerm (r k : ℕ) (reflect : Bool) :
    Equiv.Perm (Fin r) :=
  if reflect then ((finRotate r) ^ k).trans Fin.revPerm
  else (finRotate r) ^ k

/-- The dihedral encoding orbit of a fixed matching representative. -/
def RademacherDihedralEncodingOrbit {r : ℕ}
    (representative matching : Replica r ≃ Replica r) : Prop :=
  ∃ k : ℕ, ∃ reflect : Bool,
    matching =
      (rademacherPairSlotRelabel
        (rademacherDihedralPairPerm r k reflect)).trans representative

/-- Every member of a dihedral encoding orbit has the representative's exact
coefficient contribution. -/
theorem rademacherDirectMatchingContribution_eq_of_dihedralOrbit
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ)
    (representative matching : Replica r ≃ Replica r)
    (hOrbit : RademacherDihedralEncodingOrbit representative matching) :
    rademacherDirectMatchingContribution A matching =
      rademacherDirectMatchingContribution A representative := by
  obtain ⟨k, reflect, rfl⟩ := hOrbit
  exact rademacherDirectMatchingContribution_pairSlotRelabel A representative
    (rademacherDihedralPairPerm r k reflect)

/-- Direct compatibility with the row-canonical representative is diagonal
edge equality at every cycle position. -/
theorem directMatchingCompatible_refl_iff
    {ε : Type} {r : ℕ} (choice : Fin r → ε × ε) :
    RademacherDirectMatchingCompatible choice (Equiv.refl (Replica r)) ↔
      ∀ t, (choice t).1 = (choice t).2 := by
  rfl

/-- Direct compatibility with the column-canonical representative is exactly
the cyclic condition used in the explicit reindexing file. -/
theorem directMatchingCompatible_leftPairEquiv_iff
    {ε : Type} {p : ℕ} (choice : Fin (p + 1) → ε × ε) :
    RademacherDirectMatchingCompatible choice (leftPairEquiv p) ↔
      RademacherColumnCanonicalChoice choice := by
  rfl

/-- The direct row-canonical representative is the previously evaluated row
canonical coefficient contribution. -/
theorem rademacherDirectMatchingContribution_refl
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {r : ℕ}
    (A : ε → Matrix ι κ ℝ) :
    rademacherDirectMatchingContribution A (Equiv.refl (Replica r)) =
      rademacherCanonicalMatchingContribution (r := r) A := by
  classical
  unfold rademacherDirectMatchingContribution
  unfold rademacherCanonicalMatchingContribution
  simp_rw [directMatchingCompatible_refl_iff]

/-- The direct column-canonical representative is the original-coordinate
column contribution evaluated in the reindexing file. -/
theorem rademacherDirectMatchingContribution_leftPairEquiv
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] {p : ℕ}
    (A : ε → Matrix ι κ ℝ) :
    rademacherDirectMatchingContribution A (leftPairEquiv p) =
      rademacherOriginalColumnMatchingContribution (r := p + 1) A := by
  classical
  unfold rademacherDirectMatchingContribution
  unfold rademacherOriginalColumnMatchingContribution
  simp_rw [directMatchingCompatible_leftPairEquiv_iff]

/-- Every dihedral re-encoding of the row-canonical matching has exactly the
row-variance trace contribution. -/
theorem dihedralRowCanonicalContribution_eq_trace_rowVariance_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r)
    (matching : Replica r ≃ Replica r)
    (hOrbit : RademacherDihedralEncodingOrbit
      (Equiv.refl (Replica r)) matching) :
    rademacherDirectMatchingContribution A matching =
      Matrix.trace ((rademacherRowVariance A) ^ r) := by
  rw [rademacherDirectMatchingContribution_eq_of_dihedralOrbit
    A (Equiv.refl (Replica r)) matching hOrbit]
  rw [rademacherDirectMatchingContribution_refl]
  exact rademacherCanonicalMatchingContribution_eq_trace_rowVariance_pow
    A r hr

/-- Every dihedral re-encoding of the column-canonical matching has exactly
the column-variance trace contribution. -/
theorem dihedralColumnCanonicalContribution_eq_trace_columnVariance_pow
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (p : ℕ)
    (matching : Replica (p + 1) ≃ Replica (p + 1))
    (hOrbit : RademacherDihedralEncodingOrbit (leftPairEquiv p) matching) :
    rademacherDirectMatchingContribution A matching =
      Matrix.trace ((rademacherColumnVariance A) ^ (p + 1)) := by
  rw [rademacherDirectMatchingContribution_eq_of_dihedralOrbit
    A (leftPairEquiv p) matching hOrbit]
  rw [rademacherDirectMatchingContribution_leftPairEquiv]
  exact rademacherOriginalColumnMatchingContribution_eq_trace_columnVariance_pow
    A (p + 1) (by omega)

/-- The union of the two controlled dihedral encoding orbits. -/
def RademacherRowColumnDihedralClass {r : ℕ}
    (matching : Replica r ≃ Replica r) : Prop :=
  RademacherDihedralEncodingOrbit (Equiv.refl (Replica r)) matching ∨
    ∃ p : ℕ, ∃ h : r = p + 1,
      RademacherDihedralEncodingOrbit (h ▸ leftPairEquiv p) matching

/-- A genuinely non-dihedral matching is, by definition, outside both
canonical encoding orbits.  The variance-trace theorems above intentionally
make no assertion about this complement. -/
def RademacherGenuinelyNonDihedral {r : ℕ}
    (matching : Replica r ≃ Replica r) : Prop :=
  ¬RademacherRowColumnDihedralClass matching

theorem genuinelyNonDihedral_not_rowOrbit
    {r : ℕ} {matching : Replica r ≃ Replica r}
    (h : RademacherGenuinelyNonDihedral matching) :
    ¬RademacherDihedralEncodingOrbit (Equiv.refl (Replica r)) matching := by
  intro hrow
  exact h (Or.inl hrow)

/-- On the explicitly identified row/column dihedral class, the contribution
is bounded by the larger of the two variance trace moments. -/
theorem rowColumnDihedralContribution_le_maxVarianceTraces
    {ε ι κ : Type} [Fintype ε] [Fintype ι] [Fintype κ]
    [DecidableEq ε] [DecidableEq ι] [DecidableEq κ]
    (A : ε → Matrix ι κ ℝ) (r : ℕ) (hr : 0 < r)
    (matching : Replica r ≃ Replica r)
    (hClass : RademacherRowColumnDihedralClass matching) :
    rademacherDirectMatchingContribution A matching ≤
      max (Matrix.trace ((rademacherRowVariance A) ^ r))
        (Matrix.trace ((rademacherColumnVariance A) ^ r)) := by
  rcases hClass with hrow | ⟨p, h, hcol⟩
  · rw [dihedralRowCanonicalContribution_eq_trace_rowVariance_pow
      A r hr matching hrow]
    exact le_max_left _ _
  · subst r
    rw [dihedralColumnCanonicalContribution_eq_trace_columnVariance_pow
      A p matching hcol]
    exact le_max_right _ _

#print axioms rademacherDirectMatchingContribution_pairSlotRelabel
#print axioms dihedralRowCanonicalContribution_eq_trace_rowVariance_pow
#print axioms dihedralColumnCanonicalContribution_eq_trace_columnVariance_pow
#print axioms rowColumnDihedralContribution_le_maxVarianceTraces

end GraphMatrixReplica
