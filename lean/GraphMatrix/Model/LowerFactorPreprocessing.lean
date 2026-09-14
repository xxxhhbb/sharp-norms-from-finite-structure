import Mathlib

/-!
# independent-factor preprocessing: a typed finite special case

The finite role family is partitioned into a core, unused middle roles, and
detached components. An occurrence index has its own array even if its scope
equals another occurrence's scope. Scope types make it impossible for a core
factor to read a detached coordinate or for a detached factor to read another
component. The exact matrix-entry factorization below is pointwise in all
arrays; no independence or tail estimate is inferred from it.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.Model

/-- A finite independent-factor shape after its core / unused / detached
partition has been identified. `EC` and each `ED j` index *occurrences*, not
distinct scopes. The two boundary sets are retained in the core, including
roles read by no factor. -/
structure PreprocessedFactorShape
    (C U J : Type*) (D : J → Type*)
    (EC : Type*) (ED : J → Type*) where
  coreSize : C → ℕ
  unusedSize : U → ℕ
  detachedSize : ∀ j, D j → ℕ
  leftBoundary : Finset C
  rightBoundary : Finset C
  coreScope : EC → Finset C
  coreScope_nonempty : ∀ e, (coreScope e).Nonempty
  detachedScope : ∀ j, ED j → Finset (D j)
  detachedScope_nonempty : ∀ j e, (detachedScope j e).Nonempty

namespace PreprocessedFactorShape

variable {C U J : Type*} {D : J → Type*}
  {EC : Type*} {ED : J → Type*}
variable (S : PreprocessedFactorShape C U J D EC ED)

/-- Cartesian role assignments. -/
abbrev CoreTuple := ∀ c : C, Fin (S.coreSize c)
abbrev UnusedTuple := ∀ u : U, Fin (S.unusedSize u)
abbrev DetachedTuple (j : J) := ∀ d : D j, Fin (S.detachedSize j d)
abbrev AllDetachedTuple := ∀ j : J, S.DetachedTuple j

/-- Boundary labels are typed restrictions of core assignments. -/
abbrev BoundaryTuple (B : Finset C) :=
  ∀ c : {c : C // c ∈ B}, Fin (S.coreSize c.1)

/-- Every factor occurrence has a separate coordinate array. Equal scopes do
not identify the arrays. -/
structure Sample where
  core : ∀ e : EC,
    (∀ c : {c : C // c ∈ S.coreScope e}, Fin (S.coreSize c.1)) → ℝ
  detached : ∀ j : J, ∀ e : ED j,
    (∀ d : {d : D j // d ∈ S.detachedScope j e},
      Fin (S.detachedSize j d.1)) → ℝ

variable [Fintype C] [Fintype U] [Fintype J]
  [∀ j, Fintype (D j)] [Fintype EC] [∀ j, Fintype (ED j)]
variable [DecidableEq C] [DecidableEq U] [DecidableEq J]
  [∀ j, DecidableEq (D j)]

/-- Product of core occurrence arrays at one core assignment. -/
def coreAmplitude (ξ : S.Sample) (x : S.CoreTuple) : ℝ :=
  ∏ e : EC, ξ.core e (fun c => x c.1)

/-- Product of the occurrence arrays in one detached component. -/
def detachedAmplitude (ξ : S.Sample) (j : J)
    (x : S.DetachedTuple j) : ℝ :=
  ∏ e : ED j, ξ.detached j e (fun d => x d.1)

/-- Scalar sum belonging to one detached component. -/
def detachedScalar (ξ : S.Sample) (j : J) : ℝ :=
  ∑ x : S.DetachedTuple j, S.detachedAmplitude ξ j x

/-- Product of the unused role dimensions. -/
def unusedScalar : ℝ := ∏ u : U, (S.unusedSize u : ℝ)

/-- Core matrix entry, including boundary agreement tests. In particular,
an unused common-boundary coordinate forces equality of its row and column
labels through the shared core assignment. -/
def coreEntry (ξ : S.Sample)
    (row : S.BoundaryTuple S.leftBoundary)
    (col : S.BoundaryTuple S.rightBoundary)
    (x : S.CoreTuple) : ℝ :=
  if (∀ c : {c : C // c ∈ S.leftBoundary}, x c.1 = row c) ∧
      (∀ c : {c : C // c ∈ S.rightBoundary}, x c.1 = col c) then
    S.coreAmplitude ξ x
  else 0

def coreMatrix (ξ : S.Sample)
    (row : S.BoundaryTuple S.leftBoundary)
    (col : S.BoundaryTuple S.rightBoundary) : ℝ :=
  ∑ x : S.CoreTuple, S.coreEntry ξ row col x

/-- The full typed Cartesian sum before preprocessing. The unused tuple is
present in the sum; no factor reads it. -/
def fullMatrix (ξ : S.Sample)
    (row : S.BoundaryTuple S.leftBoundary)
    (col : S.BoundaryTuple S.rightBoundary) : ℝ :=
  ∑ x : S.CoreTuple, ∑ _unused : S.UnusedTuple,
    ∑ detached : S.AllDetachedTuple,
      (∏ j : J, S.detachedAmplitude ξ j (detached j)) *
        S.coreEntry ξ row col x

private theorem card_unusedTuple_eq_prod_sizes :
    (Fintype.card S.UnusedTuple : ℝ) = S.unusedScalar := by
  classical
  simp [UnusedTuple, unusedScalar, Fintype.card_pi]

/-- The samplewise matrix-entry decomposition `H=d(n) (∏ Z_j) H_c`.
It works for zero unused roles, zero detached components, repeated scopes,
and zero-dimensional role types; all sums/products keep their usual empty
conventions. -/
theorem fullMatrix_eq_unused_mul_detached_mul_core
    (ξ : S.Sample)
    (row : S.BoundaryTuple S.leftBoundary)
    (col : S.BoundaryTuple S.rightBoundary) :
    S.fullMatrix ξ row col =
      S.unusedScalar * (∏ j : J, S.detachedScalar ξ j) *
        S.coreMatrix ξ row col := by
  classical
  let A : ℝ := ∑ detached : S.AllDetachedTuple,
    ∏ j : J, S.detachedAmplitude ξ j (detached j)
  have hA : A = ∏ j : J, S.detachedScalar ξ j := by
    dsimp [A, detachedScalar]
    exact (Fintype.prod_sum (fun j x => S.detachedAmplitude ξ j x)).symm
  have hUnused : (Fintype.card S.UnusedTuple : ℝ) = S.unusedScalar :=
    S.card_unusedTuple_eq_prod_sizes
  unfold fullMatrix coreMatrix
  calc
    (∑ x : S.CoreTuple, ∑ _unused : S.UnusedTuple,
      ∑ detached : S.AllDetachedTuple,
        (∏ j : J, S.detachedAmplitude ξ j (detached j)) *
          S.coreEntry ξ row col x) =
      ∑ x : S.CoreTuple,
        (Fintype.card S.UnusedTuple : ℝ) *
          (A * S.coreEntry ξ row col x) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [← Finset.sum_mul]
        simp [A, nsmul_eq_mul, mul_assoc]
    _ = S.unusedScalar * (∏ j : J, S.detachedScalar ξ j) *
          ∑ x : S.CoreTuple, S.coreEntry ξ row col x := by
      rw [hUnused, hA]
      simp [Finset.mul_sum, mul_assoc]


end PreprocessedFactorShape
end GraphMatrixReplica.Model
