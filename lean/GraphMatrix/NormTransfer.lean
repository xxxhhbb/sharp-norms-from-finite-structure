import GraphMatrix.RoleColoredPartiteBridge

/-!
# Transfer from the partite model

This module states the norm comparison between the globally injective graph
matrix and its independently labelled partite model. The comparison is an
explicit hypothesis of this interface. Its concrete instantiation is supplied
by the color-projection and norm-transfer modules.

The nonempty-core branch has the explicit hypothesis `0 < G.roles`.
Isolated middle roles and the zero-role case are handled separately.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

/-- Real-valued version of the rational fully-partite boundary matrix. -/
def c027PartiteBoundaryMatrixReal
    (G : PaperShape) (dimension : Fin G.roles → ℕ)
    (epsilon : JointEdgeSignSample (G := G.toPartiteShape) dimension) :
    Matrix (PartiteBoundaryRow (G := G.toPartiteShape) dimension)
      (PartiteBoundaryCol (G := G.toPartiteShape) dimension) ℝ :=
  fun row col =>
    ((partiteBoundaryMatrix G.toPartiteShape dimension epsilon row col : ℚ) : ℝ)

/-- Expected operator norm of the original shared-unordered-edge paper
matrix, with the finite uniform expectation already used throughout R6. -/
def c027PaperExpectedOperatorNorm (G : PaperShape) (n : ℕ) : ℝ :=
  paperMean (fun w : PaperNoise n => ‖paperGraphMatrix G n w‖)

/-- Expected operator norm of the independent-edge fully-partite surrogate.
The role dimensions are a labelled size vector; they need not be equal. -/
def c027PartiteExpectedOperatorNorm
    (G : PaperShape) (dimension : Fin G.roles → ℕ) : ℝ :=
  paperMean (fun epsilon :
      JointEdgeSignSample (G := G.toPartiteShape) dimension =>
    ‖c027PartiteBoundaryMatrixReal G dimension epsilon‖)

/-- A labelled balanced size vector: its entries sum to the ambient size and
any two class sizes differ by at most one.  The asymmetric-looking inequality
is quantified in both orders, so it is the usual pairwise balance condition. -/
def C027BalancedSizeVector
    (G : PaperShape) (n : ℕ) (dimension : Fin G.roles → ℕ) : Prop :=
  (∑ v : Fin G.roles, dimension v) = n ∧
    ∀ v w : Fin G.roles, dimension v ≤ dimension w + 1

/-- The pointwise two-sided expected-operator-norm conclusion at one ambient
size and one labelled balanced size vector.  This is a norm statement only. -/
def C027ExpectedNormComparisonAt
    (G : PaperShape) (n : ℕ) (dimension : Fin G.roles → ℕ)
    (lowerConstant upperConstant : ℝ) : Prop :=
  lowerConstant * c027PartiteExpectedOperatorNorm G dimension ≤
      c027PaperExpectedOperatorNorm G n ∧
    c027PaperExpectedOperatorNorm G n ≤
      upperConstant * c027PartiteExpectedOperatorNorm G dimension

/-- Explicit analytic input corresponding to C027 for one fixed reduced
shape.  `threshold`, `lowerConstant`, and `upperConstant` are chosen before
`n` and `dimension`, making their shape-only dependence visible in the type.

Constructing this structure is precisely the still-unformalized C027
random-coloring/Fourier-projection obligation.  Merely importing this file
does not provide such a construction. -/
structure C027NormTransferHypothesis (G : PaperShape) where
  nonemptyCore : 0 < G.roles
  noIsolatedMiddleRoles : G.HasNoIsolatedMiddleRoles
  threshold : ℕ
  lowerConstant : ℝ
  upperConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  upperConstant_pos : 0 < upperConstant
  comparison : ∀ (n : ℕ) (dimension : Fin G.roles → ℕ),
    threshold ≤ n →
    C027BalancedSizeVector G n dimension →
    C027ExpectedNormComparisonAt G n dimension
      lowerConstant upperConstant

/-- Once an explicit C027 hypothesis has been supplied, its fixed constants
specialize to every sufficiently large balanced labelled size vector. -/
theorem C027NormTransferHypothesis.expectedNormComparison
    {G : PaperShape} (hC027 : C027NormTransferHypothesis G)
    {n : ℕ} {dimension : Fin G.roles → ℕ}
    (hn : hC027.threshold ≤ n)
    (hBalanced : C027BalancedSizeVector G n dimension) :
    C027ExpectedNormComparisonAt G n dimension
      hC027.lowerConstant hC027.upperConstant :=
  hC027.comparison n dimension hn hBalanced

/-- Existential presentation of the same large-`n`, shape-uniform constants.
This theorem is only logical unpacking of the explicit analytic hypothesis. -/
theorem C027NormTransferHypothesis.exists_shapeUniformConstants
    {G : PaperShape} (hC027 : C027NormTransferHypothesis G) :
    ∃ (n₀ : ℕ) (cLower cUpper : ℝ),
      0 < cLower ∧ 0 < cUpper ∧
      ∀ (n : ℕ) (dimension : Fin G.roles → ℕ),
        n₀ ≤ n →
        C027BalancedSizeVector G n dimension →
        C027ExpectedNormComparisonAt G n dimension cLower cUpper := by
  exact ⟨hC027.threshold, hC027.lowerConstant, hC027.upperConstant,
    hC027.lowerConstant_pos, hC027.upperConstant_pos, hC027.comparison⟩


end GraphMatrixReplica
