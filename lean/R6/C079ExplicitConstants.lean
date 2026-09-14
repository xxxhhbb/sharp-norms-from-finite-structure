import R6.C079StatePolynomialEndpoint
import R6.C079ReplicaIntervalLayers

/-! # Explicit constants and final C079 exponent bookkeeping

This module formalizes the last arithmetic step of the revised C079 proof.
For positive role count, the path-backbone defect has coefficient `r+2`, while
the off-backbone defect has coefficient `3*r^2+10*r+2`; the latter dominates
the former.  The degenerate `r = 0` case is kept faithful to C079 by setting
`K_0 = 0` and treating the domination lemma only under `1 ≤ r`.

The final theorem specializes the state-polynomial endpoint to the explicit
constants from C079.  Its only remaining hypothesis is the actual cardinality
bound for every exact defect stratum.
-/

noncomputable section

namespace GraphMatrixReplica

def c079K (r : ℕ) : ℕ :=
  if r = 0 then 0 else 3 * r ^ 2 + 10 * r + 2

def c079C (r : ℕ) : ℕ :=
  200 ^ r * (2 * r) ^ (2 * r ^ 2) * 4 ^ (r ^ 2)

theorem c079_pathDefectCoefficient_le_K (r : ℕ) (hr : 1 ≤ r) :
    r + 2 ≤ c079K r := by
  simp only [c079K, if_neg (Nat.ne_of_gt hr)]
  nlinarith

/-- C079 equation (28), separated from all combinatorial encoding claims. -/
theorem c079_complete_exponent_bookkeeping
    (r p a deltaOn D : ℕ) (hr : 1 ≤ r) :
    a * p + (r + 2) * deltaOn + c079K r * D ≤
      a * p + c079K r * (deltaOn + D) := by
  calc
    a * p + (r + 2) * deltaOn + c079K r * D ≤
        a * p + c079K r * deltaOn + c079K r * D := by
      gcongr
      exact c079_pathDefectCoefficient_le_K r hr
    _ = a * p + c079K r * (deltaOn + D) := by ring

/-- If `delta = deltaOn + D`, the same bookkeeping is in the statement form
used by C079. -/
theorem c079_complete_exponent_bookkeeping_of_split
    (r p a delta deltaOn D : ℕ) (hr : 1 ≤ r)
    (hSplit : delta = deltaOn + D) :
    a * p + (r + 2) * deltaOn + c079K r * D ≤
      a * p + c079K r * delta := by
  subst delta
  exact c079_complete_exponent_bookkeeping r p a deltaOn D hr

/-- The existing vertex-disjoint path theorem supplies exactly the block cap
used by the C079 defect stratification. -/
theorem c079_blockTarget_cap_of_disjointPaths
    {G : PartiteShape} {p s : ℕ}
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (T : AdmissiblePartitionState G p) :
    T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s := by
  exact T.toReplicaState.totalBlockCount_le_sharp hCovered family

/-- The defect used to index the exact strata is the path-excess defect
`totalDefect - s*p` from C079 equation (6). -/
theorem c079StateDefect_eq_totalDefect_sub_paths
    {G : PartiteShape} {p s : ℕ}
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (T : AdmissiblePartitionState G p) :
    c079StateDefect G p s T = T.toReplicaState.totalDefect - s * p := by
  have hBalance :=
    T.toReplicaState.totalDefect_add_totalBlockCount hCovered
  have hDefect :=
    T.toReplicaState.disjointPaths_totalDefect_lower_bound family
  have hs := family.pathCount_le_roles
  have hTargetBalance :
      c079BlockTarget G p s + s * p = (p + 1) * G.roles := by
    unfold c079BlockTarget
    calc
      (p + 1) * (G.roles - s) + s + s * p =
          (p + 1) * ((G.roles - s) + s) := by ring
      _ = (p + 1) * G.roles := by rw [Nat.sub_add_cancel hs]
  unfold c079StateDefect
  omega

/-- Fully explicit polynomial consequence of the revised C079 constants for
the fully-partite state space.  `hCount` is intentionally visible: proving it
is the remaining forward-normalization/free-seed combinatorial obligation. -/
theorem c079_statePolynomial_le_of_explicit_allDefect_count
    (G : PartiteShape) (p s a n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hBlocks : ∀ T : AdmissiblePartitionState G p,
      T.toReplicaState.totalBlockCount ≤ c079BlockTarget G p s)
    (hscale : (p + 1) ^ c079K G.roles ≤ n)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta.1)) :
    (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) ≤
      (c079BlockTarget G p s + 1) *
        (c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s) := by
  exact c079_statePolynomial_le_of_uniform_allDefect_count
    G p s a (c079K G.roles) (c079C G.roles) n dimension
    hDimension hBlocks hscale hCount

/-- Path-family specialization with no separately supplied block-cap
hypothesis. -/
theorem c079_statePolynomial_le_of_disjointPaths_and_explicit_count
    (G : PartiteShape) (p s a n : ℕ)
    (dimension : Fin G.roles → ℕ)
    (hDimension : ∀ v : Fin G.roles, dimension v ≤ n)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hscale : (p + 1) ^ c079K G.roles ≤ n)
    (hCount : ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^
            (a * (p + 1) + c079K G.roles * delta.1)) :
    (∑ T : AdmissiblePartitionState G p,
        T.toReplicaState.labelingWeight dimension) ≤
      (c079BlockTarget G p s + 1) *
        (c079C G.roles ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1)) *
            n ^ c079BlockTarget G p s) := by
  exact c079_statePolynomial_le_of_explicit_allDefect_count
    G p s a n dimension hDimension
    (c079_blockTarget_cap_of_disjointPaths hCovered family)
    hscale hCount

#print axioms c079_pathDefectCoefficient_le_K
#print axioms c079_complete_exponent_bookkeeping
#print axioms c079_complete_exponent_bookkeeping_of_split
#print axioms c079_blockTarget_cap_of_disjointPaths
#print axioms c079StateDefect_eq_totalDefect_sub_paths
#print axioms c079_statePolynomial_le_of_explicit_allDefect_count
#print axioms c079_statePolynomial_le_of_disjointPaths_and_explicit_count

end GraphMatrixReplica
