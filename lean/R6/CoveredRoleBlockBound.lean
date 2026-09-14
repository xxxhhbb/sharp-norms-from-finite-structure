import R6.PairCoarseningEvenPartition

/-! # Block bounds for every retained C078 role

After isolated middle roles are removed, every retained role is either an
endpoint of an edge or belongs to a left/right boundary.  The earlier parity
lemmas therefore give the uniform per-role block bound used before the sharper
separator argument.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A role is retained by the exact replica state when it is incident to an
edge or belongs to at least one external boundary. -/
def PartiteShape.RoleCovered (G : PartiteShape) (v : Fin G.roles) : Prop :=
  (∃ e : Fin G.edges, G.source e = v ∨ G.target e = v) ∨
    v ∈ G.leftBoundary ∨ v ∈ G.rightBoundary

/-- Every covered role has at most the moment order many equality blocks. -/
theorem ReplicaState.coveredRole_blockCount_le
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (v : Fin G.roles) (hv : G.RoleCovered v) :
    partitionBlockCount (S.partition v) ≤ p + 1 := by
  rcases hv with ⟨e, he | he⟩ | hL | hR
  · simpa only [he] using (S.edgeEndpoint_blockCount_le e).1
  · simpa only [he] using (S.edgeEndpoint_blockCount_le e).2
  · exact leftTraceCoarsens_blockCount_le (S.partition v) (S.leftGlue v hL)
  · exact rightTraceCoarsens_blockCount_le (S.partition v) (S.rightGlue v hR)

/-- Total number of equality blocks in a replica state. -/
def ReplicaState.totalBlockCount {G : PartiteShape} {p : ℕ}
    (S : ReplicaState G p) : ℕ :=
  ∑ v : Fin G.roles, partitionBlockCount (S.partition v)

/-- Coarse degree bound for a shape with no isolated middle roles.  The
sharper C078 bound `p(r-s)+s` additionally needs the matching-distance and
vertex-disjoint-path argument. -/
theorem ReplicaState.totalBlockCount_le
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (hCovered : ∀ v : Fin G.roles, G.RoleCovered v) :
    S.totalBlockCount ≤ (p + 1) * G.roles := by
  unfold ReplicaState.totalBlockCount
  calc
    (∑ v : Fin G.roles, partitionBlockCount (S.partition v)) ≤
        ∑ _v : Fin G.roles, (p + 1) := by
      apply Finset.sum_le_sum
      intro v _
      exact S.coveredRole_blockCount_le v (hCovered v)
    _ = (p + 1) * G.roles := by simp [Nat.mul_comm]

#print axioms ReplicaState.coveredRole_blockCount_le
#print axioms ReplicaState.totalBlockCount_le

end GraphMatrixReplica
