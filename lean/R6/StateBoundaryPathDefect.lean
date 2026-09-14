import R6.EdgeParityMatching
import R6.MatchingDefectPath

/-! # The C078 defect inequality on a graph path

Choose one compatible perfect matching on every graph edge.  Along a path
from a right-boundary role to a left-boundary role, each role partition
coarsens the matchings on its two sides.  The abstract matching-path theorem
therefore gives a defect contribution of at least `q - 1`.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Undirected incidence of a role with an edge of the partite shape. -/
def PartiteShape.EdgeIncident (G : PartiteShape)
    (e : Fin G.edges) (v : Fin G.roles) : Prop :=
  G.source e = v ∨ G.target e = v

theorem ReplicaState.partition_coarsens_edgePerfectMatching_of_incident
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (e : Fin G.edges) (v : Fin G.roles) (h : G.EdgeIncident e v) :
    PartitionCoarsens (S.partition v) (S.edgePerfectMatching e).partition := by
  rcases h with h | h
  · simpa only [h] using S.sourcePartition_coarsens_edgePerfectMatching e
  · simpa only [h] using S.targetPartition_coarsens_edgePerfectMatching e

/-- A finite graph-only edge path beginning at `v` and ending at a
left-boundary role.  The inductive presentation records exactly the vertices
whose defects are summed. -/
inductive PartiteShape.EdgePathToLeft (G : PartiteShape) :
    Fin G.roles → Type
  | finish (v : Fin G.roles) (hLeft : v ∈ G.leftBoundary) :
      G.EdgePathToLeft v
  | step {v : Fin G.roles} (e : Fin G.edges) (w : Fin G.roles)
      (hAtStart : G.EdgeIncident e v)
      (hAtEnd : G.EdgeIncident e w)
      (tail : G.EdgePathToLeft w) :
      G.EdgePathToLeft v

/-- Sum of replica defects over the vertices of an edge path. -/
def PartiteShape.EdgePathToLeft.vertexDefectSum
    {G : PartiteShape} {p : ℕ} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (S : ReplicaState G p) : ℕ :=
  match path with
  | .finish v _ => (p + 1) - partitionBlockCount (S.partition v)
  | .step (v := v) _ _ _ _ tail =>
      (p + 1) - partitionBlockCount (S.partition v) +
        tail.vertexDefectSum S

/-- Insert the chosen edge matchings and trace matchings to turn a graph path
into the abstract dependent matching path. -/
def PartiteShape.EdgePathToLeft.toMatchingDefectPath
    {G : PartiteShape} {p : ℕ} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (S : ReplicaState G p)
    (rho : PerfectMatching (p + 1))
    (hCurrent : PartitionCoarsens (S.partition v) rho.partition) :
    MatchingDefectPath (p + 1) rho :=
  match path with
  | .finish v hLeft =>
      .cons (S.partition v) (leftPerfectMatching p) hCurrent
        (leftTraceCoarsens_partitionCoarsens
          (S.partition v) (S.leftGlue v hLeft))
        (.nil (leftPerfectMatching p))
  | .step e w hAtStart hAtEnd tail =>
      .cons (S.partition v) (S.edgePerfectMatching e) hCurrent
        (S.partition_coarsens_edgePerfectMatching_of_incident e v hAtStart)
        (tail.toMatchingDefectPath S (S.edgePerfectMatching e)
          (S.partition_coarsens_edgePerfectMatching_of_incident e w hAtEnd))

@[simp] theorem PartiteShape.EdgePathToLeft.toMatchingDefectPath_endpoint
    {G : PartiteShape} {p : ℕ} {S : ReplicaState G p} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (rho : PerfectMatching (p + 1))
    (hCurrent : PartitionCoarsens (S.partition v) rho.partition) :
    (path.toMatchingDefectPath S rho hCurrent).endpoint = leftPerfectMatching p := by
  induction path generalizing rho with
  | finish => rfl
  | step e w hAtStart hAtEnd tail ih =>
      simp only [toMatchingDefectPath, MatchingDefectPath.endpoint]
      exact ih _ _

@[simp] theorem PartiteShape.EdgePathToLeft.toMatchingDefectPath_defectSum
    {G : PartiteShape} {p : ℕ} {S : ReplicaState G p} {v : Fin G.roles}
    (path : G.EdgePathToLeft v) (rho : PerfectMatching (p + 1))
    (hCurrent : PartitionCoarsens (S.partition v) rho.partition) :
    (path.toMatchingDefectPath S rho hCurrent).defectSum =
      path.vertexDefectSum S := by
  induction path generalizing rho with
  | finish => rfl
  | step e w hAtStart hAtEnd tail ih =>
      simp only [toMatchingDefectPath, MatchingDefectPath.defectSum,
        vertexDefectSum]
      rw [ih _ _]

/-- Every right-to-left graph path contributes total partition defect at
least `p = q - 1` at moment order `q = p + 1`. -/
theorem ReplicaState.rightToLeftPath_defect_lower_bound
    {G : PartiteShape} {p : ℕ} (S : ReplicaState G p)
    (v : Fin G.roles) (hRight : v ∈ G.rightBoundary)
    (path : G.EdgePathToLeft v) :
    p ≤ path.vertexDefectSum S := by
  let hStart : PartitionCoarsens (S.partition v)
      (rightPerfectMatching (p + 1)).partition :=
    rightTraceCoarsens_partitionCoarsens
      (S.partition v) (S.rightGlue v hRight)
  let matchingPath := path.toMatchingDefectPath S
    (rightPerfectMatching (p + 1)) hStart
  have hBound := standardTracePath_defect_lower_bound p matchingPath
    (path.toMatchingDefectPath_endpoint
      (S := S) (rightPerfectMatching (p + 1)) hStart)
  simpa [matchingPath] using hBound

#print axioms ReplicaState.partition_coarsens_edgePerfectMatching_of_incident
#print axioms ReplicaState.rightToLeftPath_defect_lower_bound

end GraphMatrixReplica
