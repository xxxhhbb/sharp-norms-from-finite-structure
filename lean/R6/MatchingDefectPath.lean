import R6.TraceMatchingDistance

/-! # Accumulating partition defects along a matching path

Each path vertex carries a replica partition coarsening the two adjacent
matching states.  The local matching distance is bounded by that vertex's
defect.  Triangle inequality then makes the endpoint distance no larger than
the sum of all vertex defects.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A dependent path that starts at a specified matching.  Every step records
the vertex partition between the current and next matching. -/
inductive MatchingDefectPath (p : ℕ) : PerfectMatching p → Type
  | nil (rho : PerfectMatching p) : MatchingDefectPath p rho
  | cons {rho : PerfectMatching p}
      (pi : ReplicaPartition p) (sigma : PerfectMatching p)
      (hCurrent : PartitionCoarsens pi rho.partition)
      (hNext : PartitionCoarsens pi sigma.partition)
      (tail : MatchingDefectPath p sigma) :
      MatchingDefectPath p rho

/-- Final matching reached by the path. -/
def MatchingDefectPath.endpoint
    {p : ℕ} {rho : PerfectMatching p} :
    MatchingDefectPath p rho → PerfectMatching p
  | .nil _ => rho
  | .cons _ _ _ _ tail => tail.endpoint

/-- Sum of p minus the block count over all path vertices. -/
def MatchingDefectPath.defectSum
    {p : ℕ} {rho : PerfectMatching p} :
    MatchingDefectPath p rho → ℕ
  | .nil _ => 0
  | .cons pi _ _ _ tail =>
      (p - partitionBlockCount pi) + tail.defectSum

/-- Endpoint distance is bounded by the accumulated vertex defects. -/
theorem MatchingDefectPath.endpointDistance_le_defectSum
    {p : ℕ} {rho : PerfectMatching p}
    (path : MatchingDefectPath p rho) :
    matchingIntersectionDistance rho path.endpoint ≤ path.defectSum := by
  induction path with
  | nil rho =>
      exact Nat.le_of_eq (matchingIntersectionDistance_self rho)
  | @cons rho pi sigma hCurrent hNext tail ih =>
      exact (matchingIntersectionDistance_triangle rho sigma tail.endpoint).trans
        (Nat.add_le_add
          (matchingIntersectionDistance_le_partitionDefect
            pi rho sigma hCurrent hNext)
          ih)

/-- C078's one-path inequality for the standard trace endpoints. -/
theorem standardTracePath_defect_lower_bound
    (p : ℕ)
    (path : MatchingDefectPath (p + 1) (rightPerfectMatching (p + 1)))
    (hEnd : path.endpoint = leftPerfectMatching p) :
    p ≤ path.defectSum := by
  calc
    p = matchingIntersectionDistance (rightPerfectMatching (p + 1))
        (leftPerfectMatching p) :=
      (right_left_matchingIntersectionDistance_eq p).symm
    _ = matchingIntersectionDistance (rightPerfectMatching (p + 1))
        path.endpoint := by rw [hEnd]
    _ ≤ path.defectSum := path.endpointDistance_le_defectSum

#print axioms MatchingDefectPath.endpointDistance_le_defectSum
#print axioms standardTracePath_defect_lower_bound

end GraphMatrixReplica
