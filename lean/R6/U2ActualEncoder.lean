import R6.U2ForwardCode
import R6.U2NormalizedState
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U2

variable {G : PartiteShape} {p s : ℕ}

theorem matchingDistance_comm {m : ℕ} (σ τ : C079MatchingPartition m) :
    c079MatchingPartitionDistance σ τ = c079MatchingPartitionDistance τ σ :=
  fixedRankIntersectionDistance_comm m σ.constantSubspacePoint τ.constantSubspacePoint

def offDefect (family : G.VertexDisjointRightToLeftPaths s) (d : Fin G.roles → ℕ) :=
  family.offBackboneRoles.sum d

def componentDefect (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) (c : G.C079CutComponent family.backboneRoles) :=
  (G.c079ComponentRoles family.backboneRoles c).sum d

abbrev Backbone (family : G.VertexDisjointRightToLeftPaths s) :=
  {x : Fin G.roles // x ∈ family.backboneRoles}
abbrev OffBackbone (family : G.VertexDisjointRightToLeftPaths s) :=
  {x : Fin G.roles // x ∉ family.backboneRoles}

/-- The target has a fixed defect vector. No original off-backbone partition,
    role matching, or proof of an encoding hypothesis is stored. -/
structure Record (p : ℕ) (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) where
  backbone : Backbone family → ReplicaPartition (p + 1)
  forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)
  seed : G.C079CutComponent family.backboneRoles → C079MatchingPartition (p + 1)
  reconstruction : (y : OffBackbone family) →
    ReconstructionCode (p + 1)
      (2 * componentDefect family d (G.c079OffBackboneComponent family y.1 y.2)) (d y.1)

def decodeRecord {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (record : Record p family d) (x : Fin G.roles) : ReplicaPartition (p + 1) :=
  if hx : x ∈ family.backboneRoles then record.backbone ⟨x, hx⟩
  else decodeReconstruction (record.seed (G.c079OffBackboneComponent family x hx))
    (record.reconstruction ⟨x, hx⟩)

def originalPrefix {family : G.VertexDisjointRightToLeftPaths s}
    (B : Backbone family → ReplicaPartition (p + 1)) (x : Fin G.roles) :
    ReplicaPartition (p + 1) :=
  if hx : x ∈ family.backboneRoles then B ⟨x, hx⟩ else ⊤

/-- Repaired backbone is computed before reading the seed field. -/
def normalizedRecord {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (record : Record p family d) (x : Fin G.roles) : ReplicaPartition (p + 1) :=
  if hx : x ∈ family.backboneRoles then
    decodeForward (originalPrefix record.backbone) record.forward x
  else (record.seed (G.c079OffBackboneComponent family x hx)).1

def ValidRecord {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (record : Record p family d) : Prop :=
  (∃ T : ReplicaState G p, T.partition = normalizedRecord record) ∧
  (∀ c, (∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.leftBoundary) →
    record.seed c = (leftPerfectMatching p).toC079MatchingPartition) ∧
  (∀ c, (∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.rightBoundary) →
    record.seed c = (rightPerfectMatching (p + 1)).toC079MatchingPartition)

theorem state_partition_injective : Function.Injective (ReplicaState.partition (G := G) (p := p)) := by
  intro S T h
  cases S
  cases T
  cases h
  rfl

/-- Construct all fields for an actual replica state. All existence inputs
    below are already proved tree/merge theorems, not coding assumptions. -/
theorem exists_record (S : ReplicaState G p)
    (family : G.VertexDisjointRightToLeftPaths s) (d : Fin G.roles → ℕ)
    (hd : ∀ x, (p + 1) - partitionBlockCount (S.partition x) = d x)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (hNoBoth : ∀ c : G.C079CutComponent family.backboneRoles,
      ¬ ((∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.leftBoundary) ∧
         (∃ v ∈ G.c079ComponentRoles family.backboneRoles c, v ∈ G.rightBoundary))) :
    ∃ record : Record p family d,
      decodeRecord record = S.partition ∧ ValidRecord record := by
  classical
  obtain ⟨seed, hBoundary, ⟨tree⟩⟩ :=
    S.exists_boundaryFaithfulComponentSeedTree family hCovered hNoBoth
  have hD : S.c079OffBackboneDefect family = offDefect family d := by
    simp only [ReplicaState.c079OffBackboneDefect, offDefect]
    exact Finset.sum_congr rfl (fun x _ => hd x)
  have hC (c : G.C079CutComponent family.backboneRoles) :
      S.c079ComponentDefect family c = componentDefect family d c := by
    simp only [ReplicaState.c079ComponentDefect, componentDefect]
    exact Finset.sum_congr rfl (fun x _ => hd x)
  have hWords : ∀ x : Fin G.roles, ∃ word : List (Fin (p + 1) × Fin (p + 1)),
      decodeBlockWord (S.partition x) word = S.c079ForwardBackbonePartition family seed x ∧
      word.length ≤ partitionBlockCount (S.partition x) -
        partitionBlockCount (S.c079ForwardBackbonePartition family seed x) := by
    intro x
    exact exists_block_word _ _ (S.coveredRole_blockCount_le x (hCovered x))
      (S.c079ForwardBackbonePartition_coarsens family seed x)
  choose words hWordsDec hWordsLen using hWords
  have hSum : (∑ x, (words x).length) ≤ 3 * G.roles * offDefect family d := by
    calc
      _ ≤ ∑ x, (partitionBlockCount (S.partition x) -
          partitionBlockCount (S.c079ForwardBackbonePartition family seed x)) :=
        Finset.sum_le_sum (fun x _ => hWordsLen x)
      _ ≤ _ := by
        simpa only [hD] using S.c079_forwardBackbone_totalBlockLoss_le_three_r_D
          family seed (tree.toAttachmentCertificate S family seed)
  obtain ⟨forward, hForward⟩ := exists_forward_code S.partition
    (S.c079ForwardBackbonePartition family seed) words hWordsDec hSum
  have hRecon : ∀ y : OffBackbone family,
      ∃ code : ReconstructionCode (p + 1)
        (2 * componentDefect family d (G.c079OffBackboneComponent family y.1 y.2)) (d y.1),
      decodeReconstruction (seed (G.c079OffBackboneComponent family y.1 y.2)) code =
        S.partition y.1 := by
    intro y
    apply exists_reconstruction_code (Nat.succ_pos _) _ (tree.roleMatching y.1) _
    · rw [matchingDistance_comm]
      simpa only [hC] using tree.seedDistance _ y.1
        (G.mem_c079OffBackboneComponent family y.1 y.2)
    · exact tree.roleRefines y.1
    · exact le_of_eq (hd y.1)
  choose reconstruction hReconstruction using hRecon
  let record : Record p family d := ⟨(fun x => S.partition x.1), forward, seed, reconstruction⟩
  refine ⟨record, ?_, ?_⟩
  · funext x
    by_cases hx : x ∈ family.backboneRoles
    · simp [decodeRecord, record, hx]
    · simp only [decodeRecord, dif_neg hx, record]
      exact hReconstruction ⟨x, hx⟩
  · refine ⟨⟨S.c079FullNormalizedState family seed hBoundary, ?_⟩, hBoundary.1, hBoundary.2⟩
    funext x
    change S.c079FullNormalizedPartition family seed x = normalizedRecord record x
    by_cases hx : x ∈ family.backboneRoles
    · simp only [ReplicaState.c079FullNormalizedPartition, normalizedRecord, dif_pos hx, record]
      have hF := congrFun hForward x
      simpa only [decodeForward, originalPrefix, dif_pos hx] using hF.symm
    · simp only [ReplicaState.c079FullNormalizedPartition, normalizedRecord, dif_neg hx, record]

abbrev DefectFiber (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ) :=
  {S : ReplicaState G p // ∀ x, (p + 1) - partitionBlockCount (S.partition x) = d x}

def encode (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (S : DefectFiber G p d) :
    {record : Record p G.maximumRightLeftPathPacking d // ValidRecord record} := by
  let ex := exists_record S.1 G.maximumRightLeftPathPacking d S.2 hCovered
    (by
      intro c hBoth
      exact (G.maximumPacking_no_bothBoundaryComponent c) ⟨hBoth.2, hBoth.1⟩)
  exact ⟨Classical.choose ex, (Classical.choose_spec ex).2⟩

theorem decode_encode (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) (S : DefectFiber G p d) :
    decodeRecord (encode G p d hCovered S).1 = S.1.partition := by
  exact (Classical.choose_spec (exists_record S.1 G.maximumRightLeftPathPacking d S.2
    hCovered (by
      intro c hBoth
      exact (G.maximumPacking_no_bothBoundaryComponent c) ⟨hBoth.2, hBoth.1⟩))).1

theorem encode_injective (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) :
    Function.Injective (encode G p d hCovered) := by
  intro S T h
  apply Subtype.ext
  apply state_partition_injective
  rw [← decode_encode G p d hCovered S, ← decode_encode G p d hCovered T, h]

#print axioms exists_record
#print axioms decode_encode
#print axioms encode_injective
end GraphMatrixReplica.C079U2
