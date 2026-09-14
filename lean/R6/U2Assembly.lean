import R6.U2EncodingBudget
import R6.C079EncoderAssembly

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U2

variable {G : PartiteShape} {p s : ℕ}

instance : Finite (ReplicaState G p) :=
  Finite.of_injective ReplicaState.partition state_partition_injective

instance : Fintype (ReplicaState G p) := Fintype.ofFinite _

open Classical in
attribute [local instance] propDecidable

/-- Identification with the proof-free state space used by the polynomial. -/
def admissibleDefectFiberEquiv (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ) :
    {T : AdmissiblePartitionState G p //
      ∀ x, (p + 1) - partitionBlockCount (T.1 x) = d x} ≃ DefectFiber G p d where
  toFun T := ⟨T.1.toReplicaState, T.2⟩
  invFun S := ⟨⟨S.1.partition, S.1.edgeParity, S.1.leftGlue, S.1.rightGlue⟩, S.2⟩
  left_inv T := rfl
  right_inv S := by
    apply Subtype.ext
    apply state_partition_injective
    rfl

/-- Only the original backbone projection of the fixed defect fiber is retained. -/
abbrev PathFiber (p : ℕ) (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) :=
  {B : Backbone family → ReplicaPartition (p + 1) //
    ∃ S : DefectFiber G p d, ∀ x : Backbone family, S.1.partition x.1 = B x}

/-- Legality and boundary faithfulness depend on the original backbone and
    its forward record. Quantifying over reconstruction makes this independence
    explicit; no reconstruction field is inspected by ValidRecord. -/
abbrev SeedFiber {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) :=
  {seed : G.C079CutComponent family.backboneRoles → C079MatchingPartition (p + 1) //
    ∀ reconstruction : ReconstructionFamily (p + 1) family d,
      ValidRecord (Record.mk B.1 forward seed reconstruction)}

abbrev AssemblyTarget (p : ℕ) (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) :=
  C079EncoderTarget (PathFiber p family d)
    (fun _ => ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d))
    (fun B forward => SeedFiber B forward)
    (fun _ _ _ => ReconstructionFamily (p + 1) family d)

def targetRecord {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
    (target : AssemblyTarget p family d) : Record p family d :=
  ⟨target.1.1, target.2.1, target.2.2.1.1, target.2.2.2⟩

def assemblyEncode (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) (S : DefectFiber G p d) :
    AssemblyTarget p G.maximumRightLeftPathPacking d := by
  let record := encode G p d hCovered S
  let B : PathFiber p G.maximumRightLeftPathPacking d := ⟨record.1.backbone, ⟨S, by
    intro x
    have h := congrFun (decode_encode G p d hCovered S) x.1
    simpa only [decodeRecord, dif_pos x.2] using h.symm⟩⟩
  exact ⟨B, record.1.forward, ⟨record.1.seed, fun _ => record.2⟩, record.1.reconstruction⟩

theorem targetRecord_assemblyEncode (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) (S : DefectFiber G p d) :
    targetRecord (assemblyEncode G p d hCovered S) = (encode G p d hCovered S).1 := rfl

theorem assemblyEncode_injective (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) :
    Function.Injective (assemblyEncode G p d hCovered) := by
  intro S T h
  apply encode_injective G p d hCovered
  apply Subtype.ext
  exact congrArg targetRecord h

/-- The previous assembly obligation is now supplied by a constructed map
    on actual states, with no hEncoding/hInjective/decoder assumption. -/
def actualAssembly (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) :
    C079EncoderAssemblyCertificate (DefectFiber G p d)
      (PathFiber p G.maximumRightLeftPathPacking d)
      (fun _ => ForwardCode (Fin G.roles) (p + 1)
        (3 * G.roles * offDefect G.maximumRightLeftPathPacking d))
      (fun B forward => SeedFiber B forward)
      (fun _ _ _ => ReconstructionFamily (p + 1) G.maximumRightLeftPathPacking d) where
  encode := assemblyEncode G p d hCovered
  injective := assemblyEncode_injective G p d hCovered

/-- Only path and compatible-seed counting remain as the separate U3 gates;
    the forward, reconstruction, and actual injection costs are discharged. -/
theorem actual_fiber_card_le (G : PartiteShape) (p : ℕ) (d : Fin G.roles → ℕ)
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x) (hr : 0 < G.roles)
    (pathBound seedBound : ℕ)
    (hPath : Fintype.card (PathFiber p G.maximumRightLeftPathPacking d) ≤ pathBound)
    (hSeed : ∀ (B : PathFiber p G.maximumRightLeftPathPacking d)
      (forward : ForwardCode (Fin G.roles) (p + 1)
        (3 * G.roles * offDefect G.maximumRightLeftPathPacking d)),
      Fintype.card (SeedFiber B forward) ≤ seedBound) :
    Fintype.card (DefectFiber G p d) ≤
      pathBound * seedBound *
        ((2 * G.roles) ^ (3 * G.roles * offDefect G.maximumRightLeftPathPacking d) *
          4 ^ (2 * G.roles * offDefect G.maximumRightLeftPathPacking d) *
          (p + 1) ^ ((10 * G.roles + 2) * offDefect G.maximumRightLeftPathPacking d)) := by
  let family := G.maximumRightLeftPathPacking
  let D := offDefect family d
  have h := (actualAssembly G p d hCovered).card_le_product pathBound
    ((2 * G.roles * (p + 1) ^ 2) ^ (3 * G.roles * D)) seedBound
    ((4 * (p + 1) ^ 2) ^ (2 * G.roles * D) * (p + 1) ^ (2 * D))
    hPath (fun _ => card_forward_code_le hr (Nat.succ_pos _)) hSeed
    (fun _ _ _ => card_reconstruction_family_le (p + 1) (Nat.succ_pos _) family d)
  have heq := c079_forward_and_reconstruction_power_eq G.roles (p + 1) D
  have hreorder : pathBound * (2 * G.roles * (p + 1) ^ 2) ^ (3 * G.roles * D) * seedBound *
      ((4 * (p + 1) ^ 2) ^ (2 * G.roles * D) * (p + 1) ^ (2 * D)) =
    pathBound * seedBound * ((2 * G.roles) ^ (3 * G.roles * D) *
      4 ^ (2 * G.roles * D) * (p + 1) ^ ((10 * G.roles + 2) * D)) := by
    rw [← heq]
    ring
  exact h.trans_eq hreorder

#print axioms actualAssembly
#print axioms actual_fiber_card_le
#print axioms admissibleDefectFiberEquiv
end GraphMatrixReplica.C079U2
