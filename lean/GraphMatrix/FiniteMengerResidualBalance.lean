import GraphMatrix.FiniteMengerResidualToggle

/-! # Degree balance of a typed residual edit program

Each residual step is interpreted as a signed edit of an arc in the split
network.  A forward residual step adds the corresponding flow arc; a reverse
residual step removes the oppositely oriented old flow arc.  We prove locally
that out-degree minus in-degree changes by `+1` at the residual source and
`-1` at the residual target.  The identity then telescopes along an arbitrary
typed program.

The vertex-capacity arc `input v -> output v` is treated separately.  Its old
occupancy is binary.  The premises of `throughUnused` and
`backThroughUsed` show that every individual vertex toggle preserves the
interval `[0,1]`; all other residual steps leave every vertex-capacity arc
unchanged.
-/

noncomputable section

open scoped BigOperators

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}
variable {family : G.VertexDisjointRightToLeftPaths s}
variable {x y z : ResidualNode G}

/-- Signed change of one directed split-network arc.  Reverse residual steps
carry coefficient `-1` on the old, oppositely oriented flow arc. -/
def ResidualStepData.flowArcDelta
    {x y : ResidualNode G} :
    ResidualStepData family x y →
      ResidualNode G → ResidualNode G → ℤ
  | .fromSource (v := v) _ => fun a b =>
      if a = .source ∧ b = .input v then 1 else 0
  | .throughUnused (v := v) _ => fun a b =>
      if a = .input v ∧ b = .output v then 1 else 0
  | .backThroughUsed (v := v) _ => fun a b =>
      if a = .input v ∧ b = .output v then -1 else 0
  | .alongEdge (a := a) (b := b) _ _ => fun u v =>
      if u = .output a ∧ v = .input b then 1 else 0
  | .reversePackedStep (a := a) (b := b) _ => fun u v =>
      if u = .output a ∧ v = .input b then -1 else 0
  | .toSink (v := v) _ => fun a b =>
      if a = .output v ∧ b = .sink then 1 else 0

/-- Change of the outgoing degree of a split-network node. -/
def ResidualStepData.outDegreeDelta
    {x y : ResidualNode G} :
    ResidualStepData family x y → ResidualNode G → ℤ
  | .fromSource _ => fun q => if q = .source then 1 else 0
  | .throughUnused (v := v) _ => fun q => if q = .input v then 1 else 0
  | .backThroughUsed (v := v) _ => fun q => if q = .input v then -1 else 0
  | .alongEdge (a := a) _ _ => fun q => if q = .output a then 1 else 0
  | .reversePackedStep (a := a) _ => fun q => if q = .output a then -1 else 0
  | .toSink (v := v) _ => fun q => if q = .output v then 1 else 0

/-- Change of the incoming degree of a split-network node. -/
def ResidualStepData.inDegreeDelta
    {x y : ResidualNode G} :
    ResidualStepData family x y → ResidualNode G → ℤ
  | .fromSource (v := v) _ => fun q => if q = .input v then 1 else 0
  | .throughUnused (v := v) _ => fun q => if q = .output v then 1 else 0
  | .backThroughUsed (v := v) _ => fun q => if q = .output v then -1 else 0
  | .alongEdge (b := b) _ _ => fun q => if q = .input b then 1 else 0
  | .reversePackedStep (b := b) _ => fun q => if q = .input b then -1 else 0
  | .toSink _ => fun q => if q = .sink then 1 else 0

/-- A single typed residual edit has the expected boundary: `+1` at its
source, `-1` at its target, and zero elsewhere. -/
theorem ResidualStepData.out_sub_in_eq_endpoints
    {x y : ResidualNode G} (step : ResidualStepData family x y)
    (q : ResidualNode G) :
    step.outDegreeDelta q - step.inDegreeDelta q =
      (if q = x then 1 else 0) - (if q = y then 1 else 0) := by
  cases step <;>
    simp [ResidualStepData.outDegreeDelta,
      ResidualStepData.inDegreeDelta] <;>
    split_ifs <;> omega

/-- Old occupancy of the unit-capacity vertex arc. -/
def oldVertexOccupancy
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : Fin G.roles) : ℤ :=
  if v ∈ family.usedRoles then 1 else 0

@[simp] theorem oldVertexOccupancy_nonneg
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : Fin G.roles) : 0 ≤ family.oldVertexOccupancy v := by
  unfold oldVertexOccupancy
  split_ifs <;> omega

@[simp] theorem oldVertexOccupancy_le_one
    (family : G.VertexDisjointRightToLeftPaths s)
    (v : Fin G.roles) : family.oldVertexOccupancy v ≤ 1 := by
  unfold oldVertexOccupancy
  split_ifs <;> omega

/-- Every individual typed edit preserves the binary capacity bound on every
vertex arc.  This is the local capacity invariant needed for executing a
node-simple residual program. -/
theorem ResidualStepData.vertexCapacity_preserved
    {x y : ResidualNode G} (step : ResidualStepData family x y)
    (v : Fin G.roles) :
    0 ≤ family.oldVertexOccupancy v +
        step.flowArcDelta (.input v) (.output v) ∧
      family.oldVertexOccupancy v +
        step.flowArcDelta (.input v) (.output v) ≤ 1 := by
  cases step <;>
    simp [oldVertexOccupancy, ResidualStepData.flowArcDelta] <;>
    split_ifs <;> simp_all

namespace ResidualProgram

/-- Sum of all signed arc edits in a typed residual program. -/
def flowArcDelta {x z : ResidualNode G} :
    family.ResidualProgram x z →
      ResidualNode G → ResidualNode G → ℤ
  | .finish _, _, _ => 0
  | .step head tail, a, b =>
      head.flowArcDelta a b + tail.flowArcDelta a b

/-- Total outgoing-degree change produced by a typed program. -/
def outDegreeDelta {x z : ResidualNode G} :
    family.ResidualProgram x z → ResidualNode G → ℤ
  | .finish _, _ => 0
  | .step head tail, q =>
      head.outDegreeDelta q + tail.outDegreeDelta q

/-- Total incoming-degree change produced by a typed program. -/
def inDegreeDelta {x z : ResidualNode G} :
    family.ResidualProgram x z → ResidualNode G → ℤ
  | .finish _, _ => 0
  | .step head tail, q =>
      head.inDegreeDelta q + tail.inDegreeDelta q

/-- The degree-balance identity telescopes along the whole residual program.
In particular, all internal split nodes retain flow conservation. -/
theorem out_sub_in_eq_endpoints
    (program : family.ResidualProgram x z) (q : ResidualNode G) :
    program.outDegreeDelta q - program.inDegreeDelta q =
      (if q = x then 1 else 0) - (if q = z then 1 else 0) := by
  induction program with
  | finish x => simp [outDegreeDelta, inDegreeDelta]
  | @step x y z head tail ih =>
      have hHead := head.out_sub_in_eq_endpoints q
      simp only [outDegreeDelta, inDegreeDelta]
      omega

theorem augmentingProgram_source_balance
    (program : family.ResidualProgram .source .sink) :
    program.outDegreeDelta .source - program.inDegreeDelta .source = 1 := by
  simpa using program.out_sub_in_eq_endpoints (q := ResidualNode.source)

theorem augmentingProgram_sink_balance
    (program : family.ResidualProgram .source .sink) :
    program.outDegreeDelta .sink - program.inDegreeDelta .sink = -1 := by
  simpa using program.out_sub_in_eq_endpoints (q := ResidualNode.sink)

theorem augmentingProgram_internal_balance
    (program : family.ResidualProgram .source .sink)
    (q : ResidualNode G) (hSource : q ≠ .source) (hSink : q ≠ .sink) :
    program.outDegreeDelta q = program.inDegreeDelta q := by
  have h := program.out_sub_in_eq_endpoints q
  simp [hSource, hSink] at h
  omega

end ResidualProgram


end PartiteShape.VertexDisjointRightToLeftPaths

end GraphMatrixReplica
