import R6.FiniteMengerResidualFinalFlow

/-! # Projection of augmented split paths to graph paths -/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

open FiniteIntegralFlow

variable {G : PartiteShape} {s : ℕ}
variable {family : G.VertexDisjointRightToLeftPaths s}

/-- The four kinds of forward arcs in the vertex-split network. -/
inductive AdmissibleSplitArc : ResidualNode G → ResidualNode G → Type
  | fromSource {v} (right : v ∈ G.rightBoundary) :
      AdmissibleSplitArc .source (.input v)
  | throughVertex (v) : AdmissibleSplitArc (.input v) (.output v)
  | alongGraphEdge {e a b}
      (atA : G.EdgeIncident e a) (atB : G.EdgeIncident e b) :
      AdmissibleSplitArc (.output a) (.input b)
  | toSink {v} (left : v ∈ G.leftBoundary) :
      AdmissibleSplitArc (.output v) .sink

theorem arcUnit_pos_iff {a b u v : ResidualNode G} :
    0 < arcUnit a b u v ↔ u = a ∧ v = b := by
  simp only [arcUnit]
  split <;> simp_all

theorem edgePathSplitFlow_pos_admissible
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    {u w : ResidualNode G} (hPos : 0 < edgePathSplitFlow path u w) :
    Nonempty (AdmissibleSplitArc u w) := by
  induction path with
  | finish v hLeft =>
      simp only [edgePathSplitFlow, addFlow, add_pos_iff] at hPos
      rcases hPos with hVertex | hSink
      · rcases arcUnit_pos_iff.mp hVertex with ⟨rfl, rfl⟩
        exact ⟨.throughVertex v⟩
      · rcases arcUnit_pos_iff.mp hSink with ⟨rfl, rfl⟩
        exact ⟨.toSink hLeft⟩
  | @step v e w hAtStart hAtEnd tail ih =>
      simp only [edgePathSplitFlow, addFlow, add_pos_iff] at hPos
      rcases hPos with hVertex | hEdge | hTail
      · rcases arcUnit_pos_iff.mp hVertex with ⟨rfl, rfl⟩
        exact ⟨.throughVertex v⟩
      · rcases arcUnit_pos_iff.mp hEdge with ⟨rfl, rfl⟩
        exact ⟨.alongGraphEdge hAtStart hAtEnd⟩
      · exact ih hTail

theorem edgePathFullSplitFlow_pos_admissible
    {v : Fin G.roles} (path : G.EdgePathToLeft v)
    (hRight : v ∈ G.rightBoundary) {u w : ResidualNode G}
    (hPos : 0 < edgePathFullSplitFlow path u w) :
    Nonempty (AdmissibleSplitArc u w) := by
  simp only [edgePathFullSplitFlow, addFlow, add_pos_iff] at hPos
  rcases hPos with hSource | hPath
  · rcases arcUnit_pos_iff.mp hSource with ⟨rfl, rfl⟩
    exact ⟨.fromSource hRight⟩
  · exact edgePathSplitFlow_pos_admissible path hPath

theorem oldSplitFlow_pos_admissible
    (family : G.VertexDisjointRightToLeftPaths s)
    {u v : ResidualNode G} (hPos : 0 < oldSplitFlow family u v) :
    Nonempty (AdmissibleSplitArc u v) := by
  rw [oldSplitFlow] at hPos
  obtain ⟨i, _, hTerm⟩ := (Finset.sum_pos_iff).1 hPos
  exact edgePathFullSplitFlow_pos_admissible (family.path i)
    (family.startRight i) hTerm

theorem ResidualStepData.addsArc_pos_admissible
    {x y : ResidualNode G} (step : ResidualStepData family x y)
    {u v : ResidualNode G} (hPos : 0 < step.addsArc (u, v)) :
    Nonempty (AdmissibleSplitArc u v) := by
  have hEq : step.addedFlowArc? = some (u, v) := by
    unfold ResidualStepData.addsArc at hPos
    split at hPos
    · assumption
    · omega
  cases step with
  | fromSource hRight =>
      simp [ResidualStepData.addedFlowArc?] at hEq
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨.fromSource hRight⟩
  | throughUnused hUnused =>
      simp [ResidualStepData.addedFlowArc?] at hEq
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨.throughVertex _⟩
  | backThroughUsed hUsed =>
      simp [ResidualStepData.addedFlowArc?] at hEq
  | alongEdge hAtA hAtB =>
      simp [ResidualStepData.addedFlowArc?] at hEq
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨.alongGraphEdge hAtA hAtB⟩
  | reversePackedStep hPacked =>
      simp [ResidualStepData.addedFlowArc?] at hEq
  | toSink hLeft =>
      simp [ResidualStepData.addedFlowArc?] at hEq
      rcases hEq with ⟨rfl, rfl⟩
      exact ⟨.toSink hLeft⟩

theorem ResidualProgram.addCount_pos_admissible
    {x z : ResidualNode G} (program : family.ResidualProgram x z)
    {u v : ResidualNode G} (hPos : 0 < program.addCount (u, v)) :
    Nonempty (AdmissibleSplitArc u v) := by
  induction program with
  | finish x => simp [ResidualProgram.addCount] at hPos
  | step head tail ih =>
      simp only [ResidualProgram.addCount, add_pos_iff] at hPos
      exact hPos.elim head.addsArc_pos_admissible ih

theorem ResidualProgram.finalSplitFlow_pos_admissible
    {x z : ResidualNode G} (program : family.ResidualProgram x z)
    {u v : ResidualNode G} (hPos : 0 < program.finalSplitFlow u v) :
    Nonempty (AdmissibleSplitArc u v) := by
  have hBeforePos : 0 < oldSplitFlow family u v + program.addCount (u, v) := by
    simp only [ResidualProgram.finalSplitFlow] at hPos
    omega
  rcases add_pos_iff.mp hBeforePos with hOld | hAdd
  · exact oldSplitFlow_pos_admissible family hOld
  · exact program.addCount_pos_admissible hAdd

noncomputable def ResidualProgram.admissibleArcOfPositive
    {x z : ResidualNode G} (program : family.ResidualProgram x z)
    {u v : ResidualNode G} (hPos : 0 < program.finalSplitFlow u v) :
    AdmissibleSplitArc u v :=
  Classical.choice (program.finalSplitFlow_pos_admissible hPos)

theorem edgePathSplitFlow_vertexArc_eq_count
    {v r : Fin G.roles} (path : G.EdgePathToLeft v) :
    edgePathSplitFlow path (.input r) (.output r) =
      ∑ o : Fin path.vertexCount,
        if path.vertexAt o = r then 1 else 0 := by
  induction path with
  | finish v hLeft =>
      change
        edgePathSplitFlow (PartiteShape.EdgePathToLeft.finish v hLeft)
            (.input r) (.output r) =
          ∑ _o : Fin 1, if v = r then 1 else 0
      simp [edgePathSplitFlow, addFlow, arcUnit, eq_comm]
  | @step v e w hAtStart hAtEnd tail ih =>
      change
        edgePathSplitFlow
            (PartiteShape.EdgePathToLeft.step e w hAtStart hAtEnd tail)
              (.input r) (.output r) =
          ∑ o : Fin (tail.vertexCount + 1),
            if Fin.cases v tail.vertexAt o = r then 1 else 0
      rw [Fin.sum_univ_succ]
      simp [edgePathSplitFlow, addFlow, arcUnit,
        PartiteShape.EdgePathToLeft.vertexAt, ih, eq_comm]

theorem edgePathFullSplitFlow_vertexArc_eq_count
    {v r : Fin G.roles} (path : G.EdgePathToLeft v) :
    edgePathFullSplitFlow path (.input r) (.output r) =
      ∑ o : Fin path.vertexCount,
        if path.vertexAt o = r then 1 else 0 := by
  simp [edgePathFullSplitFlow, addFlow, arcUnit,
    edgePathSplitFlow_vertexArc_eq_count]

theorem oldSplitFlow_vertexArc_eq_occurrenceCount
    (family : G.VertexDisjointRightToLeftPaths s) (r : Fin G.roles) :
    oldSplitFlow family (.input r) (.output r) =
      ∑ z : family.Occurrence,
        if family.occurrenceRole z = r then 1 else 0 := by
  rw [oldSplitFlow]
  simp_rw [edgePathFullSplitFlow_vertexArc_eq_count]
  change
    (∑ i : Fin s, ∑ o : Fin (family.path i).vertexCount,
      if (family.path i).vertexAt o = r then 1 else 0) =
      ∑ z : family.Occurrence,
        if (family.path z.1).vertexAt z.2 = r then 1 else 0
  exact (Fintype.sum_sigma' fun i o =>
    if (family.path i).vertexAt o = r then 1 else 0).symm

theorem oldSplitFlow_vertexArc_le_one
    (family : G.VertexDisjointRightToLeftPaths s) (r : Fin G.roles) :
    oldSplitFlow family (.input r) (.output r) ≤ 1 := by
  rw [oldSplitFlow_vertexArc_eq_occurrenceCount]
  change (∑ z ∈ (Finset.univ : Finset family.Occurrence),
    if family.occurrenceRole z = r then 1 else 0) ≤ 1
  apply Finset.sum_le_one_iff.mpr
  intro a b _ _ ha hb
  have hAr : family.occurrenceRole a = r := by
    simpa using ha
  have hBr : family.occurrenceRole b = r := by
    simpa using hb
  constructor
  · exact family.vertexAt_injective (hAr.trans hBr.symm)
  · simp [hAr]

theorem oldSplitFlow_vertexArc_eq_indicator
    (family : G.VertexDisjointRightToLeftPaths s) (r : Fin G.roles) :
    oldSplitFlow family (.input r) (.output r) =
      if r ∈ family.usedRoles then 1 else 0 := by
  by_cases hUsed : r ∈ family.usedRoles
  · have hPos := oldSplitFlow_vertexArc_pos family hUsed
    have hLe := oldSplitFlow_vertexArc_le_one family r
    simp [hUsed]
    omega
  · have hAvoid : ∀ z : family.Occurrence,
        family.occurrenceRole z ≠ r := by
      intro z hEq
      apply hUsed
      apply (family.mem_usedRoles_iff r).2
      exact ⟨z.1, z.2, hEq⟩
    rw [oldSplitFlow_vertexArc_eq_occurrenceCount]
    simp [hUsed, hAvoid]

theorem ResidualProgram.finalSplitFlow_vertexArc_le_one
    {x z : ResidualNode G} (program : family.ResidualProgram x z)
    (hSimple : program.IsNodeSimple) (r : Fin G.roles) :
    program.finalSplitFlow (.input r) (.output r) ≤ 1 := by
  have hCast := program.finalSplitFlow_cast hSimple (.input r) (.output r)
  rw [oldSplitFlow_vertexArc_eq_indicator] at hCast
  push_cast at hCast
  have hCapacity := program.finalVertexOccupancy_le_one hSimple r
  rw [ResidualProgram.finalVertexOccupancy,
    PartiteShape.VertexDisjointRightToLeftPaths.oldVertexOccupancy] at hCapacity
  have hInt :
      (program.finalSplitFlow (.input r) (.output r) : ℤ) ≤ 1 := by
    rw [hCast]
    exact hCapacity
  exact_mod_cast hInt

theorem AdmissibleSplitArc.fromInput_target
    {r : Fin G.roles} {y : ResidualNode G}
    (arc : AdmissibleSplitArc (.input r) y) :
    y = .output r := by
  cases arc
  rfl

inductive FromOutputView (r : Fin G.roles) (y : ResidualNode G) : Type
  | edge (e : Fin G.edges) (b : Fin G.roles)
      (atA : G.EdgeIncident e r) (atB : G.EdgeIncident e b)
      (target : y = .input b)
  | sink (target : y = .sink) (left : r ∈ G.leftBoundary)

def AdmissibleSplitArc.fromOutputView
    {r : Fin G.roles} {y : ResidualNode G}
    (arc : AdmissibleSplitArc (.output r) y) : FromOutputView r y := by
  cases arc with
  | alongGraphEdge atA atB => exact .edge _ _ atA atB rfl
  | toSink left => exact .sink rfl left

structure FromSourceView (y : ResidualNode G) where
  role : Fin G.roles
  right : role ∈ G.rightBoundary
  target : y = .input role

def AdmissibleSplitArc.fromSourceView
    {y : ResidualNode G} (arc : AdmissibleSplitArc .source y) :
    FromSourceView y := by
  cases arc with
  | fromSource right => exact ⟨_, right, rfl⟩

inductive ProjectedSuffix : ResidualNode G → Type
  | atSource (r : Fin G.roles) (right : r ∈ G.rightBoundary)
      (path : G.EdgePathToLeft r) : ProjectedSuffix .source
  | atInput {r : Fin G.roles} (path : G.EdgePathToLeft r) :
      ProjectedSuffix (.input r)
  | atOutput {r : Fin G.roles} (path : G.EdgePathToLeft r) :
      ProjectedSuffix (.output r)
  | atSink : ProjectedSuffix .sink

/- A single structural recursion simultaneously projects every suffix shape.
The indices rule out all malformed combinations of an admissible arc and its
already-projected tail. -/
def projectPositivePath (flow : ResidualNode G → ResidualNode G → ℕ)
    (hAdmissible : ∀ {u v}, 0 < flow u v → AdmissibleSplitArc u v) :
    {x : ResidualNode G} → PositivePath flow x .sink → ProjectedSuffix x
  | _, .finish _ => .atSink
  | _, .step positive tail =>
      match hAdmissible positive, projectPositivePath flow hAdmissible tail with
      | .fromSource right, .atInput path => .atSource _ right path
      | .throughVertex _, .atOutput path => .atInput path
      | .alongGraphEdge atA atB, .atInput path =>
          .atOutput (.step _ _ atA atB path)
      | .toSink left, .atSink => .atOutput (.finish _ left)

def projectFromInput (flow : ResidualNode G → ResidualNode G → ℕ)
    (hAdmissible : ∀ {u v}, 0 < flow u v → AdmissibleSplitArc u v)
    {r : Fin G.roles} (path : PositivePath flow (.input r) .sink) :
    G.EdgePathToLeft r := by
  cases projectPositivePath flow hAdmissible path with
  | atInput projected => exact projected

def projectFromOutput (flow : ResidualNode G → ResidualNode G → ℕ)
    (hAdmissible : ∀ {u v}, 0 < flow u v → AdmissibleSplitArc u v)
    {r : Fin G.roles} (path : PositivePath flow (.output r) .sink) :
    G.EdgePathToLeft r := by
  cases projectPositivePath flow hAdmissible path with
  | atOutput projected => exact projected

/-- A source-to-sink split path projected to a right-started graph path. -/
structure ProjectedSourcePath
    (flow : ResidualNode G → ResidualNode G → ℕ) where
  start : Fin G.roles
  startRight : start ∈ G.rightBoundary
  path : G.EdgePathToLeft start

def projectSourcePath (flow : ResidualNode G → ResidualNode G → ℕ)
    (hAdmissible : ∀ {u v}, 0 < flow u v → AdmissibleSplitArc u v)
    (splitPath : PositivePath flow .source .sink) :
    ProjectedSourcePath (G := G) flow := by
  cases projectPositivePath flow hAdmissible splitPath with
  | atSource r right path => exact ⟨r, right, path⟩

def edgePathRoleMultiplicity
    {v : Fin G.roles} : G.EdgePathToLeft v → Fin G.roles → ℕ
  | .finish v _, r => if v = r then 1 else 0
  | .step _ _ _ _ tail, r =>
      (if v = r then 1 else 0) + edgePathRoleMultiplicity tail r

theorem edgePathRoleMultiplicity_eq_sum
    {v : Fin G.roles} (path : G.EdgePathToLeft v) (r : Fin G.roles) :
    edgePathRoleMultiplicity path r =
      ∑ o : Fin path.vertexCount, if path.vertexAt o = r then 1 else 0 := by
  induction path with
  | finish v left =>
      change (if v = r then 1 else 0) =
        ∑ _o : Fin 1, if v = r then 1 else 0
      simp
  | @step v e w atA atB tail ih =>
      change
        (if v = r then 1 else 0) + edgePathRoleMultiplicity tail r =
          ∑ o : Fin (tail.vertexCount + 1),
            if Fin.cases v tail.vertexAt o = r then 1 else 0
      rw [Fin.sum_univ_succ, ih]
      rfl

def ProjectedSuffix.vertexMultiplicity {x : ResidualNode G}
    (projected : ProjectedSuffix (G := G) x) (r : Fin G.roles) : ℕ :=
  match projected with
  | .atSource _ _ path => edgePathRoleMultiplicity path r
  | .atInput path => edgePathRoleMultiplicity path r
  | .atOutput path => edgePathRoleMultiplicity path r
  | .atSink => 0

/-- Exact preservation of role occurrences by split-path projection.  A suffix
starting at an output node has already traversed that role's capacity arc, so
that one occurrence is supplied by the correction term. -/
theorem projectPositivePath_vertexMultiplicity
    (flow : ResidualNode G → ResidualNode G → ℕ)
    (hAdmissible : ∀ {u v}, 0 < flow u v → AdmissibleSplitArc u v)
    (r : Fin G.roles) : {x : ResidualNode G} →
    (splitPath : PositivePath flow x .sink) →
      splitPath.arcCount (.input r) (.output r) +
          (if x = .output r then 1 else 0) =
        (projectPositivePath flow hAdmissible splitPath).vertexMultiplicity r
  | _, .finish _ => by
      simp [PositivePath.arcCount, projectPositivePath,
        ProjectedSuffix.vertexMultiplicity]
  | _, .step positive tail => by
      classical
      have ih := projectPositivePath_vertexMultiplicity flow hAdmissible r tail
      generalize harc : hAdmissible positive = arc
      cases arc with
      | fromSource right =>
          cases hprojected : projectPositivePath flow hAdmissible tail with
          | atInput path =>
              simp [PositivePath.arcCount, projectPositivePath,
                ProjectedSuffix.vertexMultiplicity, edgePathRoleMultiplicity,
                harc, hprojected] at ih ⊢
              exact ih
      | throughVertex v =>
          cases hprojected : projectPositivePath flow hAdmissible tail with
          | atOutput path =>
              simp [PositivePath.arcCount, projectPositivePath,
                ProjectedSuffix.vertexMultiplicity, edgePathRoleMultiplicity,
                harc, hprojected] at ih ⊢
              omega
      | @alongGraphEdge e a b atA atB =>
          cases hprojected : projectPositivePath flow hAdmissible tail with
          | atInput path =>
              simp [PositivePath.arcCount, projectPositivePath,
                ProjectedSuffix.vertexMultiplicity, edgePathRoleMultiplicity,
                harc, hprojected] at ih ⊢
              omega
      | @toSink v left =>
          cases hprojected : projectPositivePath flow hAdmissible tail with
          | atSink =>
              simp [PositivePath.arcCount, projectPositivePath,
                ProjectedSuffix.vertexMultiplicity, edgePathRoleMultiplicity,
                harc, hprojected] at ih ⊢
              omega

/-- One projected right-started graph path, before assembling the global
vertex-disjointness certificate. -/
structure RightStartedProjectedPath where
  start : Fin G.roles
  right : start ∈ G.rightBoundary
  path : G.EdgePathToLeft start

/-- Projection of every unit path in a sequential flow decomposition, together
with the exact aggregate use of each vertex-capacity arc. -/
structure ProjectedDecomposition
    {flow : ResidualNode G → ResidualNode G → ℕ} {k : ℕ}
    (decomposition : UnitPathDecomposition (.source : ResidualNode G) .sink flow k) where
  item : Fin k → RightStartedProjectedPath (G := G)
  roleMultiplicity_eq : ∀ r : Fin G.roles,
    (∑ i : Fin k, edgePathRoleMultiplicity (item i).path r) =
      decomposition.totalArcCount (.input r) (.output r)

def projectUnitPathDecomposition
    {flow : ResidualNode G → ResidualNode G → ℕ} {k : ℕ}
    (hAdmissible : ∀ {u v}, 0 < flow u v → AdmissibleSplitArc u v) :
    (decomposition : UnitPathDecomposition (.source : ResidualNode G) .sink flow k) →
      ProjectedDecomposition decomposition
  | .zero sourceValueZero =>
      { item := fun i => Fin.elim0 i
        roleMultiplicity_eq := by
          intro r
          simp [UnitPathDecomposition.totalArcCount] }
  | .succ splitPath hPathSimple tailDecomposition => by
      let tailAdmissible : ∀ {u v},
          0 < splitPath.decrementedFlow u v → AdmissibleSplitArc u v := by
        intro u v hPositive
        apply hAdmissible
        exact lt_of_lt_of_le hPositive (Nat.sub_le _ _)
      let tailProjected :=
        projectUnitPathDecomposition tailAdmissible tailDecomposition
      cases hProjected : projectPositivePath flow hAdmissible splitPath with
      | atSource start right path =>
          exact
            { item := fun i => Fin.cases
                { start := start, right := right, path := path }
                tailProjected.item i
              roleMultiplicity_eq := by
                intro r
                rw [Fin.sum_univ_succ]
                have hHead :=
                  projectPositivePath_vertexMultiplicity
                    flow hAdmissible r splitPath
                simp [hProjected, ProjectedSuffix.vertexMultiplicity] at hHead
                simp only [Fin.cases_zero, Fin.cases_succ,
                  UnitPathDecomposition.totalArcCount]
                rw [hHead, tailProjected.roleMultiplicity_eq] }

def ProjectedDecomposition.toVertexDisjoint
    {flow : ResidualNode G → ResidualNode G → ℕ} {k : ℕ}
    {decomposition : UnitPathDecomposition
      (.source : ResidualNode G) .sink flow k}
    (projected : ProjectedDecomposition decomposition)
    (hCapacity : ∀ r : Fin G.roles,
      flow (.input r) (.output r) ≤ 1) :
    G.VertexDisjointRightToLeftPaths k := by
  let start : Fin k → Fin G.roles := fun i => (projected.item i).start
  let path : ∀ i : Fin k, G.EdgePathToLeft (start i) :=
    fun i => (projected.item i).path
  refine
    { start := start
      startRight := fun i => (projected.item i).right
      path := path
      vertexAt_injective := ?_ }
  intro a b hRoles
  let r := (path a.1).vertexAt a.2
  have hCount :
      (∑ i : Fin k, edgePathRoleMultiplicity (path i) r) ≤ 1 := by
    rw [projected.roleMultiplicity_eq]
    exact (decomposition.totalArcCount_le_flow (.input r) (.output r)).trans
      (hCapacity r)
  simp_rw [edgePathRoleMultiplicity_eq_sum] at hCount
  have hSigma :
      (∑ z : Σ i : Fin k, Fin ((path i).vertexCount),
        if (path z.1).vertexAt z.2 = r then 1 else 0) ≤ 1 := by
    calc
      _ = ∑ i : Fin k, ∑ o : Fin ((path i).vertexCount),
          if (path i).vertexAt o = r then 1 else 0 :=
        Fintype.sum_sigma' _
      _ ≤ 1 := hCount
  change
    (∑ z ∈ (Finset.univ : Finset
      (Σ i : Fin k, Fin ((path i).vertexCount))),
        if (path z.1).vertexAt z.2 = r then 1 else 0) ≤ 1 at hSigma
  have hPair := (Finset.sum_le_one_iff.mp hSigma) a b (by simp) (by simp)
    (by simp [r]) (by simpa [r] using hRoles.symm)
  exact hPair.1

end PartiteShape.VertexDisjointRightToLeftPaths

namespace PartiteShape

/-- Residual augmentation is sound: the toggled integral flow decomposes and
projects to one more globally vertex-disjoint graph path. -/
theorem residualAugmentationSound (G : PartiteShape) :
    G.ResidualAugmentationSound := by
  intro s family hReachable
  let chosen := VertexDisjointRightToLeftPaths.ResidualProgram.simpleAugmentingProgram
    family hReachable
  let program := chosen.1
  have hSimple : program.IsNodeSimple := chosen.2
  obtain ⟨decomposition⟩ := program.exists_augmentedSplitPathDecomposition hSimple
  let projected :=
    VertexDisjointRightToLeftPaths.projectUnitPathDecomposition
      (fun {_ _} hPositive => program.admissibleArcOfPositive hPositive)
      decomposition
  refine ⟨projected.toVertexDisjoint ?_⟩
  exact program.finalSplitFlow_vertexArc_le_one hSimple

/-- Unconditional finite right-left vertex-Menger strong duality. -/
theorem rightLeftOptima_eq (G : PartiteShape) :
    G.rightLeftPathPackingNumber = G.rightLeftSeparatorNumber :=
  G.rightLeftOptima_eq_of_residualAugmentationSound G.residualAugmentationSound

/-- The finite Menger certificate no longer requires an external hypothesis. -/
def rightLeftMengerCertificate (G : PartiteShape) :
    G.RightLeftMengerCertificate :=
  G.rightLeftMengerCertificateOfResidualAugmentationSound
    G.residualAugmentationSound

/-- The paper-normalized clean certificate is likewise unconditional. -/
def boundaryCleanRightLeftMengerCertificate (G : PartiteShape) :
    G.BoundaryCleanRightLeftMengerCertificate :=
  G.boundaryCleanRightLeftMengerCertificateOfResidualAugmentationSound
    G.residualAugmentationSound

end PartiteShape

#print axioms PartiteShape.residualAugmentationSound
#print axioms PartiteShape.rightLeftOptima_eq
#print axioms PartiteShape.rightLeftMengerCertificate
#print axioms PartiteShape.boundaryCleanRightLeftMengerCertificate

end GraphMatrixReplica
