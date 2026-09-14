import GraphMatrix.FiniteIntegralFlowReachability

/-! # Simple positive paths in finite integral flows

This file turns proposition-valued positive-flow reachability into a concrete
dependent path, erases loops, and records the exact arc multiplicities needed
to subtract one unit of flow.
-/

noncomputable section

open scoped BigOperators

namespace FiniteIntegralFlow

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A concrete directed path all of whose arcs carry positive flow. -/
inductive PositivePath {V : Type u} (flow : V → V → ℕ) : V → V → Type u
  | finish (x) : PositivePath flow x x
  | step {x y z} (positive : 0 < flow x y)
      (tail : PositivePath flow y z) : PositivePath flow x z

namespace PositivePath

variable {flow : V → V → ℕ} {x y z : V}

def nodeCount : {x z : V} → PositivePath flow x z → ℕ
  | _, _, .finish _ => 1
  | _, _, .step _ tail => nodeCount tail + 1

def nodeAt : {x z : V} → (path : PositivePath flow x z) →
    Fin path.nodeCount → V
  | _, _, .finish x => fun _ => x
  | x, _, .step _ tail => Fin.cases x (nodeAt tail)

def headOccurrence (path : PositivePath flow x z) : Fin path.nodeCount :=
  ⟨0, by cases path <;> simp [nodeCount]⟩

@[simp] theorem nodeAt_headOccurrence (path : PositivePath flow x z) :
    path.nodeAt path.headOccurrence = x := by
  cases path <;> rfl

def IsNodeSimple (path : PositivePath flow x z) : Prop :=
  Function.Injective path.nodeAt

theorem finish_isNodeSimple (x : V) :
    (PositivePath.finish (flow := flow) x).IsNodeSimple := by
  intro a b _
  apply Fin.ext
  have ha : a.val < 1 := by simpa [nodeCount] using a.isLt
  have hb : b.val < 1 := by simpa [nodeCount] using b.isLt
  omega

def snoc : {x y z : V} → PositivePath flow x y →
    (0 < flow y z) → PositivePath flow x z
  | _, _, _, .finish _, last => .step last (.finish _)
  | _, _, _, .step head tail, last => .step head (snoc tail last)

theorem toReachable (path : PositivePath flow x z) :
    Relation.ReflTransGen (PositiveArc flow) x z := by
  induction path with
  | finish x => exact .refl
  | step positive tail ih => exact .head positive ih

theorem nonempty_positivePath_iff_reachable
    (flow : V → V → ℕ) (x z : V) :
    Nonempty (PositivePath flow x z) ↔
      Relation.ReflTransGen (PositiveArc flow) x z := by
  constructor
  · rintro ⟨path⟩
    exact path.toReachable
  · intro hReachable
    induction hReachable with
    | refl => exact ⟨.finish _⟩
    | @tail b c hPrefix hStep ih =>
        obtain ⟨prefixPath⟩ := ih
        exact ⟨prefixPath.snoc hStep⟩

def suffixAt : {x z : V} → (path : PositivePath flow x z) →
    (o : Fin path.nodeCount) → PositivePath flow (path.nodeAt o) z
  | _, _, .finish x, _ => .finish x
  | _, _, .step positive tail, o =>
      Fin.cases (.step positive tail) (fun j => tail.suffixAt j) o

theorem suffixAt_node_mem (path : PositivePath flow x z)
    (o : Fin path.nodeCount) (u : Fin (path.suffixAt o).nodeCount) :
    ∃ old : Fin path.nodeCount,
      (path.suffixAt o).nodeAt u = path.nodeAt old := by
  induction path with
  | finish x => exact ⟨u, rfl⟩
  | step positive tail ih =>
      cases o using Fin.cases with
      | zero => exact ⟨u, rfl⟩
      | succ o =>
          obtain ⟨old, hOld⟩ := ih o u
          exact ⟨Fin.succ old, hOld⟩

theorem suffixAt_isNodeSimple (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (o : Fin path.nodeCount) :
    (path.suffixAt o).IsNodeSimple := by
  induction path with
  | finish x => exact finish_isNodeSimple x
  | @step x y z positive tail ih =>
      cases o using Fin.cases with
      | zero => exact hSimple
      | succ o =>
          apply ih
          intro a b hNode
          exact Fin.succ_injective _ (hSimple hNode)

structure SimpleReduction (original : PositivePath flow x z) where
  reduced : PositivePath flow x z
  isNodeSimple : reduced.IsNodeSimple
  node_mem_original : ∀ o : Fin reduced.nodeCount,
    ∃ old : Fin original.nodeCount, reduced.nodeAt o = original.nodeAt old

def SimpleReduction.ofStartEq {w : V} (original : PositivePath flow x z)
    (candidate : PositivePath flow w z) (hStart : w = x)
    (hSimple : candidate.IsNodeSimple)
    (hMem : ∀ o : Fin candidate.nodeCount,
      ∃ old : Fin original.nodeCount,
        candidate.nodeAt o = original.nodeAt old) :
    SimpleReduction original := by
  subst x
  exact
    { reduced := candidate
      isNodeSimple := hSimple
      node_mem_original := hMem }

/-- Directed loop erasure; positivity is retained in the type of the result. -/
def loopErase (path : PositivePath flow x z) : SimpleReduction path := by
  classical
  induction path with
  | finish x =>
      exact
        { reduced := .finish x
          isNodeSimple := finish_isNodeSimple x
          node_mem_original := fun o => ⟨o, rfl⟩ }
  | @step x y z positive tail tailReduction =>
      let original : PositivePath flow x z := .step positive tail
      by_cases hHeadOccurs : ∃ o : Fin tailReduction.reduced.nodeCount,
          tailReduction.reduced.nodeAt o = x
      · have hWitness : Nonempty {o : Fin tailReduction.reduced.nodeCount //
            tailReduction.reduced.nodeAt o = x} := by
          rcases hHeadOccurs with ⟨o, hNode⟩
          exact ⟨⟨o, hNode⟩⟩
        let witness := Classical.choice hWitness
        let o : Fin tailReduction.reduced.nodeCount := witness.1
        have hNode : tailReduction.reduced.nodeAt o = x := witness.2
        let candidate := tailReduction.reduced.suffixAt o
        have hCandidateSimple : candidate.IsNodeSimple :=
          tailReduction.reduced.suffixAt_isNodeSimple
            tailReduction.isNodeSimple o
        have hCandidateMem : ∀ u : Fin candidate.nodeCount,
            ∃ old : Fin original.nodeCount,
              candidate.nodeAt u = original.nodeAt old := by
          intro u
          obtain ⟨middle, hMiddle⟩ :=
            tailReduction.reduced.suffixAt_node_mem o u
          obtain ⟨old, hOld⟩ := tailReduction.node_mem_original middle
          exact ⟨Fin.succ old, hMiddle.trans hOld⟩
        simpa [original] using
          SimpleReduction.ofStartEq original candidate hNode
            hCandidateSimple hCandidateMem
      · refine
          { reduced := .step positive tailReduction.reduced
            isNodeSimple := ?_
            node_mem_original := ?_ }
        · intro a b hNodes
          cases a using Fin.cases with
          | zero =>
              cases b using Fin.cases with
              | zero => rfl
              | succ b => exact False.elim (hHeadOccurs ⟨b, hNodes.symm⟩)
          | succ a =>
              cases b using Fin.cases with
              | zero => exact False.elim (hHeadOccurs ⟨a, hNodes⟩)
              | succ b =>
                  have hab : a = b := tailReduction.isNodeSimple hNodes
                  subst b
                  rfl
        · intro u
          cases u using Fin.cases with
          | zero => exact ⟨original.headOccurrence, rfl⟩
          | succ u =>
              obtain ⟨old, hOld⟩ := tailReduction.node_mem_original u
              exact ⟨Fin.succ old, hOld⟩

/-- A positive-flow reachability witness can be chosen node-simple. -/
def simplePathOfReachable (flow : V → V → ℕ) (x z : V)
    (h : Relation.ReflTransGen (PositiveArc flow) x z) :
    {path : PositivePath flow x z // path.IsNodeSimple} := by
  let original := Classical.choice
    ((nonempty_positivePath_iff_reachable flow x z).2 h)
  exact ⟨original.loopErase.reduced, original.loopErase.isNodeSimple⟩

/-- Number of times a directed arc occurs in a concrete path. -/
def arcCount : {x z : V} → PositivePath flow x z → V → V → ℕ
  | _, _, .finish _, _, _ => 0
  | x, _, .step (y := y) _ tail, u, v =>
      (if x = u ∧ y = v then 1 else 0) + tail.arcCount u v

theorem arcCount_pos_implies_flow_pos (path : PositivePath flow x z)
    {u v : V} (h : 0 < path.arcCount u v) : 0 < flow u v := by
  induction path with
  | finish x => simp [arcCount] at h
  | @step x y z positive tail ih =>
      simp only [arcCount] at h
      by_cases hxy : x = u ∧ y = v
      · simpa [hxy.1, hxy.2] using positive
      · simpa [hxy] using ih (by simpa [hxy] using h)

theorem arcCount_pos_implies_source_occurs (path : PositivePath flow x z)
    {u v : V} (h : 0 < path.arcCount u v) :
    ∃ o : Fin path.nodeCount, path.nodeAt o = u := by
  induction path with
  | finish x => simp [arcCount] at h
  | @step x y z positive tail ih =>
      by_cases hxy : x = u ∧ y = v
      · exact ⟨(PositivePath.step positive tail).headOccurrence,
          (nodeAt_headOccurrence _).trans hxy.1⟩
      · obtain ⟨o, ho⟩ := ih (by simpa [arcCount, hxy] using h)
        exact ⟨Fin.succ o, ho⟩

theorem arcCount_le_one_of_isNodeSimple (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (u v : V) : path.arcCount u v ≤ 1 := by
  induction path with
  | finish x => simp [arcCount]
  | @step x y z positive tail ih =>
      by_cases hxy : x = u ∧ y = v
      · have hTailZero : tail.arcCount u v = 0 := by
          by_contra hNe
          have hPos : 0 < tail.arcCount u v := Nat.pos_of_ne_zero hNe
          obtain ⟨o, ho⟩ := arcCount_pos_implies_source_occurs tail hPos
          have hNodes :
              (PositivePath.step positive tail).nodeAt
                  (PositivePath.step positive tail).headOccurrence =
                (PositivePath.step positive tail).nodeAt (Fin.succ o) := by
            calc
              _ = x := nodeAt_headOccurrence _
              _ = u := hxy.1
              _ = tail.nodeAt o := ho.symm
              _ = _ := rfl
          have hIndices := hSimple hNodes
          have hVals := congrArg Fin.val hIndices
          simp [headOccurrence] at hVals
        simp [arcCount, hxy, hTailZero]
      · simpa [arcCount, hxy] using ih (by
          intro a b hNode
          exact Fin.succ_injective _ (hSimple hNode))

theorem arcCount_le_flow_of_isNodeSimple (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (u v : V) :
    path.arcCount u v ≤ flow u v := by
  by_cases hZero : path.arcCount u v = 0
  · simp [hZero]
  · exact (path.arcCount_le_one_of_isNodeSimple hSimple u v).trans
      (arcCount_pos_implies_flow_pos path (Nat.pos_of_ne_zero hZero))

def outArcCount (path : PositivePath flow x z) (v : V) : ℕ :=
  ∑ w, path.arcCount v w

def inArcCount (path : PositivePath flow x z) (v : V) : ℕ :=
  ∑ u, path.arcCount u v

@[simp] theorem outArcCount_finish (v x : V) :
    (PositivePath.finish (flow := flow) x).outArcCount v = 0 := by
  simp [outArcCount, arcCount]

@[simp] theorem inArcCount_finish (v x : V) :
    (PositivePath.finish (flow := flow) x).inArcCount v = 0 := by
  simp [inArcCount, arcCount]

@[simp] theorem outArcCount_step {x y z : V} (positive : 0 < flow x y)
    (tail : PositivePath flow y z) (v : V) :
    (PositivePath.step positive tail).outArcCount v =
      (if x = v then 1 else 0) + tail.outArcCount v := by
  classical
  simp only [outArcCount, arcCount, Finset.sum_add_distrib]
  by_cases hxv : x = v
  · subst v
    simp
  · simp [hxv]

@[simp] theorem inArcCount_step {x y z : V} (positive : 0 < flow x y)
    (tail : PositivePath flow y z) (v : V) :
    (PositivePath.step positive tail).inArcCount v =
      (if y = v then 1 else 0) + tail.inArcCount v := by
  classical
  simp only [inArcCount, arcCount, Finset.sum_add_distrib]
  by_cases hyv : y = v
  · subst v
    simp
  · simp [hyv]

/-- The arc-incidence vector of a directed path has boundary `x - z`. -/
theorem arcCount_balance (path : PositivePath flow x z) (v : V) :
    path.outArcCount v + (if z = v then 1 else 0) =
      path.inArcCount v + (if x = v then 1 else 0) := by
  induction path with
  | finish x => simp
  | @step x y z positive tail ih =>
      simp only [outArcCount_step, inArcCount_step]
      omega

def decrementedFlow (path : PositivePath flow x z) : V → V → ℕ :=
  fun u v => flow u v - path.arcCount u v

theorem decrementedFlow_add_arcCount (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (u v : V) :
    path.decrementedFlow u v + path.arcCount u v = flow u v := by
  exact Nat.sub_add_cancel (path.arcCount_le_flow_of_isNodeSimple hSimple u v)

theorem out_decrementedFlow (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (v : V) :
    Out path.decrementedFlow v = Out flow v - path.outArcCount v := by
  classical
  exact Finset.sum_tsub_distrib Finset.univ (fun w _ =>
    path.arcCount_le_flow_of_isNodeSimple hSimple v w)

theorem in_decrementedFlow (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (v : V) :
    In path.decrementedFlow v = In flow v - path.inArcCount v := by
  classical
  exact Finset.sum_tsub_distrib Finset.univ (fun u _ =>
    path.arcCount_le_flow_of_isNodeSimple hSimple u v)

def Excess (flow : V → V → ℕ) (v : V) : ℤ :=
  (Out flow v : ℤ) - (In flow v : ℤ)

/-- Subtracting a simple positive path changes excess only at its endpoints. -/
theorem excess_decrementedFlow (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (v : V) :
    Excess path.decrementedFlow v = Excess flow v -
      ((if x = v then 1 else 0) - (if z = v then 1 else 0) : ℤ) := by
  have hOutLe : path.outArcCount v ≤ Out flow v := by
    exact Finset.sum_le_sum fun w _ =>
      path.arcCount_le_flow_of_isNodeSimple hSimple v w
  have hInLe : path.inArcCount v ≤ In flow v := by
    exact Finset.sum_le_sum fun u _ =>
      path.arcCount_le_flow_of_isNodeSimple hSimple u v
  have hBalance :
      (path.outArcCount v : ℤ) - (path.inArcCount v : ℤ) =
        ((if x = v then 1 else 0) - (if z = v then 1 else 0) : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) (path.arcCount_balance v)
    push_cast at h
    split <;> split <;> simp_all <;> omega
  change
    ((Out path.decrementedFlow v : ℤ) - (In path.decrementedFlow v : ℤ)) =
      ((Out flow v : ℤ) - (In flow v : ℤ)) - _
  rw [path.out_decrementedFlow hSimple,
    path.in_decrementedFlow hSimple,
    Int.ofNat_sub hOutLe, Int.ofNat_sub hInLe]
  omega

theorem excess_decrementedFlow_source (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (hxz : x ≠ z) :
    Excess path.decrementedFlow x = Excess flow x - 1 := by
  simpa [hxz, Ne.symm hxz] using path.excess_decrementedFlow hSimple x

theorem excess_decrementedFlow_sink (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (hxz : x ≠ z) :
    Excess path.decrementedFlow z = Excess flow z + 1 := by
  simpa [hxz, Ne.symm hxz] using path.excess_decrementedFlow hSimple z

theorem excess_decrementedFlow_internal (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) {v : V} (hvx : v ≠ x) (hvz : v ≠ z) :
    Excess path.decrementedFlow v = Excess flow v := by
  simpa [Ne.symm hvx, Ne.symm hvz] using
    path.excess_decrementedFlow hSimple v

theorem in_decrementedFlow_eq_zero (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) {v : V} (hZero : In flow v = 0) :
    In path.decrementedFlow v = 0 := by
  rw [path.in_decrementedFlow hSimple, hZero]
  simp

theorem out_decrementedFlow_eq_zero (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) {v : V} (hZero : Out flow v = 0) :
    Out path.decrementedFlow v = 0 := by
  rw [path.out_decrementedFlow hSimple, hZero]
  simp

theorem out_decrementedFlow_source (path : PositivePath flow x z)
    (hSimple : path.IsNodeSimple) (hxz : x ≠ z)
    (hNoIn : In flow x = 0) (hPositive : 0 < Out flow x) :
    Out path.decrementedFlow x = Out flow x - 1 := by
  have hNoIn' : In path.decrementedFlow x = 0 :=
    path.in_decrementedFlow_eq_zero hSimple hNoIn
  have hExcess := path.excess_decrementedFlow_source hSimple hxz
  simp only [Excess, hNoIn, hNoIn', Int.ofNat_zero, sub_zero] at hExcess
  omega

end PositivePath

abbrev Excess (flow : V → V → ℕ) (v : V) : ℤ :=
  PositivePath.Excess flow v

/-- A sequential decomposition of `k` units of an integral flow into simple
positive source-to-sink paths.  Each tail lives in the flow obtained by
subtracting the preceding path. -/
inductive UnitPathDecomposition {V : Type u} [Fintype V] [DecidableEq V]
    (source sink : V) :
    (V → V → ℕ) → ℕ → Type u
  | zero {flow} (sourceValueZero : Out flow source = 0) :
      UnitPathDecomposition source sink flow 0
  | succ {flow k} (path : PositivePath flow source sink)
      (isNodeSimple : path.IsNodeSimple)
      (tail : UnitPathDecomposition source sink path.decrementedFlow k) :
      UnitPathDecomposition source sink flow (k + 1)

namespace UnitPathDecomposition

/-- Total use of a directed arc by all extracted unit paths. -/
def totalArcCount {source sink : V} {flow : V → V → ℕ} {k : ℕ} :
    UnitPathDecomposition source sink flow k → V → V → ℕ
  | .zero _, _, _ => 0
  | .succ path _ tail, u, v =>
      path.arcCount u v + tail.totalArcCount u v

/-- Path decomposition never uses an arc more often than its initial flow. -/
theorem totalArcCount_le_flow {source sink : V} {flow : V → V → ℕ} {k : ℕ}
    (decomposition : UnitPathDecomposition source sink flow k) (u v : V) :
    decomposition.totalArcCount u v ≤ flow u v := by
  induction decomposition with
  | zero hZero => simp [totalArcCount]
  | @succ flow k path hSimple tail ih =>
      have hRestore := path.decrementedFlow_add_arcCount hSimple u v
      simp only [totalArcCount]
      omega

theorem totalArcCount_le_one_of_flow_le_one
    {source sink : V} {flow : V → V → ℕ} {k : ℕ}
    (decomposition : UnitPathDecomposition source sink flow k)
    (hCapacity : flow u v ≤ 1) :
    decomposition.totalArcCount u v ≤ 1 :=
  (decomposition.totalArcCount_le_flow u v).trans hCapacity

end UnitPathDecomposition

/-- Every finite integral source/sink flow with no inflow at the source, no
outflow at the sink, and conservation elsewhere decomposes into exactly its
source value many simple positive paths.  Circulations may remain after the
last path; they are irrelevant to the source-to-sink value. -/
theorem exists_unitPathDecomposition
    (flow : V → V → ℕ) (source sink : V) (hDistinct : source ≠ sink)
    (hNoIn : In flow source = 0) (hNoOut : Out flow sink = 0)
    (hConserve : ∀ v, v ≠ source → v ≠ sink → Excess flow v = 0) :
    Nonempty (UnitPathDecomposition source sink flow (Out flow source)) := by
  classical
  induction hValue : Out flow source using Nat.strong_induction_on generalizing flow with
  | _ value ih =>
      by_cases hZero : value = 0
      · have hOutZero : Out flow source = 0 := hValue.trans hZero
        rw [hZero]
        exact ⟨.zero hOutZero⟩
      · have hPositiveValue : 0 < value := Nat.pos_of_ne_zero hZero
        have hPositiveOut : 0 < Out flow source := by omega
        have hReachable :
            Relation.ReflTransGen (PositiveArc flow) source sink := by
          apply sink_reachable_of_source_excess flow source sink
          · omega
          · intro v hvSource hvSink
            have hBalanced := hConserve v hvSource hvSink
            change (Out flow v : ℤ) - (In flow v : ℤ) = 0 at hBalanced
            have hCast : (Out flow v : ℤ) = (In flow v : ℤ) :=
              sub_eq_zero.mp hBalanced
            exact_mod_cast hCast.symm
        let chosen := PositivePath.simplePathOfReachable flow source sink hReachable
        let path : PositivePath flow source sink := chosen.1
        have hSimple : path.IsNodeSimple := chosen.2
        let nextFlow := path.decrementedFlow
        have hNoInNext : In nextFlow source = 0 :=
          path.in_decrementedFlow_eq_zero hSimple hNoIn
        have hNoOutNext : Out nextFlow sink = 0 :=
          path.out_decrementedFlow_eq_zero hSimple hNoOut
        have hConserveNext : ∀ v, v ≠ source → v ≠ sink →
            Excess nextFlow v = 0 := by
          intro v hvSource hvSink
          change PositivePath.Excess path.decrementedFlow v = 0
          rw [path.excess_decrementedFlow_internal hSimple hvSource hvSink]
          exact hConserve v hvSource hvSink
        have hNextValue : Out nextFlow source = value - 1 := by
          rw [path.out_decrementedFlow_source hSimple hDistinct hNoIn hPositiveOut]
          omega
        have hNextLt : Out nextFlow source < value := by omega
        obtain ⟨tail⟩ := ih (Out nextFlow source) hNextLt nextFlow
          hNoInNext hNoOutNext hConserveNext rfl
        have hSuccValue : Out nextFlow source + 1 = value := by omega
        have candidate : UnitPathDecomposition source sink flow
            (Out nextFlow source + 1) := .succ path hSimple tail
        rw [hSuccValue] at candidate
        exact ⟨candidate⟩


end FiniteIntegralFlow
