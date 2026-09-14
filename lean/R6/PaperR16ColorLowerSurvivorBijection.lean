import R6.PaperR16ColorLowerAutomorphismReindex
import R6.PaperR16ColorLowerConcreteSurvivorBridge
import Mathlib.Data.List.FinRange

/-!
# Uniqueness and reconstruction for the R16 lower-color survivors

The paper shape stores each simple undirected edge in increasing endpoint
order.  Thus a role permutation determines its induced edge permutation.
This rules out duplicate automorphism factors when converting the surviving
global-realization sum into a sum over automorphisms and typed assignments.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- On a simple ordered-edge paper shape, two boundary-fixing graph
automorphisms with the same role permutation have the same edge permutation.
The reversed endpoint alternatives cannot identify different stored edges,
because both stored edges have strictly increasing endpoints. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.edge_eq_of_role_eq
    {G : PaperShape} (f g : G.R16BoundaryFixingAutomorphism)
    (hrole : f.role = g.role) : f.edge = g.edge := by
  apply Equiv.ext
  intro e
  have hs : f.role (G.source e) = g.role (G.source e) :=
    congrArg (fun r : Fin G.roles ≃ Fin G.roles => r (G.source e)) hrole
  have ht : f.role (G.target e) = g.role (G.target e) :=
    congrArg (fun r : Fin G.roles ≃ Fin G.roles => r (G.target e)) hrole
  apply G.edge_injective
  rcases f.endpoints e with hf | hf <;> rcases g.endpoints e with hg | hg
  · exact Prod.ext (hf.1.symm.trans (hs.trans hg.1))
      (hf.2.symm.trans (ht.trans hg.2))
  · have h1 : G.source (f.edge e) = G.target (g.edge e) :=
      hf.1.symm.trans (hs.trans hg.1)
    have h2 : G.target (f.edge e) = G.source (g.edge e) :=
      hf.2.symm.trans (ht.trans hg.2)
    have hfo := G.edge_order (f.edge e)
    have hgo := G.edge_order (g.edge e)
    omega
  · have h1 : G.target (f.edge e) = G.source (g.edge e) :=
      hf.1.symm.trans (hs.trans hg.1)
    have h2 : G.source (f.edge e) = G.target (g.edge e) :=
      hf.2.symm.trans (ht.trans hg.2)
    have hfo := G.edge_order (f.edge e)
    have hgo := G.edge_order (g.edge e)
    omega
  · exact Prod.ext (hf.2.symm.trans (ht.trans hg.2))
      (hf.1.symm.trans (hs.trans hg.1))

/-- The full automorphism structure is determined by the role permutation. -/
theorem PaperShape.R16BoundaryFixingAutomorphism.eq_of_role_eq
    {G : PaperShape} (f g : G.R16BoundaryFixingAutomorphism)
    (hrole : f.role = g.role) : f = g :=
  PaperShape.R16BoundaryFixingAutomorphism.ext hrole
    (f.edge_eq_of_role_eq g hrole)

/-- General-size version of the automorphism-colored realization.  The
target-indexed assignment is used at `f.role v`, so no equality between the
different role-class sizes is required. -/
def PaperRoleColoring.coloredRealizationVarying
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (f : G.R16BoundaryFixingAutomorphism)
    (a : PaperRoleColorAssignment G dimension) : PaperRealization G n where
  toFun v := C.embedding (f.role v) (a (f.role v))
  inj' := by
    intro v u h
    have hRole : f.role v = f.role u := by
      by_contra hneq
      exact C.disjoint hneq (a (f.role v)) (a (f.role u)) h
    exact f.role.injective hRole

theorem PaperRoleColoring.coloredRealizationVarying_roleTag
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (f : G.R16BoundaryFixingAutomorphism)
    (a : PaperRoleColorAssignment G dimension) (v : Fin G.roles) :
    C.roleOfLabel? (C.coloredRealizationVarying f a v) =
      some (f.role v) := C.roleOfLabel?_embedding _ _

/-- Boundary compatibility is unchanged by the automorphism-colored
realization even when role-class sizes vary. -/
theorem PaperRoleColoring.coloredRealizationVarying_compatible_iff
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (f : G.R16BoundaryFixingAutomorphism)
    (a : PaperRoleColorAssignment G dimension)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension) :
    paperEntryCompatible G (C.coloredRealizationVarying f a)
        (C.paperRow row) (C.paperCol col) ↔
      partiteBoundaryEntryCompatible a row col := by
  have hleft : ∀ i : Fin G.leftSize,
      C.coloredRealizationVarying f a (G.left i) =
        C.globalRealization a (G.left i) := by
    intro i
    have hv : G.left i ∈ G.leftBoundaryFinset :=
      (G.mem_leftBoundaryFinset_iff (G.left i)).2 ⟨i, rfl⟩
    change C.embedding (f.role (G.left i)) (a (f.role (G.left i))) =
      C.embedding (G.left i) (a (G.left i))
    rw [f.left_fixed (G.left i) hv]
  have hright : ∀ j : Fin G.rightSize,
      C.coloredRealizationVarying f a (G.right j) =
        C.globalRealization a (G.right j) := by
    intro j
    have hv : G.right j ∈ G.rightBoundaryFinset :=
      (G.mem_rightBoundaryFinset_iff (G.right j)).2 ⟨j, rfl⟩
    change C.embedding (f.role (G.right j)) (a (f.role (G.right j))) =
      C.embedding (G.right j) (a (G.right j))
    rw [f.right_fixed (G.right j) hv]
  have hiff :
      paperEntryCompatible G (C.coloredRealizationVarying f a)
        (C.paperRow row) (C.paperCol col) ↔
      paperEntryCompatible G (C.globalRealization a)
        (C.paperRow row) (C.paperCol col) := by
    constructor
    · rintro ⟨hl, hr⟩
      exact ⟨fun i => (hleft i).symm.trans (hl i),
        fun j => (hright j).symm.trans (hr j)⟩
    · rintro ⟨hl, hr⟩
      exact ⟨fun i => (hleft i).trans (hl i),
        fun j => (hright j).trans (hr j)⟩
  exact hiff.trans (C.paperEntryCompatible_globalRealization_iff a row col)

/-- Every edge of the general-size realization has its automorphic target
edge tag. -/
theorem PaperRoleColoring.coloredRealizationVarying_edgeTag
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (f : G.R16BoundaryFixingAutomorphism)
    (a : PaperRoleColorAssignment G dimension)
    (e : Fin G.edges) :
    C.targetEdgeTag (paperUnorderedPair
      (C.coloredRealizationVarying f a (G.source e))
      (C.coloredRealizationVarying f a (G.target e))) = some (f.edge e) := by
  rcases f.endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · apply C.targetEdgeTag_of_endpoint_roles
    · simpa [C.coloredRealizationVarying_roleTag f a] using congrArg some hs
    · simpa [C.coloredRealizationVarying_roleTag f a] using congrArg some ht
  · apply C.targetEdgeTag_of_endpoint_roles_swapped
    · simpa [C.coloredRealizationVarying_roleTag f a] using congrArg some hs
    · simpa [C.coloredRealizationVarying_roleTag f a] using congrArg some ht

/-- Each target edge color occurs exactly once in the concrete edge word
of an automorphism-colored realization. -/
theorem PaperRoleColoring.coloredRealizationVarying_tagCount
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (f : G.R16BoundaryFixingAutomorphism)
    (a : PaperRoleColorAssignment G dimension)
    (k : Fin G.edges) :
    paperR16TaggedEdgeCount C.targetEdgeTag
      (List.ofFn fun e : Fin G.edges =>
        (C.coloredRealizationVarying f a (G.source e),
          C.coloredRealizationVarying f a (G.target e))) k = 1 := by
  letI : BEq (Option (Fin G.edges)) := instBEqOfDecidableEq
  have hperm : List.Perm
      (List.ofFn (fun e : Fin G.edges => some (f.edge e)))
      (List.ofFn (fun e : Fin G.edges => some e)) := by
    simpa [Function.comp_def] using
      (Equiv.Perm.ofFn_comp_perm f.edge (fun e : Fin G.edges => some e))
  have hbase :
      (List.ofFn (fun e : Fin G.edges => some e)).count (some k) = 1 := by
    rw [List.ofFn_eq_map]
    simpa using (List.count_map_of_injective (List.finRange G.edges)
      (fun e : Fin G.edges => some e) (fun _ _ h => Option.some.inj h) k)
  have hcount := hperm.count_eq (some k)
  have htag :
      (List.ofFn fun e : Fin G.edges =>
        (C.coloredRealizationVarying f a (G.source e),
          C.coloredRealizationVarying f a (G.target e))).map
          (fun e => C.targetEdgeTag (paperUnorderedPair e.1 e.2)) =
        List.ofFn (fun e : Fin G.edges => some (f.edge e)) := by
    simp only [List.map_ofFn]
    congr 1
    funext e
    exact C.coloredRealizationVarying_edgeTag f a e
  unfold paperR16TaggedEdgeCount
  rw [htag]
  exact hcount.trans hbase

theorem PaperRoleColoring.coloredRealizationVarying_odd
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (f : G.R16BoundaryFixingAutomorphism)
    (a : PaperRoleColorAssignment G dimension)
    (k : Fin G.edges) :
    Odd (paperR16TaggedEdgeCount C.targetEdgeTag
      (List.ofFn fun e : Fin G.edges =>
        (C.coloredRealizationVarying f a (G.source e),
          C.coloredRealizationVarying f a (G.target e))) k) := by
  rw [C.coloredRealizationVarying_tagCount f a k]
  decide

/-- The target-indexed typed monomial with possibly unequal role-class
sizes, evaluated in the original paper's one shared ambient sign field. -/
def PaperRoleColoring.varyingEdgeProduct
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (w : PaperNoise n) (a : PaperRoleColorAssignment G dimension) : ℝ :=
  ∏ e : Fin G.edges,
    paperEdgeSign w
      (C.embedding (G.source e) (a (G.source e)))
      (C.embedding (G.target e) (a (G.target e)))

/-- The original edge monomial of every general-size constructed realization
is exactly the typed assignment monomial, by the edge permutation and
unordered-edge symmetry. -/
theorem PaperRoleColoring.coloredRealizationVarying_edgeProduct
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (f : G.R16BoundaryFixingAutomorphism)
    (w : PaperNoise n) (a : PaperRoleColorAssignment G dimension) :
    (∏ e : Fin G.edges,
      paperEdgeSign w
        (C.coloredRealizationVarying f a (G.source e))
        (C.coloredRealizationVarying f a (G.target e))) =
      C.varyingEdgeProduct w a := by
  let target : Fin G.edges → ℝ := fun e =>
    paperEdgeSign w
      (C.embedding (G.source e) (a (G.source e)))
      (C.embedding (G.target e) (a (G.target e)))
  have hedge : ∀ e : Fin G.edges,
      paperEdgeSign w
          (C.coloredRealizationVarying f a (G.source e))
          (C.coloredRealizationVarying f a (G.target e)) =
        target (f.edge e) := by
    intro e
    change paperEdgeSign w
        (C.embedding (f.role (G.source e)) (a (f.role (G.source e))))
        (C.embedding (f.role (G.target e)) (a (f.role (G.target e)))) =
      target (f.edge e)
    rcases f.endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simp only [target]
      rw [← hs, ← ht]
    · simp only [target]
      rw [← ht, ← hs]
      exact paperEdgeSign_symmetric w _ _
  calc
    (∏ e : Fin G.edges,
      paperEdgeSign w
        (C.coloredRealizationVarying f a (G.source e))
        (C.coloredRealizationVarying f a (G.target e))) =
        ∏ e : Fin G.edges, target (f.edge e) := by
          apply Finset.prod_congr rfl
          intro e _
          exact hedge e
    _ = ∏ e : Fin G.edges, target e := f.edge.prod_comp target
    _ = C.varyingEdgeProduct w a := rfl

/-- The forward map from one automorphism and one typed assignment
to its concrete globally injective paper realization has no collisions. -/
theorem PaperRoleColoring.coloredRealization_pair_injective
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n) :
    Function.Injective (fun x :
      G.R16BoundaryFixingAutomorphism ×
        PaperRoleColorAssignment G dimension =>
      C.coloredRealizationVarying x.1 x.2) := by
  rintro ⟨f, a⟩ ⟨g, b⟩ hphi
  have hrole : f.role = g.role := by
    apply Equiv.ext
    intro v
    have htag := congrArg (fun phi : PaperRealization G n =>
      C.roleOfLabel? (phi v)) hphi
    rw [C.coloredRealizationVarying_roleTag f a v,
      C.coloredRealizationVarying_roleTag g b v] at htag
    exact Option.some.inj htag
  have hfg : f = g := f.eq_of_role_eq g hrole
  subst g
  have hab : a = b := by
    funext v
    have hval := congrArg (fun phi : PaperRealization G n =>
      phi (f.role.symm v)) hphi
    change C.embedding (f.role (f.role.symm v))
        (a (f.role (f.role.symm v))) =
      C.embedding (f.role (f.role.symm v))
        (b (f.role (f.role.symm v))) at hval
    rw [f.role.apply_symm_apply] at hval
    exact (C.embedding v).injective hval
  cases hab
  rfl

/-- Once a global realization's role colors match an automorphism, its
typed assignment can be recovered.  This is the concrete inverse
needed after the survivor-to-automorphism classifier has exposed its role map. -/
theorem PaperRoleColoring.exists_assignment_of_roleTag
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (f : G.R16BoundaryFixingAutomorphism)
    (hrole : ∀ v : Fin G.roles,
      C.roleOfLabel? (phi v) = some (f.role v)) :
    ∃ a : PaperRoleColorAssignment G dimension,
      phi = C.coloredRealizationVarying f a := by
  classical
  have hcoord : ∀ v : Fin G.roles,
      ∃ a : Fin (dimension v), C.embedding v a = phi (f.role.symm v) := by
    intro v
    have htag : C.roleOfLabel? (phi (f.role.symm v)) = some v := by
      simpa using hrole (f.role.symm v)
    exact (C.roleOfLabel?_eq_some_iff (phi (f.role.symm v)) v).1 htag
  choose a ha using hcoord
  refine ⟨a, ?_⟩
  apply Function.Embedding.ext
  intro v
  have hv := ha (f.role v)
  rw [f.role.symm_apply_apply] at hv
  exact hv.symm

/-- Expose the defining chosen role-color certificate of the generic
survivor classifier.  This is the fact needed to recover target-indexed
labels from a classified realization. -/
theorem paperR16SurvivingWord_toAutomorphism_roleTag
    {G : PaperShape} {n : ℕ}
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (word : Fin G.edges → Fin n × Fin n)
    (vertexColor : Fin G.roles → Option (Fin G.roles))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount tag (List.ofFn word) k))
    (hTagEndpoints : ∀ (e k : Fin G.edges),
      tag (paperUnorderedPair (word e).1 (word e).2) = some k →
        (vertexColor (G.source e) = some (G.source k) ∧
          vertexColor (G.target e) = some (G.target k)) ∨
        (vertexColor (G.source e) = some (G.target k) ∧
          vertexColor (G.target e) = some (G.source k)))
    (hLeft : ∀ v ∈ G.leftBoundaryFinset, vertexColor v = some v)
    (hRight : ∀ v ∈ G.rightBoundaryFinset, vertexColor v = some v)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (v : Fin G.roles) :
    vertexColor v = some
      ((paperR16SurvivingWord_toAutomorphism tag word vertexColor hOdd
        hTagEndpoints hLeft hRight hNoIsolated).role v) := by
  unfold paperR16SurvivingWord_toAutomorphism
  dsimp
  exact (paperR16SurvivingWord_allRolesColored tag word vertexColor
    hOdd hTagEndpoints hLeft hRight hNoIsolated v).choose_spec

/-- The concrete fixed-class classifier's role permutation is exactly the
observed partial role tag of the surviving realization. -/
theorem PaperRoleColoring.survivingRealization_roleTag
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount C.targetEdgeTag
        (List.ofFn fun e : Fin G.edges =>
          (phi (G.source e), phi (G.target e))) k))
    (hLeft : ∀ v ∈ G.leftBoundaryFinset,
      C.roleOfLabel? (phi v) = some v)
    (hRight : ∀ v ∈ G.rightBoundaryFinset,
      C.roleOfLabel? (phi v) = some v)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (v : Fin G.roles) :
    C.roleOfLabel? (phi v) = some
      ((C.survivingRealization_toAutomorphism phi hOdd hLeft hRight
        hNoIsolated).role v) := by
  unfold PaperRoleColoring.survivingRealization_toAutomorphism
  dsimp
  apply paperR16SurvivingWord_toAutomorphism_roleTag
    C.targetEdgeTag
    (fun e => (phi (G.source e), phi (G.target e)))
    (fun v => C.roleOfLabel? (phi v)) hOdd
    (by
      intro e k hTag
      let i : Fin n := phi (G.source e)
      let j : Fin n := phi (G.target e)
      change C.targetEdgeTag (paperUnorderedPair i j) = some k at hTag
      rcases le_total i j with hij | hji
      · have hOrdered : C.targetEdgeTag (i, j) = some k := by
          simpa [paperUnorderedPair, min_eq_left hij, max_eq_right hij]
            using hTag
        exact C.targetEdgeTag_endpoint_roles i j k hOrdered
      · have hOrdered : C.targetEdgeTag (j, i) = some k := by
          simpa [paperUnorderedPair, min_eq_right hji, max_eq_left hji]
            using hTag
        rcases C.targetEdgeTag_endpoint_roles j i k hOrdered with h | h
        · exact Or.inr ⟨h.2, h.1⟩
        · exact Or.inl ⟨h.2, h.1⟩)
    hLeft hRight hNoIsolated v

/-- The classifier obtained directly from a compressed paper entry also
recovers every role's actual observed color. -/
theorem PaperRoleColoring.survivingCompressedRealization_roleTag
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension)
    (hCompatible : paperEntryCompatible G phi (C.paperRow row) (C.paperCol col))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount C.targetEdgeTag
        (List.ofFn fun e : Fin G.edges =>
          (phi (G.source e), phi (G.target e))) k))
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (v : Fin G.roles) :
    C.roleOfLabel? (phi v) = some
      ((C.survivingCompressedRealization_toAutomorphism phi row col
        hCompatible hOdd hNoIsolated).role v) := by
  exact C.survivingRealization_roleTag phi hOdd
    (C.leftBoundaryColor_of_paperEntryCompatible phi row col hCompatible)
    (C.rightBoundaryColor_of_paperEntryCompatible phi row col hCompatible)
    hNoIsolated v

/-- Every actual compressed Walsh survivor has a target-indexed typed
assignment and a boundary-fixing automorphism whose concrete realization is
the original globally injective paper embedding.  No role sizes are assumed
equal. -/
theorem PaperRoleColoring.exists_automorphism_assignment_of_survivor
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (phi : PaperRealization G n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension)
    (hCompatible : paperEntryCompatible G phi (C.paperRow row) (C.paperCol col))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount C.targetEdgeTag
        (List.ofFn fun e : Fin G.edges =>
          (phi (G.source e), phi (G.target e))) k))
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    ∃ (f : G.R16BoundaryFixingAutomorphism)
      (a : PaperRoleColorAssignment G dimension),
        phi = C.coloredRealizationVarying f a ∧
        partiteBoundaryEntryCompatible a row col := by
  let f := C.survivingCompressedRealization_toAutomorphism phi row col
    hCompatible hOdd hNoIsolated
  have hrole : ∀ v : Fin G.roles,
      C.roleOfLabel? (phi v) = some (f.role v) := by
    intro v
    exact C.survivingCompressedRealization_roleTag phi row col
      hCompatible hOdd hNoIsolated v
  obtain ⟨a, hphi⟩ := C.exists_assignment_of_roleTag phi f hrole
  refine ⟨f, a, hphi, ?_⟩
  apply (C.coloredRealizationVarying_compatible_iff f a row col).mp
  rw [← hphi]
  exact hCompatible

/-- The actual Walsh survivors of one fixed compressed matrix entry are
equivalent to a boundary-fixing automorphism together with a compatible
target-indexed typed assignment.  This works with arbitrary role sizes. -/
def PaperRoleColoring.survivorPairEquiv
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    { x : G.R16BoundaryFixingAutomorphism ×
        PaperRoleColorAssignment G dimension //
      partiteBoundaryEntryCompatible x.2 row col } ≃
    { phi : PaperRealization G n //
      paperEntryCompatible G phi (C.paperRow row) (C.paperCol col) ∧
      ∀ k : Fin G.edges,
        Odd (paperR16TaggedEdgeCount C.targetEdgeTag
          (paperEmbeddingEdgeWord G phi) k) } := by
  let forward :
      { x : G.R16BoundaryFixingAutomorphism ×
          PaperRoleColorAssignment G dimension //
        partiteBoundaryEntryCompatible x.2 row col } →
      { phi : PaperRealization G n //
        paperEntryCompatible G phi (C.paperRow row) (C.paperCol col) ∧
        ∀ k : Fin G.edges,
          Odd (paperR16TaggedEdgeCount C.targetEdgeTag
            (paperEmbeddingEdgeWord G phi) k) } :=
    fun x => ⟨C.coloredRealizationVarying x.1.1 x.1.2,
      (C.coloredRealizationVarying_compatible_iff x.1.1 x.1.2 row col).2 x.2,
      fun k => C.coloredRealizationVarying_odd x.1.1 x.1.2 k⟩
  refine Equiv.ofBijective forward ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact C.coloredRealization_pair_injective (congrArg Subtype.val hxy)
  · rintro ⟨phi, hCompatible, hOdd⟩
    obtain ⟨f, a, hphi, ha⟩ :=
      C.exists_automorphism_assignment_of_survivor phi row col
        hCompatible hOdd hNoIsolated
    refine ⟨⟨(f, a), ha⟩, ?_⟩
    apply Subtype.ext
    exact hphi.symm

#print axioms PaperShape.R16BoundaryFixingAutomorphism.edge_eq_of_role_eq
#print axioms PaperShape.R16BoundaryFixingAutomorphism.eq_of_role_eq
#print axioms PaperRoleColoring.coloredRealizationVarying
#print axioms PaperRoleColoring.coloredRealizationVarying_compatible_iff
#print axioms PaperRoleColoring.coloredRealizationVarying_edgeTag
#print axioms PaperRoleColoring.coloredRealizationVarying_tagCount
#print axioms PaperRoleColoring.coloredRealizationVarying_odd
#print axioms PaperRoleColoring.coloredRealizationVarying_edgeProduct
#print axioms PaperRoleColoring.coloredRealization_pair_injective
#print axioms PaperRoleColoring.exists_assignment_of_roleTag
#print axioms paperR16SurvivingWord_toAutomorphism_roleTag
#print axioms PaperRoleColoring.survivingRealization_roleTag
#print axioms PaperRoleColoring.survivingCompressedRealization_roleTag
#print axioms PaperRoleColoring.exists_automorphism_assignment_of_survivor
#print axioms PaperRoleColoring.survivorPairEquiv

end GraphMatrixReplica
