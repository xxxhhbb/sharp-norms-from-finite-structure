import R6.C079ActiveComponents
import R6.PaperToPartiteBridge
import R6.RademacherCharacterSum
import R6.HighMomentTailMarkov

/-!
# P1 active-component coefficients: exact typed definitions

This module is the Lean-side starting point for P1.  It deliberately uses
`PaperShape.toPartiteShape` for the graph/combinatorial layer, while keeping
role-dependent label dimensions.  The edge identity is part of every random
address.

Status: draft, not executed locally.  No `sorry`, `admit`, or new axioms.

The hard moment estimates and the uniform two-layer good-event theorem are
NOT claimed in this module; their intended statements are recorded in
`P1Targets.lean`.  This file only establishes the exact objects and several
structural/degenerate-case lemmas that those estimates must use.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Roles in one genuine connected component of `P.toPartiteShape - cut`. -/
def p1ComponentRoles (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) : Finset (Fin P.roles) :=
  P.toPartiteShape.c079ComponentRoles cut c

/-- Component roles which are actually adjacent to the cut.  This is the
paper's set `B`; it is not inserted by definition into either side of a
separator. -/
def p1BoundaryRoles (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) : Finset (Fin P.roles) := by
  classical
  exact (p1ComponentRoles P cut c).filter fun v =>
    ∃ x ∈ cut, ∃ e : Fin P.edges,
      P.toPartiteShape.EdgeIncident e v ∧
      P.toPartiteShape.EdgeIncident e x

@[simp] theorem mem_p1BoundaryRoles_iff
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) (v : Fin P.roles) :
    v ∈ p1BoundaryRoles P cut c ↔
      v ∈ p1ComponentRoles P cut c ∧
        ∃ x ∈ cut, ∃ e : Fin P.edges,
          P.toPartiteShape.EdgeIncident e v ∧
          P.toPartiteShape.EdgeIncident e x := by
  classical
  simp [p1BoundaryRoles]

 theorem p1BoundaryRoles_subset_component
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :
    p1BoundaryRoles P cut c ⊆ p1ComponentRoles P cut c := by
  classical
  intro v hv
  exact (mem_p1BoundaryRoles_iff P cut c v).1 hv |>.1

/-- An active component has at least one actually observed cut-adjacent role. -/
theorem p1BoundaryRoles_nonempty
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (hActive : c.IsActive) :
    (p1BoundaryRoles P cut c).Nonempty := by
  classical
  rcases hActive.2 with ⟨v, hvK, x, hx, e, hve, hxe⟩
  refine ⟨v, (mem_p1BoundaryRoles_iff P cut c v).2 ?_⟩
  exact ⟨hvK, ⟨x, hx, e, hve, hxe⟩⟩

/-- Typed role indices used by the P1 coefficient construction. -/
abbrev P1ComponentRole (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  {v : Fin P.roles // v ∈ p1ComponentRoles P cut c}

abbrev P1BoundaryRole (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  {v : Fin P.roles // v ∈ p1BoundaryRoles P cut c}

abbrev P1InteriorRole (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  {v : Fin P.roles //
    v ∈ p1ComponentRoles P cut c ∧ v ∉ p1BoundaryRoles P cut c}

/-- Role-dependent labels.  No equal-dimension assumption is made. -/
abbrev P1ComponentLabel
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  (v : P1ComponentRole P cut c) → Fin (dimension v.1)

abbrev P1BoundaryLabel
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  (v : P1BoundaryRole P cut c) → Fin (dimension v.1)

abbrev P1InteriorLabel
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  (v : P1InteriorRole P cut c) → Fin (dimension v.1)

/-- Glue the boundary assignment and the `K \ B` assignment into one typed
assignment on `K`. -/
def p1Glue
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (b : P1BoundaryLabel P dimension cut c)
    (u : P1InteriorLabel P dimension cut c) :
    P1ComponentLabel P dimension cut c := by
  classical
  intro v
  by_cases hvB : v.1 ∈ p1BoundaryRoles P cut c
  · exact b ⟨v.1, hvB⟩
  · exact u ⟨v.1, ⟨v.2, hvB⟩⟩

@[simp] theorem p1Glue_boundary
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (b : P1BoundaryLabel P dimension cut c)
    (u : P1InteriorLabel P dimension cut c)
    (v : P1BoundaryRole P cut c) :
    p1Glue P dimension cut c b u
      ⟨v.1, p1BoundaryRoles_subset_component P cut c v.2⟩ = b v := by
  classical
  simp [p1Glue, v.2]

@[simp] theorem p1Glue_interior
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (b : P1BoundaryLabel P dimension cut c)
    (u : P1InteriorLabel P dimension cut c)
    (v : P1InteriorRole P cut c) :
    p1Glue P dimension cut c b u ⟨v.1, v.2.1⟩ = u v := by
  classical
  simp [p1Glue, v.2.2]

/-- Actual internal edges of this connected component. -/
abbrev P1InternalEdge
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  {e : Fin P.edges //
    P.source e ∈ p1ComponentRoles P cut c ∧
    P.target e ∈ p1ComponentRoles P cut c}

/-- Primitive random address of one internal edge array.  The subtype `e`
retains the edge number; the coordinate retains the two typed endpoint labels. -/
abbrev P1InternalCoordinate
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (e : P1InternalEdge P cut c) :=
  Fin (dimension (P.source e.1)) × Fin (dimension (P.target e.1))

abbrev P1InternalSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut) :=
  (e : P1InternalEdge P cut c) →
    P1InternalCoordinate P dimension cut c e → Bool

/-- One internal Walsh monomial for a complete typed component assignment. -/
def p1InternalMonomialZ
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (x : P1ComponentLabel P dimension cut c)
    (eps : P1InternalSample P dimension cut c) : ℤ :=
  ∏ e : P1InternalEdge P cut c,
    rademacherSign
      (eps e
        (x ⟨P.source e.1, e.2.1⟩,
         x ⟨P.target e.1, e.2.2⟩))

/-- The actual coefficient `gamma_{x_B}` obtained after summing all labels
of `K \ B`, for a fixed complete internal-array realization. -/
def p1GammaZ
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (b : P1BoundaryLabel P dimension cut c)
    (eps : P1InternalSample P dimension cut c) : ℤ :=
  ∑ u : P1InteriorLabel P dimension cut c,
    p1InternalMonomialZ P dimension cut c
      (p1Glue P dimension cut c b u) eps

def p1Gamma
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (b : P1BoundaryLabel P dimension cut c)
    (eps : P1InternalSample P dimension cut c) : ℝ :=
  (p1GammaZ P dimension cut c b eps : ℝ)

/-- `Q = sum_{x_B} gamma_{x_B}^2`. -/
def p1Q
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (eps : P1InternalSample P dimension cut c) : ℝ :=
  ∑ b : P1BoundaryLabel P dimension cut c,
    p1Gamma P dimension cut c b eps ^ 2

theorem p1Q_nonneg
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (eps : P1InternalSample P dimension cut c) :
    0 ≤ p1Q P dimension cut c eps := by
  classical
  unfold p1Q
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- After choosing `z0 in B`, these are the other boundary roles. -/
abbrev P1BoundaryRestRole
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) :=
  {v : Fin P.roles //
    v ∈ p1BoundaryRoles P cut c ∧ v ≠ z0}

abbrev P1BoundaryRestLabel
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) :=
  (v : P1BoundaryRestRole P cut c z0) → Fin (dimension v.1)

/-- Insert the distinguished label `j` at `z0`. -/
def p1InsertBoundary
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (j : Fin (dimension z0))
    (r : P1BoundaryRestLabel P dimension cut c z0) :
    P1BoundaryLabel P dimension cut c := by
  classical
  intro v
  by_cases h : v.1 = z0
  · exact Fin.cast (congrArg dimension h.symm) j
  · exact r ⟨v.1, ⟨v.2, h⟩⟩

@[simp] theorem p1InsertBoundary_at_z0
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (j : Fin (dimension z0))
    (r : P1BoundaryRestLabel P dimension cut c z0) :
    p1InsertBoundary P dimension cut c z0 hz0 j r ⟨z0, hz0⟩ = j := by
  classical
  simp [p1InsertBoundary]

/-- `R_j = sum_{x_{B\{z0}}} gamma_{j,x}^2`. -/
def p1R
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c)
    (j : Fin (dimension z0)) : ℝ :=
  ∑ r : P1BoundaryRestLabel P dimension cut c z0,
    p1Gamma P dimension cut c
      (p1InsertBoundary P dimension cut c z0 hz0 j r) eps ^ 2

theorem p1R_nonneg
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c)
    (j : Fin (dimension z0)) :
    0 ≤ p1R P dimension cut c z0 hz0 eps j := by
  classical
  unfold p1R
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Effective second-layer signs after the primitive crossing arrays at roles
`B \ {z0}` have been multiplied along each fixed separator label.

A separate bridge theorem must prove that the actual primitive crossing-array
sample pushes forward to this uniform product space. -/
abbrev P1SecondSample
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) :=
  (v : P1BoundaryRestRole P cut c z0) → Fin (dimension v.1) → Bool

/-- One Walsh character in the second-layer sign vectors. -/
def p1SecondCharacterZ
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles)
    (r : P1BoundaryRestLabel P dimension cut c z0)
    (eta : P1SecondSample P dimension cut c z0) : ℤ :=
  ∏ v : P1BoundaryRestRole P cut c z0,
    rademacherSign (eta v (r v))

/-- Exposed coefficient `z_j` for a fixed full internal realization. -/
def p1Z
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c)
    (eta : P1SecondSample P dimension cut c z0)
    (j : Fin (dimension z0)) : ℝ :=
  ∑ r : P1BoundaryRestLabel P dimension cut c z0,
    p1Gamma P dimension cut c
      (p1InsertBoundary P dimension cut c z0 hz0 j r) eps *
      (p1SecondCharacterZ P dimension cut c z0 r eta : ℝ)

/-- Conditional variance proxy after all roles in `B \ {z0}` are exposed. -/
def p1SigmaSq
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c)
    (eta : P1SecondSample P dimension cut c z0) : ℝ :=
  ∑ j : Fin (dimension z0),
    p1Z P dimension cut c z0 hz0 eps eta j ^ 2

theorem p1SigmaSq_nonneg
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
    (eps : P1InternalSample P dimension cut c)
    (eta : P1SecondSample P dimension cut c z0) :
    0 ≤ p1SigmaSq P dimension cut c z0 hz0 eps eta := by
  classical
  unfold p1SigmaSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Degenerate cases -/

/-- In the actual paper shape, a singleton component has no internal edge.
This uses `PaperShape.edge_order`; it would be false for a completely general
`PartiteShape` with a self-loop. -/
theorem p1InternalEdge_isEmpty_of_component_singleton
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (v : Fin P.roles)
    (hK : p1ComponentRoles P cut c = {v}) :
    IsEmpty (P1InternalEdge P cut c) := by
  classical
  refine ⟨?_⟩
  intro e
  have hsMem : P.source e.1 ∈ ({v} : Finset (Fin P.roles)) := by
    rw [← hK]
    exact e.2.1
  have htMem : P.target e.1 ∈ ({v} : Finset (Fin P.roles)) := by
    rw [← hK]
    exact e.2.2
  have hs : P.source e.1 = v := by simpa using hsMem
  have ht : P.target e.1 = v := by simpa using htMem
  have hlt := P.edge_order e.1
  rw [hs, ht] at hlt
  exact (lt_irrefl v) hlt

/-- If `B` is exactly `{z0}`, then there are no second-layer roles. -/
theorem p1BoundaryRestRole_isEmpty_of_boundary_singleton
    (P : PaperShape) (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles)
    (hB : p1BoundaryRoles P cut c = {z0}) :
    IsEmpty (P1BoundaryRestRole P cut c z0) := by
  classical
  refine ⟨?_⟩
  intro v
  have hvMem : v.1 ∈ ({z0} : Finset (Fin P.roles)) := by
    rw [← hB]
    exact v.2.1
  have hvEq : v.1 = z0 := by simpa using hvMem
  exact v.2.2 hvEq

/-- The effective second-layer sample is unique when there are no remaining
boundary roles.  This is the formal version of "no second-layer randomness". -/
theorem p1SecondSample_subsingleton_of_boundary_singleton
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles)
    (hB : p1BoundaryRoles P cut c = {z0}) :
    Subsingleton (P1SecondSample P dimension cut c z0) := by
  classical
  let hEmpty : IsEmpty (P1BoundaryRestRole P cut c z0) :=
    p1BoundaryRestRole_isEmpty_of_boundary_singleton P cut c z0 hB
  constructor
  intro eta eta'
  funext v
  exact False.elim (hEmpty.false v)

end GraphMatrixReplica
