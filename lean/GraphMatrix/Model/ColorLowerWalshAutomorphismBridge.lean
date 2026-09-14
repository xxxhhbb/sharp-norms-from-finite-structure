import GraphMatrix.Model.ColorLowerFourier
import GraphMatrix.Model.ColorLowerAutomorphism

/-! # From surviving tagged edge words to boundary-fixing automorphisms

The Fourier module supplies an odd count for each target edge-color tag.
This bridge extracts a true edge permutation and then invokes the finite
automorphism theorem.  The hypotheses identifying the tag of each realized
edge and the corresponding role colors remain explicit; deriving them from
the ambient row/column compression is a separate paper-facing obligation.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A surviving length-`|E|` tagged edge word covers every target edge
color, provided the tag of its `e`th edge is `edgeColor e`. -/
theorem paperR16TaggedWord_edgeColor_surjective
    {G : PaperShape} {n : ℕ}
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (word : Fin G.edges → Fin n × Fin n)
    (edgeColor : Fin G.edges → Fin G.edges)
    (hTag : ∀ e : Fin G.edges,
      tag (paperUnorderedPair (word e).1 (word e).2) = some (edgeColor e))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount tag (List.ofFn word) k)) :
    Function.Surjective edgeColor := by
  classical
  letI : BEq (Option (Fin G.edges)) := instBEqOfDecidableEq
  intro k
  have hpos : 0 < paperR16TaggedEdgeCount tag (List.ofFn word) k := by
    obtain ⟨m, hm⟩ := hOdd k
    omega
  unfold paperR16TaggedEdgeCount at hpos
  obtain ⟨p, hp, hpk⟩ := List.mem_map.mp (List.count_pos_iff.mp hpos)
  obtain ⟨e, he⟩ := List.mem_ofFn.mp hp
  subst p
  exact ⟨e, Option.some.inj ((hTag e).symm.trans hpk)⟩

/-- Walsh survival, tag identification, and endpoint compatibility imply
the exact finite parity certificate used by the color-lower combinatorics. -/
def paperR16TaggedWord_toOddEdgeColorMap
    {G : PaperShape} {n : ℕ}
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (word : Fin G.edges → Fin n × Fin n)
    (role : Fin G.roles → Fin G.roles)
    (edgeColor : Fin G.edges → Fin G.edges)
    (hTag : ∀ e : Fin G.edges,
      tag (paperUnorderedPair (word e).1 (word e).2) = some (edgeColor e))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount tag (List.ofFn word) k))
    (hEndpoints : ∀ e : Fin G.edges,
      (role (G.source e) = G.source (edgeColor e) ∧
        role (G.target e) = G.target (edgeColor e)) ∨
      (role (G.source e) = G.target (edgeColor e) ∧
        role (G.target e) = G.source (edgeColor e)))
    (hLeft : ∀ v ∈ G.leftBoundaryFinset, role v = v)
    (hRight : ∀ v ∈ G.rightBoundaryFinset, role v = v) :
    G.R16OddEdgeColorMap := by
  classical
  let E : Fin G.edges ≃ Fin G.edges :=
    Equiv.ofBijective edgeColor
      ⟨Finite.injective_iff_surjective.mpr
          (paperR16TaggedWord_edgeColor_surjective tag word edgeColor hTag hOdd),
        paperR16TaggedWord_edgeColor_surjective tag word edgeColor hTag hOdd⟩
  have hFiber : ∀ target : Fin G.edges,
      (Finset.univ.filter fun e : Fin G.edges => edgeColor e = target) =
        {E.symm target} := by
    intro target
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro he
      apply E.injective
      rw [E.apply_symm_apply]
      change edgeColor e = target
      exact he
    · intro he
      subst e
      exact E.apply_symm_apply target
  exact {
    role := role
    edgeColor := edgeColor
    odd_edge_fiber := by
      intro target
      rw [hFiber target]
      simp
    endpoints := hEndpoints
    left_fixed := hLeft
    right_fixed := hRight }

/-- The length-`|E|` odd Walsh criterion thus yields a boundary-fixing
automorphism once the paper's role-color interpretation is supplied. -/
def paperR16TaggedWord_toAutomorphism
    {G : PaperShape} {n : ℕ}
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (word : Fin G.edges → Fin n × Fin n)
    (role : Fin G.roles → Fin G.roles)
    (edgeColor : Fin G.edges → Fin G.edges)
    (hTag : ∀ e : Fin G.edges,
      tag (paperUnorderedPair (word e).1 (word e).2) = some (edgeColor e))
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount tag (List.ofFn word) k))
    (hEndpoints : ∀ e : Fin G.edges,
      (role (G.source e) = G.source (edgeColor e) ∧
        role (G.target e) = G.target (edgeColor e)) ∨
      (role (G.source e) = G.target (edgeColor e) ∧
        role (G.target e) = G.source (edgeColor e)))
    (hLeft : ∀ v ∈ G.leftBoundaryFinset, role v = v)
    (hRight : ∀ v ∈ G.rightBoundaryFinset, role v = v)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles) :
    G.R16BoundaryFixingAutomorphism :=
  (paperR16TaggedWord_toOddEdgeColorMap tag word role edgeColor
    hTag hOdd hEndpoints hLeft hRight).toAutomorphism hNoIsolated


end GraphMatrixReplica
