import R6.P2aConditionalProductLaw

/-!
# P2a deterministic component contraction and gamma regrouping

Status: UNEXECUTED in the present handoff environment.

This file formalizes the finite deterministic regrouping used after a complete
internal realization has been fixed.  Every crossing factor still reads the
actual `RestAddress` created from the original typed edge occurrence.

The final identification with the syntactic sub-sum obtained by expanding
`partiteBoundaryMatrix` is documented in `P2a_PROOF.md`, Section 8.1; the
present module starts from the corresponding component finite contraction and
proves the exact `gamma * eta` regrouping.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica
namespace P2a
attribute [local instance] Classical.propDecidable

/-! ## 1. Typed assignments on one genuine active component -/

abbrev ComponentRole {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (K : ActiveComponent G cut) :=
  {v : Fin G.roles // v ∈ G.c079ComponentRoles cut K.1}

abbrev ComponentAssignment
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (K : ActiveComponent G cut) :=
  ∀ v : ComponentRole K, Fin (dimension v.1)

/-- Predicate saying that a component role belongs to the actual attached set
`B_K`. -/
def ComponentTouchesCut
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    {K : ActiveComponent G cut} (v : ComponentRole K) : Prop :=
  ∃ u : Fin G.roles, u ∈ cut ∧
    ∃ e : Fin G.edges, EdgeJoins G e v.1 u

abbrev ComponentInteriorRole
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (K : ActiveComponent G cut) :=
  {v : ComponentRole K // ¬ ComponentTouchesCut v}

abbrev BoundaryAssignment
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (K : ActiveComponent G cut) :=
  ∀ z : AttachedRole cut K, Fin (dimension z.1)

abbrev InteriorAssignment
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (K : ActiveComponent G cut) :=
  ∀ v : ComponentInteriorRole K, Fin (dimension v.1.1)

/-- Exact assignment split `X_K ≃ X_{B_K} × X_{K\B_K}`.  There is no global
injectivity constraint in the typed partite assignment model. -/
def componentAssignmentEquiv
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (K : ActiveComponent G cut) :
    ComponentAssignment dimension K ≃
      (BoundaryAssignment dimension K × InteriorAssignment dimension K) where
  toFun x :=
    ⟨fun z => x ⟨z.1, z.2.1⟩,
      fun v => x v.1⟩
  invFun p v := by
    classical
    by_cases h : ComponentTouchesCut v
    · exact p.1 ⟨v.1, v.2, h⟩
    · exact p.2 ⟨v, h⟩
  left_inv x := by
    funext v
    classical
    by_cases h : ComponentTouchesCut v
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    apply Prod.ext
    · funext z
      simp [ComponentTouchesCut, z.2.2]
    · funext v
      simp [v.2]

@[simp] theorem componentAssignmentEquiv_symm_boundary
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (K : ActiveComponent G cut)
    (xB : BoundaryAssignment dimension K)
    (y : InteriorAssignment dimension K)
    (z : AttachedRole cut K) :
    (componentAssignmentEquiv dimension K).symm (xB, y)
        ⟨z.1, z.2.1⟩ = xB z := by
  classical
  simp [componentAssignmentEquiv, ComponentTouchesCut, z.2.2]

@[simp] theorem componentAssignmentEquiv_symm_interior
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (K : ActiveComponent G cut)
    (xB : BoundaryAssignment dimension K)
    (y : InteriorAssignment dimension K)
    (v : ComponentInteriorRole K) :
    (componentAssignmentEquiv dimension K).symm (xB, y) v.1 = y v := by
  classical
  simp [componentAssignmentEquiv, v.2]

/-! ## 2. Internal monomial from the fixed complete realization -/

abbrev ComponentInternalEdge
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (K : ActiveComponent G cut) :=
  {e : Fin G.edges //
    G.source e ∈ G.c079ComponentRoles cut K.1 ∧
    G.target e ∈ G.c079ComponentRoles cut K.1}

/-- The actual internal primitive coordinate read by one component assignment. -/
def componentInternalAddress
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    (K : ActiveComponent G cut)
    (e : ComponentInternalEdge K)
    (x : ComponentAssignment dimension K) :
    InternalAddress cut dimension :=
  ⟨⟨e.1,
      (x ⟨G.source e.1, e.2.1⟩,
       x ⟨G.target e.1, e.2.2⟩)⟩,
    ⟨K, e.2.1, e.2.2⟩⟩

/-- `chi_K^I(x)` from the proof: only the complete fixed internal realization
is read here. -/
def componentInternalMonomial
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    (I : InternalCube cut dimension)
    (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) : ℝ :=
  ∏ e : ComponentInternalEdge K,
    (rademacherSign (I (componentInternalAddress dimension K e x)) : ℝ)

/-! ## 3. Actual crossing products and the component finite contraction -/

/-- Crossing product for a boundary assignment, expressed through the actual
eta scalars already built from typed `RestAddress` supports. -/
def componentEtaProduct
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (R : RestCube cut dimension)
    (i : Fin N) (K : ActiveComponent G cut)
    (xB : BoundaryAssignment dimension K) : ℝ :=
  ∏ z : AttachedRole cut K,
    trialScalarEta dimension N hN
      ⟨i, ⟨K, ⟨z, xB z⟩⟩⟩ R

/-- The same crossing product evaluated on a full component assignment.  It
only reads the restriction to attached roles. -/
def componentCrossingProduct
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (R : RestCube cut dimension)
    (i : Fin N) (K : ActiveComponent G cut)
    (x : ComponentAssignment dimension K) : ℝ :=
  ∏ z : AttachedRole cut K,
    trialScalarEta dimension N hN
      ⟨i, ⟨K, ⟨z, x ⟨z.1, z.2.1⟩⟩⟩⟩ R

@[simp] theorem componentCrossingProduct_of_split
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (I : InternalCube cut dimension)
    (R : RestCube cut dimension)
    (i : Fin N) (K : ActiveComponent G cut)
    (xB : BoundaryAssignment dimension K)
    (y : InteriorAssignment dimension K) :
    componentCrossingProduct dimension N hN R i K
      ((componentAssignmentEquiv dimension K).symm (xB, y)) =
    componentEtaProduct dimension N hN R i K xB := by
  classical
  unfold componentCrossingProduct componentEtaProduct
  apply Finset.prod_congr rfl
  intro z _hg
  rw [componentAssignmentEquiv_symm_boundary]

/-- Component finite contraction after fixing the complete internal realization.
This is formula (8.4) in `P2a_PROOF.md`, with crossing products already grouped
by attached role but still reading the original typed edge-array coordinates. -/
def componentContraction
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (I : InternalCube cut dimension)
    (R : RestCube cut dimension)
    (i : Fin N) (K : ActiveComponent G cut) : ℝ :=
  ∑ x : ComponentAssignment dimension K,
    componentInternalMonomial dimension I K x *
      componentCrossingProduct dimension N hN R i K x

/-! ## 4. Gamma coefficients and exact finite regrouping -/

/-- `gamma^I_{x_B}`: sum the fixed internal monomial over all assignments on
`K \ B_K`. -/
def componentGamma
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    (I : InternalCube cut dimension)
    (K : ActiveComponent G cut)
    (xB : BoundaryAssignment dimension K) : ℝ :=
  ∑ y : InteriorAssignment dimension K,
    componentInternalMonomial dimension I K
      ((componentAssignmentEquiv dimension K).symm (xB, y))

/-- Exact deterministic identity
`T_K(s_i) = sum_{x_B} gamma^I_{x_B} prod_z eta_{i,K,z}(x_z)`.
No moment bound or good-event assumption is used. -/
theorem componentContraction_eq_gamma_eta
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (I : InternalCube cut dimension)
    (R : RestCube cut dimension)
    (i : Fin N) (K : ActiveComponent G cut) :
    componentContraction dimension N hN I R i K =
      ∑ xB : BoundaryAssignment dimension K,
        componentGamma dimension I K xB *
          componentEtaProduct dimension N hN R i K xB := by
  classical
  let e := componentAssignmentEquiv dimension K
  let f : ComponentAssignment dimension K → ℝ :=
    fun x => componentInternalMonomial dimension I K x *
      componentCrossingProduct dimension N hN R i K x
  unfold componentContraction
  change (∑ x : ComponentAssignment dimension K, f x) = _
  calc
    (∑ x : ComponentAssignment dimension K, f x) =
        ∑ p : BoundaryAssignment dimension K × InteriorAssignment dimension K,
          f (e.symm p) := by
      exact (Equiv.sum_comp e.symm f).symm
    _ = ∑ xB : BoundaryAssignment dimension K,
          ∑ y : InteriorAssignment dimension K,
            f (e.symm (xB, y)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ xB : BoundaryAssignment dimension K,
          ∑ y : InteriorAssignment dimension K,
            componentInternalMonomial dimension I K (e.symm (xB, y)) *
              componentEtaProduct dimension N hN R i K xB := by
      apply Finset.sum_congr rfl
      intro xB _hg
      apply Finset.sum_congr rfl
      intro y _hg
      dsimp only [f, e]
      rw [componentCrossingProduct_of_split dimension N hN I R i K xB y]
    _ = ∑ xB : BoundaryAssignment dimension K,
          (∑ y : InteriorAssignment dimension K,
            componentInternalMonomial dimension I K (e.symm (xB, y))) *
              componentEtaProduct dimension N hN R i K xB := by
      apply Finset.sum_congr rfl
      intro xB _hg
      rw [Finset.sum_mul]
    _ = _ := by
      rfl

/-- Deterministic polynomial `Phi_K^I` evaluated on an arbitrary family of
attached-role sign vectors. -/
def componentPhi
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    (I : InternalCube cut dimension)
    (K : ActiveComponent G cut)
    (q : ∀ z : AttachedRole cut K, Fin (dimension z.1) → ℝ) : ℝ :=
  ∑ xB : BoundaryAssignment dimension K,
    componentGamma dimension I K xB *
      ∏ z : AttachedRole cut K, q z (xB z)

/-- `T_K(s_i)` is `Phi_K^I` applied to the actual eta vectors. -/
theorem componentContraction_eq_componentPhi
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ) (N : ℕ)
    (hN : ∀ u : SeparatorRole G cut, N ≤ dimension u.1)
    (I : InternalCube cut dimension)
    (R : RestCube cut dimension)
    (i : Fin N) (K : ActiveComponent G cut) :
    componentContraction dimension N hN I R i K =
      componentPhi dimension I K
        (fun z j => trialScalarEta dimension N hN
          ⟨i, ⟨K, ⟨z, j⟩⟩⟩ R) := by
  rw [componentContraction_eq_gamma_eta]
  rfl

/-! ## 5. Boundary cases -/

/-- A singleton component may have no internal edge.  The internal monomial is
then the empty product `1`; this theorem also covers any active component with
an empty internal-edge type. -/
theorem componentInternalMonomial_eq_one_of_isEmpty
    {G : PartiteShape} {cut : Finset (Fin G.roles)}
    (dimension : Fin G.roles → ℕ)
    (I : InternalCube cut dimension)
    (K : ActiveComponent G cut)
    [IsEmpty (ComponentInternalEdge K)]
    (x : ComponentAssignment dimension K) :
    componentInternalMonomial dimension I K x = 1 := by
  simp [componentInternalMonomial]

#print axioms componentAssignmentEquiv
#print axioms componentInternalAddress
#print axioms componentCrossingProduct_of_split
#print axioms componentContraction_eq_gamma_eta
#print axioms componentContraction_eq_componentPhi
#print axioms componentInternalMonomial_eq_one_of_isEmpty

end P2a
end GraphMatrixReplica
