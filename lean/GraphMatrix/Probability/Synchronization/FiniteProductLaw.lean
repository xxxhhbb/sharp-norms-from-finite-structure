import GraphMatrix.FiniteConditionalTrials
import GraphMatrix.JointEdgeRademacherExpectation

/-!
# finite product / conditioning helpers

This module contains only finite-uniform identities.  It does not assume a
extra probabilistic independence premise.  Product laws are proved by explicit finite
sums, and conditioning on a fixed internal realization is represented by a
fiber of a product sample.

-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Public version of the elementary nonnegativity fact used by P3. -/
theorem p3_finiteUniformProbability_nonneg
    {Ω : Type} [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] :
    0 ≤ finiteUniformProbability P := by
  have h := paperMean_mono (f := fun _ : Ω => (0 : ℝ))
      (g := fun ω => if P ω then 1 else 0)
      (by intro ω; split <;> norm_num)
  simpa [finiteUniformProbability, paperMean_zero] using h

/-- Public version of the elementary upper bound used by P3. -/
theorem p3_finiteUniformProbability_le_one
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] :
    finiteUniformProbability P ≤ 1 := by
  have hmeanOne : paperMean (fun _ : Ω => (1 : ℝ)) = 1 := by
    unfold paperMean
    simp [Fintype.card_ne_zero]
  calc
    finiteUniformProbability P ≤ paperMean (fun _ : Ω => (1 : ℝ)) := by
      apply paperMean_mono
      intro ω
      split <;> norm_num
    _ = 1 := hmeanOne

/-- Finite uniform probability is invariant under an explicit equivalence. -/
theorem p3_finiteUniformProbability_equiv
    {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : B → Prop) [DecidablePred P] :
    finiteUniformProbability (fun a => P (e a)) =
      finiteUniformProbability P := by
  unfold finiteUniformProbability
  exact paperMean_equiv e (fun b => if P b then 1 else 0)

/-- Uniform mean over a product is the iterated uniform mean. -/
theorem p3_paperMean_prod_eq_iterated
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A × B → ℝ) :
    paperMean f =
      paperMean (fun a : A => paperMean (fun b : B => f (a, b))) := by
  unfold paperMean
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  push_cast
  rw [← Finset.mul_sum]
  ring

/-- Uniform averaging of a product over a dependent family of fresh
blocks.  This is the heterogeneous-component product law: the block sample
`Ω b` may depend on `b`. -/
theorem p3_paperMean_dependent_coordinateProduct
    {B : Type} [Fintype B] [DecidableEq B]
    (Ω : B → Type) [∀ b, Fintype (Ω b)]
    (F : ∀ b, Ω b → ℝ) :
    paperMean (fun w : ∀ b, Ω b => ∏ b : B, F b (w b)) =
      ∏ b : B, paperMean (F b) := by
  classical
  unfold paperMean
  rw [Fintype.card_pi]
  push_cast
  rw [← Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

/-- Exact simultaneous-event product law for heterogeneous independent fresh
blocks.  No equal-dimension assumption is present. -/
theorem p3_finiteUniformProbability_dependent_all
    {B : Type} [Fintype B] [DecidableEq B]
    (Ω : B → Type) [∀ b, Fintype (Ω b)]
    (E : ∀ b, Ω b → Prop) [∀ b, DecidablePred (E b)] :
    finiteUniformProbability
        (fun w : ∀ b, Ω b => ∀ b, E b (w b)) =
      ∏ b : B, finiteUniformProbability (E b) := by
  classical
  have hpoint (w : ∀ b, Ω b) :
      (if (∀ b, E b (w b)) then (1 : ℝ) else 0) =
        ∏ b : B, (if E b (w b) then (1 : ℝ) else 0) := by
    by_cases h : ∀ b, E b (w b)
    · simp [h]
    · rw [if_neg h]
      obtain ⟨b, hb⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])
  unfold finiteUniformProbability
  rw [show
      (fun w : ∀ b, Ω b => if (∀ b, E b (w b)) then (1 : ℝ) else 0) =
        (fun w : ∀ b, Ω b => ∏ b : B, (if E b (w b) then (1 : ℝ) else 0))
      from funext hpoint]
  exact p3_paperMean_dependent_coordinateProduct Ω
    (fun b x => if E b x then 1 else 0)

/--
Fiber integration lemma used for the second good event.

If `G` has probability at least `p`, and on every good first coordinate the
fiber success probability is at least `q`, then the joint product sample has
probability at least `p*q` of `G ∧ success`.
-/
theorem p3_finiteUniformProbability_good_fiber_lower
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (G : A → Prop) (S : A → B → Prop)
    [DecidablePred G] [∀ a, DecidablePred (S a)]
    (p q : ℝ) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hG : p ≤ finiteUniformProbability G)
    (hS : ∀ a, G a → q ≤ finiteUniformProbability (S a)) :
    p * q ≤
      finiteUniformProbability (fun x : A × B => G x.1 ∧ S x.1 x.2) := by
  classical
  have hinner (a : A) :
      paperMean (fun b : B =>
        if G a ∧ S a b then (1 : ℝ) else 0) =
      if G a then finiteUniformProbability (S a) else 0 := by
    by_cases hg : G a
    · simp only [hg, true_and, if_true]
      rfl
    · simp [hg, paperMean_zero]
  have hpoint (a : A) :
      (if G a then q else 0) ≤
        (if G a then finiteUniformProbability (S a) else 0) := by
    by_cases hg : G a
    · simpa [hg] using hS a hg
    · simp [hg]
  have hfactor :
      paperMean (fun a : A => if G a then q else 0) =
        q * finiteUniformProbability G := by
    unfold finiteUniformProbability paperMean
    have hh (a : A) :
        (if G a then q else 0) =
          q * (if G a then (1 : ℝ) else 0) := by
      by_cases hg : G a <;> simp [hg]
    simp_rw [hh]
    rw [← Finset.mul_sum]
    ring
  have hjoint :
      paperMean (fun a : A =>
        if G a then finiteUniformProbability (S a) else 0) =
      finiteUniformProbability
        (fun x : A × B => G x.1 ∧ S x.1 x.2) := by
    unfold finiteUniformProbability
    rw [p3_paperMean_prod_eq_iterated]
    exact (congrArg paperMean (funext hinner)).symm
  calc
    p * q ≤ q * finiteUniformProbability G := by
      have := mul_le_mul_of_nonneg_left hG hq0
      simpa [mul_comm] using this
    _ = paperMean (fun a : A => if G a then q else 0) := hfactor.symm
    _ ≤ paperMean (fun a : A =>
          if G a then finiteUniformProbability (S a) else 0) :=
      paperMean_mono hpoint
    _ = finiteUniformProbability
          (fun x : A × B => G x.1 ∧ S x.1 x.2) := hjoint

/-- Functions on a sigma-type are exactly dependent families of functions. -/
def p3_sigmaFunctionEquiv
    {I : Type} (A : I → Type) (X : Type) :
    ((Σ i, A i) → X) ≃ (∀ i, A i → X) where
  toFun f i a := f ⟨i, a⟩
  invFun g x := g x.1 x.2
  left_inv f := by
    funext x
    rcases x with ⟨i, a⟩
    rfl
  right_inv g := by
    funext i a
    rfl

/-- The actual joint edge-array sample is a Bool assignment to raw typed
addresses `(edge id, source label, target label)`. -/
abbrev P3EdgeRawAddress {G : PartiteShape}
    (dimension : Fin G.roles → ℕ) : Type :=
  Σ e : Fin G.edges, EdgeSignCoordinate dimension e

/-- Exact equivalence between the existing edge-indexed sample and the raw
address formulation used in the disjoint-support proof. -/
def p3_jointEdgeSampleRawAddressEquiv
    {G : PartiteShape} (dimension : Fin G.roles → ℕ) :
    JointEdgeSignSample dimension ≃ (P3EdgeRawAddress dimension → Bool) :=
  (p3_sigmaFunctionEquiv
    (fun e : Fin G.edges => EdgeSignCoordinate dimension e) Bool).symm

/-- Raw addresses with different edge IDs are different, independently of
numerical label values. -/
theorem p3_rawAddress_ne_of_edge_ne
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    {e e' : Fin G.edges} (hee : e ≠ e')
    (c : EdgeSignCoordinate dimension e)
    (c' : EdgeSignCoordinate dimension e') :
    (⟨e, c⟩ : P3EdgeRawAddress dimension) ≠ ⟨e', c'⟩ := by
  intro h
  exact hee (congrArg Sigma.fst h)

/-- On a fixed edge, embedding its directed source/target coordinate into the
raw address type is injective. -/
theorem p3_rawAddress_fixed_edge_injective
    {G : PartiteShape} {dimension : Fin G.roles → ℕ}
    (e : Fin G.edges) :
    Function.Injective
      (fun c : EdgeSignCoordinate dimension e =>
        (⟨e, c⟩ : P3EdgeRawAddress dimension)) := by
  intro c c' h
  cases h
  rfl


end GraphMatrixReplica
