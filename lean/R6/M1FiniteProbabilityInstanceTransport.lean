import R6.P3ActualP1ComponentLaw

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica

/-- Transport the finite probability without unfolding its event or coefficients. -/
theorem root_finiteProbability_instances {Omega : Type}
    (i j : Fintype Omega) (E : Omega → Prop) (d e : DecidablePred E) :
    @finiteUniformProbability Omega i E d =
      @finiteUniformProbability Omega j E e := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim d e
  rfl

/-- All outer and component-local finite/decision instances may be transported
before the component events are elaborated or unfolded. -/
theorem root_product_finiteProbability_instances
    {A : Type} {B : A → Type}
    (i j : Fintype A) (f g : ∀ a, Fintype (B a))
    (E : ∀ a, B a → Prop) (d e : ∀ a, DecidablePred (E a)) :
    (letI := i
     ∏ a : A, @finiteUniformProbability (B a) (f a) (E a) (d a)) =
    (letI := j
     ∏ a : A, @finiteUniformProbability (B a) (g a) (E a) (e a)) := by
  cases Subsingleton.elim i j
  cases Subsingleton.elim f g
  cases Subsingleton.elim d e
  rfl

/-- Predicate equivalence and instance transport as separate obligations. -/
theorem root_finiteProbability_congr_instances {Omega : Type}
    (i j : Fintype Omega) (E F : Omega → Prop)
    (d : DecidablePred E) (e : DecidablePred F)
    (h : ∀ x, E x ↔ F x) :
    @finiteUniformProbability Omega i E d =
      @finiteUniformProbability Omega j F e := by
  have hEF : E = F := funext (fun x => propext (h x))
  subst F
  exact root_finiteProbability_instances i j E d e

#print axioms root_finiteProbability_instances
#print axioms root_product_finiteProbability_instances
#print axioms root_finiteProbability_congr_instances
end GraphMatrixReplica
