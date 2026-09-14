import GraphMatrix.Main.UniformLowerEndpoint
import GraphMatrix.RademacherWalshProjection

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
open Model Model.C2Actual
attribute [local instance] Classical.propDecidable

/-- Projecting a complete joint sample to its actual nonfresh coordinates
preserves every component contraction at every separator tuple. -/
theorem main_componentContraction_joint_eq
    (G : PartiteShape) (cut : Finset (Fin G.roles)) (dimension : Fin G.roles → ℕ)
    (ε : JointEdgeSignSample (G := G) dimension)
    (s : CutAssignment (G := G) cut dimension) (K : P2a.ActiveComponent G cut) :
    actualComponentContraction (G := G) cut dimension
        ((sampleSplitEquiv (G := G) cut dimension ε).1) s K =
      componentContractionAt (G := G) cut dimension
        ((P2a.internalRestEquiv (G := G) cut dimension ε).1)
        ((P2a.internalRestEquiv (G := G) cut dimension ε).2) s K := by
  unfold actualComponentContraction componentContractionAt
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  · unfold P2a.componentInternalMonomial
    apply Finset.prod_congr rfl
    intro e _
    rw [frozenInternalCube_apply, internalRestEquiv_internal_apply]
    rfl
  · unfold componentCrossingProductAt
    apply Finset.prod_congr rfl
    intro z _
    unfold separatorEta
    apply Finset.prod_congr rfl
    intro c _
    rw [frozenRestCube_crossing_apply, internalRestEquiv_rest_apply]
    rfl

/-- Averaging unused independent coordinates changes no observable. -/
theorem main_paperMean_prod_fst {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → ℝ) : paperMean (fun p : A × B => f p.1) = paperMean f := by
  have h := P2a.paperMean_prod (fun a : A => fun _b : B => f a)
  simpa only [P2a.paperMean_eq_original, paperMean_const_function] using h

/-- The full family of actual frozen contractions has exactly the same law
as the family read from a uniform complete internal/rest pair. Fresh coordinates
are removed only after proving that every family entry ignores them. -/
theorem main_contractionFamily_mean
    (G : PartiteShape) (cut : Finset (Fin G.roles)) (dimension : Fin G.roles → ℕ)
    (H : (CutAssignment (G := G) cut dimension → P2a.ActiveComponent G cut → ℝ) → ℝ) :
    paperMean (fun ω : FrozenSample (G := G) cut dimension =>
      H (fun s K => actualComponentContraction (G := G) cut dimension ω s K)) =
    paperMean (fun p : P2a.InternalCube (G := G) cut dimension ×
        P2a.RestCube (G := G) cut dimension =>
      H (fun s K => componentContractionAt (G := G) cut dimension p.1 p.2 s K)) := by
  let f := fun ω : FrozenSample (G := G) cut dimension =>
    H (fun s K => actualComponentContraction (G := G) cut dimension ω s K)
  have hsplit := paperMean_equiv (sampleSplitEquiv (G := G) cut dimension)
    (fun p : FrozenSample (G := G) cut dimension × FreshSample (G := G) cut dimension => f p.1)
  have hrest := paperMean_equiv (P2a.internalRestEquiv (G := G) cut dimension)
    (fun p : P2a.InternalCube (G := G) cut dimension × P2a.RestCube (G := G) cut dimension =>
      H (fun s K => componentContractionAt (G := G) cut dimension p.1 p.2 s K))
  calc
    _ = paperMean (fun ε : JointEdgeSignSample (G := G) dimension =>
        f ((sampleSplitEquiv (G := G) cut dimension ε).1)) :=
      (hsplit.trans (main_paperMean_prod_fst f)).symm
    _ = paperMean (fun ε : JointEdgeSignSample (G := G) dimension =>
        H (fun s K => componentContractionAt (G := G) cut dimension
          ((P2a.internalRestEquiv (G := G) cut dimension ε).1)
          ((P2a.internalRestEquiv (G := G) cut dimension ε).2) s K)) := by
      apply congrArg paperMean
      funext ε
      dsimp [f]
      congr 1
      funext s K
      exact main_componentContraction_joint_eq G cut dimension ε s K
    _ = _ := hrest

/-- Exact actual witness-event probability, with a single separator tuple and
the product of all genuine active contractions on both sides. -/
theorem main_frozen_witness_probability_eq_internalRest
    (G : PartiteShape) (cut : Finset (Fin G.roles)) (dimension : Fin G.roles → ℕ) (t : ℝ) :
    finiteUniformProbability (fun ω : FrozenSample (G := G) cut dimension =>
      ∃ s : CutAssignment (G := G) cut dimension,
        t ≤ |actualWeight (G := G) cut dimension ω s|) =
    finiteUniformProbability (fun p : P2a.InternalCube (G := G) cut dimension ×
        P2a.RestCube (G := G) cut dimension =>
      ∃ s : CutAssignment (G := G) cut dimension,
        t ≤ |∏ K : P2a.ActiveComponent G cut,
          componentContractionAt (G := G) cut dimension p.1 p.2 s K|) := by
  have h := main_contractionFamily_mean G cut dimension
    (fun F => if ∃ s, t ≤ |∏ K, F s K| then (1 : ℝ) else 0)
  unfold finiteUniformProbability actualWeight
  convert h using 1 <;> congr!

end GraphMatrixReplica
