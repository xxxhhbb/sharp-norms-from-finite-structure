import GraphMatrix.Probability.Synchronization.ActualWeightedSumSync
import GraphMatrix.Main.ActualSimultaneousEvent

noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

/-- The actual simultaneous contraction event has conditional probability at
least one half for every full internally-good realization. -/
theorem main_actual_sync_half_uniform_floor
    (P : PaperShape) (hr : 0 < P.roles) :
    ∃ eps : ℝ, 0 < eps ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ (cut : Finset (Fin P.roles)) (n : ℕ), N ≤ n →
      ∀ I : P2a.InternalCube (G := P.toPartiteShape) cut
          (fun _ : Fin P.roles => n / P.roles),
        mainInternalGood P cut (fun _ : Fin P.roles => n / P.roles) n I →
        (1 / 2 : ℝ) ≤ finiteUniformProbability
          (mainSimultaneousComponentEvent P cut
            (fun _ : Fin P.roles => n / P.roles) eps n I) := by
  classical
  obtain ⟨eps, heps, N, hN, hsync⟩ :=
    p3_actual_weightedSum_sync_half_uniform_floor P hr
  refine ⟨eps, heps, N, hN, ?_⟩
  intro cut n hn I hI
  have h := hsync cut n hn I hI
  have hw : (1 / 2 : ℝ) ≤ finiteUniformProbability
      (mainWeightedTrialSuccess P cut (fun _ : Fin P.roles => n / P.roles)
        (n / P.roles) (fun _ => le_rfl) eps n I) := by
    convert h using 1
    apply main_finiteProbability_congr_instances _ _ _ _ _ _
    intro R
    rfl
  exact hw.trans (main_weightedTrial_probability_le_actual P cut
    (fun _ : Fin P.roles => n / P.roles) (n / P.roles) (fun _ => le_rfl) eps n I)

/-- Graph-only positive witness constants for every cut, with no probabilistic
or norm-bound hypothesis remaining. -/
theorem main_actual_uniformWitness_constants
    (P : PaperShape) (hr : 0 < P.roles) (cut : Finset (Fin P.roles)) :
    ∃ c p : ℝ, 0 < c ∧ 0 < p ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      p ≤ mainUniformWitnessProbability P cut c n := by
  obtain ⟨eps, heps, N, hN, hsync⟩ := main_actual_sync_half_uniform_floor P hr
  exact main_uniformWitness_constants_of_conditional P hr cut eps heps N
    (fun n hn I hI => hsync cut n hn I hI)

end GraphMatrixReplica
