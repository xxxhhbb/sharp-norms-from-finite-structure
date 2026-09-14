import GraphMatrix.Main.InternalSampleProduct
import GraphMatrix.Main.UniformLowerEndpoint

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GraphMatrixReplica
attribute [local instance] Classical.propDecidable

/-- and count the same actual component-role subtype. -/
theorem main_P1_componentRoleCount_eq (P : PaperShape) (cut : Finset (Fin P.roles))
    (K : P2a.ActiveComponent P.toPartiteShape cut) :
    P1AD.roleCount P cut K.1 = Fintype.card (P2a.ComponentRole K) := by
  simp [P1AD.roleCount, p1ComponentRoles, P2a.ComponentRole]

/-- The actual equal floor color classes satisfy P1's heterogeneous balance
conditions, uniformly over every cut and component. -/
theorem main_uniformFloor_balanced (P : PaperShape) (hr : 0 < P.roles)
    (cut : Finset (Fin P.roles)) (K : P.toPartiteShape.C079CutComponent cut)
    (n : ℕ) (hn : 2 * P.roles ≤ n) :
    P1AD.Balanced P (fun _ : Fin P.roles => n / P.roles) cut K
      (1 / (2 * (P.roles : ℝ))) 1 n := by
  intro v hv
  have h := main_uniformRoleDimension_bounds P.roles n hr hn
  refine ⟨h.1, ?_⟩
  simpa only [one_mul, Nat.cast_le] using h.2

/-- A single positive graph constant bounds the probability of the complete
actual internally-good event for every cut and all sufficiently large n.
The floor dimensions and the full good event are instantiated, not assumed. -/
theorem main_internalGood_uniform_floor (P : PaperShape) (hr : 0 < P.roles) :
    ∃ q : ℝ, 0 < q ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ (cut : Finset (Fin P.roles)) (n : ℕ), N ≤ n →
        q ≤ finiteUniformProbability
          (mainInternalGood P cut (fun _ : Fin P.roles => n / P.roles) n) := by
  have hrR : (1 : ℝ) ≤ (P.roles : ℝ) := by exact_mod_cast hr
  have ha : 0 < (1 / (2 * (P.roles : ℝ))) := by positivity
  have hab : (1 / (2 * (P.roles : ℝ))) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  obtain ⟨p, hp, N, hN, hP⟩ :=
    main_internalGood_uniform_graph P (1 / (2 * (P.roles : ℝ))) 1 ha hab
  refine ⟨(min p 1) ^ P.roles, pow_pos (lt_min hp (by norm_num)) _,
    max N (2 * P.roles), hN.trans (le_max_left _ _), ?_⟩
  intro cut n hn
  have hcard : Fintype.card (P2a.ActiveComponent P.toPartiteShape cut) ≤ P.roles := by
    rw [main_activeComponent_card_eq_count]
    exact P.toPartiteShape.c079ActiveComponentCount_le_roles cut
  have hmin0 : 0 ≤ min p 1 := le_min hp.le (by norm_num)
  calc
    (min p 1) ^ P.roles ≤
        (min p 1) ^ Fintype.card (P2a.ActiveComponent P.toPartiteShape cut) :=
      pow_le_pow_of_le_one hmin0 (min_le_right p 1) hcard
    _ ≤ p ^ Fintype.card (P2a.ActiveComponent P.toPartiteShape cut) :=
      pow_le_pow_left₀ hmin0 (min_le_left p 1) _
    _ ≤ _ := hP cut _ n ((le_max_left _ _).trans hn)
      (fun K => main_uniformFloor_balanced P hr cut K.1 n ((le_max_right _ _).trans hn))

end GraphMatrixReplica
