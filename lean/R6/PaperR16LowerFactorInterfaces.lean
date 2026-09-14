import Mathlib

/-!
# R16 lower-bound and independent-factor finite interfaces

These are algebraic components of the lower-bound and factor appendices.
The Hilbert-space stacking inequality, conditional moderate deviation,
weighted tilt, replica-state count, and asymptotic norm estimates are not
deduced from these finite identities.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.PaperR16

/-- One synchronized separator label is enough to lower-bound the product
of active-component magnitudes.  This is deliberately not a product of
individually optimized labels. -/
theorem synchronized_product_at_one_label
    {A : Type*} [Fintype A]
    (component : A → ℝ) (threshold : A → ℝ)
    (hThreshold : ∀ a, 0 ≤ threshold a)
    (hWitness : ∀ a, threshold a ≤ |component a|) :
    (∏ a : A, threshold a) ≤ |∏ a : A, component a| := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod
    (fun a _ => hThreshold a)
    (fun a _ => hWitness a)

/-- The empty active-component family contributes exactly one; it cannot
create a logarithmic factor. -/
theorem no_active_component_weight :
    (∏ _a : Fin 0, (1 : ℝ)) = 1 := by simp

/-- The finite Hölder interpolation step in the lower stacking proof:
`(∑ Z²)^3 ≤ (∑ Z)^2 (∑ Z⁴)` for every nonnegative family.  Both
Cauchy--Schwarz applications are proved here, with no probabilistic premise. -/
theorem finite_nonnegative_moment_interpolation
    {Ω : Type*} (s : Finset Ω) (Z : Ω → ℝ)
    (hZ : ∀ ω ∈ s, 0 ≤ Z ω) :
    (∑ ω ∈ s, Z ω ^ 2) ^ 3 ≤
      (∑ ω ∈ s, Z ω) ^ 2 * (∑ ω ∈ s, Z ω ^ 4) := by
  let m1 : ℝ := ∑ ω ∈ s, Z ω
  let m2 : ℝ := ∑ ω ∈ s, Z ω ^ 2
  let m3 : ℝ := ∑ ω ∈ s, Z ω ^ 3
  let m4 : ℝ := ∑ ω ∈ s, Z ω ^ 4
  have hm1 : 0 ≤ m1 := Finset.sum_nonneg fun ω hω => hZ ω hω
  have hm2 : 0 ≤ m2 := Finset.sum_nonneg fun ω _ => sq_nonneg (Z ω)
  have hm3 : 0 ≤ m3 := Finset.sum_nonneg fun ω hω => pow_nonneg (hZ ω hω) _
  have hm4 : 0 ≤ m4 := Finset.sum_nonneg fun ω hω => pow_nonneg (hZ ω hω) _
  have h12 : m2 ^ 2 ≤ m1 * m3 := by
    simpa only [m1, m2, m3] using
      (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (r := fun ω => Z ω ^ 2)
        (f := fun ω => Z ω)
        (g := fun ω => Z ω ^ 3)
        (fun ω hω => hZ ω hω)
        (fun ω hω => pow_nonneg (hZ ω hω) _)
        (fun ω _ => by ring_nf; exact le_rfl))
  have h23 : m3 ^ 2 ≤ m2 * m4 := by
    simpa only [m2, m3, m4] using
      (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (r := fun ω => Z ω ^ 3)
        (f := fun ω => Z ω ^ 2)
        (g := fun ω => Z ω ^ 4)
        (fun ω _ => sq_nonneg (Z ω))
        (fun ω hω => pow_nonneg (hZ ω hω) _)
        (fun ω _ => by ring_nf; exact le_rfl))
  have h4 : m2 ^ 4 ≤ m1 ^ 2 * m2 * m4 := by
    calc
      m2 ^ 4 = (m2 ^ 2) ^ 2 := by ring
      _ ≤ (m1 * m3) ^ 2 := pow_le_pow_left₀ (sq_nonneg m2) h12 2
      _ = m1 ^ 2 * m3 ^ 2 := by ring
      _ ≤ m1 ^ 2 * (m2 * m4) :=
        mul_le_mul_of_nonneg_left h23 (sq_nonneg m1)
      _ = m1 ^ 2 * m2 * m4 := by ring
  change m2 ^ 3 ≤ m1 ^ 2 * m4
  by_cases hz : m2 = 0
  · simp [hz, mul_nonneg (sq_nonneg m1) hm4]
  · have hp : 0 < m2 := lt_of_le_of_ne hm2 (Ne.symm hz)
    have hCancel : m2 ^ 3 * m2 ≤ (m1 ^ 2 * m4) * m2 := by
      nlinarith [h4]
    exact le_of_mul_le_mul_right hCancel hp

/-- Quantitative first-moment consequence with the paper's fourth-moment
constant `3`.  `hFourth` is kept explicit: it is the separate Rademacher
pairing/Hilbert-space computation, not inferred from interpolation. -/
theorem finite_first_moment_lower_of_fourth
    {Ω : Type*} (s : Finset Ω) (Z : Ω → ℝ)
    (hZ : ∀ ω ∈ s, 0 ≤ Z ω)
    (hFourth :
      (s.card : ℝ) * (∑ ω ∈ s, Z ω ^ 4) ≤
        3 * (∑ ω ∈ s, Z ω ^ 2) ^ 2) :
    (s.card : ℝ) * (∑ ω ∈ s, Z ω ^ 2) ≤
      3 * (∑ ω ∈ s, Z ω) ^ 2 := by
  let m1 : ℝ := ∑ ω ∈ s, Z ω
  let m2 : ℝ := ∑ ω ∈ s, Z ω ^ 2
  let m4 : ℝ := ∑ ω ∈ s, Z ω ^ 4
  have hm2 : 0 ≤ m2 := Finset.sum_nonneg fun ω _ => sq_nonneg (Z ω)
  have hN : 0 ≤ (s.card : ℝ) := by positivity
  have hInterp : m2 ^ 3 ≤ m1 ^ 2 * m4 :=
    finite_nonnegative_moment_interpolation s Z hZ
  change (s.card : ℝ) * m2 ≤ 3 * m1 ^ 2
  by_cases hz : m2 = 0
  · simp [hz, sq_nonneg m1]
  · have hp : 0 < m2 := lt_of_le_of_ne hm2 (Ne.symm hz)
    have hMain :
        ((s.card : ℝ) * m2) * m2 ^ 2 ≤
          (3 * m1 ^ 2) * m2 ^ 2 := by
      calc
        ((s.card : ℝ) * m2) * m2 ^ 2 =
            (s.card : ℝ) * m2 ^ 3 := by ring
        _ ≤ (s.card : ℝ) * (m1 ^ 2 * m4) :=
          mul_le_mul_of_nonneg_left hInterp hN
        _ = m1 ^ 2 * ((s.card : ℝ) * m4) := by ring
        _ ≤ m1 ^ 2 * (3 * m2 ^ 2) :=
          mul_le_mul_of_nonneg_left hFourth (sq_nonneg m1)
        _ = (3 * m1 ^ 2) * m2 ^ 2 := by ring
    exact le_of_mul_le_mul_right hMain (pow_pos hp 2)

/-- All full assignments of detached independent coordinate families
factor as a product of scalar sums.  This is the finite algebra behind
independence in the exact detached-moment restoration. -/
theorem detached_product_sum
    {J : Type*} [Fintype J] [DecidableEq J]
    (Ω : J → Type*) [∀ j, Fintype (Ω j)]
    (f : ∀ j, Ω j → ℝ) :
    (∑ ω : ∀ j, Ω j, ∏ j : J, f j (ω j)) =
      ∏ j : J, (∑ x : Ω j, f j x) := by
  classical
  exact (Fintype.prod_sum f).symm

/-- Detached `2p`-moments multiply over disjoint finite sample spaces.
No claim about their size is made. -/
theorem detached_even_moment_sum
    {J : Type*} [Fintype J] [DecidableEq J]
    (Ω : J → Type*) [∀ j, Fintype (Ω j)]
    (Z : ∀ j, Ω j → ℝ) (p : ℕ) :
    (∑ ω : ∀ j, Ω j, (∏ j : J, Z j (ω j)) ^ (2 * p)) =
      ∏ j : J, (∑ x : Ω j, (Z j x) ^ (2 * p)) := by
  classical
  simp only [← Finset.prod_pow]
  exact detached_product_sum Ω (fun j x => (Z j x) ^ (2 * p))

/-- Exact finite-sample version of the full trace-moment restoration at the
end of Appendix F.  `coreTrace` is a deterministic trace-moment observable
on an independent core sample space; no quantitative bound on it is assumed
or obtained. -/
theorem detached_core_trace_moment_sum
    {J Ψ : Type*} [Fintype J] [DecidableEq J] [Fintype Ψ]
    (Ω : J → Type*) [∀ j, Fintype (Ω j)]
    (Z : ∀ j, Ω j → ℝ) (coreTrace : Ψ → ℝ)
    (d : ℝ) (p : ℕ) :
    (∑ ω : ∀ j, Ω j, ∑ ψ : Ψ,
        (d * ∏ j : J, Z j (ω j)) ^ (2 * p) * coreTrace ψ) =
      d ^ (2 * p) *
        (∏ j : J, ∑ x : Ω j, (Z j x) ^ (2 * p)) *
          (∑ ψ : Ψ, coreTrace ψ) := by
  classical
  calc
    (∑ ω : ∀ j, Ω j, ∑ ψ : Ψ,
        (d * ∏ j : J, Z j (ω j)) ^ (2 * p) * coreTrace ψ) =
      (∑ ω : ∀ j, Ω j,
        (d * ∏ j : J, Z j (ω j)) ^ (2 * p)) *
          (∑ ψ : Ψ, coreTrace ψ) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = d ^ (2 * p) *
          (∑ ω : ∀ j, Ω j,
            (∏ j : J, Z j (ω j)) ^ (2 * p)) *
          (∑ ψ : Ψ, coreTrace ψ) := by
      simp [mul_pow, Finset.mul_sum]
    _ = d ^ (2 * p) *
          (∏ j : J, ∑ x : Ω j, (Z j x) ^ (2 * p)) *
          (∑ ψ : Ψ, coreTrace ψ) := by
      rw [detached_even_moment_sum]

/-- A finite separator-layer incidence double-counting identity.  The
predicate represents a whole factor scope contained in a layer, not merely
pairwise incidence in the two-section graph. -/
theorem factor_layer_charge_eq
    {E L : Type*} [Fintype E] [Fintype L]
    (contained : E → L → Prop) [DecidableRel contained]
    (weight : E → ℝ) :
    (∑ e : E,
        weight e *
          ((Finset.univ.filter fun l : L => contained e l).card : ℝ)) =
      ∑ l : L, ∑ e : E, if contained e l then weight e else 0 := by
  classical
  calc
    (∑ e : E,
        weight e *
          ((Finset.univ.filter fun l : L => contained e l).card : ℝ)) =
      ∑ e : E, ∑ l : L, if contained e l then weight e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        simp [Finset.sum_ite, Finset.sum_const_zero, mul_comm]
    _ = ∑ l : L, ∑ e : E, if contained e l then weight e else 0 :=
      Finset.sum_comm

/-- The paper's factor-defect charge follows from the *explicit* interval
containment bound `hBound`.  Proving that bound from the original replica
states remains a separate obligation. -/
theorem factor_defect_charge_le
    {E L : Type*} [Fintype E] [Fintype L]
    (contained : E → L → Prop) [DecidableRel contained]
    (weight : E → ℝ) (hWeight : ∀ e, 0 ≤ weight e)
    (defect : E → ℕ)
    (hBound : ∀ e,
      defect e ≤ (Finset.univ.filter fun l : L => contained e l).card) :
    (∑ e : E, weight e * (defect e : ℝ)) ≤
      ∑ l : L, ∑ e : E, if contained e l then weight e else 0 := by
  classical
  rw [← factor_layer_charge_eq contained weight]
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (hWeight e)
  exact_mod_cast hBound e

/-- Lower-bound role bookkeeping after the active roles have been removed.
Here `active + separator ≤ residual` is the genuine combinatorial premise. -/
theorem lower_role_exponent_bookkeeping
    (residual active separator : ℕ)
    (h : active + separator ≤ residual) :
    residual - (active + separator) + active = residual - separator := by
  omega

#print axioms synchronized_product_at_one_label
#print axioms finite_nonnegative_moment_interpolation
#print axioms finite_first_moment_lower_of_fourth
#print axioms detached_product_sum
#print axioms detached_even_moment_sum
#print axioms detached_core_trace_moment_sum
#print axioms factor_layer_charge_eq
#print axioms factor_defect_charge_le

end GraphMatrixReplica.PaperR16
