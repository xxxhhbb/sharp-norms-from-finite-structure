import R6.P3LargeNArithmetic

/-! # Actual P1-to-P3 one-component tail -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica
open WeightedSignTilt

/-- Uniformly over every legitimate local choice in a fixed graph, every
internally-good complete realization has the P3 one-component tail under its
actual second-layer law.  The constants precede the cut, component,
distinguished role, dimensions and realization. -/
theorem p3_component_tail_uniform_graph
    (P : PaperShape) (a b epsTilt : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hepsTilt : 0 < epsTilt) :
    ∃ pExt cS CS : ℝ, ∃ n0 : ℕ,
      0 < pExt ∧ 0 < cS ∧ 0 < CS ∧ 1 ≤ n0 ∧
      ∀ (cut : Finset (Fin P.roles))
        (c : P.toPartiteShape.C079CutComponent cut),
        c.IsActive →
        ∀ (z0 : Fin P.roles) (hz0 : z0 ∈ p1BoundaryRoles P cut c)
          (dimension : Fin P.roles → ℕ) (n : ℕ), n0 ≤ n →
          P1AD.Balanced P dimension cut c a b n →
          ∀ epsInternal : P1InternalSample P dimension cut c,
            P1AD.InternalGood P dimension cut c z0 hz0 n epsInternal →
            let k := P1AD.roleCount P cut c
            let t := epsTilt * (n : ℝ) ^ ((k : ℝ) / 2) *
              Real.sqrt (Real.log (n : ℝ))
            pExt * ((1 / 2 : ℝ) *
                Real.exp (-(96 * epsTilt ^ 2 * Real.log (n : ℝ) / cS))) ≤
              finiteUniformProbability
                (fun x : P1SecondSample P dimension cut c z0 ×
                    (Fin (dimension z0) → Bool) =>
                  t ≤ |weightedSum
                    (fun j => p1Z P dimension cut c z0 hz0
                      epsInternal x.1 j) x.2|) := by
  classical
  obtain ⟨pInt, pExt, cQ, CQ, cS, CS, nP,
      hpInt, hpExt, hcQ, hCQ, hcS, hCS, hnP, hP⟩ :=
    P1AD.p1_D_uniform_graph P a b ha hab
  obtain ⟨nA, hA⟩ := p3_exists_large_n_tilt_inputs CS cS epsTilt hcS hepsTilt
  refine ⟨pExt, cS, CS, max nP nA, hpExt, hcS, hCS, ?_, ?_⟩
  · exact hnP.trans (le_max_left nP nA)
  intro cut c hActive z0 hz0 dimension n hn hsize epsInternal hInternal
  have hnP' : nP ≤ n := (le_max_left nP nA).trans hn
  have hnA' : nA ≤ n := (le_max_right nP nA).trans hn
  have hLocal := hP cut c hActive z0 hz0 dimension n hnP' hsize
  have hSecondProb := hLocal.2.2.1 epsInternal hInternal
  have hSecondBounds := hLocal.2.2.2
  let k := P1AD.roleCount P cut c
  let t := epsTilt * (n : ℝ) ^ ((k : ℝ) / 2) *
    Real.sqrt (Real.log (n : ℝ))
  have hInputs := hA n k hnA'
  have hn1 : 1 ≤ n := hInputs.1
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnPow : 0 < (n : ℝ) ^ k := pow_pos hnR k
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  letI : Nonempty (P1SecondSample P dimension cut c z0) :=
    ⟨fun _ _ => false⟩
  dsimp [k, t]
  exact p3_component_tail_after_second_good
    (P1AD.SecondGood P dimension cut c z0 hz0 n epsInternal)
    (fun eta j => p1Z P dimension cut c z0 hz0 epsInternal eta j)
    (fun eta => p1SigmaSq P dimension cut c z0 hz0 epsInternal eta)
    (epsTilt * (n : ℝ) ^ ((P1AD.roleCount P cut c : ℝ) / 2) *
      Real.sqrt (Real.log (n : ℝ)))
    ((n : ℝ) ^ ((P1AD.roleCount P cut c : ℝ) / 2 - 1 / 4))
    cS CS ((n : ℝ) ^ P1AD.roleCount P cut c) epsTilt
    (Real.log (n : ℝ)) pExt
    hcS hnPow ht0 hpExt.le hSecondProb
    (by intro eta hgood; rfl)
    (by intro eta hgood; exact (hSecondBounds epsInternal eta hgood).1)
    (by intro eta hgood; exact (hSecondBounds epsInternal eta hgood).2.1)
    hInputs.2.1
    (by intro eta hgood j; exact (hSecondBounds epsInternal eta hgood).2.2 j)
    hInputs.2.2.1
    hInputs.2.2.2

#print axioms p3_component_tail_uniform_graph

end GraphMatrixReplica
