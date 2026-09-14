import R6.P1ActiveComponentCoefficients
import R6.P1CrossingArrays
import R6.EdgeParityEvenEndpoint
import R6.EvenFiberPairing
import R6.PaperMomentToMean

/-!
# P1 formalization targets

Status: specification-only companion to `P1ActiveComponentCoefficients`.
There are intentionally no axioms and no theorem declarations with omitted
proofs.  The commented statements below are the next obligations.

The key quantifier order to preserve is

```
forall eps_internal,
  InternalGood eps_internal ->
    probability_second (SecondGood eps_internal) >= p_ext
```

not an average over `eps_internal` conditioned only on `InternalGood`.
-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica

/-- Finite uniform mean, specialized to the exact internal sample. -/
def p1InternalMean
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (F : P1InternalSample P dimension cut c → ℝ) : ℝ :=
  paperMean F

/-- Finite uniform mean over the effective second layer. -/
def p1SecondMean
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (cut : Finset (Fin P.roles))
    (c : P.toPartiteShape.C079CutComponent cut)
    (z0 : Fin P.roles)
    (F : P1SecondSample P dimension cut c z0 → ℝ) : ℝ :=
  paperMean F

/-- Product of heterogeneous role dimensions over a finite role set. -/
def p1DimensionProduct
    (P : PaperShape) (dimension : Fin P.roles → ℕ)
    (A : Finset (Fin P.roles)) : ℕ :=
  ∏ v ∈ A, dimension v

/-
TARGET A: exact second moment for one actual coefficient.

For `b : P1BoundaryLabel ...`, prove

  p1InternalMean ... (fun eps => p1Gamma ... b eps ^ 2)
    = (p1DimensionProduct P dimension
        (p1ComponentRoles P cut c \ p1BoundaryRoles P cut c) : ℝ)

with a singleton branch.  The proof must show distinct `K\B` assignments
produce distinct internal Walsh supports; it may not assume injectivity.
-/

/-
TARGET B: fixed-order internal moments, enough for P1.

For q = 2, 8, 16 there are constants depending only on q and the fixed
internal graph such that

  E |gamma_b|^(2q) <= C * L^q.

Then derive, retaining all cross terms,

  E Q^2 <= C (E Q)^2,
  E R_j^16 <= C * (prod_{x != z0} m_x)^16.

Suggested combinatorial route:
`replicaEdgeCharacterAverage_eq_indicator`
  -> `edgeParityCompatible_even_left/right`
  -> `exists_fiberwisePairing_of_even_fibers`
  -> finite pairing-code count.
-/

/-
TARGET C: arbitrary deterministic coefficients in the second layer.

After fixing a complete internal realization `eps`, prove for each j

  E_2 |p1Z ... eps eta j|^32 <= C * (p1R ... eps j)^16

and

  E_2 (p1SigmaSq ... eps eta)^2 <= C * (p1Q ... eps)^2,
  E_2 (p1SigmaSq ... eps eta) = p1Q ... eps.

This theorem must quantify over the actual deterministic coefficient array
produced by `eps`.  It is the formal reason the later success bound is
uniform for EVERY internal good realization.
-/

/-
TARGET D: finite-uniform Paley--Zygmund + good events.

Define an internal good event from Q and all R_j and prove positive uniform
probability.  Then prove the pointwise-in-realization statement

  forall eps,
    InternalGood eps ->
      finiteUniformProbability (SecondGood eps) >= p_ext.

No conditional-average substitute is acceptable.
-/

/-
TARGET E: primitive crossing arrays.

Construct the original typed crossing address space, with addresses carrying
(edge id, endpoint orientation, role label coordinate), and prove its map

  primitive crossing sample -> P1SecondSample

pushes uniform measure to the uniform product measure.  This discharges the
fact that the eta-vectors used above are the real products of crossing-edge
signs, rather than newly postulated independent signs.
-/

end GraphMatrixReplica
