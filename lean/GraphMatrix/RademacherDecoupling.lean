import GraphMatrix.PartialNCKStageMatrices
import GraphMatrix.TraceNormBridge
import GraphMatrix.GlobalEdgeParity

/-! # Finite square-free Rademacher decoupling infrastructure

This file separates the algebraic coloring/polarization step from the one
genuinely analytic coefficient-contraction step.  A chaos term has `q`
ordered coordinates; the coupled chaos reads all coordinates from one sign
array, while the fully decoupled chaos reads coordinate `k` from copy `k`.

For every deterministic coloring of the coordinate set, the coupled chaos is
the exact sum of its `q^q` color-pattern pieces.  The norm triangle inequality
and its finite-mean version are proved below.  Degree one is fully decoupled
without loss.  No general coupled/decoupled comparison is asserted merely
from the color decomposition: bounding every color projection by the fully
decoupled mean is the remaining contraction argument.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace GraphMatrixReplica

section GenericChaos

variable {ι τ E : Type} [Fintype ι] [DecidableEq ι] [Fintype τ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered coordinate data for a finite homogeneous chaos.  Square-freeness
is the injectivity of every active term's coordinate map. -/
structure PaperSquareFreeChaosData (q : ℕ) where
  coordinate : τ → Fin q → ι
  coefficient : τ → E
  squareFree : ∀ t, coefficient t ≠ 0 → Function.Injective (coordinate t)

/-- Scalar sign monomial of one coupled term. -/
def paperCoupledSignMonomial {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (epsilon : ι → Bool) (t : τ) : ℝ :=
  ∏ k : Fin q, paperSign (epsilon (D.coordinate t k))

/-- A finite homogeneous square-free Banach-valued Rademacher chaos. -/
def paperCoupledRademacherChaos {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (epsilon : ι → Bool) : E :=
  ∑ t : τ, paperCoupledSignMonomial D epsilon t • D.coefficient t

/-- The corresponding fully decoupled chaos, with an independent sign array
for every ordered coordinate position. -/
def paperFullyDecoupledRademacherChaos {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (epsilon : Fin q → ι → Bool) : E :=
  ∑ t : τ, (∏ k : Fin q,
    paperSign (epsilon k (D.coordinate t k))) • D.coefficient t

/-- A coloring records the exact color word read by a chaos term. -/
def paperTermColorPattern {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (t : τ) : Fin q → Fin q :=
  fun k => color (D.coordinate t k)

/-- One exact color-pattern projection of the coupled chaos. -/
def paperCoupledColorPatternPiece {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (pattern : Fin q → Fin q)
    (epsilon : ι → Bool) : E :=
  ∑ t : τ,
    if pattern = paperTermColorPattern D color t then
      paperCoupledSignMonomial D epsilon t • D.coefficient t
    else 0

/-- Exact finite coloring decomposition.  It is purely algebraic and does not
use square-freeness. -/
theorem paperCoupledChaos_eq_sum_colorPatternPieces {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (epsilon : ι → Bool) :
    paperCoupledRademacherChaos D epsilon =
      ∑ pattern : Fin q → Fin q,
        paperCoupledColorPatternPiece D color pattern epsilon := by
  classical
  unfold paperCoupledRademacherChaos paperCoupledColorPatternPiece
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _ht
  simp

/-- Triangle inequality after the exact coloring decomposition. -/
theorem norm_paperCoupledChaos_le_sum_colorPatternPieces {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) (epsilon : ι → Bool) :
    ‖paperCoupledRademacherChaos D epsilon‖ ≤
      ∑ pattern : Fin q → Fin q,
        ‖paperCoupledColorPatternPiece D color pattern epsilon‖ := by
  rw [paperCoupledChaos_eq_sum_colorPatternPieces D color epsilon]
  exact norm_sum_le _ _

/-- Finite-mean triangle inequality for a fixed coloring. -/
theorem paperMean_norm_coupled_le_sum_colorPatternMeans {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
      ∑ pattern : Fin q → Fin q,
        paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledColorPatternPiece D color pattern epsilon‖) := by
  calc
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
        paperMean (fun epsilon : ι → Bool =>
          ∑ pattern : Fin q → Fin q,
            ‖paperCoupledColorPatternPiece D color pattern epsilon‖) := by
      apply paperMean_mono
      exact norm_paperCoupledChaos_le_sum_colorPatternPieces D color
    _ = _ := paperMean_sum _

/-- Diagonal specialization of the fully decoupled chaos is exactly the
coupled chaos, in every degree. -/
@[simp] theorem paperFullyDecoupledChaos_diagonal {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (epsilon : ι → Bool) :
    paperFullyDecoupledRademacherChaos D (fun _ => epsilon) =
      paperCoupledRademacherChaos D epsilon := by
  rfl

/-- The unique sign copy in degree one. -/
def paperDegreeOneNoiseEquiv (ι : Type) :
    (Fin 1 → ι → Bool) ≃ (ι → Bool) where
  toFun epsilon := epsilon 0
  invFun epsilon := fun _ => epsilon
  left_inv epsilon := by
    funext k i
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    rfl
  right_inv _ := rfl

@[simp] theorem paperFullyDecoupledChaos_degreeOne_apply
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 1)
    (epsilon : Fin 1 → ι → Bool) :
    paperFullyDecoupledRademacherChaos D epsilon =
      paperCoupledRademacherChaos D (paperDegreeOneNoiseEquiv ι epsilon) := by
  classical
  unfold paperFullyDecoupledRademacherChaos paperCoupledRademacherChaos
    paperCoupledSignMonomial paperDegreeOneNoiseEquiv
  apply Finset.sum_congr rfl
  intro t _ht
  congr 1

/-- Degree-one coupled and decoupled expected norms are exactly equal. -/
theorem paperMean_norm_coupled_eq_fullyDecoupled_degreeOne
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 1) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) =
      paperMean (fun epsilon : Fin 1 → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D epsilon‖) := by
  symm
  calc
    paperMean (fun epsilon : Fin 1 → ι → Bool =>
        ‖paperFullyDecoupledRademacherChaos D epsilon‖) =
        paperMean (fun epsilon : Fin 1 → ι → Bool =>
          ‖paperCoupledRademacherChaos D
            (paperDegreeOneNoiseEquiv ι epsilon)‖) := by
      congr 1
    _ = paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledRademacherChaos D epsilon‖) :=
      paperMean_equiv (α := Fin 1 → ι → Bool) (β := ι → Bool)
        (paperDegreeOneNoiseEquiv ι)
        (fun epsilon : ι → Bool => ‖paperCoupledRademacherChaos D epsilon‖)

/-- Exact reduction of the general comparison to the color-projection
contraction estimate.  This theorem deliberately exposes that analytic input;
it is not advertised as an unconditional decoupling theorem. -/
theorem paperMean_norm_coupled_le_patternCard_mul_decoupled_of_projection
    {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q)
    (hProjection : ∀ pattern : Fin q → Fin q,
      paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledColorPatternPiece D color pattern epsilon‖) ≤
        paperMean (fun epsilon : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D epsilon‖)) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
      (Fintype.card (Fin q → Fin q) : ℝ) *
        paperMean (fun epsilon : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D epsilon‖) := by
  calc
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
        ∑ pattern : Fin q → Fin q,
          paperMean (fun epsilon : ι → Bool =>
            ‖paperCoupledColorPatternPiece D color pattern epsilon‖) :=
      paperMean_norm_coupled_le_sum_colorPatternMeans D color
    _ ≤ ∑ _pattern : Fin q → Fin q,
          paperMean (fun epsilon : Fin q → ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos D epsilon‖) := by
      exact Finset.sum_le_sum fun pattern _ => hProjection pattern
    _ = (Fintype.card (Fin q → Fin q) : ℝ) *
          paperMean (fun epsilon : Fin q → ι → Bool =>
            ‖paperFullyDecoupledRademacherChaos D epsilon‖) := by
      simp

@[simp] theorem paperColorPattern_card (q : ℕ) :
    Fintype.card (Fin q → Fin q) = q ^ q := by
  simp

/-- The preceding honest reduction has the explicit coloring constant `q^q`.
The displayed projection premise is still the sole missing contraction step. -/
theorem paperMean_norm_coupled_le_q_pow_q_mul_decoupled_of_projection
    {q : ℕ}
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) q)
    (color : ι → Fin q)
    (hProjection : ∀ pattern : Fin q → Fin q,
      paperMean (fun epsilon : ι → Bool =>
          ‖paperCoupledColorPatternPiece D color pattern epsilon‖) ≤
        paperMean (fun epsilon : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D epsilon‖)) :
    paperMean (fun epsilon : ι → Bool =>
        ‖paperCoupledRademacherChaos D epsilon‖) ≤
      (q : ℝ) ^ q *
        paperMean (fun epsilon : Fin q → ι → Bool =>
          ‖paperFullyDecoupledRademacherChaos D epsilon‖) := by
  simpa using
    (paperMean_norm_coupled_le_patternCard_mul_decoupled_of_projection
      D color hProjection)

/-- Degree-two exact four-pattern polarization, retained as a named endpoint
for the first genuinely nonlinear case. -/
theorem paperCoupledChaos_degreeTwo_eq_fourPatternSum
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 2)
    (color : ι → Fin 2) (epsilon : ι → Bool) :
    paperCoupledRademacherChaos D epsilon =
      ∑ pattern : Fin 2 → Fin 2,
        paperCoupledColorPatternPiece D color pattern epsilon :=
  paperCoupledChaos_eq_sum_colorPatternPieces D color epsilon

/-- Degree-two norm consequence of the exact four-pattern identity. -/
theorem norm_paperCoupledChaos_degreeTwo_le_fourPatternSum
    (D : PaperSquareFreeChaosData (ι := ι) (τ := τ) (E := E) 2)
    (color : ι → Fin 2) (epsilon : ι → Bool) :
    ‖paperCoupledRademacherChaos D epsilon‖ ≤
      ∑ pattern : Fin 2 → Fin 2,
        ‖paperCoupledColorPatternPiece D color pattern epsilon‖ :=
  norm_paperCoupledChaos_le_sum_colorPatternPieces D color epsilon

end GenericChaos

/-! ## The paper oriented matrix as a square-free chaos -/

/-- Turn one sign array on unordered ambient pairs into the paper's curried
shared-noise table. -/
def paperSym2NoiseToPaper {n : ℕ} (epsilon : Sym2 (Fin n) → Bool) :
    PaperNoise n :=
  fun i j => epsilon s(i, j)

@[simp] theorem paperEdgeSign_sym2Noise {n : ℕ}
    (epsilon : Sym2 (Fin n) → Bool) (i j : Fin n) :
    paperEdgeSign (paperSym2NoiseToPaper epsilon) i j =
      paperSign (epsilon s(i, j)) := by
  by_cases h : i ≤ j
  · simp [paperEdgeSign, paperSym2NoiseToPaper, paperSign,
      min_eq_left h, max_eq_right h]
  · have h' : j ≤ i := le_of_not_ge h
    simp [paperEdgeSign, paperSym2NoiseToPaper, paperSign,
      min_eq_right h', max_eq_left h', Sym2.eq_swap]

/-- Deterministic matrix coefficient of one oriented realization. -/
def paperOrientedChaosCoefficient
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (phi : PaperRealization G n) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ := by
  classical
  exact fun row col =>
    if paperEntryCompatible G phi row col ∧
        paperOrientationCompatible G orientation phi then 1 else 0

/-- Concrete homogeneous square-free chaos data for a fixed paper
orientation.  Square-freeness follows from the shape's simple-edge hypothesis and
the global injectivity of each realization. -/
def paperOrientedSquareFreeChaosData
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool) :
    PaperSquareFreeChaosData
      (ι := Sym2 (Fin n)) (τ := PaperRealization G n)
      (E := Matrix (PaperRow G n) (PaperCol G n) ℝ) G.edges where
  coordinate phi e := s(phi (G.source e), phi (G.target e))
  coefficient := paperOrientedChaosCoefficient G n orientation
  squareFree := by
    intro phi _hCoefficient e f hef
    have hMapped :
        Sym2.map phi s(G.source e, G.target e) =
          Sym2.map phi s(G.source f, G.target f) := by
      simpa using hef
    have hShape : s(G.source e, G.target e) =
        s(G.source f, G.target f) :=
      (Sym2.map.injective phi.injective) hMapped
    apply G.edge_injective
    have hCanonical := congrArg paperCanonicalAmbientEdge hShape
    simpa [paperCanonicalAmbientEdge_mk,
      min_eq_left (le_of_lt (G.edge_order e)),
      max_eq_right (le_of_lt (G.edge_order e)),
      min_eq_left (le_of_lt (G.edge_order f)),
      max_eq_right (le_of_lt (G.edge_order f))] using hCanonical

/-- The generic coupled chaos is exactly the existing oriented paper matrix
under the unordered-pair noise representation. -/
theorem paperCoupledOrientedChaos_eq_paperOrientedGraphMatrix
    (G : PaperShape) (n : ℕ) (orientation : Fin G.edges → Bool)
    (epsilon : Sym2 (Fin n) → Bool) :
    paperCoupledRademacherChaos
        (paperOrientedSquareFreeChaosData G n orientation) epsilon =
      paperOrientedGraphMatrix G n orientation
        (paperSym2NoiseToPaper epsilon) := by
  classical
  ext row col
  unfold paperCoupledRademacherChaos paperCoupledSignMonomial
    paperOrientedSquareFreeChaosData paperOrientedChaosCoefficient
    paperOrientedGraphMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro phi _hphi
  change (∏ e : Fin G.edges,
      paperSign (epsilon s(phi (G.source e), phi (G.target e)))) *
        (if paperEntryCompatible G phi row col ∧
            paperOrientationCompatible G orientation phi then 1 else 0) =
      if paperEntryCompatible G phi row col ∧
          paperOrientationCompatible G orientation phi then
        ∏ e : Fin G.edges, paperEdgeSign
          (paperSym2NoiseToPaper epsilon)
          (phi (G.source e)) (phi (G.target e))
      else 0
  by_cases hCompatible : paperEntryCompatible G phi row col ∧
      paperOrientationCompatible G orientation phi
  · rw [if_pos hCompatible, if_pos hCompatible, mul_one]
    apply Finset.prod_congr rfl
    intro e _he
    rw [paperEdgeSign_sym2Noise]
  · rw [if_neg hCompatible, if_neg hCompatible, mul_zero]


end GraphMatrixReplica
