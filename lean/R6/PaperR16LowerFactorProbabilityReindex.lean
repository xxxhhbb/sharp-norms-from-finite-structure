import R6.PaperR16LowerFactorNormInterface
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Pi

/-!
# F1a: probability reindex for the raw independent-factor model

This file is a Lean draft for the probability-only part of F1a.
It starts from the actual `RawFactorShape.RawSample` primitive coordinates,
keeps the original occurrence label in every coordinate, partitions those
coordinates into the canonical core block and the unique detached-component
blocks, and proves that the primitive product law is carried to the grouped
product law.

No symmetry, centering, variance, identical-law, or tail assumption occurs.
The only probability assumption is that each occurrence law `ν e` is a
probability measure on `ℝ`.

Execution status in the return package: NOT RUN LOCALLY.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace GraphMatrixReplica.PaperR16.RawFactorShape

universe u v
variable {W : Type u} {E : Type v} [Fintype W] [Fintype E] [DecidableEq W]
variable (S : RawFactorShape W E)

/-- The cell-index type of the original occurrence array `ξ.array e`. -/
abbrev RawCell (e : E) :=
  ∀ w : {w : W // w ∈ S.scope e}, Fin (S.size w.1)

/-- A primitive random coordinate is an occurrence label together with one
cell of that occurrence array.  Keeping `e : E` in the sigma type is what
prevents equal scopes from ever being identified. -/
abbrev RawPrimitiveCoord := Σ e : E, S.RawCell e

/-- Flatten the actual source record `RawSample` into its primitive real
coordinates. -/
def flattenRawSample (ξ : S.RawSample) : S.RawPrimitiveCoord → ℝ
  | ⟨e, a⟩ => ξ.array e a

/-- Inverse of `flattenRawSample`. -/
def unflattenRawSample (x : S.RawPrimitiveCoord → ℝ) : S.RawSample where
  array := fun e a => x ⟨e, a⟩

@[simp] theorem flatten_unflattenRawSample
    (x : S.RawPrimitiveCoord → ℝ) :
    S.flattenRawSample (S.unflattenRawSample x) = x := by
  funext p
  rcases p with ⟨e, a⟩
  rfl

@[simp] theorem unflatten_flattenRawSample (ξ : S.RawSample) :
    S.unflattenRawSample (S.flattenRawSample ξ) = ξ := by
  rcases ξ with ⟨array⟩
  rfl

/-- Exact equivalence between the source record and the primitive-coordinate
function space. -/
def rawSampleEquiv : S.RawSample ≃ (S.RawPrimitiveCoord → ℝ) where
  toFun := S.flattenRawSample
  invFun := S.unflattenRawSample
  left_inv := S.unflatten_flattenRawSample
  right_inv := S.flatten_unflattenRawSample

/-- Primitive coordinates whose occurrence is a canonical core occurrence. -/
abbrev CorePrimitiveCoord :=
  {p : S.RawPrimitiveCoord // S.CoreOccurrence p.1}

/-- Primitive coordinates whose occurrence belongs to detached component
`j`. -/
abbrev DetachedPrimitiveCoord (j : S.DetachedComponent) :=
  {p : S.RawPrimitiveCoord // S.DetachedOccurrence j p.1}

/-- One block for the core and one block for every detached component. -/
abbrev ProbabilityBlock := Unit ⊕ S.DetachedComponent

/-- Primitive coordinate type in a selected block. -/
def BlockCoord : S.ProbabilityBlock → Type (max u v)
  | Sum.inl _ => S.CorePrimitiveCoord
  | Sum.inr j => S.DetachedPrimitiveCoord j

noncomputable instance rawPrimitiveCoordFintype :
    Fintype S.RawPrimitiveCoord := by
  classical
  exact Fintype.ofFinite _

noncomputable instance corePrimitiveCoordFintype :
    Fintype S.CorePrimitiveCoord := by
  classical
  exact Fintype.ofFinite _

noncomputable instance detachedPrimitiveCoordFintype
    (j : S.DetachedComponent) : Fintype (S.DetachedPrimitiveCoord j) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance blockCoordFintype (b : S.ProbabilityBlock) :
    Fintype (S.BlockCoord b) := by
  classical
  cases b with
  | inl u => change Fintype S.CorePrimitiveCoord; infer_instance
  | inr j => change Fintype (S.DetachedPrimitiveCoord j); infer_instance

/-- The unique detached component selected by a non-core occurrence. -/
def detachedComponentOfOccurrence (e : E)
    (h : ¬ S.CoreOccurrence e) : S.DetachedComponent :=
  Classical.choose ((S.not_coreOccurrence_iff_detached e).mp h)

@[simp] theorem detachedOccurrence_detachedComponentOfOccurrence
    (e : E) (h : ¬ S.CoreOccurrence e) :
    S.DetachedOccurrence (S.detachedComponentOfOccurrence e h) e :=
  Classical.choose_spec ((S.not_coreOccurrence_iff_detached e).mp h)

/-- Forget the group tag. -/
def blockCoordToRaw :
    (Σ b : S.ProbabilityBlock, S.BlockCoord b) → S.RawPrimitiveCoord
  | ⟨Sum.inl _, p⟩ => p.1
  | ⟨Sum.inr _, p⟩ => p.1

/-- Assign a raw primitive coordinate to the core block or to its unique
canonical detached component. -/
def rawPrimitiveToBlock (p : S.RawPrimitiveCoord) :
    Σ b : S.ProbabilityBlock, S.BlockCoord b := by
  classical
  by_cases hc : S.CoreOccurrence p.1
  · exact ⟨Sum.inl (), ⟨p, hc⟩⟩
  · let j := S.detachedComponentOfOccurrence p.1 hc
    have hj : S.DetachedOccurrence j p.1 := by
      dsimp [j]
      exact S.detachedOccurrence_detachedComponentOfOccurrence p.1 hc
    exact ⟨Sum.inr j, ⟨p, hj⟩⟩

@[simp] theorem blockCoordToRaw_rawPrimitiveToBlock
    (p : S.RawPrimitiveCoord) :
    S.blockCoordToRaw (S.rawPrimitiveToBlock p) = p := by
  classical
  by_cases hc : S.CoreOccurrence p.1 <;> simp [rawPrimitiveToBlock, hc, blockCoordToRaw]

@[simp] theorem rawPrimitiveToBlock_blockCoordToRaw
    (p : Σ b : S.ProbabilityBlock, S.BlockCoord b) :
    S.rawPrimitiveToBlock (S.blockCoordToRaw p) = p := by
  classical
  rcases p with ⟨b, p⟩
  cases b with
  | inl u =>
      cases u
      have hc : S.CoreOccurrence p.1.1 := p.2
      change (if hc : S.CoreOccurrence p.1.1 then _ else _) = _
      rw [dif_pos hc]
      apply Sigma.ext rfl
      exact heq_of_eq (Subtype.ext rfl)
  | inr j =>
      have hd : S.DetachedOccurrence j p.1.1 := p.2
      have hn : ¬ S.CoreOccurrence p.1.1 := by
        intro hc
        exact S.core_occurrence_not_detached p.1.1 hc j hd
      have hj : S.detachedComponentOfOccurrence p.1.1 hn = j := by
        exact S.detached_occurrence_component_unique
          (S.detachedOccurrence_detachedComponentOfOccurrence p.1.1 hn) hd
      change (if hc : S.CoreOccurrence p.1.1 then _ else _) = _
      rw [dif_neg hn]
      apply Sigma.ext (congrArg Sum.inr hj)
      apply (Subtype.heq_iff_coe_eq (by intro a; dsimp only [blockCoordToRaw]; rw [hj])).mpr
      rfl

/-- Exact partition of every primitive coordinate into the core block or one
unique detached-component block. -/
def blockPrimitiveEquiv :
    (Σ b : S.ProbabilityBlock, S.BlockCoord b) ≃ S.RawPrimitiveCoord where
  toFun := S.blockCoordToRaw
  invFun := S.rawPrimitiveToBlock
  left_inv := S.rawPrimitiveToBlock_blockCoordToRaw
  right_inv := S.blockCoordToRaw_rawPrimitiveToBlock

/-- Reindex flat primitive samples by the block partition and then curry the
sigma index.  This is the measurable raw-to-(core × detached blocks) map at
primitive-coordinate level. -/
def rawFlatToBlocksMeasurableEquiv :
    (S.RawPrimitiveCoord → ℝ) ≃ᵐ
      (∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : (Σ b : S.ProbabilityBlock, S.BlockCoord b) => ℝ)
      S.blockPrimitiveEquiv.symm).trans
    (MeasurableEquiv.piCurry
      (fun b : S.ProbabilityBlock => fun _ : S.BlockCoord b => ℝ))

@[simp] theorem rawFlatToBlocksMeasurableEquiv_apply
    (x : S.RawPrimitiveCoord → ℝ) (b : S.ProbabilityBlock)
    (p : S.BlockCoord b) :
    S.rawFlatToBlocksMeasurableEquiv x b p =
      x (S.blockCoordToRaw ⟨b, p⟩) := by
  change (MeasurableEquiv.piCongrLeft (fun _ => ℝ) S.blockPrimitiveEquiv.symm x) ⟨b, p⟩ = x (S.blockPrimitiveEquiv ⟨b, p⟩)
  simpa only [Equiv.symm_apply_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ)
      S.blockPrimitiveEquiv.symm x (S.blockPrimitiveEquiv ⟨b, p⟩))

/-- Original primitive product law.  `ν e` is reused for every cell in the
array of occurrence `e`. -/
def rawPrimitiveLaw (ν : E → Measure ℝ) :
    Measure (S.RawPrimitiveCoord → ℝ) :=
  Measure.infinitePi (fun p : S.RawPrimitiveCoord => ν p.1)

/-- Per-coordinate law inside one canonical block. -/
def blockCoordinateLaw (ν : E → Measure ℝ)
    (b : S.ProbabilityBlock) (p : S.BlockCoord b) : Measure ℝ :=
  ν (S.blockCoordToRaw ⟨b, p⟩).1

/-- Product law of all primitive coordinates in one block. -/
def oneBlockLaw (ν : E → Measure ℝ) (b : S.ProbabilityBlock) :
    Measure (S.BlockCoord b → ℝ) :=
  Measure.infinitePi (S.blockCoordinateLaw ν b)

instance blockCoordinateLaw_probability (ν : E → Measure ℝ)
    [∀ e : E, IsProbabilityMeasure (ν e)] (b : S.ProbabilityBlock) (p : S.BlockCoord b) :
    IsProbabilityMeasure (S.blockCoordinateLaw ν b p) := by
  unfold blockCoordinateLaw
  infer_instance

instance oneBlockLaw_probability (ν : E → Measure ℝ)
    [∀ e : E, IsProbabilityMeasure (ν e)] (b : S.ProbabilityBlock) :
    IsProbabilityMeasure (S.oneBlockLaw ν b) := by
  unfold oneBlockLaw
  infer_instance

/-- Product of the core-block law and all detached-component block laws. -/
def groupedPrimitiveLaw (ν : E → Measure ℝ) :
    Measure (∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) :=
  Measure.infinitePi (S.oneBlockLaw ν)

/-- The measurable reindex sends the original primitive product law to the
actual grouped product law.  This is a pushforward theorem, not a fresh
independence assumption on the grouped variables. -/
theorem map_rawPrimitiveLaw_eq_groupedPrimitiveLaw
    (ν : E → Measure ℝ) [∀ e : E, IsProbabilityMeasure (ν e)] :
    Measure.map (S.rawFlatToBlocksMeasurableEquiv)
        (S.rawPrimitiveLaw ν) =
      S.groupedPrimitiveLaw ν := by
  classical
  let e₁ : (S.RawPrimitiveCoord → ℝ) ≃ᵐ
      ((p : Σ b : S.ProbabilityBlock, S.BlockCoord b) → ℝ) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : (Σ b : S.ProbabilityBlock, S.BlockCoord b) => ℝ)
      S.blockPrimitiveEquiv.symm
  let e₂ : ((p : Σ b : S.ProbabilityBlock, S.BlockCoord b) → ℝ) ≃ᵐ
      (∀ b : S.ProbabilityBlock, S.BlockCoord b → ℝ) :=
    MeasurableEquiv.piCurry
      (fun b : S.ProbabilityBlock => fun _ : S.BlockCoord b => ℝ)

  have h₁ :
      Measure.map e₁ (S.rawPrimitiveLaw ν) =
        Measure.infinitePi
          (fun p : Σ b : S.ProbabilityBlock, S.BlockCoord b =>
            ν (S.blockCoordToRaw p).1) := by
    simpa [rawPrimitiveLaw, e₁, blockPrimitiveEquiv] using
      (Measure.infinitePi_map_piCongrLeft
        (fun p : Σ b : S.ProbabilityBlock, S.BlockCoord b =>
          ν (S.blockCoordToRaw p).1)
        S.blockPrimitiveEquiv.symm)

  have h₂ :
      Measure.map e₂
          (Measure.infinitePi
            (fun p : Σ b : S.ProbabilityBlock, S.BlockCoord b =>
              ν (S.blockCoordToRaw p).1)) =
        S.groupedPrimitiveLaw ν := by
    change Measure.map e₂ _ = Measure.infinitePi (fun b =>
      Measure.infinitePi (fun p : S.BlockCoord b => ν (S.blockCoordToRaw ⟨b, p⟩).1))
    simpa [e₂] using
      (Measure.infinitePi_map_piCurry
        (fun b : S.ProbabilityBlock =>
          fun p : S.BlockCoord b => ν (S.blockCoordToRaw ⟨b, p⟩).1))

  change Measure.map (e₂ ∘ e₁) (S.rawPrimitiveLaw ν) =
    S.groupedPrimitiveLaw ν
  rw [← Measure.map_map e₂.measurable e₁.measurable, h₁, h₂]

/-- Since the block index is finite, the grouped law is Mathlib's finite
`Measure.pi` as well. -/
theorem groupedPrimitiveLaw_eq_pi
    (ν : E → Measure ℝ) [∀ e : E, IsProbabilityMeasure (ν e)] :
    S.groupedPrimitiveLaw ν = Measure.pi (S.oneBlockLaw ν) := by
  classical
  exact Measure.infinitePi_eq_pi (S.oneBlockLaw ν)

/-- Same finite-product conversion inside one block. -/
theorem oneBlockLaw_eq_pi
    (ν : E → Measure ℝ) [∀ e : E, IsProbabilityMeasure (ν e)]
    (b : S.ProbabilityBlock) :
    S.oneBlockLaw ν b = Measure.pi (S.blockCoordinateLaw ν b) := by
  classical
  exact Measure.infinitePi_eq_pi (S.blockCoordinateLaw ν b)

/-- Package a core test and detached-component tests into a family indexed by
`ProbabilityBlock`. -/
def blockTest
    (fc : (S.CorePrimitiveCoord → ℝ) → ℝ)
    (fj : ∀ j : S.DetachedComponent,
      (S.DetachedPrimitiveCoord j → ℝ) → ℝ) :
    ∀ b : S.ProbabilityBlock, (S.BlockCoord b → ℝ) → ℝ
  | Sum.inl _ => fc
  | Sum.inr j => fj j

/-- Exact finite-product integral identity on the grouped law.  Mathlib's
`integral_fintype_prod_eq_prod` is unconditional; in the intended F1a use the
functions are bounded Borel, hence integrable automatically under the
probability laws. -/
theorem integral_blockTest_eq_prod
    (ν : E → Measure ℝ) [∀ e : E, IsProbabilityMeasure (ν e)]
    (fc : (S.CorePrimitiveCoord → ℝ) → ℝ)
    (fj : ∀ j : S.DetachedComponent,
      (S.DetachedPrimitiveCoord j → ℝ) → ℝ) :
    (∫ x,
        ∏ b : S.ProbabilityBlock, S.blockTest fc fj b (x b)
      ∂S.groupedPrimitiveLaw ν) =
      ∏ b : S.ProbabilityBlock,
        ∫ y, S.blockTest fc fj b y ∂S.oneBlockLaw ν b := by
  classical
  rw [S.groupedPrimitiveLaw_eq_pi ν]
  exact MeasureTheory.integral_fintype_prod_eq_prod (S.blockTest fc fj)

/-- The same identity in the core-times-product-of-detached form used in the
paper.  In particular it applies to any bounded Borel tests. -/
theorem integral_core_mul_detached_eq
    (ν : E → Measure ℝ) [∀ e : E, IsProbabilityMeasure (ν e)]
    (fc : (S.CorePrimitiveCoord → ℝ) → ℝ)
    (fj : ∀ j : S.DetachedComponent,
      (S.DetachedPrimitiveCoord j → ℝ) → ℝ) :
    (∫ x,
        fc (x (Sum.inl ())) *
          ∏ j : S.DetachedComponent, fj j (x (Sum.inr j))
      ∂S.groupedPrimitiveLaw ν) =
      (∫ y, fc y ∂S.oneBlockLaw ν (Sum.inl ())) *
        ∏ j : S.DetachedComponent,
          ∫ y, fj j y ∂S.oneBlockLaw ν (Sum.inr j) := by
  classical
  have h := S.integral_blockTest_eq_prod ν fc fj
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, blockTest] at h
  exact h

/-- Restriction of an actual raw sample to the primitive core block. -/
def rawCoreBlock (ξ : S.RawSample) : S.CorePrimitiveCoord → ℝ :=
  fun p => ξ.array p.1.1 p.1.2

/-- Restriction of an actual raw sample to one primitive detached block. -/
def rawDetachedBlock (ξ : S.RawSample) (j : S.DetachedComponent) :
    S.DetachedPrimitiveCoord j → ℝ :=
  fun p => ξ.array p.1.1 p.1.2

/-- A canonical core array coordinate depends only on raw primitive core
coordinates.  This is stronger than a statement about equal scopes: the
original occurrence label `e.1` appears explicitly in the queried primitive
coordinate. -/
theorem canonicalSample_core_congr
    {ξ ξ' : S.RawSample}
    (h : S.rawCoreBlock ξ = S.rawCoreBlock ξ') :
    (S.canonicalSample ξ).core = (S.canonicalSample ξ').core := by
  classical
  funext e coords
  let hp : S.CorePrimitiveCoord :=
    ⟨⟨e.1, fun w =>
      coords ⟨⟨w.1, e.2 w.1 w.2⟩, by
        simp [RawFactorShape.canonicalPreprocessedShape, w.2]⟩⟩, e.2⟩
  have hh := congrFun h hp
  simpa [rawCoreBlock, canonicalSample, hp] using hh

/-- A canonical detached array coordinate in component `j` depends only on
raw primitive coordinates assigned to `j`. -/
theorem canonicalSample_detached_congr
    (j : S.DetachedComponent) {ξ ξ' : S.RawSample}
    (h : S.rawDetachedBlock ξ j = S.rawDetachedBlock ξ' j) :
    (S.canonicalSample ξ).detached j =
      (S.canonicalSample ξ').detached j := by
  classical
  funext e coords
  let hp : S.DetachedPrimitiveCoord j :=
    ⟨⟨e.1, fun w =>
      coords ⟨⟨w.1, e.2 w.1 w.2⟩, by
        simp [RawFactorShape.canonicalPreprocessedShape, w.2]⟩⟩, e.2⟩
  have hh := congrFun h hp
  simpa [rawDetachedBlock, canonicalSample, hp] using hh

/-- Repeated scopes are harmless at the type level: equality of scopes never
removes the occurrence label from a primitive coordinate. -/
theorem rawPrimitiveCoord_occurrence_visible (p : S.RawPrimitiveCoord) :
    p.1 = (S.blockCoordToRaw (S.rawPrimitiveToBlock p)).1 := by
  simp

#print axioms RawFactorShape.rawSampleEquiv
#print axioms RawFactorShape.blockPrimitiveEquiv
#print axioms RawFactorShape.map_rawPrimitiveLaw_eq_groupedPrimitiveLaw
#print axioms RawFactorShape.integral_core_mul_detached_eq
#print axioms RawFactorShape.canonicalSample_core_congr
#print axioms RawFactorShape.canonicalSample_detached_congr

end GraphMatrixReplica.PaperR16.RawFactorShape
