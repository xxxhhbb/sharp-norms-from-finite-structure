import GraphMatrix.Model.FiniteColorLpTransfer
import GraphMatrix.Model.ColorCompressionNorm

/-!
# Auxiliary edge-color signs for the lower transfer

This file proves the finite Fourier and probability steps.  A tag identifies
which target edge-color pair an ordered ambient noise coordinate belongs to.
For the paper application it is evaluated only at the canonical unordered
pair `(min i j, max i j)`.  The identification of the surviving realizations
with boundary-fixing automorphisms is a separate combinatorial theorem.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Flip every ambient noise bit bearing an auxiliary edge-color tag. -/
def paperR16FlipTaggedNoise {n : ℕ}
    (tag : Fin n × Fin n → Option ι) (α : ι → Bool)
    (w : PaperNoise n) : PaperNoise n :=
  fun i j => match tag (i, j) with
    | none => w i j
    | some k => if α k then w i j else !(w i j)

/-- Each fixed auxiliary sign assignment acts by an involution on the whole
finite ambient noise space. -/
theorem paperR16FlipTaggedNoise_involutive {n : ℕ}
    (tag : Fin n × Fin n → Option ι) (α : ι → Bool) :
    Function.Involutive (paperR16FlipTaggedNoise tag α) := by
  intro w
  funext i j
  unfold paperR16FlipTaggedNoise
  cases h : tag (i, j) with
  | none => simp [h]
  | some k => cases hα : α k <;> cases hw : w i j <;> simp [h, hα, hw]

/-- The auxiliary flip is a genuine equivalence of ambient samples. -/
def paperR16FlipTaggedNoiseEquiv {n : ℕ}
    (tag : Fin n × Fin n → Option ι) (α : ι → Bool) :
    PaperNoise n ≃ PaperNoise n :=
  { toFun := paperR16FlipTaggedNoise tag α
    invFun := paperR16FlipTaggedNoise tag α
    left_inv := paperR16FlipTaggedNoise_involutive tag α
    right_inv := paperR16FlipTaggedNoise_involutive tag α }

/-- Fixed auxiliary flips preserve the uniform law of all ambient signs. -/
theorem paperMean_flipTaggedNoise {n : ℕ}
    (tag : Fin n × Fin n → Option ι) (α : ι → Bool)
    (f : PaperNoise n → ℝ) :
    paperMean (fun w => f (paperR16FlipTaggedNoise tag α w)) =
      paperMean f :=
  paperMean_equiv (paperR16FlipTaggedNoiseEquiv tag α) f

/-- The sign on a flipped canonical ambient coordinate acquires the
auxiliary character attached to its tag. -/
theorem paperEdgeSign_flipTaggedNoise {n : ℕ}
    (tag : Fin n × Fin n → Option ι) (α : ι → Bool)
    (w : PaperNoise n) (i j : Fin n) :
    paperEdgeSign (paperR16FlipTaggedNoise tag α w) i j =
      paperEdgeSign w i j *
        (match tag (paperUnorderedPair i j) with
          | none => 1
          | some k => paperSign (α k)) := by
  unfold paperEdgeSign paperR16FlipTaggedNoise paperUnorderedPair
  cases h : tag (min i j, max i j) with
  | none => simp [h]
  | some k => cases hα : α k <;> cases hw : w (min i j) (max i j) <;>
      norm_num [h, hα, hw, paperSign]

/-- A full Walsh character is the product of all target auxiliary signs. -/
def paperR16FullWalshCharacter (α : ι → Bool) : ℝ :=
  ∏ k : ι, paperSign (α k)

/-- Orthogonality isolates precisely monomials in which every target tag
occurs oddly often.  This parity test is independent of any graph shape. -/
theorem paperR16FullWalsh_orthogonality (count : ι → ℕ) :
    paperMean (fun α : ι → Bool =>
      paperR16FullWalshCharacter α *
        ∏ k : ι, paperSign (α k) ^ count k) =
      if ∀ k : ι, Odd (count k) then 1 else 0 := by
  classical
  have hpoint : (fun α : ι → Bool =>
      paperR16FullWalshCharacter α *
        ∏ k : ι, paperSign (α k) ^ count k) =
      (fun α => ∏ k : ι, paperSign (α k) ^ (count k + 1)) := by
    funext α
    simp only [paperR16FullWalshCharacter, pow_add, pow_one]
    rw [Finset.prod_mul_distrib]
    exact mul_comm _ _
  rw [hpoint, paperMean_sign_monomial]
  congr 1
  apply propext
  constructor
  · intro h k
    exact Nat.not_even_iff_odd.mp ((Nat.even_add_one).mp (h k))
  · intro h k
    exact (Nat.even_add_one).mpr (Nat.not_even_iff_odd.mpr (h k))

/-- Number of occurrences of one target edge-color tag in an ambient edge
word.  Untagged ambient edges do not contribute. -/
def paperR16TaggedEdgeCount {n : ℕ}
    (tag : Fin n × Fin n → Option ι)
    (word : List (Fin n × Fin n)) (k : ι) : ℕ :=
  @List.count (Option ι) instBEqOfDecidableEq (some k)
    (word.map (fun e => tag (paperUnorderedPair e.1 e.2)))

/-- The auxiliary factor in a flipped edge word has exactly the powers
recorded by the target edge-color counts. -/
theorem paperR16TaggedWord_character {n : ℕ}
    (tag : Fin n × Fin n → Option ι)
    (word : List (Fin n × Fin n)) (α : ι → Bool) :
    (word.map (fun e =>
      match tag (paperUnorderedPair e.1 e.2) with
      | none => (1 : ℝ)
      | some k => paperSign (α k))).prod =
      ∏ k : ι, paperSign (α k) ^ paperR16TaggedEdgeCount tag word k := by
  classical
  letI : BEq (Option ι) := instBEqOfDecidableEq
  let tags : List (Option ι) :=
    word.map (fun e => tag (paperUnorderedPair e.1 e.2))
  let χ : Option ι → ℝ := fun z => z.elim 1 (fun k => paperSign (α k))
  have hfun : (fun e : Fin n × Fin n =>
      match tag (paperUnorderedPair e.1 e.2) with
      | none => (1 : ℝ)
      | some k => paperSign (α k)) =
      (fun e => χ (tag (paperUnorderedPair e.1 e.2))) := by
    funext e
    cases tag (paperUnorderedPair e.1 e.2) <;> rfl
  calc
    (word.map (fun e =>
      match tag (paperUnorderedPair e.1 e.2) with
      | none => (1 : ℝ)
      | some k => paperSign (α k))).prod = (tags.map χ).prod := by
        rw [hfun]
        simp [tags, List.map_map, Function.comp_def]
    _ = ∏ z : Option ι, χ z ^ tags.count z :=
      paperWordProduct_eq_powers tags χ
    _ = ∏ k : ι, paperSign (α k) ^ paperR16TaggedEdgeCount tag word k := by
      simp [χ, tags, paperR16TaggedEdgeCount]

/-- Flipping a complete ambient edge word multiplies its original monomial
by the product of precisely the auxiliary characters occurring in the word. -/
theorem paperR16TaggedWord_flip {n : ℕ}
    (tag : Fin n × Fin n → Option ι)
    (word : List (Fin n × Fin n)) (α : ι → Bool)
    (w : PaperNoise n) :
    (word.map (fun e => paperEdgeSign
      (paperR16FlipTaggedNoise tag α w) e.1 e.2)).prod =
      (word.map (fun e => paperEdgeSign w e.1 e.2)).prod *
        ∏ k : ι, paperSign (α k) ^ paperR16TaggedEdgeCount tag word k := by
  have hfun : (fun e : Fin n × Fin n => paperEdgeSign
      (paperR16FlipTaggedNoise tag α w) e.1 e.2) =
      (fun e => paperEdgeSign w e.1 e.2 *
        (match tag (paperUnorderedPair e.1 e.2) with
          | none => 1
          | some k => paperSign (α k))) := by
    funext e
    exact paperEdgeSign_flipTaggedNoise tag α w e.1 e.2
  calc
    (word.map (fun e => paperEdgeSign
        (paperR16FlipTaggedNoise tag α w) e.1 e.2)).prod =
      (word.map (fun e => paperEdgeSign w e.1 e.2 *
        (match tag (paperUnorderedPair e.1 e.2) with
          | none => 1
          | some k => paperSign (α k)))).prod := by
        rw [hfun]
    _ = (word.map (fun e => paperEdgeSign w e.1 e.2)).prod *
        (word.map (fun e =>
          match tag (paperUnorderedPair e.1 e.2) with
          | none => (1 : ℝ)
          | some k => paperSign (α k))).prod := List.prod_map_mul
    _ = _ := by rw [paperR16TaggedWord_character]

/-- Full Walsh extraction of one global edge monomial.  A monomial survives
if and only if every target edge-color pair is used an odd number of times. -/
theorem paperR16TaggedWord_fullWalshProjection {n : ℕ}
    (tag : Fin n × Fin n → Option ι)
    (word : List (Fin n × Fin n)) (w : PaperNoise n) :
    paperMean (fun α : ι → Bool =>
      paperR16FullWalshCharacter α *
        (word.map (fun e => paperEdgeSign
          (paperR16FlipTaggedNoise tag α w) e.1 e.2)).prod) =
      if ∀ k : ι, Odd (paperR16TaggedEdgeCount tag word k) then
        (word.map (fun e => paperEdgeSign w e.1 e.2)).prod else 0 := by
  classical
  let base : ℝ :=
    (word.map (fun e => paperEdgeSign w e.1 e.2)).prod
  let count : ι → ℕ := paperR16TaggedEdgeCount tag word
  calc
    paperMean (fun α : ι → Bool =>
      paperR16FullWalshCharacter α *
        (word.map (fun e => paperEdgeSign
          (paperR16FlipTaggedNoise tag α w) e.1 e.2)).prod) =
      paperMean (fun α : ι → Bool =>
        base * (paperR16FullWalshCharacter α *
          ∏ k : ι, paperSign (α k) ^ count k)) := by
        congr 1
        funext α
        rw [paperR16TaggedWord_flip]
        simp only [base, count]
        ring
    _ = base * paperMean (fun α : ι → Bool =>
          paperR16FullWalshCharacter α *
            ∏ k : ι, paperSign (α k) ^ count k) :=
      paperMean_const_mul_color _ _
    _ = if ∀ k : ι, Odd (paperR16TaggedEdgeCount tag word k) then
        (word.map (fun e => paperEdgeSign w e.1 e.2)).prod else 0 := by
      rw [paperR16FullWalsh_orthogonality]
      simp only [base, count]
      split_ifs <;> simp

/-- Finite uniform `L^q` is invariant under a sample-space equivalence.
The proof uses counting measure, so it applies for every real exponent. -/
theorem paperFiniteUniformLq_equiv
    {Ω E : Type} [Fintype Ω] [NormedAddCommGroup E]
    (e : Ω ≃ Ω) (f : Ω → E) (q : ℝ) :
    paperFiniteUniformLq (fun ω => f (e ω)) q =
      paperFiniteUniformLq f q := by
  classical
  letI : MeasurableSpace Ω := ⊤
  let μ : MeasureTheory.Measure Ω :=
    (Fintype.card Ω : NNReal)⁻¹ • MeasureTheory.Measure.count
  have hcount : MeasureTheory.Measure.map e MeasureTheory.Measure.count =
      MeasureTheory.Measure.count := by
    ext s hs
    rw [MeasureTheory.Measure.map_apply (Measurable.of_discrete) hs]
    rw [MeasureTheory.Measure.count_apply (hs.preimage Measurable.of_discrete),
      MeasureTheory.Measure.count_apply hs]
    exact congrArg (fun z : ENat => (z : ENNReal))
      (Set.encard_preimage_of_bijective e.bijective s)
  have hμ : MeasureTheory.Measure.map e μ = μ := by
    simp [μ, hcount]
  have hpres : MeasureTheory.MeasurePreserving e μ μ :=
    ⟨Measurable.of_discrete, hμ⟩
  change MeasureTheory.lpNorm (f ∘ e) (ENNReal.ofReal q) μ =
    MeasureTheory.lpNorm f (ENNReal.ofReal q) μ
  have hf : MeasureTheory.AEStronglyMeasurable f μ :=
    MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable
  have hfe : MeasureTheory.AEStronglyMeasurable (f ∘ e) μ :=
    MeasureTheory.StronglyMeasurable.of_discrete.aestronglyMeasurable
  simpa [MeasureTheory.lpNorm, hf, hfe] using
    congrArg ENNReal.toReal
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := f) (p := ENNReal.ofReal q) hf hpres)

/-- Every full Walsh character is a scalar sign. -/
theorem paperR16FullWalshCharacter_norm_eq_one (α : ι → Bool) :
    ‖paperR16FullWalshCharacter α‖ = 1 := by
  unfold paperR16FullWalshCharacter
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro k _
  cases α k <;> norm_num [paperSign]

/-- Average the signed, law-preserving ambient matrices over all auxiliary
edge-color signs. -/
def paperR16FullWalshProject {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (tag : Fin n × Fin n → Option ι)
    (F : PaperNoise n → E) (w : PaperNoise n) : E :=
  (Fintype.card (ι → Bool) : ℝ)⁻¹ •
    ∑ α : ι → Bool,
      paperR16FullWalshCharacter α • F (paperR16FlipTaggedNoise tag α w)

/-- Full Walsh projection is an `L^q` contraction for every real `q ≥ 1`.
This uses only finite Minkowski and the exact involutive noise law; it does
not assume any graph-theoretic extraction identity. -/
theorem paperR16FullWalshProject_lq_le {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (tag : Fin n × Fin n → Option ι)
    (F : PaperNoise n → E) (q : ℝ) (hq : 1 ≤ q) :
    paperFiniteUniformLq (paperR16FullWalshProject tag F) q ≤
      paperFiniteUniformLq F q := by
  classical
  let c : ℝ := (Fintype.card (ι → Bool) : ℝ)⁻¹
  let colored : (ι → Bool) → PaperNoise n → E :=
    fun α w => paperR16FullWalshCharacter α •
      F (paperR16FlipTaggedNoise tag α w)
  have hc : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hidentity : ∀ w : PaperNoise n,
      paperR16FullWalshProject tag F w =
        c • ∑ α : ι → Bool, colored α w := by
    intro w
    rfl
  have hcolored : ∀ α : ι → Bool,
      paperFiniteUniformLq (colored α) q = paperFiniteUniformLq F q := by
    intro α
    have hnorm : (‖paperR16FullWalshCharacter α‖₊ : ℝ) = 1 := by
      simp [nnnorm, paperR16FullWalshCharacter_norm_eq_one α]
    have heq : colored α = paperR16FullWalshCharacter α •
        (F ∘ paperR16FlipTaggedNoise tag α) := by
      funext w
      rfl
    rw [heq]
    unfold paperFiniteUniformLq
    rw [MeasureTheory.lpNorm_const_smul, hnorm]
    simp only [one_mul]
    exact paperFiniteUniformLq_equiv
      (paperR16FlipTaggedNoiseEquiv tag α) F q
  have hmain := paperFiniteUniformLq_le_of_finiteColorSum
    (paperR16FullWalshProject tag F) colored c hc hidentity q hq
  simp_rw [hcolored] at hmain
  have hcard : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ι → Bool)).ne'
  simpa [c, nsmul_eq_mul, hcard] using hmain


end GraphMatrixReplica
