import GraphMatrix.Counting.DefectStratification
import GraphMatrix.Counting.ForwardNormalization

/-! # C079 multilevel encoder assembly

This module gives a genuinely lossless, multilevel finite-code interface for
the remaining C079 counting argument.  An assembly certificate must contain
an injective map from an exact state fiber into dependent path-state,
forward-coarsening, free-seed, and reconstruction data.  The theorems then
multiply uniform bounds on the successive fibers.

No normalization map or decoder is constructed here.  In particular, the
existence of an `C079EncoderAssemblyCertificate` is a visible mathematical
obligation; it cannot be inferred merely from the arithmetic bounds.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

universe uState uPath uForward uSeed uReconstruction

/-- Dependent four-level target of the C079 encoder.  Reconstruction data may
depend on the selected path state, forward coarsening, and free seed. -/
abbrev C079EncoderTarget
    (PathState : Type uPath)
    (Forward : PathState → Type uForward)
    (FreeSeed : (path : PathState) → Forward path → Type uSeed)
    (Reconstruction : (path : PathState) →
      (forward : Forward path) → FreeSeed path forward →
        Type uReconstruction) :=
  Σ path : PathState,
    Σ forward : Forward path,
      Σ seed : FreeSeed path forward,
        Reconstruction path forward seed

/-- A lossless encoder assembly.  A future concrete C079 proof must build
`encode` from the actual state and prove the displayed injectivity, normally
by retaining the original backbone and decoding only forward records. -/
structure C079EncoderAssemblyCertificate
    (State : Type uState)
    (PathState : Type uPath)
    (Forward : PathState → Type uForward)
    (FreeSeed : (path : PathState) → Forward path → Type uSeed)
    (Reconstruction : (path : PathState) →
      (forward : Forward path) → FreeSeed path forward →
        Type uReconstruction) where
  encode : State →
    C079EncoderTarget PathState Forward FreeSeed Reconstruction
  injective : Function.Injective encode

/-- Uniform cardinality estimate for one dependent sigma fiber. -/
theorem c079_card_sigma_le_mul
    {index : Type uPath} [Fintype index]
    {fiber : index → Type uForward} [∀ i, Fintype (fiber i)]
    (bound : ℕ) (hFiber : ∀ i, Fintype.card (fiber i) ≤ bound) :
    Fintype.card (Σ i, fiber i) ≤ Fintype.card index * bound := by
  rw [Fintype.card_sigma]
  calc
    (∑ i, Fintype.card (fiber i)) ≤ ∑ _i : index, bound := by
      exact Finset.sum_le_sum fun i _ => hFiber i
    _ = Fintype.card index * bound := by simp [Nat.mul_comm]

/-- Core multilevel fiber theorem.  It turns an actual injective assembly and
four uniform level bounds into the expected product cardinality bound. -/
theorem C079EncoderAssemblyCertificate.card_le_product
    {State : Type uState} {PathState : Type uPath}
    {Forward : PathState → Type uForward}
    {FreeSeed : (path : PathState) → Forward path → Type uSeed}
    {Reconstruction : (path : PathState) →
      (forward : Forward path) → FreeSeed path forward →
        Type uReconstruction}
    [Fintype State] [Fintype PathState]
    [∀ path, Fintype (Forward path)]
    [∀ path forward, Fintype (FreeSeed path forward)]
    [∀ path forward seed, Fintype (Reconstruction path forward seed)]
    (certificate : C079EncoderAssemblyCertificate State PathState
      Forward FreeSeed Reconstruction)
    (pathBound forwardBound seedBound reconstructionBound : ℕ)
    (hPath : Fintype.card PathState ≤ pathBound)
    (hForward : ∀ path,
      Fintype.card (Forward path) ≤ forwardBound)
    (hSeed : ∀ path forward,
      Fintype.card (FreeSeed path forward) ≤ seedBound)
    (hReconstruction : ∀ path forward seed,
      Fintype.card (Reconstruction path forward seed) ≤
        reconstructionBound) :
    Fintype.card State ≤
      pathBound * forwardBound * seedBound * reconstructionBound := by
  classical
  calc
    Fintype.card State ≤
        Fintype.card
          (C079EncoderTarget PathState Forward FreeSeed Reconstruction) :=
      Fintype.card_le_of_injective certificate.encode certificate.injective
    _ ≤ Fintype.card PathState *
          (forwardBound * (seedBound * reconstructionBound)) := by
      apply c079_card_sigma_le_mul
      intro path
      calc
        Fintype.card
            (Σ forward : Forward path,
              Σ seed : FreeSeed path forward,
                Reconstruction path forward seed) ≤
            Fintype.card (Forward path) *
              (seedBound * reconstructionBound) := by
          apply c079_card_sigma_le_mul
          intro forward
          calc
            Fintype.card
                (Σ seed : FreeSeed path forward,
                  Reconstruction path forward seed) ≤
                Fintype.card (FreeSeed path forward) *
                  reconstructionBound := by
              exact c079_card_sigma_le_mul reconstructionBound
                (hReconstruction path forward)
            _ ≤ seedBound * reconstructionBound :=
              Nat.mul_le_mul_right reconstructionBound (hSeed path forward)
        _ ≤ forwardBound * (seedBound * reconstructionBound) :=
          Nat.mul_le_mul_right _ (hForward path)
    _ ≤ pathBound * (forwardBound *
          (seedBound * reconstructionBound)) :=
      Nat.mul_le_mul_right _ hPath
    _ = pathBound * forwardBound * seedBound * reconstructionBound := by
      ring

/-- Version whose forward and reconstruction level bounds are supplied by
explicit injective fixed-length codes. -/
theorem C079EncoderAssemblyCertificate.card_le_of_level_codes
    {State : Type uState} {PathState : Type uPath}
    {Forward : PathState → Type uForward}
    {FreeSeed : (path : PathState) → Forward path → Type uSeed}
    {Reconstruction : (path : PathState) →
      (forward : Forward path) → FreeSeed path forward →
        Type uReconstruction}
    [Fintype State] [Fintype PathState]
    [∀ path, Fintype (Forward path)]
    [∀ path forward, Fintype (FreeSeed path forward)]
    [∀ path forward seed, Fintype (Reconstruction path forward seed)]
    (certificate : C079EncoderAssemblyCertificate State PathState
      Forward FreeSeed Reconstruction)
    (pathBound forwardAlphabet forwardLength seedBound
      reconstructionAlphabet reconstructionLength : ℕ)
    (hPath : Fintype.card PathState ≤ pathBound)
    (forwardCode : ∀ path,
      C079FixedLengthCode (Forward path)
        forwardAlphabet forwardLength)
    (hSeed : ∀ path forward,
      Fintype.card (FreeSeed path forward) ≤ seedBound)
    (reconstructionCode : ∀ path forward seed,
      C079FixedLengthCode (Reconstruction path forward seed)
        reconstructionAlphabet reconstructionLength) :
    Fintype.card State ≤
      pathBound * forwardAlphabet ^ forwardLength * seedBound *
        reconstructionAlphabet ^ reconstructionLength := by
  exact certificate.card_le_product
    pathBound (forwardAlphabet ^ forwardLength) seedBound
      (reconstructionAlphabet ^ reconstructionLength)
    hPath (fun path => (forwardCode path).card_le) hSeed
      (fun path forward seed =>
        (reconstructionCode path forward seed).card_le)

/-- Exact-defect specialization: a valid four-level encoder assembly bounds
the actual C079 coefficient, rather than an unrelated abstract state type. -/
theorem c079DefectCoefficient_le_of_encoderAssembly
    {G : PartiteShape} {p s : ℕ}
    (delta : Fin (c079BlockTarget G p s + 1))
    {PathState : Type uPath}
    {Forward : PathState → Type uForward}
    {FreeSeed : (path : PathState) → Forward path → Type uSeed}
    {Reconstruction : (path : PathState) →
      (forward : Forward path) → FreeSeed path forward →
        Type uReconstruction}
    [Fintype PathState]
    [∀ path, Fintype (Forward path)]
    [∀ path forward, Fintype (FreeSeed path forward)]
    [∀ path forward seed, Fintype (Reconstruction path forward seed)]
    (certificate : C079EncoderAssemblyCertificate
      (C079DefectStratum G p s delta.1) PathState
        Forward FreeSeed Reconstruction)
    (pathBound forwardAlphabet forwardLength seedBound
      reconstructionAlphabet reconstructionLength : ℕ)
    (hPath : Fintype.card PathState ≤ pathBound)
    (forwardCode : ∀ path,
      C079FixedLengthCode (Forward path)
        forwardAlphabet forwardLength)
    (hSeed : ∀ path forward,
      Fintype.card (FreeSeed path forward) ≤ seedBound)
    (reconstructionCode : ∀ path forward seed,
      C079FixedLengthCode (Reconstruction path forward seed)
        reconstructionAlphabet reconstructionLength) :
    c079DefectCoefficient G p s delta ≤
      pathBound * forwardAlphabet ^ forwardLength * seedBound *
        reconstructionAlphabet ^ reconstructionLength := by
  exact certificate.card_le_of_level_codes
    pathBound forwardAlphabet forwardLength seedBound
      reconstructionAlphabet reconstructionLength
    hPath forwardCode hSeed reconstructionCode

/-- Direct `hCount`-shaped endpoint for all exact defect fibers.  The final
product comparison is kept explicit so the trace-order shift `p+1` cannot be
hidden by the encoder assembly. -/
theorem c079_hCount_of_encoderAssemblies
    (G : PartiteShape) (p s a K C : ℕ)
    (PathState : Fin (c079BlockTarget G p s + 1) → Type uPath)
    (Forward : ∀ delta, PathState delta → Type uForward)
    (FreeSeed : ∀ delta,
      (path : PathState delta) → Forward delta path → Type uSeed)
    (Reconstruction : ∀ delta,
      (path : PathState delta) →
        (forward : Forward delta path) →
          FreeSeed delta path forward → Type uReconstruction)
    [∀ delta, Fintype (PathState delta)]
    [∀ delta path, Fintype (Forward delta path)]
    [∀ delta path forward,
      Fintype (FreeSeed delta path forward)]
    [∀ delta path forward seed,
      Fintype (Reconstruction delta path forward seed)]
    (certificate : ∀ delta,
      C079EncoderAssemblyCertificate
        (C079DefectStratum G p s delta.1) (PathState delta)
          (Forward delta) (FreeSeed delta) (Reconstruction delta))
    (pathBound forwardAlphabet forwardLength seedBound
      reconstructionAlphabet reconstructionLength :
        Fin (c079BlockTarget G p s + 1) → ℕ)
    (hPath : ∀ delta,
      Fintype.card (PathState delta) ≤ pathBound delta)
    (forwardCode : ∀ delta path,
      C079FixedLengthCode (Forward delta path)
        (forwardAlphabet delta) (forwardLength delta))
    (hSeed : ∀ delta path forward,
      Fintype.card (FreeSeed delta path forward) ≤ seedBound delta)
    (reconstructionCode : ∀ delta path forward seed,
      C079FixedLengthCode (Reconstruction delta path forward seed)
        (reconstructionAlphabet delta) (reconstructionLength delta))
    (hProduct : ∀ delta,
      pathBound delta * forwardAlphabet delta ^ forwardLength delta *
          seedBound delta *
            reconstructionAlphabet delta ^ reconstructionLength delta ≤
        C ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1) + K * delta.1)) :
    ∀ delta : Fin (c079BlockTarget G p s + 1),
      c079DefectCoefficient G p s delta ≤
        C ^ (2 * (p + 1)) *
          (p + 1) ^ (a * (p + 1) + K * delta.1) := by
  intro delta
  exact (c079DefectCoefficient_le_of_encoderAssembly delta
    (certificate delta)
    (pathBound delta) (forwardAlphabet delta) (forwardLength delta)
      (seedBound delta) (reconstructionAlphabet delta)
        (reconstructionLength delta)
    (hPath delta) (forwardCode delta) (hSeed delta)
      (reconstructionCode delta)).trans (hProduct delta)


end GraphMatrixReplica
