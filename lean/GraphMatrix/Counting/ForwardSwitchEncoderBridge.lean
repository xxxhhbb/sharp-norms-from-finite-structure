import GraphMatrix.Counting.MatchingSwitchDescentCore
import GraphMatrix.Counting.DefectVectorCount
import GraphMatrix.Counting.EncoderAssembly

/-! # Concrete switch records inside fixed-defect encoding

This module fills one real code slot of the C079 assembly.  A matching
partition in a metric ball is encoded by an actual switch word.  Decoding the
word from its fixed anchor recovers the original matching partition, so the
record is injective.  The defect-vector factor is the already proved
stars-and-bars composition code.

The scope is a fixed matching anchor and radius.  These results do not encode
forward *merges* of arbitrary replica partitions, identify the anchor from an
admissible graph state, or charge the free-seed/width factor.  Accordingly no
full `C079DefectStratum` encoder or all-defect `hCount` is asserted here.
-/

noncomputable section

namespace GraphMatrixReplica

/-- An arbitrary finite alphabet enumeration gives switch words the exact
fixed-length code type expected by `C079FixedLengthCode`.  The actual switch
word is retained and decoded independently of this enumeration. -/
def c079SwitchWordCodeEquiv (m t : ℕ) :
    C079SwitchWord m t ≃ (Fin t → Fin (4 * m ^ 2)) :=
  Fintype.equivOfCardEq (by
    simp [C079SwitchWord]
    congr 1
    ring)

/-- Restrict the previously proved metric-ball inclusion to a map of finite
fibers. -/
def c079MetricBallToOutputs {m t : ℕ}
    (σ : C079MatchingPartition m) (hm : 0 < m) :
    {τ : C079MatchingPartition m // τ ∈ c079MatchingMetricBall σ t} →
      {τ : C079MatchingPartition m // τ ∈ c079SwitchOutputs σ t} :=
  fun τ => ⟨τ.1, c079MatchingMetricBall_subset_switchOutputs σ hm τ.2⟩

/-- A genuine fixed-length switch word for each member of the metric ball. -/
def c079MetricBallRecord {m t : ℕ}
    (σ : C079MatchingPartition m) (hm : 0 < m)
    (τ : {υ : C079MatchingPartition m // υ ∈ c079MatchingMetricBall σ t}) :
    C079SwitchWord m t :=
  c079SwitchRecord σ (c079MetricBallToOutputs σ hm τ)

/-- The switch decoder reconstructs the matched partition from its word and
fixed anchor. -/
theorem c079MetricBallRecord_decode {m t : ℕ}
    (σ : C079MatchingPartition m) (hm : 0 < m)
    (τ : {υ : C079MatchingPartition m // υ ∈ c079MatchingMetricBall σ t}) :
    c079DecodeSwitchWord σ (c079MetricBallRecord σ hm τ) = τ.1 :=
  c079SwitchRecord_decode σ (c079MetricBallToOutputs σ hm τ)

/-- Equality of records implies equality of the encoded matching partitions.
This is the concrete single-layer losslessness required by the assembly. -/
theorem c079MetricBallRecord_injective {m t : ℕ}
    (σ : C079MatchingPartition m) (hm : 0 < m) :
    Function.Injective (c079MetricBallRecord (t := t) σ hm) := by
  intro τ υ h
  apply Subtype.ext
  calc
    τ.1 = c079DecodeSwitchWord σ (c079MetricBallRecord σ hm τ) :=
      (c079MetricBallRecord_decode σ hm τ).symm
    _ = c079DecodeSwitchWord σ (c079MetricBallRecord σ hm υ) := by rw [h]
    _ = υ.1 := c079MetricBallRecord_decode σ hm υ

/-- The metric-ball fiber supplies a proved fixed-length code, with no
unproved reachability or injectivity parameter. -/
def c079MetricBallFixedLengthCode {m t : ℕ}
    (σ : C079MatchingPartition m) (hm : 0 < m) :
    C079FixedLengthCode
      {τ : C079MatchingPartition m // τ ∈ c079MatchingMetricBall σ t}
      (4 * m ^ 2) t where
  encode := fun τ => c079SwitchWordCodeEquiv m t
    (c079MetricBallRecord σ hm τ)
  injective := by
    intro τ υ h
    apply c079MetricBallRecord_injective (t := t) σ hm
    exact (c079SwitchWordCodeEquiv m t).injective h

/-- The code can be inverted at the partition level by first decoding its
fixed-length switch word. -/
theorem c079MetricBallFixedLengthCode_decode {m t : ℕ}
    (σ : C079MatchingPartition m) (hm : 0 < m)
    (τ : {υ : C079MatchingPartition m // υ ∈ c079MatchingMetricBall σ t}) :
    c079DecodeSwitchWord σ
        ((c079SwitchWordCodeEquiv m t).symm
          ((c079MetricBallFixedLengthCode σ hm).encode τ)) = τ.1 := by
  simpa [c079MetricBallFixedLengthCode] using
    c079MetricBallRecord_decode σ hm τ

/-- In the precise product scope “defect vector × one matching metric ball”,
the composition code and the actual switch record multiply their bounds.
There is no claim that an entire admissible graph state injects into this
product. -/
theorem c079DefectVector_metricBall_card_le
    (k delta m t : ℕ) (σ : C079MatchingPartition m) (hm : 0 < m) :
    Fintype.card
      (C079DefectVector k delta ×
        {τ : C079MatchingPartition m // τ ∈ c079MatchingMetricBall σ t}) ≤
      2 ^ (delta + k) * (4 * m ^ 2) ^ t := by
  classical
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul (c079DefectVector_card_le_pow k delta)
    (c079MetricBallFixedLengthCode σ hm).card_le

/-- A forward matching fiber anchored by the chosen fixed-defect path data.
Its elements are genuine matchings within the given intersection distance;
the anchor may vary with the defect vector. -/
abbrev C079DefectSwitchForward {k delta m : ℕ}
    (anchor : C079DefectVector k delta → C079MatchingPartition m)
    (B : ℕ) (d : C079DefectVector k delta) :=
  {τ : C079MatchingPartition m //
    τ ∈ c079MatchingMetricBall (anchor d) B}

/-- The `Forward` layer of an encoder assembly is supplied automatically when
it is an anchored matching metric ball.  The only remaining premises are a
genuine state-to-assembly injection, a bound for each free-seed fiber, and
fixed-length codes for reconstruction fibers.  In particular no merge code,
normalization map, or width charge is obtained by this theorem. -/
theorem c079DefectCoefficient_le_of_switchForwardAssembly
    {G : PartiteShape} {p s : ℕ}
    (d : Fin (c079BlockTarget G p s + 1))
    (k m B seedBound reconstructionAlphabet reconstructionLength : ℕ)
    (anchor : C079DefectVector k d.1 → C079MatchingPartition m)
    (hm : 0 < m)
    {FreeSeed : (path : C079DefectVector k d.1) →
      C079DefectSwitchForward anchor B path → Type*}
    {Reconstruction : (path : C079DefectVector k d.1) →
      (forward : C079DefectSwitchForward anchor B path) →
        FreeSeed path forward → Type*}
    [∀ path forward, Fintype (FreeSeed path forward)]
    [∀ path forward seed,
      Fintype (Reconstruction path forward seed)]
    (certificate : C079EncoderAssemblyCertificate
      (C079DefectStratum G p s d.1) (C079DefectVector k d.1)
        (C079DefectSwitchForward anchor B) FreeSeed Reconstruction)
    (hSeed : ∀ path forward,
      Fintype.card (FreeSeed path forward) ≤ seedBound)
    (reconstructionCode : ∀ path forward seed,
      C079FixedLengthCode (Reconstruction path forward seed)
        reconstructionAlphabet reconstructionLength) :
    c079DefectCoefficient G p s d ≤
      2 ^ (d.1 + k) * (4 * m ^ 2) ^ B * seedBound *
        reconstructionAlphabet ^ reconstructionLength := by
  exact c079DefectCoefficient_le_of_encoderAssembly d certificate
    (2 ^ (d.1 + k)) (4 * m ^ 2) B seedBound
    reconstructionAlphabet reconstructionLength
    (c079DefectVector_card_le_pow k d.1)
    (fun path => c079MetricBallFixedLengthCode (anchor path) hm)
    hSeed reconstructionCode


end GraphMatrixReplica
