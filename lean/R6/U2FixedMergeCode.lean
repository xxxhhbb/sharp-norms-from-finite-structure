import R6.U2BlockMerge
import R6.C079ForwardSwitchEncoderBridge

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U2

theorem decodeBlockWord_append {m : ℕ} (π : ReplicaPartition m)
    (a b : List (Fin m × Fin m)) :
    decodeBlockWord π (a ++ b) = decodeBlockWord (decodeBlockWord π a) b := by
  induction a generalizing π with
  | nil => rfl
  | cons ij rest ih => exact ih _

theorem decodeBlockWord_replicate {m : ℕ} (π : ReplicaPartition m)
    (i : Fin m) (n : ℕ) :
    decodeBlockWord π (List.replicate n (i, i)) = π := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, decodeBlockWord, mergeBlock_self] using ih

theorem exists_ofFn_eq {α : Type*} (l : List α) (n : ℕ) (h : l.length = n) :
    ∃ f : Fin n → α, List.ofFn f = l := by
  subst n
  exact ⟨l.get, List.ofFn_get l⟩

abbrev MergeCode (m t : ℕ) := Fin t → Fin m × Fin m

def decodeMergeCode {m t : ℕ} (π : ReplicaPartition m) (code : MergeCode m t) :
    ReplicaPartition m := decodeBlockWord π (List.ofFn code)

theorem exists_merge_code {m t : ℕ} (hm : 0 < m) (π σ : ReplicaPartition m)
    (hσ : partitionBlockCount σ ≤ m) (h : PartitionCoarsens π σ)
    (ht : partitionBlockCount σ - partitionBlockCount π ≤ t) :
    ∃ code : MergeCode m t, decodeMergeCode σ code = π := by
  obtain ⟨word, hdec, hlen⟩ := exists_block_word π σ hσ h
  let i : Fin m := ⟨0, hm⟩
  let padded := word ++ List.replicate (t - word.length) (i, i)
  have hp : padded.length = t := by
    simp only [padded, List.length_append, List.length_replicate]
    omega
  obtain ⟨code, hcode⟩ := exists_ofFn_eq padded t hp
  refine ⟨code, ?_⟩
  rw [decodeMergeCode, hcode]
  simp only [padded, decodeBlockWord_append, decodeBlockWord_replicate, hdec]

def mergeCode {m t : ℕ} (hm : 0 < m) (π σ : ReplicaPartition m)
    (hσ : partitionBlockCount σ ≤ m) (h : PartitionCoarsens π σ)
    (ht : partitionBlockCount σ - partitionBlockCount π ≤ t) : MergeCode m t :=
  Classical.choose (exists_merge_code hm π σ hσ h ht)

theorem mergeCode_decode {m t : ℕ} (hm : 0 < m) (π σ : ReplicaPartition m)
    (hσ : partitionBlockCount σ ≤ m) (h : PartitionCoarsens π σ)
    (ht : partitionBlockCount σ - partitionBlockCount π ≤ t) :
    decodeMergeCode σ (mergeCode hm π σ hσ h ht) = π :=
  Classical.choose_spec (exists_merge_code hm π σ hσ h ht)

theorem card_merge_code (m t : ℕ) : Fintype.card (MergeCode m t) = m ^ (2 * t) := by
  simp [MergeCode, ← pow_two, ← pow_mul]

/-- The actual coarsening fiber is encoded, with no injectivity hypothesis. -/
def coarseningCode {m t : ℕ} (hm : 0 < m) (σ : ReplicaPartition m)
    (hσ : partitionBlockCount σ ≤ m)
    (π : {π : ReplicaPartition m // PartitionCoarsens π σ ∧
      partitionBlockCount σ - partitionBlockCount π ≤ t}) : MergeCode m t :=
  mergeCode hm π.1 σ hσ π.2.1 π.2.2

theorem coarseningCode_injective {m t : ℕ} (hm : 0 < m) (σ : ReplicaPartition m)
    (hσ : partitionBlockCount σ ≤ m) : Function.Injective (coarseningCode (t := t) hm σ hσ) := by
  intro π τ hcode
  apply Subtype.ext
  calc
    π.1 = decodeMergeCode σ (coarseningCode hm σ hσ π) := (mergeCode_decode _ _ _ _ _ _).symm
    _ = decodeMergeCode σ (coarseningCode hm σ hσ τ) := congrArg _ hcode
    _ = τ.1 := mergeCode_decode _ _ _ _ _ _

/-- A local off-backbone record: switch from its seed, then merge current blocks. -/
abbrev ReconstructionCode (m radius defect : ℕ) :=
  C079SwitchWord m radius × MergeCode m defect

def decodeReconstruction {m radius defect : ℕ} (seed : C079MatchingPartition m)
    (code : ReconstructionCode m radius defect) : ReplicaPartition m :=
  decodeMergeCode (c079DecodeSwitchWord seed code.1).1 code.2

theorem exists_reconstruction_code {m radius defect : ℕ}
    (hm : 0 < m) (seed σ : C079MatchingPartition m) (π : ReplicaPartition m)
    (hdist : c079MatchingPartitionDistance seed σ ≤ radius)
    (hσ : PartitionCoarsens π σ.1) (hdef : m - partitionBlockCount π ≤ defect) :
    ∃ code : ReconstructionCode m radius defect, decodeReconstruction seed code = π := by
  let ball : {τ : C079MatchingPartition m // τ ∈ c079MatchingMetricBall seed radius} :=
    ⟨σ, by simpa [c079MatchingMetricBall] using hdist⟩
  let sw := c079MetricBallRecord seed hm ball
  have hsw : c079DecodeSwitchWord seed sw = σ := c079MetricBallRecord_decode seed hm ball
  have hcard : partitionBlockCount σ.1 ≤ m := le_of_eq σ.blockCount_eq
  have hgap : partitionBlockCount σ.1 - partitionBlockCount π ≤ defect := by
    simpa only [σ.blockCount_eq] using hdef
  refine ⟨(sw, mergeCode hm π σ.1 hcard hσ hgap), ?_⟩
  simp only [decodeReconstruction, hsw]
  exact mergeCode_decode _ _ _ _ _ _

theorem card_reconstruction_code (m radius defect : ℕ) :
    Fintype.card (ReconstructionCode m radius defect) =
      (4 * m ^ 2) ^ radius * m ^ (2 * defect) := by
  rw [Fintype.card_prod, card_merge_code]
  congr 1
  simp [C079SwitchWord]
  congr 1
  ring

#print axioms mergeCode_decode
#print axioms coarseningCode_injective
#print axioms exists_reconstruction_code
#print axioms card_reconstruction_code
end GraphMatrixReplica.C079U2
