import GraphMatrix.Counting.Encoding.FixedMergeCode
noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.ReplicaEncoding

abbrev ForwardLetter (ι : Type*) (m : ℕ) := Option (ι × (Fin m × Fin m))
abbrev ForwardCode (ι : Type*) (m b : ℕ) := Fin b → ForwardLetter ι m

def extractLetter {ι : Type*} [DecidableEq ι] {m : ℕ} (x : ι) :
    ForwardLetter ι m → Option (Fin m × Fin m)
  | none => none
  | some (y, ij) => if x = y then some ij else none

def roleWord {ι : Type*} [DecidableEq ι] {m : ℕ} (x : ι)
    (word : List (ForwardLetter ι m)) := word.filterMap (extractLetter x)

def tagged {ι : Type*} {m : ℕ} (x : ι) (word : List (Fin m × Fin m)) :
    List (ForwardLetter ι m) := word.map (fun ij => some (x, ij))

theorem roleWord_tagged {ι : Type*} [DecidableEq ι] {m : ℕ} (x y : ι)
    (word : List (Fin m × Fin m)) :
    roleWord x (tagged y word) = if x = y then word else [] := by
  induction word with
  | nil => simp [roleWord, tagged]
  | cons ij rest ih =>
    by_cases h : x = y <;> simp_all [roleWord, tagged, extractLetter]

theorem roleWord_append {ι : Type*} [DecidableEq ι] {m : ℕ} (x : ι)
    (a b : List (ForwardLetter ι m)) :
    roleWord x (a ++ b) = roleWord x a ++ roleWord x b := by
  exact List.filterMap_append

theorem roleWord_flatten {ι : Type*} [DecidableEq ι] {m : ℕ}
    (xs : List ι) (hn : xs.Nodup) (words : ι → List (Fin m × Fin m)) (x : ι) :
    roleWord x (xs.flatMap (fun y => tagged y (words y))) =
      if x ∈ xs then words x else [] := by
  induction xs with
  | nil => simp [roleWord]
  | cons y ys ih =>
    have hn' := List.nodup_cons.mp hn
    rw [List.flatMap_cons, roleWord_append, roleWord_tagged, ih hn'.2]
    by_cases h : x = y
    · subst y
      simp [hn'.1]
    · simp [h]

def decodeForward {ι : Type*} [DecidableEq ι] {m b : ℕ}
    (original : ι → ReplicaPartition m) (code : ForwardCode ι m b) (x : ι) :
    ReplicaPartition m := decodeBlockWord (original x) (roleWord x (List.ofFn code))

/-- One role tag per actual merge; padding uses only the null letter. -/
theorem exists_forward_code {ι : Type*} [Fintype ι] [DecidableEq ι] {m b : ℕ}
    (original target : ι → ReplicaPartition m)
    (words : ι → List (Fin m × Fin m))
    (hdec : ∀ x, decodeBlockWord (original x) (words x) = target x)
    (hlen : (∑ x, (words x).length) ≤ b) :
    ∃ code : ForwardCode ι m b, decodeForward original code = target := by
  let xs := (Finset.univ : Finset ι).toList
  let word := xs.flatMap (fun x => tagged x (words x))
  have hwlen : word.length = ∑ x, (words x).length := by
    simp [word, xs, tagged, List.length_flatMap, Finset.sum_map_toList]
  let padded := word ++ List.replicate (b - word.length) none
  have hp : padded.length = b := by
    simp only [padded, List.length_append, List.length_replicate]
    omega
  obtain ⟨code, hc⟩ := exists_ofFn_eq padded b hp
  refine ⟨code, funext fun x => ?_⟩
  have hex : roleWord x word = words x := by
    simpa [word, xs] using roleWord_flatten xs (Finset.nodup_toList _) words x
  have hnull (n : ℕ) : roleWord x (List.replicate n (none : ForwardLetter ι m)) = [] := by
    induction n with
    | zero => rfl
    | succ n ih => simpa [roleWord, List.replicate_succ, extractLetter] using ih
  simp only [decodeForward, hc, padded, roleWord_append, hex, hnull, List.append_nil]
  exact hdec x

theorem card_forward_code {ι : Type*} [Fintype ι] (m b : ℕ) :
    Fintype.card (ForwardCode ι m b) = (1 + Fintype.card ι * m ^ 2) ^ b := by
  simp [ForwardCode, ForwardLetter, pow_two, Nat.add_comm, Nat.mul_assoc]

theorem card_forward_code_le {r m b : ℕ} (hr : 0 < r) (hm : 0 < m) :
    Fintype.card (ForwardCode (Fin r) m b) ≤ (2 * r * m ^ 2) ^ b := by
  rw [card_forward_code, Fintype.card_fin]
  apply Nat.pow_le_pow_left
  have h : 0 < r * m ^ 2 := Nat.mul_pos hr (pow_pos hm _)
  nlinarith

end GraphMatrixReplica.ReplicaEncoding
