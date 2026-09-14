import GraphMatrix.RademacherEvenWordPairing

/-! # Counting recursive perfect-matching codes

At the first unmatched position of a word of length `2 (n++1)`, choose its
partner among the remaining `2n+1` positions and recurse after deleting the
pair.  This gives the standard odd-double-factorial count.  The elementary
upper bound `(2n)^n` is the combinatorial factor required by trace-moment
proofs of noncommutative Khintchine; unlike an enumeration by arbitrary
equivalences, it has the correct square-root moment scale.
-/

noncomputable section

namespace GraphMatrixReplica

/-- Recursive code for an unlabeled perfect matching on `2n` linearly
ordered positions.  The concrete deletion/reindexing map is deliberately
kept separate from this cardinality calculation. -/
def RademacherPerfectMatchingCode : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin (2 * n + 1) × RademacherPerfectMatchingCode n

instance instFintypeRademacherPerfectMatchingCode :
    ∀ n, Fintype (RademacherPerfectMatchingCode n)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | n + 1 => by
      letI := instFintypeRademacherPerfectMatchingCode n
      change Fintype (Fin (2 * n + 1) × RademacherPerfectMatchingCode n)
      infer_instance

instance instDecidableEqRademacherPerfectMatchingCode :
    ∀ n, DecidableEq (RademacherPerfectMatchingCode n)
  | 0 => by
      change DecidableEq PUnit
      infer_instance
  | n + 1 => by
      letI := instDecidableEqRademacherPerfectMatchingCode n
      change DecidableEq (Fin (2 * n + 1) × RademacherPerfectMatchingCode n)
      infer_instance

/-- The odd double factorial, written in the recursion naturally used by
perfect matchings. -/
def rademacherPerfectMatchingCount : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * rademacherPerfectMatchingCount n

theorem card_rademacherPerfectMatchingCode (n : ℕ) :
    Fintype.card (RademacherPerfectMatchingCode n) =
      rademacherPerfectMatchingCount n := by
  induction n with
  | zero => simp [RademacherPerfectMatchingCode,
      rademacherPerfectMatchingCount]
  | succ n ih =>
      simp [RademacherPerfectMatchingCode,
        rademacherPerfectMatchingCount, ih]

theorem rademacherPerfectMatchingCount_pos (n : ℕ) :
    0 < rademacherPerfectMatchingCount n := by
  induction n with
  | zero => simp [rademacherPerfectMatchingCount]
  | succ n ih =>
      simp only [rademacherPerfectMatchingCount]
      positivity

/-- Correct-scale crude count: `(2n-1)!! ≤ (2n)^n`. -/
theorem rademacherPerfectMatchingCount_le (n : ℕ) :
    rademacherPerfectMatchingCount n ≤ (2 * n) ^ n := by
  induction n with
  | zero => simp [rademacherPerfectMatchingCount]
  | succ n ih =>
      rw [rademacherPerfectMatchingCount]
      calc
        (2 * n + 1) * rademacherPerfectMatchingCount n ≤
            (2 * n + 1) * (2 * n) ^ n :=
          Nat.mul_le_mul_left _ ih
        _ ≤ (2 * (n + 1)) * (2 * (n + 1)) ^ n := by
          apply Nat.mul_le_mul
          · omega
          · exact Nat.pow_le_pow_left (by omega) n
        _ = (2 * (n + 1)) ^ (n + 1) := by
          rw [pow_succ]
          exact Nat.mul_comm _ _

theorem card_rademacherPerfectMatchingCode_le (n : ℕ) :
    Fintype.card (RademacherPerfectMatchingCode n) ≤ (2 * n) ^ n := by
  rw [card_rademacherPerfectMatchingCode]
  exact rademacherPerfectMatchingCount_le n

/-- Once every canonical matching code has contribution at most `B`, the
entire matching sum costs at most `(2n)^n B`.  This is the precise finite-sum
bookkeeping needed after the still-separate word-to-code coverage and
per-matching contraction arguments. -/
theorem sum_rademacherPerfectMatchingCode_le
    (n : ℕ) (term : RademacherPerfectMatchingCode n → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hterm : ∀ code, term code ≤ B) :
    (∑ code, term code) ≤ ((2 * n) ^ n : ℕ) * B := by
  calc
    (∑ code, term code) ≤ ∑ _code : RademacherPerfectMatchingCode n, B := by
      exact Finset.sum_le_sum fun code _ => hterm code
    _ = (Fintype.card (RademacherPerfectMatchingCode n) : ℝ) * B := by
      simp [nsmul_eq_mul]
    _ ≤ ((2 * n) ^ n : ℕ) * B := by
      gcongr
      exact_mod_cast card_rademacherPerfectMatchingCode_le n


end GraphMatrixReplica
