import Mathlib

/-! # C079 forward-normalization coding ledger

This file formalizes the finite-code and power bookkeeping used in Sections
4--5 of C079.  It deliberately does **not** construct the concrete matching
switches, merge sequences, normalization map, or decoder.  Those mathematical
objects enter only through an explicit injective fixed-length encoding.

Consequently the cardinality theorems below are reusable endpoints for a
future lossless encoder, not a claim that such an encoder has already been
formalized.
-/

noncomputable section

namespace GraphMatrixReplica

/-- A fixed-length finite code for a finite type.  In the C079 application,
the source type is a switch ball, a family of forward coarsenings, or a
reconstruction fiber.  The injectivity field is intentionally visible. -/
structure C079FixedLengthCode (alpha : Type*) [Fintype alpha]
    (alphabet length : ℕ) where
  encode : alpha → (Fin length → Fin alphabet)
  injective : Function.Injective encode

/-- Any genuinely injective fixed-length code gives the expected cardinality
bound.  This is the only finite-encoding principle used in this module. -/
theorem C079FixedLengthCode.card_le
    {alpha : Type*} [Fintype alpha] {alphabet length : ℕ}
    (code : C079FixedLengthCode alpha alphabet length) :
    Fintype.card alpha ≤ alphabet ^ length := by
  classical
  calc
    Fintype.card alpha ≤
        Fintype.card (Fin length → Fin alphabet) :=
      Fintype.card_le_of_injective code.encode code.injective
    _ = alphabet ^ length := by simp

/-- Conditional switch-ball endpoint for the radius estimate in C079 (14).
Supplying `code` is exactly the still-separate task of padding a concrete
switch path to length `t` and proving that the chosen encoding is lossless. -/
theorem c079_matchingSwitchRadius_card_le_of_code
    {alpha : Type*} [Fintype alpha] (p t : ℕ)
    (code : C079FixedLengthCode alpha (4 * p ^ 2) t) :
    Fintype.card alpha ≤ (4 * p ^ 2) ^ t :=
  code.card_le

/-- Conditional forward-coarsening endpoint for C079 (22).  No concrete
partition coarsening algorithm is asserted here. -/
theorem c079_forwardCoarsening_card_le_of_code
    {alpha : Type*} [Fintype alpha] (r p B : ℕ)
    (code : C079FixedLengthCode alpha (2 * r * p ^ 2) B) :
    Fintype.card alpha ≤ (2 * r * p ^ 2) ^ B :=
  code.card_le

/-- Exact separation of the forward-coarsening budget into a shape-only base
and the polynomial exponent `6*r*D`. -/
theorem c079_forwardCoarsening_power_eq
    (r p D : ℕ) :
    (2 * r * p ^ 2) ^ (3 * r * D) =
      (2 * r) ^ (3 * r * D) * p ^ (6 * r * D) := by
  rw [mul_pow, pow_mul]
  congr 1
  ring

/-- The forward-coarsening code specialized to the proved merge budget
`B = 3*r*D`, with its polynomial part separated. -/
theorem c079_forwardCoarsening_card_le_normalized
    {alpha : Type*} [Fintype alpha] (r p D : ℕ)
    (code : C079FixedLengthCode alpha (2 * r * p ^ 2) (3 * r * D)) :
    Fintype.card alpha ≤
      (2 * r) ^ (3 * r * D) * p ^ (6 * r * D) := by
  calc
    Fintype.card alpha ≤ (2 * r * p ^ 2) ^ (3 * r * D) :=
      code.card_le
    _ = (2 * r) ^ (3 * r * D) * p ^ (6 * r * D) :=
      c079_forwardCoarsening_power_eq r p D

/-- Exact separation of the off-backbone reconstruction budget (23).
The switch words cost `4*r*D` powers of `p`, and the final merges cost
`2*D`, for total exponent `(4*r+2)*D`. -/
theorem c079_reconstruction_power_eq
    (r p D : ℕ) :
    (4 * p ^ 2) ^ (2 * r * D) * p ^ (2 * D) =
      4 ^ (2 * r * D) * p ^ ((4 * r + 2) * D) := by
  calc
    (4 * p ^ 2) ^ (2 * r * D) * p ^ (2 * D) =
        (4 ^ (2 * r * D) * p ^ (2 * (2 * r * D))) *
          p ^ (2 * D) := by
      rw [mul_pow, pow_mul p 2 (2 * r * D)]
    _ = 4 ^ (2 * r * D) *
          (p ^ (2 * (2 * r * D)) * p ^ (2 * D)) := by ring
    _ = 4 ^ (2 * r * D) *
          p ^ (2 * (2 * r * D) + 2 * D) := by
      rw [pow_add]
    _ = 4 ^ (2 * r * D) * p ^ ((4 * r + 2) * D) := by
      congr 2
      ring

/-- A product of explicitly injective switch and merge records has exactly
the reconstruction bound used in C079 (23).  The theorem still does not
construct those records from partitions. -/
theorem c079_reconstruction_card_le_of_codes
    {switchData mergeData : Type*}
    [Fintype switchData] [Fintype mergeData]
    (r p D : ℕ)
    (switchCode : C079FixedLengthCode switchData
      (4 * p ^ 2) (2 * r * D))
    (mergeCode : C079FixedLengthCode mergeData (p ^ 2) D) :
    Fintype.card (switchData × mergeData) ≤
      4 ^ (2 * r * D) * p ^ ((4 * r + 2) * D) := by
  calc
    Fintype.card (switchData × mergeData) =
        Fintype.card switchData * Fintype.card mergeData := by simp
    _ ≤ (4 * p ^ 2) ^ (2 * r * D) * (p ^ 2) ^ D :=
      Nat.mul_le_mul switchCode.card_le mergeCode.card_le
    _ = (4 * p ^ 2) ^ (2 * r * D) * p ^ (2 * D) := by
      rw [pow_mul p 2 D]
    _ = 4 ^ (2 * r * D) * p ^ ((4 * r + 2) * D) :=
      c079_reconstruction_power_eq r p D

/-- The two forward-only operations have total polynomial exponent
`(10*r+2)*D`; no inverse splitting of a coarsened backbone is used. -/
theorem c079_forward_and_reconstruction_power_eq
    (r p D : ℕ) :
    (2 * r * p ^ 2) ^ (3 * r * D) *
        ((4 * p ^ 2) ^ (2 * r * D) * p ^ (2 * D)) =
      (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D) *
        p ^ ((10 * r + 2) * D) := by
  rw [c079_forwardCoarsening_power_eq,
    c079_reconstruction_power_eq]
  calc
    ((2 * r) ^ (3 * r * D) * p ^ (6 * r * D)) *
        (4 ^ (2 * r * D) * p ^ ((4 * r + 2) * D)) =
      (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D) *
        (p ^ (6 * r * D) * p ^ ((4 * r + 2) * D)) := by ring
    _ = (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D) *
        p ^ (6 * r * D + (4 * r + 2) * D) := by
      rw [pow_add]
    _ = (2 * r) ^ (3 * r * D) * 4 ^ (2 * r * D) *
        p ^ ((10 * r + 2) * D) := by
      congr 2
      ring

#print axioms C079FixedLengthCode.card_le
#print axioms c079_matchingSwitchRadius_card_le_of_code
#print axioms c079_forwardCoarsening_card_le_of_code
#print axioms c079_forwardCoarsening_card_le_normalized
#print axioms c079_forwardCoarsening_power_eq
#print axioms c079_reconstruction_power_eq
#print axioms c079_reconstruction_card_le_of_codes
#print axioms c079_forward_and_reconstruction_power_eq

end GraphMatrixReplica
