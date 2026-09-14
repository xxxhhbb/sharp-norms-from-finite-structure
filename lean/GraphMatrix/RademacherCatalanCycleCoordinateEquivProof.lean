import GraphMatrix.RademacherCatalanCoordinateWeightEquivProof

/-! # Literal cycle coordinates versus Catalan coordinate decorations

We pass through typed open alternating paths.  A row path of length `n`
has `n+1` row vertices and `n` column cells; a column path is the transpose
typed analogue.  This representation makes the shared endpoints in the
Catalan node decomposition explicit.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Row-starting alternating coordinate path with fixed row endpoints. -/
def RademacherRowCoordinatePath
    (ι κ : Type) {n : ℕ} (_M : RademacherNoncrossingMatching n)
    (i j : ι) :=
  {x : (Fin (n + 1) → ι) × (Fin n → κ) //
    x.1 ⟨0, by omega⟩ = i ∧ x.1 ⟨n, by omega⟩ = j}

/-- Column-starting alternating coordinate path with fixed column endpoints. -/
def RademacherColumnCoordinatePath
    (ι κ : Type) {n : ℕ} (_M : RademacherNoncrossingMatching n)
    (i j : κ) :=
  {x : (Fin n → ι) × (Fin (n + 1) → κ) //
    x.2 ⟨0, by omega⟩ = i ∧ x.2 ⟨n, by omega⟩ = j}

/-! ## Node restriction maps -/

def rademacherRowPathOutside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j : ι} (p : RademacherRowCoordinatePath ι κ
      (.node inside outside) i j) :
    RademacherRowCoordinatePath ι κ outside
      (p.1.1 ⟨a + 1, by omega⟩) j :=
  ⟨(fun u => p.1.1 ⟨u.1 + (a + 1), by omega⟩,
      fun u => p.1.2 ⟨u.1 + (a + 1), by omega⟩), by
    constructor
    · exact congrArg p.1.1 (Fin.ext (by simp))
    · calc
        p.1.1 ⟨(⟨b, by omega⟩ : Fin (b + 1)).1 + (a + 1), by omega⟩ =
            p.1.1 ⟨a + b + 1, by omega⟩ := congrArg p.1.1 (Fin.ext (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]))
        _ = j := p.2.2⟩

def rademacherRowPathInside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j : ι} (p : RademacherRowCoordinatePath ι κ
      (.node inside outside) i j) :
    RademacherColumnCoordinatePath ι κ inside
      (p.1.2 ⟨0, by omega⟩) (p.1.2 ⟨a, by omega⟩) :=
  ⟨(fun u => p.1.1 ⟨u.1 + 1, by omega⟩,
      fun u => p.1.2 ⟨u.1, by omega⟩), ⟨rfl, rfl⟩⟩

def rademacherColumnPathOutside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j : κ} (p : RademacherColumnCoordinatePath ι κ
      (.node inside outside) i j) :
    RademacherColumnCoordinatePath ι κ outside
      (p.1.2 ⟨a + 1, by omega⟩) j :=
  ⟨(fun u => p.1.1 ⟨u.1 + (a + 1), by omega⟩,
      fun u => p.1.2 ⟨u.1 + (a + 1), by omega⟩), by
    constructor
    · exact congrArg p.1.2 (Fin.ext (by simp))
    · calc
        p.1.2 ⟨(⟨b, by omega⟩ : Fin (b + 1)).1 + (a + 1), by omega⟩ =
            p.1.2 ⟨a + b + 1, by omega⟩ := congrArg p.1.2 (Fin.ext (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]))
        _ = j := p.2.2⟩

def rademacherColumnPathInside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j : κ} (p : RademacherColumnCoordinatePath ι κ
      (.node inside outside) i j) :
    RademacherRowCoordinatePath ι κ inside
      (p.1.1 ⟨0, by omega⟩) (p.1.1 ⟨a, by omega⟩) :=
  ⟨(fun u => p.1.1 ⟨u.1, by omega⟩,
      fun u => p.1.2 ⟨u.1 + 1, by omega⟩), ⟨rfl, rfl⟩⟩

/-! ## Node assembly maps -/

def rademacherRowPathAssemble
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : ι} {c₀ c₁ : κ}
    (pout : RademacherRowCoordinatePath ι κ outside mid j)
    (pin : RademacherColumnCoordinatePath ι κ inside c₀ c₁) :
    RademacherRowCoordinatePath ι κ (.node inside outside) i j :=
  ⟨(fun s =>
        if h0 : s.1 = 0 then i
        else if hi : s.1 ≤ a then pin.1.1 ⟨s.1 - 1, by omega⟩
        else pout.1.1 ⟨s.1 - (a + 1), by omega⟩,
      fun t =>
        if hi : t.1 ≤ a then pin.1.2 ⟨t.1, by omega⟩
        else pout.1.2 ⟨t.1 - (a + 1), by omega⟩), by
    constructor
    · simp
    · have hle : ¬(a + b + 1 ≤ a) := by omega
      simpa [hle] using pout.2.2⟩

def rademacherColumnPathAssemble
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : κ} {r₀ r₁ : ι}
    (pout : RademacherColumnCoordinatePath ι κ outside mid j)
    (pin : RademacherRowCoordinatePath ι κ inside r₀ r₁) :
    RademacherColumnCoordinatePath ι κ (.node inside outside) i j :=
  ⟨(fun t =>
        if hi : t.1 ≤ a then pin.1.1 ⟨t.1, by omega⟩
        else pout.1.1 ⟨t.1 - (a + 1), by omega⟩,
      fun s =>
        if h0 : s.1 = 0 then i
        else if hi : s.1 ≤ a then pin.1.2 ⟨s.1 - 1, by omega⟩
        else pout.1.2 ⟨s.1 - (a + 1), by omega⟩), by
    constructor
    · simp
    · have hle : ¬(a + b + 1 ≤ a) := by omega
      simpa [hle] using pout.2.2⟩

/-! The four literal application formulas are sufficient to prove both
inverse laws without relying on proof-term equality of bounded indices. -/

@[simp] theorem rademacherRowPathAssemble_row_zero
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : ι} {c₀ c₁ : κ}
    (pout : RademacherRowCoordinatePath ι κ outside mid j)
    (pin : RademacherColumnCoordinatePath ι κ inside c₀ c₁) :
    (rademacherRowPathAssemble (i := i) pout pin).1.1 ⟨0, by omega⟩ = i := by
  simp [rademacherRowPathAssemble]

@[simp] theorem rademacherRowPathAssemble_row_inside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : ι} {c₀ c₁ : κ}
    (pout : RademacherRowCoordinatePath ι κ outside mid j)
    (pin : RademacherColumnCoordinatePath ι κ inside c₀ c₁)
    (u : Fin a) :
    (rademacherRowPathAssemble (i := i) pout pin).1.1
        ⟨u.1 + 1, by omega⟩ = pin.1.1 u := by
  simp [rademacherRowPathAssemble]

@[simp] theorem rademacherRowPathAssemble_row_outside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : ι} {c₀ c₁ : κ}
    (pout : RademacherRowCoordinatePath ι κ outside mid j)
    (pin : RademacherColumnCoordinatePath ι κ inside c₀ c₁)
    (u : Fin (b + 1)) :
    (rademacherRowPathAssemble (i := i) pout pin).1.1
        ⟨u.1 + (a + 1), by omega⟩ = pout.1.1 u := by
  have h0 : u.1 + (a + 1) ≠ 0 := by omega
  have hi : ¬(u.1 + (a + 1) ≤ a) := by omega
  simp [rademacherRowPathAssemble, h0, hi]

@[simp] theorem rademacherRowPathAssemble_col_inside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : ι} {c₀ c₁ : κ}
    (pout : RademacherRowCoordinatePath ι κ outside mid j)
    (pin : RademacherColumnCoordinatePath ι κ inside c₀ c₁)
    (u : Fin (a + 1)) :
    (rademacherRowPathAssemble (i := i) pout pin).1.2
        ⟨u.1, by omega⟩ = pin.1.2 u := by
  have hi : u.1 ≤ a := by omega
  simp [rademacherRowPathAssemble, hi]

@[simp] theorem rademacherRowPathAssemble_col_outside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : ι} {c₀ c₁ : κ}
    (pout : RademacherRowCoordinatePath ι κ outside mid j)
    (pin : RademacherColumnCoordinatePath ι κ inside c₀ c₁)
    (u : Fin b) :
    (rademacherRowPathAssemble (i := i) pout pin).1.2
        ⟨u.1 + (a + 1), by omega⟩ = pout.1.2 u := by
  have hi : ¬(u.1 + (a + 1) ≤ a) := by omega
  simp [rademacherRowPathAssemble, hi]

@[simp] theorem rademacherColumnPathAssemble_col_zero
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : κ} {r₀ r₁ : ι}
    (pout : RademacherColumnCoordinatePath ι κ outside mid j)
    (pin : RademacherRowCoordinatePath ι κ inside r₀ r₁) :
    (rademacherColumnPathAssemble (i := i) pout pin).1.2 ⟨0, by omega⟩ = i := by
  simp [rademacherColumnPathAssemble]

@[simp] theorem rademacherColumnPathAssemble_col_inside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : κ} {r₀ r₁ : ι}
    (pout : RademacherColumnCoordinatePath ι κ outside mid j)
    (pin : RademacherRowCoordinatePath ι κ inside r₀ r₁)
    (u : Fin a) :
    (rademacherColumnPathAssemble (i := i) pout pin).1.2
        ⟨u.1 + 1, by omega⟩ = pin.1.2 u := by
  simp [rademacherColumnPathAssemble]

@[simp] theorem rademacherColumnPathAssemble_col_outside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : κ} {r₀ r₁ : ι}
    (pout : RademacherColumnCoordinatePath ι κ outside mid j)
    (pin : RademacherRowCoordinatePath ι κ inside r₀ r₁)
    (u : Fin (b + 1)) :
    (rademacherColumnPathAssemble (i := i) pout pin).1.2
        ⟨u.1 + (a + 1), by omega⟩ = pout.1.2 u := by
  have h0 : u.1 + (a + 1) ≠ 0 := by omega
  have hi : ¬(u.1 + (a + 1) ≤ a) := by omega
  simp [rademacherColumnPathAssemble, h0, hi]

@[simp] theorem rademacherColumnPathAssemble_row_inside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : κ} {r₀ r₁ : ι}
    (pout : RademacherColumnCoordinatePath ι κ outside mid j)
    (pin : RademacherRowCoordinatePath ι κ inside r₀ r₁)
    (u : Fin (a + 1)) :
    (rademacherColumnPathAssemble (i := i) pout pin).1.1
        ⟨u.1, by omega⟩ = pin.1.1 u := by
  have hi : u.1 ≤ a := by omega
  simp [rademacherColumnPathAssemble, hi]

@[simp] theorem rademacherColumnPathAssemble_row_outside
    {ι κ : Type} {a b : ℕ}
    {inside : RademacherNoncrossingMatching a}
    {outside : RademacherNoncrossingMatching b}
    {i j mid : κ} {r₀ r₁ : ι}
    (pout : RademacherColumnCoordinatePath ι κ outside mid j)
    (pin : RademacherRowCoordinatePath ι κ inside r₀ r₁)
    (u : Fin b) :
    (rademacherColumnPathAssemble (i := i) pout pin).1.1
        ⟨u.1 + (a + 1), by omega⟩ = pout.1.1 u := by
  have hi : ¬(u.1 + (a + 1) ≤ a) := by omega
  simp [rademacherColumnPathAssemble, hi]

/-! ## Exact node splitting

These equivalences are the coordinate-level Fubini maps.  In particular,
they retain both boundary values shared by the root edge and its two child
paths; no cardinality or choice principle is used. -/

def rademacherRowPathNodeSplit
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : ι) :
    RademacherRowCoordinatePath ι κ (.node inside outside) i j →
      (Σ mid : ι, Σ c₁ : κ, Σ c₀ : κ,
        RademacherRowCoordinatePath ι κ outside mid j ×
          RademacherColumnCoordinatePath ι κ inside c₀ c₁) := fun p =>
  ⟨p.1.1 ⟨a + 1, by omega⟩, p.1.2 ⟨a, by omega⟩,
    p.1.2 ⟨0, by omega⟩, rademacherRowPathOutside p,
    rademacherRowPathInside p⟩

/-- Splitting a literal row path at a Catalan node and assembling its two
pieces is judgmentally coordinate preserving.  This is the hard direction
needed for injectivity of the eventual coordinate equivalence. -/
theorem rademacherRowPathAssemble_split
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : ι)
    (p : RademacherRowCoordinatePath ι κ (.node inside outside) i j) :
    let d := rademacherRowPathNodeSplit inside outside i j p
    rademacherRowPathAssemble (i := i) d.2.2.2.1 d.2.2.2.2 = p := by
    dsimp [rademacherRowPathNodeSplit]
    apply Subtype.ext
    apply Prod.ext
    · funext s
      by_cases h0 : s.1 = 0
      · have hs0 : s = ⟨0, by omega⟩ := Fin.ext h0
        rw [hs0]
        calc
          (rademacherRowPathAssemble
              (rademacherRowPathOutside p) (rademacherRowPathInside p)).1.1
                ⟨0, by omega⟩ = i := rademacherRowPathAssemble_row_zero _ _
          _ = p.1.1 ⟨0, by omega⟩ := p.2.1.symm
      · by_cases hi : s.1 ≤ a
        · have hs : 0 < s.1 := Nat.pos_of_ne_zero h0
          have hsne : s ≠ 0 := by
            intro h
            exact h0 (congrArg Fin.val h)
          have hindex : (⟨s.1 - 1 + 1, by omega⟩ : Fin (a + b + 2)) = s :=
            Fin.ext (Nat.sub_add_cancel (by omega))
          simpa [rademacherRowPathAssemble, h0, hsne, hi,
            rademacherRowPathInside] using congrArg p.1.1 hindex
        · have ha : a + 1 ≤ s.1 := by omega
          have hsne : s ≠ 0 := by
            intro h
            exact h0 (congrArg Fin.val h)
          have hindex :
              (⟨s.1 - (a + 1) + (a + 1), by omega⟩ : Fin (a + b + 2)) = s :=
            Fin.ext (Nat.sub_add_cancel ha)
          simpa [rademacherRowPathAssemble, h0, hsne, hi,
            rademacherRowPathOutside] using congrArg p.1.1 hindex
    · funext t
      by_cases hi : t.1 ≤ a
      · simp [rademacherRowPathAssemble, hi,
          rademacherRowPathInside]
      · have ha : a + 1 ≤ t.1 := by omega
        have hindex :
            (⟨t.1 - (a + 1) + (a + 1), by omega⟩ : Fin (a + b + 1)) = t :=
          Fin.ext (Nat.sub_add_cancel ha)
        simpa [rademacherRowPathAssemble, hi,
          rademacherRowPathOutside] using congrArg p.1.2 hindex

theorem rademacherRowPathNodeSplit_injective
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : ι) :
    Function.Injective (rademacherRowPathNodeSplit (κ := κ) inside outside i j) := by
  intro p q h
  have hp := rademacherRowPathAssemble_split inside outside i j p
  have hq := rademacherRowPathAssemble_split inside outside i j q
  dsimp only at hp hq
  rw [h] at hp
  exact hp.symm.trans hq

def rademacherColumnPathNodeSplit
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : κ) :
    RademacherColumnCoordinatePath ι κ (.node inside outside) i j →
      (Σ mid : κ, Σ r₁ : ι, Σ r₀ : ι,
        RademacherColumnCoordinatePath ι κ outside mid j ×
          RademacherRowCoordinatePath ι κ inside r₀ r₁) := fun p =>
  ⟨p.1.2 ⟨a + 1, by omega⟩, p.1.1 ⟨a, by omega⟩,
    p.1.1 ⟨0, by omega⟩, rademacherColumnPathOutside p,
    rademacherColumnPathInside p⟩

/-- Column-typed symmetric coordinate reconstruction theorem. -/
theorem rademacherColumnPathAssemble_split
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : κ)
    (p : RademacherColumnCoordinatePath ι κ (.node inside outside) i j) :
    let d := rademacherColumnPathNodeSplit inside outside i j p
    rademacherColumnPathAssemble (i := i) d.2.2.2.1 d.2.2.2.2 = p := by
    dsimp [rademacherColumnPathNodeSplit]
    apply Subtype.ext
    apply Prod.ext
    · funext t
      by_cases hi : t.1 ≤ a
      · simp [rademacherColumnPathAssemble, hi,
          rademacherColumnPathInside]
      · have ha : a + 1 ≤ t.1 := by omega
        have hindex :
            (⟨t.1 - (a + 1) + (a + 1), by omega⟩ : Fin (a + b + 1)) = t :=
          Fin.ext (Nat.sub_add_cancel ha)
        simpa [rademacherColumnPathAssemble, hi,
          rademacherColumnPathOutside] using congrArg p.1.1 hindex
    · funext s
      by_cases h0 : s.1 = 0
      · have hs0 : s = ⟨0, by omega⟩ := Fin.ext h0
        rw [hs0]
        calc
          (rademacherColumnPathAssemble
              (rademacherColumnPathOutside p) (rademacherColumnPathInside p)).1.2
                ⟨0, by omega⟩ = i := rademacherColumnPathAssemble_col_zero _ _
          _ = p.1.2 ⟨0, by omega⟩ := p.2.1.symm
      · by_cases hi : s.1 ≤ a
        · have hs : 0 < s.1 := Nat.pos_of_ne_zero h0
          have hsne : s ≠ 0 := by
            intro h
            exact h0 (congrArg Fin.val h)
          have hindex : (⟨s.1 - 1 + 1, by omega⟩ : Fin (a + b + 2)) = s :=
            Fin.ext (Nat.sub_add_cancel (by omega))
          simpa [rademacherColumnPathAssemble, h0, hsne, hi,
            rademacherColumnPathInside] using congrArg p.1.2 hindex
        · have ha : a + 1 ≤ s.1 := by omega
          have hsne : s ≠ 0 := by
            intro h
            exact h0 (congrArg Fin.val h)
          have hindex :
              (⟨s.1 - (a + 1) + (a + 1), by omega⟩ : Fin (a + b + 2)) = s :=
            Fin.ext (Nat.sub_add_cancel ha)
          simpa [rademacherColumnPathAssemble, h0, hsne, hi,
            rademacherColumnPathOutside] using congrArg p.1.2 hindex

theorem rademacherColumnPathNodeSplit_injective
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : κ) :
    Function.Injective (rademacherColumnPathNodeSplit (ι := ι) inside outside i j) := by
  intro p q h
  have hp := rademacherColumnPathAssemble_split inside outside i j p
  have hq := rademacherColumnPathAssemble_split inside outside i j q
  dsimp only at hp hq
  rw [h] at hp
  exact hp.symm.trans hq


end GraphMatrixReplica
