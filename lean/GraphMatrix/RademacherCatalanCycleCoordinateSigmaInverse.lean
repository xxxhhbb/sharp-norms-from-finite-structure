import GraphMatrix.RademacherCatalanCycleCoordinateEquivProof

/-! # A nondependent encoding of Catalan node coordinates -/

noncomputable section
namespace GraphMatrixReplica

structure RademacherRowNodeCoordinateData
    (ι κ : Type) (a b : ℕ) (j : ι) where
  mid : ι
  c₁ : κ
  c₀ : κ
  outsideRows : Fin (b + 1) → ι
  outsideCols : Fin b → κ
  insideRows : Fin a → ι
  insideCols : Fin (a + 1) → κ
  outside_start : outsideRows 0 = mid
  outside_end : outsideRows ⟨b, by omega⟩ = j
  inside_start : insideCols 0 = c₀
  inside_end : insideCols ⟨a, by omega⟩ = c₁

structure RademacherColumnNodeCoordinateData
    (ι κ : Type) (a b : ℕ) (j : κ) where
  mid : κ
  r₁ : ι
  r₀ : ι
  outsideRows : Fin b → ι
  outsideCols : Fin (b + 1) → κ
  insideRows : Fin (a + 1) → ι
  insideCols : Fin a → κ
  outside_start : outsideCols 0 = mid
  outside_end : outsideCols ⟨b, by omega⟩ = j
  inside_start : insideRows 0 = r₀
  inside_end : insideRows ⟨a, by omega⟩ = r₁

def rademacherRowPathNodeRawEquiv
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : ι) :
    RademacherRowCoordinatePath ι κ (.node inside outside) i j ≃
      RademacherRowNodeCoordinateData ι κ a b j where
  toFun p :=
    { mid := p.1.1 ⟨a + 1, by omega⟩
      c₁ := p.1.2 ⟨a, by omega⟩
      c₀ := p.1.2 0
      outsideRows := fun u => p.1.1 ⟨u.1 + (a + 1), by omega⟩
      outsideCols := fun u => p.1.2 ⟨u.1 + (a + 1), by omega⟩
      insideRows := fun u => p.1.1 ⟨u.1 + 1, by omega⟩
      insideCols := fun u => p.1.2 ⟨u.1, by omega⟩
      outside_start := congrArg p.1.1 (Fin.ext (by simp))
      outside_end := by
        calc
          p.1.1 ⟨(⟨b, by omega⟩ : Fin (b + 1)).1 + (a + 1), by omega⟩ =
              p.1.1 ⟨a + b + 1, by omega⟩ :=
            congrArg p.1.1 (Fin.ext (by simp [Nat.add_assoc, Nat.add_left_comm]))
          _ = j := p.2.2
      inside_start := rfl
      inside_end := rfl }
  invFun d :=
    rademacherRowPathAssemble (i := i)
      ⟨(d.outsideRows, d.outsideCols), d.outside_start, d.outside_end⟩
      ⟨(d.insideRows, d.insideCols), d.inside_start, d.inside_end⟩
  left_inv p := rademacherRowPathAssemble_split inside outside i j p
  right_inv d := by
    rcases d with ⟨mid, c₁, c₀, outsideRows, outsideCols,
      insideRows, insideCols, hos, hoe, his, hie⟩
    dsimp [rademacherRowPathAssemble]
    congr 1
    · simpa [show ¬(a + 1 ≤ a) by omega] using hos
    · simpa using hie
    · funext u
      have h : ¬(u.1 + (a + 1) ≤ a) := by omega
      simp [h]
    · funext u
      have h : ¬(u.1 + (a + 1) ≤ a) := by omega
      simp [h]
    · funext u
      have h0 : u.1 + 1 ≠ 0 := by omega
      have hi : u.1 + 1 ≤ a := by omega
      simp [h0, hi]
    · funext u
      have hi : u.1 ≤ a := by omega
      simp [hi]

def rademacherColumnPathNodeRawEquiv
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (i j : κ) :
    RademacherColumnCoordinatePath ι κ (.node inside outside) i j ≃
      RademacherColumnNodeCoordinateData ι κ a b j where
  toFun p :=
    { mid := p.1.2 ⟨a + 1, by omega⟩
      r₁ := p.1.1 ⟨a, by omega⟩
      r₀ := p.1.1 0
      outsideRows := fun u => p.1.1 ⟨u.1 + (a + 1), by omega⟩
      outsideCols := fun u => p.1.2 ⟨u.1 + (a + 1), by omega⟩
      insideRows := fun u => p.1.1 ⟨u.1, by omega⟩
      insideCols := fun u => p.1.2 ⟨u.1 + 1, by omega⟩
      outside_start := congrArg p.1.2 (Fin.ext (by simp))
      outside_end := by
        calc
          p.1.2 ⟨(⟨b, by omega⟩ : Fin (b + 1)).1 + (a + 1), by omega⟩ =
              p.1.2 ⟨a + b + 1, by omega⟩ :=
            congrArg p.1.2 (Fin.ext (by simp [Nat.add_assoc, Nat.add_left_comm]))
          _ = j := p.2.2
      inside_start := rfl
      inside_end := rfl }
  invFun d :=
    rademacherColumnPathAssemble (i := i)
      ⟨(d.outsideRows, d.outsideCols), d.outside_start, d.outside_end⟩
      ⟨(d.insideRows, d.insideCols), d.inside_start, d.inside_end⟩
  left_inv p := rademacherColumnPathAssemble_split inside outside i j p
  right_inv d := by
    rcases d with ⟨mid, r₁, r₀, outsideRows, outsideCols,
      insideRows, insideCols, hos, hoe, his, hie⟩
    dsimp [rademacherColumnPathAssemble]
    congr 1
    · simpa [show ¬(a + 1 ≤ a) by omega] using hos
    · simpa using hie
    · funext u
      have h : ¬(u.1 + (a + 1) ≤ a) := by omega
      simp [h]
    · funext u
      have h0 : u.1 + (a + 1) ≠ 0 := by omega
      have h : ¬(u.1 + (a + 1) ≤ a) := by omega
      simp [h0, h]
    · funext u
      have hi : u.1 ≤ a := by omega
      simp [hi]
    · funext u
      have h0 : u.1 + 1 ≠ 0 := by omega
      have hi : u.1 + 1 ≤ a := by omega
      simp [h0, hi]


end GraphMatrixReplica
