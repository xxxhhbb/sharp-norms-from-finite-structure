import R6.PaperRademacherCatalanRawToDecoration

/-! # Closed cycle coordinates and Catalan row paths -/

noncomputable section
namespace GraphMatrixReplica

def rademacherClosedCycleToRowPath
    {ι κ : Type} {n : ℕ} (hn : 0 < n)
    (M : RademacherNoncrossingMatching n) :
    ((Fin n → ι) × (Fin n → κ)) →
      (Σ i : ι, RademacherRowCoordinatePath ι κ M i i) := fun x =>
  ⟨x.1 ⟨0, hn⟩,
    ⟨(fun s => if h : s.1 < n then x.1 ⟨s.1, h⟩ else x.1 ⟨0, hn⟩,
       x.2), by
      constructor
      · simp [hn]
      · simp⟩⟩

def rademacherClosedRowPathCoordinates
    {ι κ : Type} {n : ℕ} (M : RademacherNoncrossingMatching n) :
    (Σ i : ι, RademacherRowCoordinatePath ι κ M i i) →
      ((Fin n → ι) × (Fin n → κ)) := fun x =>
  (fun t => x.2.1.1 ⟨t.1, by omega⟩, x.2.1.2)

theorem rademacherClosedRowPathCoordinates_leftInverse
    {ι κ : Type} {n : ℕ} (hn : 0 < n)
    (M : RademacherNoncrossingMatching n) :
    Function.LeftInverse (rademacherClosedRowPathCoordinates M)
      (rademacherClosedCycleToRowPath (ι := ι) (κ := κ) hn M) := by
  intro x
  apply Prod.ext
  · funext t
    simp [rademacherClosedRowPathCoordinates,
      rademacherClosedCycleToRowPath, t.2]
  · rfl

theorem rademacherClosedCycleToRowPath_surjective
    {ι κ : Type} {n : ℕ} (hn : 0 < n)
    (M : RademacherNoncrossingMatching n) :
    Function.Surjective
      (rademacherClosedCycleToRowPath (ι := ι) (κ := κ) hn M) := by
  rintro ⟨i, ⟨⟨rows, cols⟩, hstart, hend⟩⟩
  subst i
  let x : (Fin n → ι) × (Fin n → κ) :=
    (fun t => rows ⟨t.1, by omega⟩, cols)
  refine ⟨x, ?_⟩
  dsimp [rademacherClosedCycleToRowPath, x]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · funext s
    by_cases hs : s.1 < n
    · simp [x, rademacherClosedCycleToRowPath, hs]
    · have hsn : s.1 = n := by omega
      have hsfin : s = ⟨n, by omega⟩ := Fin.ext hsn
      simp [x, rademacherClosedCycleToRowPath, hs, hsfin]
      exact hend.symm
  · rfl

def rademacherClosedCycleRowPathEquiv
    {ι κ : Type} {n : ℕ} (hn : 0 < n)
    (M : RademacherNoncrossingMatching n) :
    ((Fin n → ι) × (Fin n → κ)) ≃
      (Σ i : ι, RademacherRowCoordinatePath ι κ M i i) :=
  Equiv.ofBijective (rademacherClosedCycleToRowPath hn M)
    ⟨(rademacherClosedRowPathCoordinates_leftInverse hn M).injective,
      rademacherClosedCycleToRowPath_surjective hn M⟩

/-- The complete, unconditional coordinate equivalence required by the
cycle-coordinate interface. -/
def rademacherClosedCycleCoordinateDecorationEquiv
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) :
    ((Fin (a + b + 1) → ι) × (Fin (a + b + 1) → κ)) ≃
      (Σ i : ι, RademacherRowCoordinateDecoration ι κ
        (.node inside outside) i i) :=
  (rademacherClosedCycleRowPathEquiv (by omega) (.node inside outside)).trans
    (Equiv.sigmaCongrRight fun i =>
      rademacherRowPathCoordinateDecorationEquiv (.node inside outside) i i)

#print axioms rademacherClosedCycleRowPathEquiv
#print axioms rademacherClosedCycleCoordinateDecorationEquiv

end GraphMatrixReplica
