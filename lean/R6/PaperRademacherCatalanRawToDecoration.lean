import R6.PaperRademacherCatalanCycleCoordinateSigmaInverse

/-! # Catalan raw coordinates and recursive decorations -/

noncomputable section
namespace GraphMatrixReplica

def rademacherRowNodeRawChildPathsEquiv
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (j : ι) :
    RademacherRowNodeCoordinateData ι κ a b j ≃
      (Σ mid : ι, Σ c₁ : κ, Σ c₀ : κ,
        RademacherRowCoordinatePath ι κ outside mid j ×
          RademacherColumnCoordinatePath ι κ inside c₀ c₁) where
  toFun d := ⟨d.mid, d.c₁, d.c₀,
    ⟨(d.outsideRows, d.outsideCols), d.outside_start, d.outside_end⟩,
    ⟨(d.insideRows, d.insideCols), d.inside_start, d.inside_end⟩⟩
  invFun d :=
    { mid := d.1
      c₁ := d.2.1
      c₀ := d.2.2.1
      outsideRows := d.2.2.2.1.1.1
      outsideCols := d.2.2.2.1.1.2
      insideRows := d.2.2.2.2.1.1
      insideCols := d.2.2.2.2.1.2
      outside_start := d.2.2.2.1.2.1
      outside_end := d.2.2.2.1.2.2
      inside_start := d.2.2.2.2.2.1
      inside_end := d.2.2.2.2.2.2 }
  left_inv d := by cases d; rfl
  right_inv d := by
    rcases d with ⟨mid, c₁, c₀, ⟨out, hout⟩, ⟨inn, hinn⟩⟩
    rcases out with ⟨orows, ocols⟩
    rcases inn with ⟨irows, icols⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Prod.ext <;> apply Subtype.ext <;> rfl

def rademacherColumnNodeRawChildPathsEquiv
    {ι κ : Type} {a b : ℕ}
    (inside : RademacherNoncrossingMatching a)
    (outside : RademacherNoncrossingMatching b) (j : κ) :
    RademacherColumnNodeCoordinateData ι κ a b j ≃
      (Σ mid : κ, Σ r₁ : ι, Σ r₀ : ι,
        RademacherColumnCoordinatePath ι κ outside mid j ×
          RademacherRowCoordinatePath ι κ inside r₀ r₁) where
  toFun d := ⟨d.mid, d.r₁, d.r₀,
    ⟨(d.outsideRows, d.outsideCols), d.outside_start, d.outside_end⟩,
    ⟨(d.insideRows, d.insideCols), d.inside_start, d.inside_end⟩⟩
  invFun d :=
    { mid := d.1
      r₁ := d.2.1
      r₀ := d.2.2.1
      outsideRows := d.2.2.2.1.1.1
      outsideCols := d.2.2.2.1.1.2
      insideRows := d.2.2.2.2.1.1
      insideCols := d.2.2.2.2.1.2
      outside_start := d.2.2.2.1.2.1
      outside_end := d.2.2.2.1.2.2
      inside_start := d.2.2.2.2.2.1
      inside_end := d.2.2.2.2.2.2 }
  left_inv d := by cases d; rfl
  right_inv d := by
    rcases d with ⟨mid, r₁, r₀, ⟨out, hout⟩, ⟨inn, hinn⟩⟩
    rcases out with ⟨orows, ocols⟩
    rcases inn with ⟨irows, icols⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Prod.ext <;> apply Subtype.ext <;> rfl

mutual
  /-- A literal row-starting path is exactly the recursively nested
  edge-free row decoration. -/
  noncomputable def rademacherRowPathCoordinateDecorationEquiv
      {ι κ : Type} : {n : ℕ} → (M : RademacherNoncrossingMatching n) →
      (i j : ι) → RademacherRowCoordinatePath ι κ M i j ≃
        RademacherRowCoordinateDecoration ι κ M i j
    | 0, .empty, i, j =>
        { toFun := fun p => ⟨by
            calc
              i = p.1.1 ⟨0, by omega⟩ := p.2.1.symm
              _ = p.1.1 ⟨0, by omega⟩ := congrArg p.1.1 (Fin.ext (by simp))
              _ = j := p.2.2⟩
          invFun := fun h =>
            ⟨(fun _ => i, fun t => Fin.elim0 t), rfl, h.down⟩
          left_inv := by
            intro p
            apply Subtype.ext
            apply Prod.ext
            · funext s
              calc
                i = p.1.1 ⟨0, by omega⟩ := p.2.1.symm
                _ = p.1.1 s := congrArg p.1.1 (Fin.ext (by simp))
            · funext t
              exact Fin.elim0 t
          right_inv := by
            intro x
            cases x
            congr }
    | _, .node inside outside, i, j =>
        (rademacherRowPathNodeRawEquiv inside outside i j).trans
          ((rademacherRowNodeRawChildPathsEquiv inside outside j).trans
            (Equiv.sigmaCongrRight fun mid =>
              Equiv.sigmaCongrRight fun c₁ =>
                Equiv.sigmaCongrRight fun c₀ =>
                  Equiv.prodCongr
                    (rademacherRowPathCoordinateDecorationEquiv outside mid j)
                    (rademacherColumnPathCoordinateDecorationEquiv inside c₀ c₁)))

  /-- Column-starting transpose-typed path/decor-ation equivalence. -/
  noncomputable def rademacherColumnPathCoordinateDecorationEquiv
      {ι κ : Type} : {n : ℕ} → (M : RademacherNoncrossingMatching n) →
      (i j : κ) → RademacherColumnCoordinatePath ι κ M i j ≃
        RademacherColumnCoordinateDecoration ι κ M i j
    | 0, .empty, i, j =>
        { toFun := fun p => ⟨by
            calc
              i = p.1.2 ⟨0, by omega⟩ := p.2.1.symm
              _ = p.1.2 ⟨0, by omega⟩ := congrArg p.1.2 (Fin.ext (by simp))
              _ = j := p.2.2⟩
          invFun := fun h =>
            ⟨(fun t => Fin.elim0 t, fun _ => i), rfl, h.down⟩
          left_inv := by
            intro p
            apply Subtype.ext
            apply Prod.ext
            · funext t
              exact Fin.elim0 t
            · funext s
              calc
                i = p.1.2 ⟨0, by omega⟩ := p.2.1.symm
                _ = p.1.2 s := congrArg p.1.2 (Fin.ext (by simp))
          right_inv := by
            intro x
            cases x
            congr }
    | _, .node inside outside, i, j =>
        (rademacherColumnPathNodeRawEquiv inside outside i j).trans
          ((rademacherColumnNodeRawChildPathsEquiv inside outside j).trans
            (Equiv.sigmaCongrRight fun mid =>
              Equiv.sigmaCongrRight fun r₁ =>
                Equiv.sigmaCongrRight fun r₀ =>
                  Equiv.prodCongr
                    (rademacherColumnPathCoordinateDecorationEquiv outside mid j)
                    (rademacherRowPathCoordinateDecorationEquiv inside r₀ r₁)))
end

#print axioms rademacherRowNodeRawChildPathsEquiv
#print axioms rademacherColumnNodeRawChildPathsEquiv
#print axioms rademacherRowPathCoordinateDecorationEquiv
#print axioms rademacherColumnPathCoordinateDecorationEquiv

end GraphMatrixReplica
