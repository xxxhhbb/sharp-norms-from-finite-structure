import GraphMatrix.RademacherColorProjectionContraction

/-! # Uniform law of an injectively selected finite Bool field

After fixing disjoint role colors, the paper's ambient unordered-edge signs
must restrict to independent typed edge coordinates.  The combinatorial
no-collision map is `PaperRoleColoring.ambientEdge_injective`; this module
proves the finite-uniform measure fact that any injective selection of Bool
coordinates has the full independent product law.  Instantiating the
selection with the paper's unordered-edge map remains a separate adapter.
-/

noncomputable section

namespace GraphMatrixReplica

abbrev PaperUnusedInjectiveCoordinate {A B : Type} (e : A ↪ B) :=
  {b : B // ¬∃ a : A, e a = b}

/-- Split a finite Bool field into the coordinates in an embedding's image
and the unused coordinates. -/
def paperInjectiveRestrictionEquiv
    {A B : Type} (e : A ↪ B) :
    (B → Bool) ≃
      ((A → Bool) × (PaperUnusedInjectiveCoordinate e → Bool)) := by
  classical
  exact {
  toFun w := (fun a => w (e a), fun b => w b.1)
  invFun x := fun b =>
    if h : ∃ a : A, e a = b then x.1 h.choose
    else x.2 ⟨b, h⟩
  left_inv w := by
    funext b
    change (if h : ∃ a : A, e a = b then w (e h.choose)
      else w b) = w b
    split
    next h => rw [h.choose_spec]
    next h => rfl
  right_inv x := by
    apply Prod.ext
    · funext a
      change (if h : ∃ a' : A, e a' = e a then x.1 h.choose
        else x.2 ⟨e a, h⟩) = x.1 a
      split
      next h =>
        have hChoose : h.choose = a := e.injective h.choose_spec
        rw [hChoose]
      next h => exact (h ⟨a, rfl⟩).elim
    · funext b
      change (if h : ∃ a : A, e a = b.1 then x.1 h.choose
        else x.2 ⟨b.1, h⟩) = x.2 b
      split
      next h => exact (b.2 h).elim
      next h =>
        have hb : (⟨b.1, h⟩ : PaperUnusedInjectiveCoordinate e) = b :=
          Subtype.ext rfl
        rw [hb]
  }

/-- The selected coordinates of a uniform finite Bool field are themselves
uniform, hence jointly independent.  No probabilistic axiom is used. -/
theorem paperMean_injectiveBoolRestriction
    {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (f : (A → Bool) → ℝ) :
    paperMean (fun w : B → Bool => f (fun a => w (e a))) =
      paperMean f := by
  classical
  let E := paperInjectiveRestrictionEquiv e
  calc
    paperMean (fun w : B → Bool => f (fun a => w (e a))) =
        paperMean (fun x :
            (A → Bool) × (PaperUnusedInjectiveCoordinate e → Bool) =>
          f x.1) := by
      exact paperMean_equiv E (fun x => f x.1)
    _ = paperMean f := paperMean_prod_fst f


end GraphMatrixReplica
