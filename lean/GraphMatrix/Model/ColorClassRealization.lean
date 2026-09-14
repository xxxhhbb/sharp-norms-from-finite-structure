import GraphMatrix.Model.ColorUpperTransfer
import GraphMatrix.RoleColoredPartiteBridge

/-! # Realizing one ambient coloring as disjoint role classes

Every color map determines a possibly empty finite label class for each role.
The canonical finite equivalence from a class to `Fin` of its cardinality gives
the `PaperRoleColoring` required by the fixed-color partite bridge. This file
does not assert the induced edge arrays are independent; that is a separate
distributional statement.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- The size vector of the role classes of one ambient coloring. -/
def paperR16ColorClassDimension (G : PaperShape) (n : ℕ)
    (color : Fin n → Fin G.roles) : Fin G.roles → ℕ :=
  fun v => Fintype.card {i : Fin n // color i = v}

/-- Canonical indexing of one (possibly empty) color class. -/
def paperR16ColorClassEquiv (G : PaperShape) (n : ℕ)
    (color : Fin n → Fin G.roles) (v : Fin G.roles) :
    Fin (paperR16ColorClassDimension G n color v) ≃
      {i : Fin n // color i = v} :=
  (Fintype.equivFin {i : Fin n // color i = v}).symm

/-- Any ambient coloring gives pairwise disjoint labelled role classes. -/
def paperR16ColorClassRoleColoring (G : PaperShape) (n : ℕ)
    (color : Fin n → Fin G.roles) :
    PaperRoleColoring G (paperR16ColorClassDimension G n color) n where
  embedding v := {
    toFun := fun a => (paperR16ColorClassEquiv G n color v a).1
    inj' := by
      intro a b hab
      apply (paperR16ColorClassEquiv G n color v).injective
      exact Subtype.ext hab
  }
  disjoint := by
    intro v w hvw a b hab
    have hv : color ((paperR16ColorClassEquiv G n color v a).1) = v :=
      (paperR16ColorClassEquiv G n color v a).2
    have hw : color ((paperR16ColorClassEquiv G n color w b).1) = w :=
      (paperR16ColorClassEquiv G n color w b).2
    exact hvw (hv.symm.trans ((congrArg color hab).trans hw))

/-- The image of the role-class embedding is exactly that color class. -/
theorem paperR16ColorClass_embedding_image_iff
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles)
    (v : Fin G.roles) (i : Fin n) :
    (∃ a : Fin (paperR16ColorClassDimension G n color v),
      (paperR16ColorClassRoleColoring G n color).embedding v a = i) ↔
      color i = v := by
  constructor
  · rintro ⟨a, rfl⟩
    exact (paperR16ColorClassEquiv G n color v a).2
  · intro hi
    let a := (paperR16ColorClassEquiv G n color v).symm ⟨i, hi⟩
    refine ⟨a, ?_⟩
    change ((paperR16ColorClassEquiv G n color v) a).1 = i
    simpa [a] using congrArg Subtype.val
      ((paperR16ColorClassEquiv G n color v).apply_symm_apply ⟨i, hi⟩)

/-- A coloring-respecting globally injective realization is exactly one
rolewise assignment in its finite color classes. -/
def paperR16ColorRespectingRealizationEquiv
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles) :
    {phi : PaperRealization G n // paperR16ColorRespects G color phi} ≃
      PaperRoleColorAssignment G (paperR16ColorClassDimension G n color) where
  toFun phi v :=
    (paperR16ColorClassEquiv G n color v).symm
      ⟨phi.1 v, phi.2 v⟩
  invFun assignment := by
    refine ⟨(paperR16ColorClassRoleColoring G n color).globalRealization
      assignment, ?_⟩
    intro v
    exact (paperR16ColorClassEquiv G n color v (assignment v)).2
  left_inv := by
    intro phi
    apply Subtype.ext
    apply Function.Embedding.ext
    intro v
    change ((paperR16ColorClassEquiv G n color v)
      ((paperR16ColorClassEquiv G n color v).symm
        ⟨phi.1 v, phi.2 v⟩)).1 = phi.1 v
    simpa using congrArg Subtype.val
      ((paperR16ColorClassEquiv G n color v).apply_symm_apply
        ⟨phi.1 v, phi.2 v⟩)
  right_inv := by
    intro assignment
    funext v
    change (paperR16ColorClassEquiv G n color v).symm
      ((paperR16ColorClassEquiv G n color v) (assignment v)) = assignment v
    exact (paperR16ColorClassEquiv G n color v).symm_apply_apply
      (assignment v)


end GraphMatrixReplica
