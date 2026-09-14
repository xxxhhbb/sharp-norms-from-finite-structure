import R6.PaperR16ColorClassRealization
import R6.PaperR16ColoredPaddingIdentity

/-! # Fixed-color R16 matrix as a zero-padded fiber matrix

The role dimensions are the actual cardinalities of the fibers of the fixed
ambient coloring.  No balancing assumption or probabilistic statement enters
this deterministic matrix identity.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

private abbrev fiberDimension (G : PaperShape) (n : ℕ)
    (color : Fin n → Fin G.roles) := paperR16ColorClassDimension G n color

private abbrev fiberColoring (G : PaperShape) (n : ℕ)
    (color : Fin n → Fin G.roles) := paperR16ColorClassRoleColoring G n color

/-- Every chosen fiber embedding covers its complete color class, including
the case of an empty fiber. -/
theorem paperR16ColorClass_exactColorClasses
    (G : PaperShape) (n : ℕ) (color : Fin n → Fin G.roles) :
    (fiberColoring G n color).ExactColorClasses color := by
  intro v i
  exact (paperR16ColorClass_embedding_image_iff G n color v i).symm

theorem paperR16ColoredGraphMatrix_selected_fiber_entry
    (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (color : Fin n → Fin G.roles)
    (row : PartiteBoundaryRow (G := G.toPartiteShape)
      (fiberDimension G n color))
    (col : PartiteBoundaryCol (G := G.toPartiteShape)
      (fiberDimension G n color)) :
    paperR16ColoredGraphMatrix G n w color
        ((fiberColoring G n color).paperRow row)
        ((fiberColoring G n color).paperCol col) =
      paperRoleColoredBoundaryMatrix G (fiberDimension G n color) n
        (fiberColoring G n color) w row col := by
  exact paperR16ColoredGraphMatrix_apply_selected G
    (fiberDimension G n color) n (fiberColoring G n color)
    color (paperR16ColorClass_exactColorClasses G n color) w row col

/-- A fixed R16 coloring yields exactly the zero padding of the typed matrix
whose role dimensions are the cardinalities of its color fibers. -/
theorem paperR16ColoredGraphMatrix_eq_fiber_zeroPadded
    (G : PaperShape) (n : ℕ) (w : PaperNoise n)
    (color : Fin n → Fin G.roles) :
    paperR16ColoredGraphMatrix G n w color =
      (fiberColoring G n color).zeroPaddedBoundaryMatrix
        (paperRoleColoredBoundaryMatrix G (fiberDimension G n color) n
          (fiberColoring G n color) w) := by
  exact paperR16ColoredGraphMatrix_eq_zeroPadded G
    (fiberDimension G n color) n (fiberColoring G n color)
    color (paperR16ColorClass_exactColorClasses G n color) w

#print axioms paperR16ColorClass_exactColorClasses
#print axioms paperR16ColoredGraphMatrix_selected_fiber_entry
#print axioms paperR16ColoredGraphMatrix_eq_fiber_zeroPadded

end GraphMatrixReplica
