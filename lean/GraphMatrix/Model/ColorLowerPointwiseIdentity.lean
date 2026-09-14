import GraphMatrix.Model.ColorLowerSurvivorBijection
import GraphMatrix.Model.ColorLowerProjectedMatrix
import GraphMatrix.Model.TypedEdgeNoiseLaw

/-! The pointwise fixed-color identity for the lower projection. -/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica


theorem PaperRoleColoring.projectedEntry_eq_aut_smul_typed
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (w : PaperNoise n)
    (row : PartiteBoundaryRow (G := G.toPartiteShape) dimension)
    (col : PartiteBoundaryCol (G := G.toPartiteShape) dimension) :
    paperR16ProjectedGraphEntry G n C.targetEdgeTag w
        (C.paperRow row) (C.paperCol col) =
      (Fintype.card G.R16BoundaryFixingAutomorphism : ℕ) •
        paperRoleColoredBoundaryMatrix G dimension n C w row col := by
  classical
  let P : PaperRealization G n → Prop := fun phi =>
    paperEntryCompatible G phi (C.paperRow row) (C.paperCol col) ∧
      ∀ k : Fin G.edges,
        Odd (paperR16TaggedEdgeCount C.targetEdgeTag
          (paperEmbeddingEdgeWord G phi) k)
  let term : PaperRealization G n → ℝ := fun phi =>
    ((paperEmbeddingEdgeWord G phi).map
      (fun e => paperEdgeSign w e.1 e.2)).prod
  have hSurvivor :
      paperR16ProjectedGraphEntry G n C.targetEdgeTag w
          (C.paperRow row) (C.paperCol col) =
        ∑ phi : {phi : PaperRealization G n // P phi}, term phi.1 := by
    rw [paperR16ProjectedGraphEntry_eq_survivorSum]
    calc
      (∑ phi : PaperRealization G n,
        if paperEntryCompatible G phi (C.paperRow row) (C.paperCol col) then
          if ∀ k : Fin G.edges,
              Odd (paperR16TaggedEdgeCount C.targetEdgeTag
                (paperEmbeddingEdgeWord G phi) k) then
            term phi else 0
        else 0) =
          ∑ phi : PaperRealization G n,
            if P phi then term phi else 0 := by
              apply Finset.sum_congr rfl
              intro phi _
              by_cases hc : paperEntryCompatible G phi
                (C.paperRow row) (C.paperCol col) <;>
              by_cases ho : ∀ k : Fin G.edges,
                Odd (paperR16TaggedEdgeCount C.targetEdgeTag
                  (paperEmbeddingEdgeWord G phi) k) <;>
              simp [P, hc, ho]
      _ = ∑ phi ∈ Finset.univ.filter P, term phi := by
        simp [Finset.sum_filter]
      _ = ∑ phi : {phi : PaperRealization G n // P phi}, term phi.1 := by
        exact Finset.sum_subtype _ (by simp) _
  have hTyped :
      paperRoleColoredBoundaryMatrix G dimension n C w row col =
        ∑ a : PaperRoleColorAssignment G dimension,
          if partiteBoundaryEntryCompatible a row col then
            C.varyingEdgeProduct w a else 0 := by
    unfold paperRoleColoredBoundaryMatrix
    simp_rw [C.paperEntryCompatible_globalRealization_iff]
    rfl
  calc
    paperR16ProjectedGraphEntry G n C.targetEdgeTag w
        (C.paperRow row) (C.paperCol col) =
        ∑ phi : {phi : PaperRealization G n // P phi}, term phi.1 := hSurvivor
    _ = ∑ x : {x : G.R16BoundaryFixingAutomorphism ×
          PaperRoleColorAssignment G dimension //
          partiteBoundaryEntryCompatible x.2 row col},
          term (C.coloredRealizationVarying x.1.1 x.1.2) := by
      symm
      exact Fintype.sum_equiv (C.survivorPairEquiv row col hNoIsolated)
        (fun x => term (C.coloredRealizationVarying x.1.1 x.1.2))
        (fun phi => term phi.1) (fun _ => rfl)
    _ = ∑ x : {x : G.R16BoundaryFixingAutomorphism ×
          PaperRoleColorAssignment G dimension //
          partiteBoundaryEntryCompatible x.2 row col},
          C.varyingEdgeProduct w x.1.2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (paperEmbeddingEdgeWord_product G n w
        (C.coloredRealizationVarying x.1.1 x.1.2)).trans
          (C.coloredRealizationVarying_edgeProduct x.1.1 w x.1.2)
    _ = ∑ x ∈ (Finset.univ.filter fun x :
          G.R16BoundaryFixingAutomorphism ×
            PaperRoleColorAssignment G dimension =>
          partiteBoundaryEntryCompatible x.2 row col),
          C.varyingEdgeProduct w x.2 := by
      exact (Finset.sum_subtype
        (p := fun x : G.R16BoundaryFixingAutomorphism ×
          PaperRoleColorAssignment G dimension =>
          partiteBoundaryEntryCompatible x.2 row col)
        (Finset.univ.filter (fun x :
          G.R16BoundaryFixingAutomorphism ×
            PaperRoleColorAssignment G dimension =>
          partiteBoundaryEntryCompatible x.2 row col))
        (by intro x; simp)
        (fun x => C.varyingEdgeProduct w x.2)).symm
    _ = ∑ x : G.R16BoundaryFixingAutomorphism ×
          PaperRoleColorAssignment G dimension,
          if partiteBoundaryEntryCompatible x.2 row col then
            C.varyingEdgeProduct w x.2 else 0 := by
      simp [Finset.sum_filter]
    _ = (Fintype.card G.R16BoundaryFixingAutomorphism : ℕ) •
          paperRoleColoredBoundaryMatrix G dimension n C w row col := by
      rw [hTyped, Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ]

/-- The compressed Walsh projection is pointwise the automorphism count
times the exact fixed-color typed matrix, for arbitrary role sizes. -/
theorem PaperRoleColoring.projectedCompressed_eq_aut_smul_typed
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (w : PaperNoise n) :
    (paperR16ProjectedGraphMatrix G n C.targetEdgeTag w).submatrix
        C.paperRowEmbedding C.paperColEmbedding =
      (Fintype.card G.R16BoundaryFixingAutomorphism : ℕ) •
        paperRoleColoredBoundaryMatrix G dimension n C w := by
  ext row col
  rw [Matrix.submatrix_apply, Matrix.smul_apply,
    paperR16ProjectedGraphMatrix_apply]
  exact C.projectedEntry_eq_aut_smul_typed hNoIsolated w row col

/-- In the paper's real-valued notation, the typed matrix is the real cast
of `partiteBoundaryMatrix` fed by the ambient sample's independent selected
cross-color signs. -/
theorem PaperRoleColoring.projectedCompressed_eq_aut_smul_readTyped
    {G : PaperShape} {dimension : Fin G.roles → ℕ} {n : ℕ}
    (C : PaperRoleColoring G dimension n)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (w : PaperNoise n) :
    (paperR16ProjectedGraphMatrix G n C.targetEdgeTag w).submatrix
        C.paperRowEmbedding C.paperColEmbedding =
      (Fintype.card G.R16BoundaryFixingAutomorphism : ℕ) •
        (fun row col =>
          ((partiteBoundaryMatrix G.toPartiteShape dimension
            (C.readJointEdgeSignSample w) row col : ℚ) : ℝ)) := by
  rw [C.projectedCompressed_eq_aut_smul_typed hNoIsolated w,
    C.coloredBoundaryMatrix_eq_readTyped w]
  rfl


end GraphMatrixReplica
