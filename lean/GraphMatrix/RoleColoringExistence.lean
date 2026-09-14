import GraphMatrix.RoleColoredPartiteBridge

/-! # Finite existence of disjoint role colors

The C027 reduction partitions an ambient label set into one color class per
shape role.  This file supplies the finite combinatorial existence statement
needed by the exact entry bridge: any role dimensions whose total is at most
the ambient size have pairwise disjoint embeddings.  It also packages the
uniform floor-size choice `n / G.roles`, including the zero-role edge case.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Disjoint role colors exist whenever their total requested cardinality fits
inside the ambient finite label set. -/
def paperRoleColoringOfTotalDimensionLE
    (G : PaperShape) (dimension : Fin G.roles → ℕ) (n : ℕ)
    (hTotal : (∑ v : Fin G.roles, dimension v) ≤ n) :
    PaperRoleColoring G dimension n := by
  classical
  have hCard :
      Fintype.card (Σ v : Fin G.roles, Fin (dimension v)) ≤
        Fintype.card (Fin n) := by
    simpa [Fintype.card_sigma] using hTotal
  let E : (Σ v : Fin G.roles, Fin (dimension v)) ↪ Fin n :=
    (Function.Embedding.nonempty_of_card_le hCard).some
  exact {
    embedding := fun v => {
      toFun := fun a => E ⟨v, a⟩
      inj' := by
        intro a b hab
        have hsigma : (⟨v, a⟩ : Σ u, Fin (dimension u)) = ⟨v, b⟩ :=
          E.injective hab
        exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
    }
    disjoint := by
      intro v w hvw a b hab
      have hsigma : (⟨v, a⟩ : Σ u, Fin (dimension u)) = ⟨w, b⟩ :=
        E.injective hab
      exact hvw (congrArg Sigma.fst hsigma)
  }

/-- The constant floor-size vector fits in the ambient set. -/
theorem uniformPaperRoleDimension_total_le (G : PaperShape) (n : ℕ) :
    (∑ _v : Fin G.roles, n / G.roles) ≤ n := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]
  exact Nat.mul_div_le n G.roles

/-- Canonical balanced-enough role colors with every class of size
`floor (n / G.roles)`. -/
def uniformPaperRoleColoring (G : PaperShape) (n : ℕ) :
    PaperRoleColoring G (fun _ : Fin G.roles => n / G.roles) n :=
  paperRoleColoringOfTotalDimensionLE G
    (fun _ : Fin G.roles => n / G.roles) n
    (uniformPaperRoleDimension_total_le G n)


end GraphMatrixReplica
