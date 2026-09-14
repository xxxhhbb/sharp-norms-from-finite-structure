import R6.FiniteMengerResidualProgram

/-! # Local vertex-capacity invariants for residual toggling

This file executes the vertex part of a type-valued residual edit program.
Roles crossed forward through an unused vertex are inserted; roles crossed
backwards through an occupied vertex are removed.  The transition premises
prove that additions are disjoint from the old used-role set and removals are
a subset of it.  Thus the toggled set is an honest unit-capacity vertex set,
with an exact cardinal formula.
-/

noncomputable section

namespace GraphMatrixReplica

namespace PartiteShape.VertexDisjointRightToLeftPaths

variable {G : PartiteShape} {s : ℕ}
variable {family : G.VertexDisjointRightToLeftPaths s}
variable {x z : ResidualNode G}

def ResidualStepData.addedVertex? {x y : ResidualNode G} :
    ResidualStepData family x y → Option (Fin G.roles)
  | .throughUnused (v := v) _ => some v
  | _ => none

def ResidualStepData.removedVertex? {x y : ResidualNode G} :
    ResidualStepData family x y → Option (Fin G.roles)
  | .backThroughUsed (v := v) _ => some v
  | _ => none

namespace ResidualProgram

def addedVertexRoles {x z : ResidualNode G} :
    family.ResidualProgram x z → Finset (Fin G.roles)
  | .finish _ => ∅
  | .step head tail =>
      match head.addedVertex? with
      | none => tail.addedVertexRoles
      | some v => insert v tail.addedVertexRoles

def removedVertexRoles {x z : ResidualNode G} :
    family.ResidualProgram x z → Finset (Fin G.roles)
  | .finish _ => ∅
  | .step head tail =>
      match head.removedVertex? with
      | none => tail.removedVertexRoles
      | some v => insert v tail.removedVertexRoles

theorem addedVertexRoles_disjoint_usedRoles
    (program : family.ResidualProgram x z) :
    Disjoint program.addedVertexRoles family.usedRoles := by
  induction program with
  | finish x => simp [addedVertexRoles]
  | step head tail ih =>
      cases head <;>
        simp_all [addedVertexRoles, ResidualStepData.addedVertex?]

theorem removedVertexRoles_subset_usedRoles
    (program : family.ResidualProgram x z) :
    program.removedVertexRoles ⊆ family.usedRoles := by
  induction program with
  | finish x => simp [removedVertexRoles]
  | step head tail ih =>
      cases head <;>
        simp_all [removedVertexRoles, ResidualStepData.removedVertex?,
          Finset.insert_subset_iff]

theorem addedVertexRoles_disjoint_removedVertexRoles
    (program : family.ResidualProgram x z) :
    Disjoint program.addedVertexRoles program.removedVertexRoles :=
  program.addedVertexRoles_disjoint_usedRoles.mono_right
    program.removedVertexRoles_subset_usedRoles

/-- Execute all vertex-capacity toggles. -/
def toggledUsedRoles (program : family.ResidualProgram x z) :
    Finset (Fin G.roles) :=
  (family.usedRoles \ program.removedVertexRoles) ∪
    program.addedVertexRoles

theorem mem_toggledUsedRoles_iff
    (program : family.ResidualProgram x z) (v : Fin G.roles) :
    v ∈ program.toggledUsedRoles ↔
      (v ∈ family.usedRoles ∧ v ∉ program.removedVertexRoles) ∨
        v ∈ program.addedVertexRoles := by
  simp [toggledUsedRoles]

theorem addedVertex_mem_toggledUsedRoles
    (program : family.ResidualProgram x z) {v : Fin G.roles}
    (hAdd : v ∈ program.addedVertexRoles) :
    v ∈ program.toggledUsedRoles := by
  rw [program.mem_toggledUsedRoles_iff]
  exact Or.inr hAdd

theorem removedVertex_not_mem_toggledUsedRoles
    (program : family.ResidualProgram x z) {v : Fin G.roles}
    (hRemove : v ∈ program.removedVertexRoles) :
    v ∉ program.toggledUsedRoles := by
  have hOld : v ∈ family.usedRoles :=
    program.removedVertexRoles_subset_usedRoles hRemove
  have hNotAdd : v ∉ program.addedVertexRoles := by
    intro hAdd
    exact Finset.disjoint_left.mp
      program.addedVertexRoles_disjoint_usedRoles hAdd hOld
  simp [toggledUsedRoles, hRemove, hNotAdd]

theorem untouchedVertex_mem_toggledUsedRoles_iff
    (program : family.ResidualProgram x z) {v : Fin G.roles}
    (hNotAdd : v ∉ program.addedVertexRoles)
    (hNotRemove : v ∉ program.removedVertexRoles) :
    v ∈ program.toggledUsedRoles ↔ v ∈ family.usedRoles := by
  simp [toggledUsedRoles, hNotAdd, hNotRemove]

/-- Exact unit-capacity cardinal update for the vertex set. -/
theorem toggledUsedRoles_card
    (program : family.ResidualProgram x z) :
    program.toggledUsedRoles.card =
      family.usedRoles.card - program.removedVertexRoles.card +
        program.addedVertexRoles.card := by
  have hDisjoint : Disjoint
      (family.usedRoles \ program.removedVertexRoles)
      program.addedVertexRoles :=
    (program.addedVertexRoles_disjoint_usedRoles.mono_right
      (Finset.sdiff_subset)).symm
  rw [toggledUsedRoles, Finset.card_union_of_disjoint hDisjoint,
    Finset.card_sdiff_of_subset program.removedVertexRoles_subset_usedRoles]

#print axioms addedVertexRoles_disjoint_usedRoles
#print axioms removedVertexRoles_subset_usedRoles
#print axioms toggledUsedRoles_card

end ResidualProgram

end PartiteShape.VertexDisjointRightToLeftPaths

end GraphMatrixReplica
