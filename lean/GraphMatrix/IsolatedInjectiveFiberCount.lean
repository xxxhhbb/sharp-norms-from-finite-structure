import GraphMatrix.IsolatedRoleMarginalization
import Mathlib.Data.Fintype.CardEmbedding

/-! # Exact injective isolated-coordinate fibers

Fixing an assignment on the covered roles leaves precisely an embedding of
the isolated roles into the labels not already used by the covered
assignment.  Consequently, an injective covered assignment has
`(n - |covered|).descFactorial |isolated|` injective extensions, while a
non-injective covered assignment has none.  The uniform upper bound
`n ^ |isolated|` is recorded independently of either case.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- Labels already used by a fixed covered assignment. -/
def coveredAssignmentImage
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {isolated : Finset α}
    (covered : PaperVisibleTuple n (coveredRoles isolated)) : Finset (Fin n) :=
  Finset.univ.image covered

/-- Labels still available after fixing a covered assignment. -/
def freshLabelsForCovered
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {isolated : Finset α}
    (covered : PaperVisibleTuple n (coveredRoles isolated)) : Finset (Fin n) :=
  Finset.univ \ coveredAssignmentImage covered

/-- Hidden assignments whose merge with the fixed covered assignment is
globally injective. -/
def InjectiveHiddenFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated)) :=
  { hidden : PaperVisibleTuple n isolated //
      Function.Injective
        (mergeCoveredIsolatedAssignment isolated covered hidden) }

noncomputable instance injectiveHiddenFiberFintype
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated)) :
    Fintype (InjectiveHiddenFiber isolated covered) := by
  classical
  apply Fintype.subtype
    (Finset.univ.filter fun hidden : PaperVisibleTuple n isolated =>
      Function.Injective
        (mergeCoveredIsolatedAssignment isolated covered hidden))
  intro hidden
  simp

/-- Restricting an injective merge to the covered roles remains injective. -/
theorem injective_covered_of_injective_merge
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hidden : PaperVisibleTuple n isolated)
    (hMerge : Function.Injective
      (mergeCoveredIsolatedAssignment isolated covered hidden)) :
    Function.Injective covered := by
  intro x y hxy
  apply Subtype.ext
  apply hMerge
  simpa using hxy

/-- When the covered assignment is injective, a globally injective hidden
fiber is exactly an embedding of the isolated roles into the fresh labels. -/
def injectiveHiddenFiberEquivFreshEmbedding
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hCovered : Function.Injective covered) :
    InjectiveHiddenFiber isolated covered ≃
      (({x : α // x ∈ isolated}) ↪
        {y : Fin n // y ∈ freshLabelsForCovered covered}) where
  toFun fiber :=
    { toFun := fun x =>
        ⟨fiber.1 x, by
          apply Finset.mem_sdiff.2
          refine ⟨Finset.mem_univ _, ?_⟩
          intro hUsed
          rcases Finset.mem_image.mp hUsed with ⟨y, _hyUniv, hy⟩
          have hRoles : x.1 = y.1 := fiber.2 (by
            rw [mergeCoveredIsolatedAssignment_apply_isolated
              isolated covered fiber.1 x.1 x.2]
            rw [mergeCoveredIsolatedAssignment_apply_covered
              isolated covered fiber.1 y.1 y.2]
            exact hy.symm)
          have hNotIsolated : y.1 ∉ isolated :=
            (Finset.mem_sdiff.mp y.2).2
          exact hNotIsolated (hRoles ▸ x.2)⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        apply fiber.2
        simpa using congrArg Subtype.val hxy }
  invFun embedding :=
    ⟨fun x => (embedding x).1, by
      intro x y hxy
      by_cases hx : x ∈ isolated
      · by_cases hy : y ∈ isolated
        · have hEmbedding : embedding ⟨x, hx⟩ = embedding ⟨y, hy⟩ := by
            apply Subtype.ext
            have hValues := hxy
            rw [mergeCoveredIsolatedAssignment_apply_isolated
              isolated covered (fun z => (embedding z).1) x hx,
              mergeCoveredIsolatedAssignment_apply_isolated
              isolated covered (fun z => (embedding z).1) y hy] at hValues
            exact hValues
          exact congrArg Subtype.val (embedding.injective hEmbedding)
        · have hFresh :=
            (Finset.mem_sdiff.mp (embedding ⟨x, hx⟩).2).2
          exfalso
          apply hFresh
          apply Finset.mem_image.mpr
          refine ⟨⟨y, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hy⟩⟩,
            Finset.mem_univ _, ?_⟩
          have hValues := hxy
          rw [mergeCoveredIsolatedAssignment_apply_isolated
              isolated covered (fun z => (embedding z).1) x hx,
            mergeCoveredIsolatedAssignment_apply_covered
              isolated covered (fun z => (embedding z).1) y
                (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hy⟩)] at hValues
          exact hValues.symm
      · by_cases hy : y ∈ isolated
        · have hFresh :=
            (Finset.mem_sdiff.mp (embedding ⟨y, hy⟩).2).2
          exfalso
          apply hFresh
          apply Finset.mem_image.mpr
          refine ⟨⟨x, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩⟩,
            Finset.mem_univ _, ?_⟩
          have hValues := hxy
          rw [mergeCoveredIsolatedAssignment_apply_covered
              isolated covered (fun z => (embedding z).1) x
                (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩),
            mergeCoveredIsolatedAssignment_apply_isolated
              isolated covered (fun z => (embedding z).1) y hy] at hValues
          exact hValues
        · have hCoveredValues :
              covered ⟨x, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩⟩ =
                covered ⟨y, Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hy⟩⟩ := by
            have hValues := hxy
            rw [mergeCoveredIsolatedAssignment_apply_covered
                isolated covered (fun z => (embedding z).1) x
                  (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩),
              mergeCoveredIsolatedAssignment_apply_covered
                isolated covered (fun z => (embedding z).1) y
                  (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hy⟩)] at hValues
            exact hValues
          exact congrArg Subtype.val (hCovered hCoveredValues)⟩
  left_inv fiber := by
    apply Subtype.ext
    funext x
    rfl
  right_inv embedding := by
    apply Function.Embedding.ext
    intro x
    apply Subtype.ext
    rfl

/-- An injective covered assignment uses exactly one label per covered role. -/
theorem card_freshLabelsForCovered
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hCovered : Function.Injective covered) :
    (freshLabelsForCovered covered).card =
      n - (coveredRoles isolated).card := by
  classical
  have hSubset : coveredAssignmentImage covered ⊆ (Finset.univ : Finset (Fin n)) :=
    Finset.subset_univ _
  rw [freshLabelsForCovered, Finset.card_sdiff,
    Finset.inter_eq_left.2 hSubset]
  simp [coveredAssignmentImage,
    Finset.card_image_of_injective _ hCovered]

/-- Exact injective-extension count for an injective covered assignment. -/
theorem card_injectiveHiddenFiber_of_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hCovered : Function.Injective covered) :
    Fintype.card (InjectiveHiddenFiber isolated covered) =
      (n - (coveredRoles isolated).card).descFactorial isolated.card := by
  classical
  calc
    Fintype.card (InjectiveHiddenFiber isolated covered) =
        Fintype.card
          (({x : α // x ∈ isolated}) ↪
            {y : Fin n // y ∈ freshLabelsForCovered covered}) :=
      Fintype.card_congr
        (injectiveHiddenFiberEquivFreshEmbedding isolated covered hCovered)
    _ = (Fintype.card {y : Fin n //
          y ∈ freshLabelsForCovered covered}).descFactorial
          (Fintype.card {x : α // x ∈ isolated}) :=
      Fintype.card_embedding_eq
    _ = (n - (coveredRoles isolated).card).descFactorial isolated.card := by
      rw [Fintype.card_coe, Fintype.card_coe,
        card_freshLabelsForCovered isolated covered hCovered]

/-- A non-injective covered assignment has no globally injective extension. -/
theorem card_injectiveHiddenFiber_of_not_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (hCovered : ¬ Function.Injective covered) :
    Fintype.card (InjectiveHiddenFiber isolated covered) = 0 := by
  classical
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun fiber => hCovered
    (injective_covered_of_injective_merge isolated covered fiber.1 fiber.2)⟩

/-- Complete piecewise exact count. -/
theorem card_injectiveHiddenFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated)) :
    Fintype.card (InjectiveHiddenFiber isolated covered) =
      if Function.Injective covered then
        (n - (coveredRoles isolated).card).descFactorial isolated.card
      else 0 := by
  classical
  by_cases hCovered : Function.Injective covered
  · simp [hCovered,
      card_injectiveHiddenFiber_of_injective isolated covered hCovered]
  · simp [hCovered,
      card_injectiveHiddenFiber_of_not_injective isolated covered hCovered]

/-- Every injective hidden fiber is contained in the full hidden-assignment
space, giving the uniform power bound without a case split. -/
theorem card_injectiveHiddenFiber_le_pow
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated)) :
    Fintype.card (InjectiveHiddenFiber isolated covered) ≤
      n ^ isolated.card := by
  calc
    Fintype.card (InjectiveHiddenFiber isolated covered) ≤
        Fintype.card (PaperVisibleTuple n isolated) :=
      Fintype.card_le_of_embedding
        ⟨Subtype.val, Subtype.val_injective⟩
    _ = n ^ isolated.card := card_isolatedAssignments n isolated

/-- Scalar interface: summing one core value over the admissible injective
fiber multiplies it by the exact fiber cardinality. -/
theorem sum_injectiveHiddenFiber_const
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (core : ℝ) :
    (∑ _fiber : InjectiveHiddenFiber isolated covered, core) =
      (Fintype.card (InjectiveHiddenFiber isolated covered) : ℝ) * core := by
  simp

/-- Equivalent all-hidden-assignments interface: the global-injectivity
indicator turns the hidden sum into the exact scalar fiber count. -/
theorem sum_hidden_if_merge_injective_eq_card_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    (core : ℝ) :
    (∑ hidden : PaperVisibleTuple n isolated,
        if Function.Injective
            (mergeCoveredIsolatedAssignment isolated covered hidden) then
          core
        else 0) =
      (Fintype.card (InjectiveHiddenFiber isolated covered) : ℝ) * core := by
  classical
  let p : PaperVisibleTuple n isolated → Prop := fun hidden =>
    Function.Injective
      (mergeCoveredIsolatedAssignment isolated covered hidden)
  have hCard :
      Fintype.card (InjectiveHiddenFiber isolated covered) =
        (Finset.univ.filter p).card := by
    simpa only [InjectiveHiddenFiber, p] using
      (@Fintype.card_subtype
        (PaperVisibleTuple n isolated) inferInstance p
        (injectiveHiddenFiberFintype isolated covered) (Classical.decPred p))
  calc
    (∑ hidden : PaperVisibleTuple n isolated,
        if Function.Injective
            (mergeCoveredIsolatedAssignment isolated covered hidden) then
          core
        else 0) =
        ∑ hidden ∈ Finset.univ with p hidden, core := by
      rw [Finset.sum_filter]
    _ = ((Finset.univ.filter p).card : ℝ) * core := by simp
    _ = (Fintype.card (InjectiveHiddenFiber isolated covered) : ℝ) * core := by
      rw [hCard]

/-- The isolated injective scalar multiplying a nonnegative core is bounded
by `n ^ |isolated|` times that core. -/
theorem injectiveHiddenFiber_card_mul_le_pow_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (isolated : Finset α)
    (covered : PaperVisibleTuple n (coveredRoles isolated))
    {core : ℝ} (hCore : 0 ≤ core) :
    (Fintype.card (InjectiveHiddenFiber isolated covered) : ℝ) * core ≤
      (n ^ isolated.card : ℝ) * core := by
  exact mul_le_mul_of_nonneg_right
    (mod_cast card_injectiveHiddenFiber_le_pow isolated covered) hCore


end GraphMatrixReplica
