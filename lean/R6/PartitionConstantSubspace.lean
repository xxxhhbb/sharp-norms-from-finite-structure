import R6.ReplicaPartitionState
import R6.IntersectionDistanceMetric
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Functions constant on the blocks of a replica partition

The quotient-function space is linearly equivalent to the subspace of replica
vectors that are constant on every partition block. Consequently this
subspace has dimension equal to the number of blocks. This is the bridge from
the partition state to the linear-algebra metric used in C078.
-/

noncomputable section

namespace GraphMatrixReplica

variable {K : Type*} [DivisionRing K]

/-- Replica vectors constant on every equivalence class of the partition. -/
def partitionConstantSubspace {p : ℕ} (pi : ReplicaPartition p) :
    Submodule K (Replica p → K) where
  carrier := {f | ∀ a b, pi.r a b → f a = f b}
  zero_mem' := by
    intro a b _
    rfl
  add_mem' := by
    intro f g hf hg a b hab
    change f a + g a = f b + g b
    rw [hf a b hab, hg a b hab]
  smul_mem' := by
    intro c f hf a b hab
    change c * f a = c * f b
    rw [hf a b hab]

@[simp] theorem mem_partitionConstantSubspace_iff
    {p : ℕ} (pi : ReplicaPartition p) (f : Replica p → K) :
    f ∈ partitionConstantSubspace (K := K) pi ↔
      ∀ a b, pi.r a b → f a = f b := by
  rfl

/-- Pull a function on quotient blocks back to the replicas. -/
def quotientFunctionToConstant {p : ℕ} (pi : ReplicaPartition p) :
    (Quotient pi → K) →ₗ[K] partitionConstantSubspace (K := K) pi where
  toFun := fun g =>
    ⟨fun a => g (Quotient.mk'' a), fun a b hab =>
      congrArg g (Quotient.sound hab)⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c f
    apply Subtype.ext
    rfl

theorem quotientFunctionToConstant_injective
    {p : ℕ} (pi : ReplicaPartition p) :
    Function.Injective (quotientFunctionToConstant (K := K) pi) := by
  intro f g h
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  exact congrArg (fun z => z.1 a) h

theorem quotientFunctionToConstant_surjective
    {p : ℕ} (pi : ReplicaPartition p) :
    Function.Surjective (quotientFunctionToConstant (K := K) pi) := by
  intro f
  let g : Quotient pi → K :=
    Quotient.lift f.1 (fun a b hab => f.2 a b hab)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  funext a
  rfl

/-- Linear equivalence between block functions and constant-on-block replica
vectors. -/
def quotientFunctionLinearEquivConstant
    {p : ℕ} (pi : ReplicaPartition p) :
    (Quotient pi → K) ≃ₗ[K] partitionConstantSubspace (K := K) pi :=
  LinearEquiv.ofBijective (quotientFunctionToConstant (K := K) pi)
    ⟨quotientFunctionToConstant_injective (K := K) pi,
      quotientFunctionToConstant_surjective (K := K) pi⟩

/-- The dimension of the constant-on-block subspace is exactly the number of
partition blocks. -/
theorem finrank_partitionConstantSubspace_eq_blockCount
    {p : ℕ} (pi : ReplicaPartition p) :
    Module.finrank K (partitionConstantSubspace (K := K) pi) =
      partitionBlockCount pi := by
  classical
  calc
    Module.finrank K (partitionConstantSubspace (K := K) pi) =
        Module.finrank K (Quotient pi → K) :=
      (quotientFunctionLinearEquivConstant (K := K) pi).finrank_eq.symm
    _ = Fintype.card (Quotient pi) :=
      Module.finrank_fintype_fun_eq_card K
    _ = partitionBlockCount pi := by
      rfl

#print axioms quotientFunctionLinearEquivConstant
#print axioms finrank_partitionConstantSubspace_eq_blockCount

end GraphMatrixReplica
