import R6.U2Assembly
import R6.C079DefectVectorCount

/-!
U3: exact rolewise-profile decomposition of the ACTUAL defect stratum.
The profile total is s*p + delta, not delta.
This module has not been executed in Lean in the return environment.
-/

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.C079U3
open C079U2

open Classical in
attribute [local instance] propDecidable

variable {G : PartiteShape} {p s delta : ℕ}

/-- The partition-data presentation of an actual replica state. -/
def asAdmissible (S : ReplicaState G p) : AdmissiblePartitionState G p :=
  ⟨S.partition, S.edgeParity, S.leftGlue, S.rightGlue⟩

@[simp] theorem asAdmissible_toReplicaState (S : ReplicaState G p) :
    (asAdmissible S).toReplicaState = S := by
  cases S
  rfl

@[simp] theorem asAdmissible_of_admissible (T : AdmissiblePartitionState G p) :
    asAdmissible T.toReplicaState = T := by
  cases T
  rfl

/-- The actual unshifted role profile. -/
def roleProfile (S : ReplicaState G p) (x : Fin G.roles) : ℕ :=
  (p + 1) - partitionBlockCount (S.partition x)

/-- Excess on an indexed actual path, computed from a role profile. -/
def pathExcess (p : ℕ) (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) (i : Fin s) : ℕ :=
  (∑ o : Fin (family.path i).vertexCount,
    d ((family.path i).vertexAt o)) - p

def onDefect (p : ℕ) (family : G.VertexDisjointRightToLeftPaths s)
    (d : Fin G.roles → ℕ) : ℕ :=
  ∑ i : Fin s, pathExcess p family d i

/-- Nonempty replicas force at least one quotient block, without evenness. -/
theorem one_le_blockCount (π : ReplicaPartition (p + 1)) :
    1 ≤ partitionBlockCount π := by
  classical
  change 0 < Fintype.card (Quotient π)
  exact Fintype.card_pos_iff.mpr
    ⟨Quotient.mk'' ((0 : Fin (p + 1)), false)⟩

theorem roleProfile_le (S : ReplicaState G p) (x : Fin G.roles) :
    roleProfile S x ≤ p := by
  have h := one_le_blockCount (S.partition x)
  unfold roleProfile
  omega

theorem totalDefect_le_role_mul (S : ReplicaState G p) :
    S.totalDefect ≤ G.roles * p := by
  have h : (∑ x : Fin G.roles, roleProfile S x) ≤
      ∑ _x : Fin G.roles, p :=
    Finset.sum_le_sum (fun x _ => roleProfile_le S x)
  simpa [roleProfile, ReplicaState.totalDefect] using h

theorem blockTarget_add_baseline (family : G.VertexDisjointRightToLeftPaths s) :
    c079BlockTarget G p s + s * p = (p + 1) * G.roles := by
  have hs := family.pathCount_le_roles
  unfold c079BlockTarget
  calc
    (p + 1) * (G.roles - s) + s + s * p =
        (p + 1) * ((G.roles - s) + s) := by ring
    _ = (p + 1) * G.roles := by rw [Nat.sub_add_cancel hs]

/-- The exact offset is established before forming any finite profile type. -/
theorem stratum_totalDefect
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s)
    (T : C079DefectStratum G p s delta) :
    T.1.toReplicaState.totalDefect = s * p + delta := by
  have hBalance := T.1.toReplicaState.totalDefect_add_totalBlockCount hCovered
  have hTarget := blockTarget_add_baseline (p := p) family
  have hStratum := T.2
  omega

theorem defectFiber_totalDefect {d : Fin G.roles → ℕ}
    (S : DefectFiber G p d) : S.1.totalDefect = ∑ x, d x := by
  unfold ReplicaState.totalDefect
  exact Finset.sum_congr rfl (fun x _ => S.2 x)

theorem defectFiber_onDefect {d : Fin G.roles → ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) :
    S.1.c079OnBackboneDefect family = onDefect p family d := by
  unfold ReplicaState.c079OnBackboneDefect onDefect
  apply Finset.sum_congr rfl
  intro i _
  rw [(family.path i).vertexDefectSum_eq_sum_occurrences]
  unfold pathExcess
  congr 1
  exact Finset.sum_congr rfl (fun o _ => S.2 ((family.path i).vertexAt o))

theorem defectFiber_offDefect {d : Fin G.roles → ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) :
    S.1.c079OffBackboneDefect family = offDefect family d := by
  unfold ReplicaState.c079OffBackboneDefect offDefect
  exact Finset.sum_congr rfl (fun x _ => S.2 x)

/-- The off-backbone total is automatically in the numerical budget range. -/
theorem offDefect_le_role_mul {d : Fin G.roles → ℕ}
    (family : G.VertexDisjointRightToLeftPaths s)
    (S : DefectFiber G p d) :
    offDefect family d ≤ G.roles * p := by
  calc
    offDefect family d ≤ ∑ x : Fin G.roles, d x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = S.1.totalDefect := (defectFiber_totalDefect S).symm
    _ ≤ G.roles * p := totalDefect_le_role_mul S.1

/-- No truncation ambiguity: a fixed profile of total s*p+delta has the
actual excess split delta = onDefect + offDefect. -/
theorem defectFiber_excess_split {d : Fin G.roles → ℕ}
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hTotal : (∑ x, d x) = s * p + delta)
    (S : DefectFiber G p d) :
    delta = onDefect p family d + offDefect family d := by
  have hDefect := c079StateDefect_eq_totalDefect_sub_paths
    hCovered family (asAdmissible S.1)
  have hSplit := c079StateDefect_eq_onBackbone_add_offBackbone
    hCovered family (asAdmissible S.1)
  simp only [asAdmissible_toReplicaState] at hDefect hSplit
  rw [defectFiber_totalDefect S, hTotal] at hDefect
  rw [defectFiber_onDefect family S, defectFiber_offDefect family S] at hSplit
  omega

/-- Exact finite profile index, retaining the path baseline. -/
abbrev StratumProfile (G : PartiteShape) (p s delta : ℕ) :=
  C079DefectVector G.roles (s * p + delta)

/-- Inverse-side membership uses block balance, not a counting premise. -/
theorem profile_gives_stratum
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s)
    (d : StratumProfile G p s delta) (S : DefectFiber G p d.1) :
    (asAdmissible S.1).toReplicaState.totalBlockCount + delta =
      c079BlockTarget G p s := by
  have hBalance := S.1.totalDefect_add_totalBlockCount hCovered
  have hTotal := defectFiber_totalDefect S
  rw [d.2] at hTotal
  have hTarget := blockTarget_add_baseline (p := p) family
  simp only [asAdmissible_toReplicaState]
  omega

/-- Exact bijection onto ALL role profiles with the correct total. -/
def stratumProfileEquiv
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s) :
    C079DefectStratum G p s delta ≃
      Σ d : StratumProfile G p s delta, DefectFiber G p d.1 where
  toFun T :=
    ⟨⟨roleProfile T.1.toReplicaState,
       stratum_totalDefect hCovered family T⟩,
      ⟨T.1.toReplicaState, fun _ => rfl⟩⟩
  invFun z :=
    ⟨asAdmissible z.2.1, profile_gives_stratum hCovered family z.1 z.2⟩
  left_inv T := by
    apply Subtype.ext
    exact asAdmissible_of_admissible T.1
  right_inv z := by
    rcases z with ⟨⟨d, hd⟩, ⟨S, hS⟩⟩
    have he : roleProfile S = d := funext hS
    cases he
    rfl

/-- The exact coefficient is the sum of the actual fixed-profile fibers. -/
theorem stratum_card_eq_sum_profiles
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s) :
    Fintype.card (C079DefectStratum G p s delta) =
      ∑ d : StratumProfile G p s delta,
        Fintype.card (DefectFiber G p d.1) := by
  rw [Fintype.card_congr (stratumProfileEquiv hCovered family)]
  exact Fintype.card_sigma

theorem coefficient_eq_sum_profiles
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s)
    (delta : Fin (c079BlockTarget G p s + 1)) :
    c079DefectCoefficient G p s delta =
      ∑ d : StratumProfile G p s delta.1,
        Fintype.card (DefectFiber G p d.1) := by
  exact stratum_card_eq_sum_profiles hCovered family

/-- The only entropy premise is the numerical feasible-total range. -/
theorem profile_card_le (hTotal : s * p + delta ≤ G.roles * p) :
    Fintype.card (StratumProfile G p s delta) ≤
      2 ^ (G.roles * (p + 1)) := by
  have h := c079DefectVector_card_le_role_pow G.roles
    (s * p + delta) G.roles (Nat.le_refl _)
  apply h.trans
  apply Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
  nlinarith

/-- Nonemptiness supplies the feasible-total range; it is not assumed as
an additional structural condition on the theorem. -/
theorem profile_card_le_of_nonempty_stratum
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hNonempty : Nonempty (C079DefectStratum G p s delta)) :
    Fintype.card (StratumProfile G p s delta) ≤
      2 ^ (G.roles * (p + 1)) := by
  obtain ⟨T⟩ := hNonempty
  apply profile_card_le
  rw [← stratum_totalDefect hCovered family T]
  exact totalDefect_le_role_mul T.1.toReplicaState

/-- Beyond the sharper feasible range, the actual stratum is empty. -/
theorem stratum_card_eq_zero_of_total_gt
    (hCovered : ∀ x : Fin G.roles, G.RoleCovered x)
    (family : G.VertexDisjointRightToLeftPaths s)
    (hTotal : G.roles * p < s * p + delta) :
    Fintype.card (C079DefectStratum G p s delta) = 0 := by
  letI : IsEmpty (C079DefectStratum G p s delta) := ⟨fun T => by
    have h := totalDefect_le_role_mul T.1.toReplicaState
    rw [stratum_totalDefect hCovered family T] at h
    omega⟩
  simp

#print axioms stratumProfileEquiv
#print axioms coefficient_eq_sum_profiles
#print axioms defectFiber_excess_split
#print axioms profile_card_le_of_nonempty_stratum
#print axioms stratum_card_eq_zero_of_total_gt
end GraphMatrixReplica.C079U3
