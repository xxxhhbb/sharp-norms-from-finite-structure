import R6.U3RecordSemantics
import R6.C079CompatibleMatchingSeedCount
import R6.C079MatchingSwitchDescentCore
import R6.C079PartitionInterval

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica.C079U3
open C079U2

theorem root_matching_refines_of_edgeParity {m : ℕ}
    (π : ReplicaPartition m) (σ : C079MatchingPartition m)
    (h : EdgeParityCompatible π σ.1) : PartitionCoarsens π σ.1 := by
  obtain ⟨ρ, hπ, hσ⟩ := exists_perfectMatching_coarsened_by_edgeEndpoints π σ.1 h
  have heq : σ = ρ.toC079MatchingPartition := by
    by_contra hne
    obtain ⟨a, b, hab, hnot⟩ := c079_exists_target_pair_not_current σ ρ.toC079MatchingPartition hne
    exact hnot (hσ a b hab)
  rw [heq]
  exact hπ

theorem root_even_of_matching_refinement {m : ℕ}
    (π : ReplicaPartition m) (σ : C079MatchingPartition m)
    (h : PartitionCoarsens π σ.1) : IsEvenPartition π := by
  obtain ⟨ρ, hρ⟩ := σ.2
  apply pairEquivCoarsens_evenPartition π ρ.pairingEquiv
  intro k
  apply h
  rw [← hρ]
  change (ρ.pairingEquiv.symm (ρ.pairingEquiv (k, false))).1 =
    (ρ.pairingEquiv.symm (ρ.pairingEquiv (k, true))).1
  simp

theorem root_edgeParity_symm {m : ℕ} {π σ : ReplicaPartition m}
    (h : EdgeParityCompatible π σ) : EdgeParityCompatible σ π := by
  intro a
  have heq : partitionMeetCell σ π a = partitionMeetCell π σ a := by
    classical
    ext b
    simp only [partitionMeetCell, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  change Even (partitionMeetCell σ π a).card
  rw [heq]
  exact h a

theorem root_state_edgeParity_incident {G : PartiteShape} {p : ℕ}
    (T : ReplicaState G p) (e : Fin G.edges) (x y : Fin G.roles)
    (hxy : x ≠ y) (hx : G.EdgeIncident e x) (hy : G.EdgeIncident e y) :
    EdgeParityCompatible (T.partition x) (T.partition y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hxy rfl).elim
  · exact T.edgeParity e
  · exact root_edgeParity_symm (T.edgeParity e)
  · exact (hxy rfl).elim

variable {G : PartiteShape} {p s : ℕ}
  {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
  {B : PathFiber p family d}
  {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}

theorem root_seed_refines_neighbor (seed : SeedFiber B forward)
    (c : G.C079CutComponent family.backboneRoles)
    (x : Fin G.roles) (hx : x ∈ backboneNeighbors family c) :
    PartitionCoarsens (repairedAt B forward x) (seed.1 c).1 := by
  classical
  obtain ⟨hxBack, y, hy, e, hex, hey⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyOff, hyComp⟩ := (G.mem_c079ComponentRoles_iff family.backboneRoles c y).1 hy
  obtain ⟨T, hT⟩ := seedRecord_has_actual_state seed
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact hyOff hxBack
  have hpar := root_state_edgeParity_incident T e x y hxy hex hey
  have hxT : T.partition x = repairedAt B forward x := by
    rw [hT]
    exact normalizedRecord_backbone seed x hxBack
  have hc : G.c079OffBackboneComponent family y hyOff = c := hyComp
  have hyT : T.partition y = (seed.1 c).1 := by
    rw [hT]
    simp only [normalizedRecord, dif_neg hyOff, seedRecord, hc]
  rw [hxT, hyT] at hpar
  exact root_matching_refines_of_edgeParity _ _ hpar

/-- Actual validity supplies the refinement; no compatibility assumption is added. -/
theorem root_seed_refines_neighborMeet (seed : SeedFiber B forward)
    (c : G.C079CutComponent family.backboneRoles) :
    PartitionCoarsens (neighborMeet B forward c) (seed.1 c).1 := by
  classical
  change (seed.1 c).1 ≤ (backboneNeighbors family c).inf (repairedAt B forward)
  apply Finset.le_inf
  intro x hx
  exact root_seed_refines_neighbor seed c x hx

theorem root_neighborMeet_even_of_seed (seed : SeedFiber B forward)
    (c : G.C079CutComponent family.backboneRoles) :
    IsEvenPartition (neighborMeet B forward c) :=
  root_even_of_matching_refinement _ _ (root_seed_refines_neighborMeet seed c)

/-- U1 also bounds an empty compatible-seed type, without an external evenness premise. -/
theorem root_compatibleSeed_card_le {m : ℕ} (θ : ReplicaPartition m) :
    Nat.card (C079CompatibleMatchingSeed θ) ≤
      (2 * m) ^ (m - partitionBlockCount θ) := by
  classical
  by_cases h : Nonempty (C079CompatibleMatchingSeed θ)
  · obtain ⟨σ⟩ := h
    exact c079_compatibleSeed_card_le θ
      (root_even_of_matching_refinement θ σ.1 σ.2)
  · letI : IsEmpty (C079CompatibleMatchingSeed θ) := not_nonempty_iff.mp h
    simp

local instance : Fintype (FreeComponent family) := Fintype.ofFinite _

/-- The actual SeedFiber injects into independent compatible-matching choices.
This is a counting injection, with no probabilistic independence assertion. -/
theorem root_seedFiber_card_le_product
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) :
    Nat.card (SeedFiber B forward) ≤
      ∏ c : FreeComponent family,
        (2 * (p + 1)) ^ ((p + 1) - partitionBlockCount (neighborMeet B forward c.1)) := by
  classical
  letI : Fintype (SeedFiber B forward) := Fintype.ofFinite _
  letI : ∀ c : FreeComponent family,
      Fintype (C079CompatibleMatchingSeed (neighborMeet B forward c.1)) :=
    fun _ => Fintype.ofFinite _
  let f : SeedFiber B forward →
      ((c : FreeComponent family) → C079CompatibleMatchingSeed (neighborMeet B forward c.1)) :=
    fun seed c => ⟨seed.1 c.1, root_seed_refines_neighborMeet seed c.1⟩
  have hf : Function.Injective f := by
    intro seed seed' h
    apply freeSeedRestriction_injective B forward
    funext c
    exact congrArg Subtype.val (congrFun h c)
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (SeedFiber B forward) ≤
        Fintype.card ((c : FreeComponent family) →
          C079CompatibleMatchingSeed (neighborMeet B forward c.1)) :=
      Fintype.card_le_of_injective f hf
    _ = ∏ c : FreeComponent family,
        Fintype.card (C079CompatibleMatchingSeed (neighborMeet B forward c.1)) := Fintype.card_pi
    _ ≤ _ := by
      apply Finset.prod_le_prod'
      intro c _
      simpa only [Nat.card_eq_fintype_card] using
        root_compatibleSeed_card_le (neighborMeet B forward c.1)

def rootSeedEntropy (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) : ℕ :=
  ∑ c : FreeComponent family,
    ((p + 1) - partitionBlockCount (neighborMeet B forward c.1))

theorem root_freeComponent_card_le_roles
    (family : G.VertexDisjointRightToLeftPaths s) :
    Fintype.card (FreeComponent family) ≤ G.roles := by
  classical
  have hSub : Fintype.card (FreeComponent family) ≤
      Fintype.card (G.C079CutComponent family.backboneRoles) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hSurj : Function.Surjective
      (G.c079CutGraph family.backboneRoles).connectedComponentMk := by
    intro c
    obtain ⟨v, rfl⟩ := Quot.exists_rep c
    exact ⟨v, rfl⟩
  have hQuot : Fintype.card (G.C079CutComponent family.backboneRoles) ≤
      Fintype.card {v : Fin G.roles // v ∉ family.backboneRoles} :=
    Fintype.card_le_of_surjective _ hSurj
  have hRoles : Fintype.card {v : Fin G.roles // v ∉ family.backboneRoles} ≤
      G.roles := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun v : {v : Fin G.roles // v ∉ family.backboneRoles} => v.1)
      Subtype.val_injective
  exact hSub.trans (hQuot.trans hRoles)

/-- The crude entropy bound used to absorb powers of two. The sharper
active-component bound remains a separate geometric obligation. -/
theorem root_seedEntropy_le_roles_mul_order
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) :
    rootSeedEntropy B forward ≤ G.roles * p := by
  classical
  have hEach (c : FreeComponent family) :
      (p + 1) - partitionBlockCount (neighborMeet B forward c.1) ≤ p := by
    have hOne := one_le_c079TraceJoinRank (neighborMeet B forward c.1)
    have hRank := c079TraceJoinRank_le_blockCount (neighborMeet B forward c.1)
    omega
  calc
    rootSeedEntropy B forward ≤ ∑ _c : FreeComponent family, p :=
      Finset.sum_le_sum (fun c _ => hEach c)
    _ = Fintype.card (FreeComponent family) * p := by simp
    _ ≤ G.roles * p := Nat.mul_le_mul_right p (root_freeComponent_card_le_roles family)

theorem root_seedFiber_card_le_entropy
    (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) :
    Nat.card (SeedFiber B forward) ≤ (2 * (p + 1)) ^ rootSeedEntropy B forward := by
  have h := root_seedFiber_card_le_product B forward
  rw [Finset.prod_pow_eq_pow_sum] at h
  exact h

#print axioms root_seed_refines_neighbor
#print axioms root_seed_refines_neighborMeet
#print axioms root_neighborMeet_even_of_seed
#print axioms root_compatibleSeed_card_le
#print axioms root_seedFiber_card_le_product
#print axioms root_freeComponent_card_le_roles
#print axioms root_seedEntropy_le_roles_mul_order
#print axioms root_seedFiber_card_le_entropy

end GraphMatrixReplica.C079U3
