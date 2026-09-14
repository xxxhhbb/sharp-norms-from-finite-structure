import GraphMatrix.Counting.Bounds.SeedLayerGeometry
import GraphMatrix.Counting.Bounds.ForwardWordBudget
import GraphMatrix.Counting.ReplicaIntervalLayers

noncomputable section
open scoped BigOperators
namespace GraphMatrixReplica.ReplicaCounting
open ReplicaEncoding
attribute [local instance] Classical.propDecidable

variable {G : PartiteShape} {p s : ℕ}
  {family : G.VertexDisjointRightToLeftPaths s} {d : Fin G.roles → ℕ}
  {B : PathFiber p family d}
  {forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)}

theorem main_seedEntropy_eq_sum_crossing (seed : SeedFiber B forward) :
    mainSeedEntropy B forward = ∑ k ∈ Finset.Icc 1 p,
      Nat.card (CrossingFreeComponent B forward k) := by
  classical
  let ell := fun c : FreeComponent family => c079PartitionLower (neighborMeet B forward c.1)
  let upper := fun c : FreeComponent family => c079PartitionUpper (neighborMeet B forward c.1)
  have hw (c : FreeComponent family) : upper c - ell c =
      (p + 1) - partitionBlockCount (neighborMeet B forward c.1) :=
    c079PartitionUpper_sub_lower _ (evenPartition_blockCount_le _
      (main_neighborMeet_even_of_seed seed c.1))
  have hc (k : ℕ) : Nat.card (CrossingFreeComponent B forward k) =
      (c079IntervalLayer ell upper k).card := by
    simp [CrossingFreeComponent, Nat.card_eq_fintype_card,
      Fintype.card_subtype, c079IntervalLayer, ell, upper]
  simp_rw [hc]
  rw [c079_sum_intervalLayerCards_eq_sum_widths ell upper p
    (fun c => c079PartitionUpper_le_orderMinusOne _)]
  simp_rw [hw]
  unfold mainSeedEntropy
  apply Finset.sum_congr
  · ext c
    simp
  · intro c _
    rfl

theorem main_seedEntropy_le_sum_active (hCore : G.IsBoundaryCore)
    (seed : SeedFiber B forward) : mainSeedEntropy B forward ≤
      ∑ k ∈ Finset.Icc 1 p, G.c079ActiveComponentCount (mainSeedLayer seed k) := by
  rw [main_seedEntropy_eq_sum_crossing seed]
  exact Finset.sum_le_sum fun k _ => main_crossing_free_card_le_active hCore seed k

theorem main_seedLayer_isSeparator (hCore : G.IsBoundaryCore)
    (seed : SeedFiber B forward) (k : ℕ) (hk : k ∈ Finset.Icc 1 p) :
    G.IsRightLeftSeparator (mainSeedLayer seed k) := by
  intro v hv path
  exact path.exists_hitOccurrence _
    (((mainSeedState seed).c079IntervalCertificate
      (G.roleCovered_of_isBoundaryCore hCore)).rightToLeftPath_hits_layer hk v hv path)

theorem main_active_le_maximum_add_excess (cut : Finset (Fin G.roles))
    (hCut : G.IsRightLeftSeparator cut) :
    G.c079ActiveComponentCount cut ≤ G.activeComponentMaximum +
      G.roles * (cut.card - G.rightLeftSeparatorNumber) := by
  have hmin := G.minimumRightLeftSeparator_isMinimum
  have hle : G.rightLeftSeparatorNumber ≤ cut.card := hmin.2 cut hCut
  by_cases heq : cut.card = G.rightLeftSeparatorNumber
  · have hm : G.IsMinimumRightLeftSeparator cut := ⟨hCut, fun other ho => by
      rw [heq]; exact hmin.2 other ho⟩
    simpa [heq] using G.c079ActiveComponentCount_le_maximum cut hm
  · have hp : 1 ≤ cut.card - G.rightLeftSeparatorNumber := by omega
    have hr := Nat.mul_le_mul_left G.roles hp
    have ha := G.c079ActiveComponentCount_le_roles cut
    omega

theorem main_seedEntropy_le_totalDefect_charge (hCore : G.IsBoundaryCore)
    (hs : s = G.rightLeftSeparatorNumber) (seed : SeedFiber B forward) :
    mainSeedEntropy B forward ≤ G.activeComponentMaximum * p +
      G.roles * ((mainSeedState seed).totalDefect - s * p) := by
  classical
  have he := (mainSeedState seed).c079_sum_layerExcess_eq_totalDefect_sub_paths
    (G.roleCovered_of_isBoundaryCore hCore) family
  change (∑ k ∈ Finset.Icc 1 p, ((mainSeedLayer seed k).card - s)) = _ at he
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 p, G.c079ActiveComponentCount (mainSeedLayer seed k) :=
      main_seedEntropy_le_sum_active hCore seed
    _ ≤ ∑ k ∈ Finset.Icc 1 p, (G.activeComponentMaximum +
        G.roles * ((mainSeedLayer seed k).card - s)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [hs] using main_active_le_maximum_add_excess _
        (main_seedLayer_isSeparator hCore seed k hk)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, he]
      simp [Nat.mul_comm]

theorem main_seedState_totalDefect_le (hCore : G.IsBoundaryCore)
    (seed : SeedFiber B forward) :
    (mainSeedState seed).totalDefect ≤ s * p + onDefect p family d + forwardLoss B forward := by
  classical
  obtain ⟨O, hO⟩ := B.2
  have hOrig (x : Fin G.roles) (hx : x ∈ family.backboneRoles) :
      originalPrefix B.1 x = O.1.partition x := by
    simpa [originalPrefix, hx] using (hO ⟨x, hx⟩).symm
  have hOff : (mainSeedState seed).c079OffBackboneDefect family = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxOff : x ∉ family.backboneRoles := by
      simpa [PartiteShape.VertexDisjointRightToLeftPaths.offBackboneRoles] using hx
    rw [mainSeedState_partition, normalizedRecord_off_blockCount seed x hxOff, Nat.sub_self]
  rw [(mainSeedState seed).c079_totalDefect_eq_backbone_add_offBackbone family, hOff,
    Nat.add_zero]
  have hBase : (∑ x ∈ family.backboneRoles,
      ((p + 1) - partitionBlockCount (originalPrefix B.1 x))) =
      s * p + onDefect p family d := by
    calc
      _ = ∑ x ∈ family.backboneRoles, ((p + 1) - partitionBlockCount (O.1.partition x)) :=
        Finset.sum_congr rfl (fun x hx => by rw [hOrig x hx])
      _ = _ := by
        rw [O.1.c079_sum_backboneRoles_eq_sum_pathDefects family,
          O.1.c079_sum_pathDefects_eq_baseline_add_excess family,
          defectFiber_onDefect family O]
  calc
    _ ≤ ∑ x ∈ family.backboneRoles,
        (((p + 1) - partitionBlockCount (originalPrefix B.1 x)) +
          (partitionBlockCount (originalPrefix B.1 x) - partitionBlockCount (repairedAt B forward x))) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [mainSeedState_partition, normalizedRecord_backbone seed x hx]
      have hb : partitionBlockCount (originalPrefix B.1 x) ≤ p + 1 := by
        rw [hOrig x hx]
        exact O.1.coveredRole_blockCount_le x (G.roleCovered_of_isBoundaryCore hCore x)
      omega
    _ = _ := by rw [Finset.sum_add_distrib, hBase]; rfl

/-- Fine entropy charge for an actual legal seed, with no assumed charge inequality. -/
theorem main_seedEntropy_le_onDefect_forwardLoss (hCore : G.IsBoundaryCore)
    (hs : s = G.rightLeftSeparatorNumber) (seed : SeedFiber B forward) :
    mainSeedEntropy B forward ≤ G.activeComponentMaximum * p +
      G.roles * (onDefect p family d + forwardLoss B forward) := by
  have ht := main_seedState_totalDefect_le hCore seed
  have hd : (mainSeedState seed).totalDefect - s * p ≤
      onDefect p family d + forwardLoss B forward := by omega
  exact (main_seedEntropy_le_totalDefect_charge hCore hs seed).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left G.roles hd) _)

/-- Uniform actual seed-fiber budget, including empty fibers and arbitrary forward words. -/
theorem main_seedFiber_card_le_requested (hCore : G.IsBoundaryCore)
    (hs : s = G.rightLeftSeparatorNumber) (B : PathFiber p family d)
    (forward : ForwardCode (Fin G.roles) (p + 1) (3 * G.roles * offDefect family d)) :
    Fintype.card (SeedFiber B forward) ≤
      2 ^ (G.roles * (p + 1)) * (p + 1) ^
        (G.activeComponentMaximum * (p + 1) + G.roles * onDefect p family d +
          3 * G.roles ^ 2 * offDefect family d) := by
  classical
  by_cases h : Nonempty (SeedFiber B forward)
  · obtain ⟨seed⟩ := h
    have hFine := main_seedEntropy_le_onDefect_forwardLoss hCore hs seed
    have hLoss := forwardLoss_le B forward
    have hCrude := main_seedEntropy_le_roles_mul_order B forward
    have hExp : mainSeedEntropy B forward ≤
        G.activeComponentMaximum * (p + 1) + G.roles * onDefect p family d +
          3 * G.roles ^ 2 * offDefect family d := by
      calc
        _ ≤ G.activeComponentMaximum * p + G.roles * (onDefect p family d + forwardLoss B forward) := hFine
        _ ≤ G.activeComponentMaximum * (p + 1) + G.roles *
            (onDefect p family d + 3 * G.roles * offDefect family d) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (by omega))
            (Nat.mul_le_mul_left _ (Nat.add_le_add_left hLoss _))
        _ = _ := by ring
    have hTwo : mainSeedEntropy B forward ≤ G.roles * (p + 1) :=
      hCrude.trans (Nat.mul_le_mul_left _ (by omega))
    calc
      _ ≤ (2 * (p + 1)) ^ mainSeedEntropy B forward := by
        simpa only [Nat.card_eq_fintype_card] using main_seedFiber_card_le_entropy B forward
      _ = 2 ^ mainSeedEntropy B forward * (p + 1) ^ mainSeedEntropy B forward := by rw [mul_pow]
      _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hTwo)
        (Nat.pow_le_pow_right (by omega) hExp)
  · haveI : IsEmpty (SeedFiber B forward) := not_nonempty_iff.mp h
    simp

end GraphMatrixReplica.ReplicaCounting
