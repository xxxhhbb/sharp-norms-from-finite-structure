import R6.PaperGraphMatrixEntryMoments

/-! # R16 independent-color upper transfer: finite combinatorial core

This file treats the random coloring in R16, Lemma `color-upper`. Each ambient
label independently takes one of the `G.roles` colors. For a globally injective
realization, exactly one color is prescribed at each of its `G.roles` image
labels, and the other labels are free. The resulting retention probability is
`(G.roles) ^ (-G.roles)`; it is not the fixed balanced coloring used by the
lower transfer. No operator-norm or `L^q` inequality is claimed here.
-/

noncomputable section
open scoped BigOperators

namespace GraphMatrixReplica

/-- A coloring of all ambient labels respects one injective realization. -/
def paperR16ColorRespects (G : PaperShape) {n : ℕ}
    (color : Fin n → Fin G.roles) (phi : PaperRealization G n) : Prop :=
  ∀ v, color (phi v) = v

noncomputable instance paperR16ColorRespectsDecidable (G : PaperShape) {n : ℕ}
    (color : Fin n → Fin G.roles) (phi : PaperRealization G n) :
    Decidable (paperR16ColorRespects G color phi) :=
  Classical.propDecidable _

/-- The labels not used by a globally injective realization. -/
abbrev PaperR16UnusedLabel (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) :=
  {i : Fin n // ¬∃ v : Fin G.roles, phi v = i}

/-- Colorings that retain `phi` are equivalent to arbitrary colorings of the
unused ambient labels. This is the exact finite independence statement. -/
def paperR16RetainingColorEquiv (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) :
    {color : Fin n → Fin G.roles // paperR16ColorRespects G color phi} ≃
      (PaperR16UnusedLabel G phi → Fin G.roles) where
  toFun color i := color.1 i.1
  invFun free := by
    classical
    refine ⟨(fun i => if h : ∃ v : Fin G.roles, phi v = i then
      Classical.choose h else free ⟨i, h⟩), ?_⟩
    intro v
    have h : ∃ u : Fin G.roles, phi u = phi v := ⟨v, rfl⟩
    simp only [dif_pos h]
    exact phi.injective (Classical.choose_spec h)
  left_inv := by
    classical
    intro color
    apply Subtype.ext
    funext i
    by_cases h : ∃ v : Fin G.roles, phi v = i
    · obtain ⟨v, rfl⟩ := h
      have hmem : ∃ u : Fin G.roles, phi u = phi v := ⟨v, rfl⟩
      simp only [dif_pos hmem]
      have hchoose : Classical.choose hmem = v :=
        phi.injective (Classical.choose_spec hmem)
      simpa [hchoose] using (color.property v).symm
    · simp [h]
  right_inv := by
    classical
    intro free
    funext i
    have h : ¬∃ v : Fin G.roles, phi v = i.1 := i.2
    simp [h]

/-- The image labels of `phi` are in bijection with shape roles. -/
def paperR16UsedLabelEquiv (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) :
    Fin G.roles ≃ {i : Fin n // ∃ v : Fin G.roles, phi v = i} := by
  apply Equiv.ofBijective (fun v => (⟨phi v, ⟨v, rfl⟩⟩ :
    {i : Fin n // ∃ v : Fin G.roles, phi v = i}))
  constructor
  · intro v w h
    exact phi.injective (congrArg Subtype.val h)
  · rintro ⟨i, v, hv⟩
    exact ⟨v, Subtype.ext hv⟩

/-- There are `roles^(n-roles)` colorings that retain any one injective
realization. -/
theorem paperR16_retainingColor_card (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) :
    Nat.card {color : Fin n → Fin G.roles //
      paperR16ColorRespects G color phi} = G.roles ^ (n - G.roles) := by
  classical
  rw [Nat.card_congr (paperR16RetainingColorEquiv G phi), Nat.card_fun]
  have hComplement :
      Nat.card (PaperR16UnusedLabel G phi) = n - G.roles := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have hUsed :
        Fintype.card {i : Fin n // ∃ v : Fin G.roles, phi v = i} = G.roles := by
      simpa using (Fintype.card_congr (paperR16UsedLabelEquiv G phi)).symm
    rw [hUsed]
    simp
  rw [hComplement]
  simp

/-- A fixed injection appears in the sum over all ambient colorings with
exactly `roles^(n-roles)` copies. -/
theorem paperR16_sum_color_indicator (G : PaperShape) {n : ℕ}
    (phi : PaperRealization G n) (x : ℝ) :
    (∑ color : Fin n → Fin G.roles,
      if paperR16ColorRespects G color phi then x else 0) =
        (G.roles ^ (n - G.roles) : ℕ) • x := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const]
  rw [← Fintype.card_subtype]
  rw [show Fintype.card {color : Fin n → Fin G.roles //
      paperR16ColorRespects G color phi} =
        G.roles ^ (n - G.roles) by
      simpa [Nat.card_eq_fintype_card] using paperR16_retainingColor_card G phi]

/-- Full-size zero-padded matrix retaining only injections whose ambient
labels carry their prescribed role colors. -/
def paperR16ColoredGraphMatrix (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) (color : Fin n → Fin G.roles) :
    Matrix (PaperRow G n) (PaperCol G n) ℝ := by
  classical
  exact fun row col =>
    ∑ phi : PaperRealization G n,
      if paperR16ColorRespects G color phi then
        if paperEntryCompatible G phi row col then
          ∏ e : Fin G.edges, paperEdgeSign w
            (phi (G.source e)) (phi (G.target e))
        else 0
      else 0

/-- Exact unnormalized R16 color averaging, pointwise in the ambient signs.
The factor is the count of extensions of the prescribed role colors away from
the injection image. -/
theorem paperR16_sum_coloredGraphMatrix (G : PaperShape) (n : ℕ)
    (w : PaperNoise n) (row : PaperRow G n) (col : PaperCol G n) :
    (∑ color : Fin n → Fin G.roles,
      paperR16ColoredGraphMatrix G n w color row col) =
      (G.roles ^ (n - G.roles) : ℕ) •
        paperGraphMatrix G n w row col := by
  classical
  unfold paperR16ColoredGraphMatrix paperGraphMatrix
  calc
    (∑ color : Fin n → Fin G.roles,
      ∑ phi : PaperRealization G n,
        if paperR16ColorRespects G color phi then
          (if paperEntryCompatible G phi row col then
            ∏ e : Fin G.edges, paperEdgeSign w
              (phi (G.source e)) (phi (G.target e))
          else 0)
        else 0) =
      ∑ phi : PaperRealization G n,
        ∑ color : Fin n → Fin G.roles,
          if paperR16ColorRespects G color phi then
            (if paperEntryCompatible G phi row col then
              ∏ e : Fin G.edges, paperEdgeSign w
                (phi (G.source e)) (phi (G.target e))
            else 0)
          else 0 := Finset.sum_comm
    _ = ∑ phi : PaperRealization G n,
        (G.roles ^ (n - G.roles) : ℕ) •
          (if paperEntryCompatible G phi row col then
            ∏ e : Fin G.edges, paperEdgeSign w
              (phi (G.source e)) (phi (G.target e))
          else 0) := by
      apply Finset.sum_congr rfl
      intro phi _
      exact paperR16_sum_color_indicator G phi _
    _ = (G.roles ^ (n - G.roles) : ℕ) •
        ∑ phi : PaperRealization G n,
          if paperEntryCompatible G phi row col then
            ∏ e : Fin G.edges, paperEdgeSign w
              (phi (G.source e)) (phi (G.target e))
          else 0 := by rw [Finset.smul_sum]

/-- R16 equation `M_G = v^v E_color H_color`, pointwise for nonempty shapes
in the asymptotic range `v ≤ n`. The color expectation is the finite uniform
mean, and the equality holds for each fixed ambient sign sample. -/
theorem paperR16_color_average (G : PaperShape) (n : ℕ)
    (hroles : 0 < G.roles) (hn : G.roles ≤ n)
    (w : PaperNoise n) (row : PaperRow G n) (col : PaperCol G n) :
    paperGraphMatrix G n w row col =
      (G.roles : ℝ) ^ G.roles *
        paperMean (fun color : Fin n → Fin G.roles =>
          paperR16ColoredGraphMatrix G n w color row col) := by
  have ha : (G.roles : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hroles)
  have hpow : (G.roles : ℝ) ^ n =
      (G.roles : ℝ) ^ G.roles * (G.roles : ℝ) ^ (n - G.roles) := by
    rw [← pow_add]
    congr 1
    omega
  unfold paperMean
  rw [show Fintype.card (Fin n → Fin G.roles) = G.roles ^ n by
    simp]
  rw [paperR16_sum_coloredGraphMatrix]
  simp only [Nat.cast_pow, nsmul_eq_mul]
  rw [hpow]
  field_simp [ha]

/-- Matrix-valued form of the same pointwise identity, ready for a separate
convexity or Minkowski norm transfer. -/
theorem paperR16_matrix_color_average (G : PaperShape) (n : ℕ)
    (hroles : 0 < G.roles) (hn : G.roles ≤ n) (w : PaperNoise n) :
    paperGraphMatrix G n w =
      fun row col => (G.roles : ℝ) ^ G.roles *
        paperMean (fun color : Fin n → Fin G.roles =>
          paperR16ColoredGraphMatrix G n w color row col) := by
  funext row col
  exact paperR16_color_average G n hroles hn w row col

#print axioms paperR16_retainingColor_card
#print axioms paperR16_sum_color_indicator
#print axioms paperR16_sum_coloredGraphMatrix
#print axioms paperR16_color_average
#print axioms paperR16_matrix_color_average

end GraphMatrixReplica
