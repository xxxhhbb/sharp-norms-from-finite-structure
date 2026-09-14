import GraphMatrix.Model.ColorLowerFourier
import GraphMatrix.Model.ColorLowerWalshAutomorphismBridge

/-! # Saturation of the target edge-color tags after full Walsh extraction

The paper word has exactly as many edges as there are target edge colors.
If every target color occurs oddly in its tag word, each color occurs at
least once. Pigeonhole then forces *every* source edge to be tagged. This
removes the `hTag` existence assumption from the next combinatorial step;
constructing the corresponding role-color map remains separate.
-/

noncomputable section

namespace GraphMatrixReplica

/-- For a word with `m` positions and `m` possible nonempty tags, an odd
count of every tag forces every position to have a tag. -/
theorem paperR16OddOptionWord_allTagged
    (m : ℕ) (f : Fin m → Option (Fin m))
    (hOdd : ∀ k : Fin m,
      Odd (@List.count (Option (Fin m)) instBEqOfDecidableEq
        (some k) (List.ofFn f))) :
    ∀ e : Fin m, ∃ k : Fin m, f e = some k := by
  classical
  letI : BEq (Option (Fin m)) := instBEqOfDecidableEq
  have hCovered : ∀ k : Fin m, ∃ e : Fin m, f e = some k := by
    intro k
    have hpos : 0 < List.count (some k) (List.ofFn f) := by
      obtain ⟨t, ht⟩ := hOdd k
      omega
    exact List.mem_ofFn.mp (List.count_pos_iff.mp hpos)
  choose g hg using hCovered
  have hgInj : Function.Injective g := by
    intro k l hkl
    have hk : f (g l) = some k := by simpa only [hkl] using hg k
    exact Option.some.inj (hk.symm.trans (hg l))
  have hgSurj : Function.Surjective g :=
    Finite.injective_iff_surjective.mp hgInj
  intro e
  obtain ⟨k, hk⟩ := hgSurj e
  subst e
  exact ⟨k, hg k⟩

/-- The generic Fourier survival predicate constructs an edge-color map
for the entire source edge word, with no prior `hTag` premise. -/
theorem paperR16TaggedWord_hasEdgeColorMap
    {G : PaperShape} {n : ℕ}
    (tag : Fin n × Fin n → Option (Fin G.edges))
    (word : Fin G.edges → Fin n × Fin n)
    (hOdd : ∀ k : Fin G.edges,
      Odd (paperR16TaggedEdgeCount tag (List.ofFn word) k)) :
    ∃ edgeColor : Fin G.edges → Fin G.edges,
      ∀ e : Fin G.edges,
        tag (paperUnorderedPair (word e).1 (word e).2) =
          some (edgeColor e) := by
  classical
  let f : Fin G.edges → Option (Fin G.edges) :=
    fun e => tag (paperUnorderedPair (word e).1 (word e).2)
  have hCount : ∀ k : Fin G.edges,
      @List.count (Option (Fin G.edges)) instBEqOfDecidableEq
        (some k) (List.ofFn f) =
        paperR16TaggedEdgeCount tag (List.ofFn word) k := by
    intro k
    simp [paperR16TaggedEdgeCount, f, List.map_ofFn, Function.comp_def]
  have hEvery : ∀ e : Fin G.edges, ∃ k : Fin G.edges, f e = some k :=
    paperR16OddOptionWord_allTagged G.edges f (by
      intro k
      rw [hCount k]
      exact hOdd k)
  let edgeColor : Fin G.edges → Fin G.edges := fun e => (hEvery e).choose
  refine ⟨edgeColor, ?_⟩
  intro e
  exact (hEvery e).choose_spec


end GraphMatrixReplica
