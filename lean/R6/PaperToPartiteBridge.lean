import R6.PaperGraphMatrixEntryMoments
import R6.SeparatorPathCertificate

/-! # Bridge from the paper shape to the replica separator calculus

`PaperShape` records the ordered boundary embeddings used by BLNvH v2,
Definition 4.5.  The C078 replica calculus only needs their underlying finite
sets.  This file makes that forgetting map explicit and proves that its
`RoleCovered` side condition is exactly the absence of isolated middle roles.

This is a structural bridge only: it does not identify the original
globally-injective trace expansion with the fully-partite replica sum.
-/

noncomputable section

namespace GraphMatrixReplica

/-- The underlying set of roles in the ordered left boundary. -/
def PaperShape.leftBoundaryFinset (G : PaperShape) :
    Finset (Fin G.roles) :=
  Finset.univ.map G.left

/-- The underlying set of roles in the ordered right boundary. -/
def PaperShape.rightBoundaryFinset (G : PaperShape) :
    Finset (Fin G.roles) :=
  Finset.univ.map G.right

@[simp] theorem PaperShape.mem_leftBoundaryFinset_iff
    (G : PaperShape) (v : Fin G.roles) :
    v ∈ G.leftBoundaryFinset ↔ ∃ i : Fin G.leftSize, G.left i = v := by
  simp [PaperShape.leftBoundaryFinset]

@[simp] theorem PaperShape.mem_rightBoundaryFinset_iff
    (G : PaperShape) (v : Fin G.roles) :
    v ∈ G.rightBoundaryFinset ↔ ∃ i : Fin G.rightSize, G.right i = v := by
  simp [PaperShape.rightBoundaryFinset]

/-- Forget boundary order, retaining exactly the incidence data consumed by
the separator/path replica calculus. -/
def PaperShape.toPartiteShape (G : PaperShape) : PartiteShape where
  roles := G.roles
  edges := G.edges
  source := G.source
  target := G.target
  leftBoundary := G.leftBoundaryFinset
  rightBoundary := G.rightBoundaryFinset

@[simp] theorem PaperShape.toPartiteShape_roles (G : PaperShape) :
    G.toPartiteShape.roles = G.roles := rfl

@[simp] theorem PaperShape.toPartiteShape_edges (G : PaperShape) :
    G.toPartiteShape.edges = G.edges := rfl

@[simp] theorem PaperShape.toPartiteShape_source (G : PaperShape)
    (e : Fin G.edges) :
    G.toPartiteShape.source e = G.source e := rfl

@[simp] theorem PaperShape.toPartiteShape_target (G : PaperShape)
    (e : Fin G.edges) :
    G.toPartiteShape.target e = G.target e := rfl

@[simp] theorem PaperShape.toPartiteShape_leftBoundary (G : PaperShape) :
    G.toPartiteShape.leftBoundary = G.leftBoundaryFinset := rfl

@[simp] theorem PaperShape.toPartiteShape_rightBoundary (G : PaperShape) :
    G.toPartiteShape.rightBoundary = G.rightBoundaryFinset := rfl

/-- A role is an isolated middle role precisely when it lies in neither
boundary and is incident to no shape edge. -/
def PaperShape.IsolatedMiddleRole (G : PaperShape) (v : Fin G.roles) : Prop :=
  v ∉ G.leftBoundaryFinset ∧
    v ∉ G.rightBoundaryFinset ∧
    ∀ e : Fin G.edges, G.source e ≠ v ∧ G.target e ≠ v

/-- The retained-role hypothesis of the replica calculus is exactly the
negation of being an isolated middle role in the paper model. -/
theorem PaperShape.toPartiteShape_roleCovered_iff_not_isolated
    (G : PaperShape) (v : Fin G.roles) :
    G.toPartiteShape.RoleCovered v ↔ ¬ G.IsolatedMiddleRole v := by
  constructor
  · intro hCovered hIsolated
    rcases hCovered with ⟨e, he | he⟩ | hLeft | hRight
    · exact (hIsolated.2.2 e).1 he
    · exact (hIsolated.2.2 e).2 he
    · exact hIsolated.1 hLeft
    · exact hIsolated.2.1 hRight
  · intro hNotIsolated
    by_contra hNotCovered
    apply hNotIsolated
    refine ⟨?_, ?_, ?_⟩
    · intro hLeft
      exact hNotCovered (Or.inr (Or.inl hLeft))
    · intro hRight
      exact hNotCovered (Or.inr (Or.inr hRight))
    · intro e
      constructor
      · intro hSource
        exact hNotCovered (Or.inl ⟨e, Or.inl hSource⟩)
      · intro hTarget
        exact hNotCovered (Or.inl ⟨e, Or.inr hTarget⟩)

/-- A paper shape has no isolated middle roles. -/
def PaperShape.HasNoIsolatedMiddleRoles (G : PaperShape) : Prop :=
  ∀ v : Fin G.roles, ¬ G.IsolatedMiddleRole v

theorem PaperShape.hasNoIsolatedMiddleRoles_iff_all_roleCovered
    (G : PaperShape) :
    G.HasNoIsolatedMiddleRoles ↔
      ∀ v : Fin G.roles, G.toPartiteShape.RoleCovered v := by
  constructor
  · intro h v
    exact (G.toPartiteShape_roleCovered_iff_not_isolated v).2 (h v)
  · intro h v
    exact (G.toPartiteShape_roleCovered_iff_not_isolated v).1 (h v)

/-- Once an original-model trace state has been mapped into the replica
state type, the existing sharp separator bound applies to every paper shape
without isolated middle roles. -/
theorem ReplicaState.totalBlockCount_le_paperMinSeparator
    {G : PaperShape} {p : ℕ} (S : ReplicaState G.toPartiteShape p)
    (hNoIsolated : G.HasNoIsolatedMiddleRoles)
    (certificate : G.toPartiteShape.RightLeftMengerCertificate) :
    S.totalBlockCount ≤
      (p + 1) * (G.roles - certificate.cut.card) + certificate.cut.card := by
  exact S.totalBlockCount_le_minSeparator
    ((G.hasNoIsolatedMiddleRoles_iff_all_roleCovered).1 hNoIsolated)
    certificate

#print axioms PaperShape.toPartiteShape_roleCovered_iff_not_isolated
#print axioms PaperShape.hasNoIsolatedMiddleRoles_iff_all_roleCovered
#print axioms ReplicaState.totalBlockCount_le_paperMinSeparator

end GraphMatrixReplica
