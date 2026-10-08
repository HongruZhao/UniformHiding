import A4.MatchingGram

/-!
# Coloring the connected components of two matchings

This supplies the literal loop-count factor in finite Wick regroupings.
The connected-component index is built from the exact `componentVertices`
definition used in A4, rather than from an alternative graph convention.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def MatchingComponent {n : ℕ} (M N : PM n) : Type :=
  {C : Finset (Fin (2 * n)) // C ∈ Finset.univ.image (componentVertices M N)}

instance matchingComponent_fintype {n : ℕ} (M N : PM n) : Fintype (MatchingComponent M N) := by
  unfold MatchingComponent
  infer_instance

theorem card_matchingComponent {n : ℕ} (M N : PM n) :
    Fintype.card (MatchingComponent M N) = matchingKappa M N := by
  classical
  unfold MatchingComponent matchingKappa
  exact Fintype.card_coe _

def vertexMatchingComponent {n : ℕ} (M N : PM n) (i : Fin (2 * n)) :
    MatchingComponent M N :=
  ⟨componentVertices M N i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

theorem vertexMatchingComponent_surjective {n : ℕ} (M N : PM n) :
    Function.Surjective (vertexMatchingComponent M N) := by
  intro C
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp C.property
  exact ⟨i, Subtype.ext hi⟩

def matchingComponentRepresentative {n : ℕ} (M N : PM n)
    (C : MatchingComponent M N) : Fin (2 * n) :=
  Classical.choose (vertexMatchingComponent_surjective M N C)

@[simp] theorem vertexMatchingComponent_representative {n : ℕ} (M N : PM n)
    (C : MatchingComponent M N) :
    vertexMatchingComponent M N (matchingComponentRepresentative M N C) = C :=
  Classical.choose_spec (vertexMatchingComponent_surjective M N C)

@[simp] theorem vertexMatchingComponent_mate_left {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : vertexMatchingComponent M N (M i) = vertexMatchingComponent M N i := by
  apply Subtype.ext
  exact (componentVertices_eq_of_reachable M N (.single (Or.inl rfl))).symm

@[simp] theorem vertexMatchingComponent_mate_right {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : vertexMatchingComponent M N (N i) = vertexMatchingComponent M N i := by
  apply Subtype.ext
  exact (componentVertices_eq_of_reachable M N (.single (Or.inr rfl))).symm

def CompatibleMatchingColoring {n : ℕ} (M N : PM n) (α : Type*) :=
  {c : Fin (2 * n) → α // (∀ i, c (M i) = c i) ∧ (∀ i, c (N i) = c i)}

theorem compatibleMatchingColoring_eq_of_reachable {n : ℕ} {α : Type*}
    (M N : PM n) (c : CompatibleMatchingColoring M N α)
    {i j : Fin (2 * n)} (h : Relation.ReflTransGen (matchingAdjacent M N) i j) :
    c.val i = c.val j := by
  induction h with
  | refl => rfl
  | @tail j k hij hjk ih =>
    rcases hjk with hM | hN
    · rw [← hM]
      exact ih.trans (c.property.1 j).symm
    · rw [← hN]
      exact ih.trans (c.property.2 j).symm

theorem compatibleMatchingColoring_eq_of_component {n : ℕ} {α : Type*}
    (M N : PM n) (c : CompatibleMatchingColoring M N α)
    {i j : Fin (2 * n)} (h : vertexMatchingComponent M N i = vertexMatchingComponent M N j) :
    c.val i = c.val j := by
  apply compatibleMatchingColoring_eq_of_reachable M N c
  exact (componentVertices_eq_iff M N i j).mp (congrArg Subtype.val h)

def componentColoringToVertexColoring {n : ℕ} {α : Type*}
    (M N : PM n) (f : MatchingComponent M N → α) : CompatibleMatchingColoring M N α :=
  ⟨fun i => f (vertexMatchingComponent M N i),
    ⟨fun i => congrArg f (vertexMatchingComponent_mate_left M N i),
     fun i => congrArg f (vertexMatchingComponent_mate_right M N i)⟩⟩

def vertexColoringToComponentColoring {n : ℕ} {α : Type*}
    (M N : PM n) (c : CompatibleMatchingColoring M N α) : MatchingComponent M N → α :=
  fun C => c.val (matchingComponentRepresentative M N C)

/-- Assigning a color to each union component is equivalent to compatibility with both matchings. -/
def matchingColoringEquiv {n : ℕ} {α : Type*} (M N : PM n) :
    (MatchingComponent M N → α) ≃ CompatibleMatchingColoring M N α where
  toFun := componentColoringToVertexColoring M N
  invFun := vertexColoringToComponentColoring M N
  left_inv f := by
    funext C
    simp only [vertexColoringToComponentColoring, componentColoringToVertexColoring,
      vertexMatchingComponent_representative]
  right_inv c := by
    apply Subtype.ext
    funext i
    exact compatibleMatchingColoring_eq_of_component M N c
      (vertexMatchingComponent_representative M N (vertexMatchingComponent M N i))

instance compatibleMatchingColoring_finite {n : ℕ} (M N : PM n) (k : ℕ) :
    Finite (CompatibleMatchingColoring M N (Fin k)) := by
  unfold CompatibleMatchingColoring
  infer_instance

instance compatibleMatchingColoring_fintype {n : ℕ} (M N : PM n) (k : ℕ) :
    Fintype (CompatibleMatchingColoring M N (Fin k)) := Fintype.ofFinite _

theorem card_compatibleMatchingColoring {n : ℕ} (M N : PM n) (k : ℕ) :
    Fintype.card (CompatibleMatchingColoring M N (Fin k)) = k ^ matchingKappa M N := by
  classical
  rw [← Fintype.card_congr (matchingColoringEquiv M N), Fintype.card_fun,
    Fintype.card_fin, card_matchingComponent]

end MatsumotoPaper
