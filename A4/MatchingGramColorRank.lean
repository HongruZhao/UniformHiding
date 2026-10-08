import A4.MatchingGramSymplectic

/-!
# Grouping finite color maps by the number of used colors

This is the exact falling-factorial counting mechanism in the signed Gram
expansion.  Surjections retain all domain points; the image grouping does
not approximate a coloring count.
-/

open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

def SurjectiveFiniteMap (α β : Type*) := {f : α → β // Function.Surjective f}

instance surjectiveFiniteMap_finite (α β : Type*) [Finite α] [Finite β] :
    Finite (SurjectiveFiniteMap α β) := by
  unfold SurjectiveFiniteMap
  infer_instance

instance surjectiveFiniteMap_fintype (α β : Type*) [Finite α] [Finite β] :
    Fintype (SurjectiveFiniteMap α β) := Fintype.ofFinite _

def surjectiveFiniteMapCodomainEquiv {α β γ : Type*} (e : β ≃ γ) :
    SurjectiveFiniteMap α β ≃ SurjectiveFiniteMap α γ where
  toFun f := ⟨fun i => e (f.val i), e.surjective.comp f.property⟩
  invFun f := ⟨fun i => e.symm (f.val i), e.symm.surjective.comp f.property⟩
  left_inv f := by apply Subtype.ext; funext i; exact e.symm_apply_apply _
  right_inv f := by apply Subtype.ext; funext i; exact e.apply_symm_apply _

def finiteMapImage {α : Type*} [Fintype α] {k : ℕ} (f : α → Fin k) : Finset (Fin k) :=
  Finset.univ.image f

def imageRankMap {α : Type*} [Fintype α] {k : ℕ}
    (f : (S : Finset (Fin k)) × SurjectiveFiniteMap α S) : α → Fin k :=
  fun i => (f.2.val i).val

theorem finiteMapImage_imageRankMap {α : Type*} [Fintype α] {k : ℕ}
    (S : Finset (Fin k)) (f : SurjectiveFiniteMap α S) :
    finiteMapImage (imageRankMap ⟨S, f⟩) = S := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact hi ▸ (f.val i).property
  · intro hj
    obtain ⟨i, hi⟩ := f.property ⟨j, hj⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩

theorem imageRankMap_bijective {α : Type*} [Fintype α] {k : ℕ} :
    Function.Bijective (imageRankMap (α := α) (k := k)) := by
  classical
  constructor
  · rintro ⟨S, f⟩ ⟨T, g⟩ h
    have hST : S = T := by
      calc
        S = finiteMapImage (imageRankMap ⟨S, f⟩) := (finiteMapImage_imageRankMap S f).symm
        _ = finiteMapImage (imageRankMap ⟨T, g⟩) := congrArg finiteMapImage h
        _ = T := finiteMapImage_imageRankMap T g
    subst T
    have hfg : f = g := by
      apply Subtype.ext
      funext i
      exact Subtype.ext (congrFun h i)
    subst g
    rfl
  · intro f
    let S := finiteMapImage f
    let g : α → S := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hg : Function.Surjective g := by
      intro j
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.property
      exact ⟨i, Subtype.ext hi⟩
    exact ⟨⟨S, g, hg⟩, rfl⟩

def imageRankEquiv {α : Type*} [Fintype α] (k : ℕ) :
    ((S : Finset (Fin k)) × SurjectiveFiniteMap α S) ≃ (α → Fin k) :=
  Equiv.ofBijective imageRankMap imageRankMap_bijective

theorem card_surjectiveFiniteMap_finset {α : Type*} [Fintype α] {k : ℕ}
    (S : Finset (Fin k)) :
    Fintype.card (SurjectiveFiniteMap α S) =
      Fintype.card (SurjectiveFiniteMap α (Fin S.card)) := by
  classical
  exact Fintype.card_congr (surjectiveFiniteMapCodomainEquiv (S.orderIsoOfFin rfl).toEquiv.symm)

theorem card_surjectiveFiniteMap_fin_eq_zero {α : Type*} [Fintype α] {r : ℕ}
    (hr : Fintype.card α < r) : Fintype.card (SurjectiveFiniteMap α (Fin r)) = 0 := by
  have hno : ∀ f : SurjectiveFiniteMap α (Fin r), False := by
    intro f
    apply not_le_of_gt hr
    simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective f.val f.property
  exact Fintype.card_eq_zero_iff.mpr ⟨hno⟩

theorem pow_card_eq_sum_surjective_ranks {α : Type*} [Fintype α] (k : ℕ) :
    k ^ Fintype.card α =
      ∑ r ∈ Finset.range (k + 1),
        k.choose r * Fintype.card (SurjectiveFiniteMap α (Fin r)) := by
  classical
  calc
    _ = Fintype.card (α → Fin k) := by rw [Fintype.card_fun, Fintype.card_fin]
    _ = Fintype.card ((S : Finset (Fin k)) × SurjectiveFiniteMap α S) :=
      (Fintype.card_congr (imageRankEquiv (α := α) k)).symm
    _ = ∑ S : Finset (Fin k), Fintype.card (SurjectiveFiniteMap α S) := Fintype.card_sigma
    _ = ∑ S : Finset (Fin k), Fintype.card (SurjectiveFiniteMap α (Fin S.card)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact card_surjectiveFiniteMap_finset S
    _ = ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        Fintype.card (SurjectiveFiniteMap α (Fin S.card)) := by
      have hu : (Finset.univ : Finset (Finset (Fin k))) =
          (Finset.univ : Finset (Fin k)).powerset := by ext S; simp
      rw [hu]
    _ = ∑ r ∈ Finset.range (k + 1),
        k.choose r * Fintype.card (SurjectiveFiniteMap α (Fin r)) := by
      rw [Finset.sum_powerset]
      simp only [Finset.card_univ, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro r hr
      simpa only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
        Finset.sum_powersetCard r (Finset.univ : Finset (Fin k))
          (fun j => Fintype.card (SurjectiveFiniteMap α (Fin j)))

theorem pow_card_eq_sum_surjective_ranks_bounded {α : Type*} [Fintype α]
    {n k : ℕ} (hn : Fintype.card α ≤ n) (hk : n ≤ k) :
    k ^ Fintype.card α =
      ∑ r : Fin (n + 1), k.choose r.val * Fintype.card (SurjectiveFiniteMap α (Fin r.val)) := by
  rw [pow_card_eq_sum_surjective_ranks]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun r : ℕ => k.choose r * Fintype.card (SurjectiveFiniteMap α (Fin r))) (n + 1)
  rw [hfin]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hk 1))
  intro r hrk hrn
  have hr : n < r := by
    have hge : n + 1 ≤ r := by simpa only [Finset.mem_range, not_lt] using hrn
    omega
  rw [card_surjectiveFiniteMap_fin_eq_zero (lt_of_le_of_lt hn hr), mul_zero]

theorem coloringBinomialWeight_nat (k r : ℕ) :
    coloringBinomialWeight (k : ℝ) r = (k.choose r : ℝ) := by
  unfold coloringBinomialWeight
  rw [Nat.cast_choose_eq_descPochhammer_div ℝ k r]
  congr 1
  rw [descPochhammer_eval_eq_prod_range]
  exact Fin.prod_univ_eq_prod_range (fun j : ℕ => (k : ℝ) - j) r

end MatsumotoPaper
