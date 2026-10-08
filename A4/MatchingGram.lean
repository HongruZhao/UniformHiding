import A4.Target

/-!
# Graph structure of Matsumoto's matching Gram matrix

The statements below apply to every degree.  They concern the literal finite
Gram matrix used by `MatsumotoPaper.Target`; they do not assume a moment
recurrence or replace the required negative-parameter nonsingularity theorem.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

@[simp] theorem matchingAdjacent_swap {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) : matchingAdjacent N M i j ↔ matchingAdjacent M N i j := by
  simp only [matchingAdjacent, or_comm]

instance matchingAdjacent_symmetric {n : ℕ} (M N : PM n) :
    Std.Symm (matchingAdjacent M N) where
  symm i j h := by
    rcases h with h | h
    · left
      simpa only [← h, M.apply_apply]
    · right
      simpa only [← h, N.apply_apply]

@[simp] theorem mem_componentVertices_iff {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) :
    j ∈ componentVertices M N i ↔
      Relation.ReflTransGen (matchingAdjacent M N) i j := by
  classical
  simp [componentVertices]

@[simp] theorem self_mem_componentVertices {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : i ∈ componentVertices M N i := by
  exact (mem_componentVertices_iff M N i i).mpr .refl

theorem componentVertices_eq_of_reachable {n : ℕ} (M N : PM n)
    {i j : Fin (2 * n)}
    (h : Relation.ReflTransGen (matchingAdjacent M N) i j) :
    componentVertices M N i = componentVertices M N j := by
  classical
  ext k
  simp only [mem_componentVertices_iff]
  constructor
  · intro hik
    exact (symm h).trans hik
  · intro hjk
    exact h.trans hjk

theorem componentVertices_eq_iff {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) :
    componentVertices M N i = componentVertices M N j ↔
      Relation.ReflTransGen (matchingAdjacent M N) i j := by
  constructor
  · intro h
    apply (mem_componentVertices_iff M N i j).mp
    rw [h]
    exact self_mem_componentVertices M N j
  · exact componentVertices_eq_of_reachable M N

theorem componentVertices_disjoint_or_eq {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) :
    Disjoint (componentVertices M N i) (componentVertices M N j) ∨
      componentVertices M N i = componentVertices M N j := by
  classical
  by_cases h : Disjoint (componentVertices M N i) (componentVertices M N j)
  · exact Or.inl h
  · right
    obtain ⟨k, hik, hjk⟩ := Finset.not_disjoint_iff.mp h
    apply componentVertices_eq_of_reachable M N
    exact ((mem_componentVertices_iff M N i k).mp hik).trans
      (symm ((mem_componentVertices_iff M N j k).mp hjk))

@[simp] theorem componentVertices_swap {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : componentVertices N M i = componentVertices M N i := by
  have h : matchingAdjacent N M = matchingAdjacent M N := by
    funext a b
    exact propext (matchingAdjacent_swap M N a b)
  classical
  ext j
  rw [mem_componentVertices_iff, mem_componentVertices_iff, h]

@[simp] theorem matchingKappa_symm {n : ℕ} (M N : PM n) :
    matchingKappa N M = matchingKappa M N := by
  have h : componentVertices N M = componentVertices M N := by
    funext i
    exact componentVertices_swap M N i
  simp only [matchingKappa, h]

theorem reachable_self_iff {n : ℕ} (M : PM n) (i j : Fin (2 * n)) :
    Relation.ReflTransGen (matchingAdjacent M M) i j ↔ j = i ∨ j = M i := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail j k hj hk ih =>
      have hmate : M j = k := by simpa only [matchingAdjacent, or_self] using hk
      rcases ih with rfl | rfl
      · exact Or.inr hmate.symm
      · exact Or.inl (by simpa only [M.apply_apply] using hmate.symm)
  · rintro (rfl | rfl)
    · exact .refl
    · exact .single (Or.inl rfl)

@[simp] theorem componentVertices_self {n : ℕ} (M : PM n)
    (i : Fin (2 * n)) : componentVertices M M i = {i, M i} := by
  classical
  ext j
  simp only [mem_componentVertices_iff, reachable_self_iff,
    Finset.mem_insert, Finset.mem_singleton]

theorem componentVertices_image_pairReps {n : ℕ} (M N : PM n) :
    M.pairReps.image (componentVertices M N) =
      Finset.univ.image (componentVertices M N) := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (Finset.subset_univ _)
  · intro C hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    rcases (M.exactly_one_mem_pairReps i).1 with hi | hi
    · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · refine Finset.mem_image.mpr ⟨M i, hi, ?_⟩
      exact (componentVertices_eq_of_reachable M N
        (Relation.ReflTransGen.single (Or.inl rfl))).symm

theorem matchingKappa_le {n : ℕ} (M N : PM n) : matchingKappa M N ≤ n := by
  classical
  rw [matchingKappa, ← componentVertices_image_pairReps M N]
  exact (Finset.card_image_le).trans_eq M.card_pairReps

/-- The smaller endpoint of the pair containing a given vertex. -/
def matchingPairRep {n : ℕ} (M : PM n) (i : Fin (2 * n)) : Fin (2 * n) :=
  min i (M i)

theorem matchingPairRep_eq_or {n : ℕ} (M : PM n) (i : Fin (2 * n)) :
    matchingPairRep M i = i ∨ matchingPairRep M i = M i := by
  exact min_choice i (M i)

@[simp] theorem matchingPairRep_mem {n : ℕ} (M : PM n) (i : Fin (2 * n)) :
    matchingPairRep M i ∈ M.pairReps := by
  rcases lt_or_gt_of_ne (M.apply_ne i).symm with hi | hi
  · simp only [matchingPairRep, min_eq_left (le_of_lt hi), M.mem_pairReps_iff]
    exact hi
  · simp only [matchingPairRep, min_eq_right (le_of_lt hi), M.mem_pairReps_iff,
      M.apply_apply]
    exact hi

@[simp] theorem matchingPairRep_mate {n : ℕ} (M : PM n) (i : Fin (2 * n)) :
    matchingPairRep M (M i) = matchingPairRep M i := by
  simp only [matchingPairRep, M.apply_apply, min_comm]

theorem matchingPairRep_eq_iff {n : ℕ} (M : PM n) (i j : Fin (2 * n)) :
    matchingPairRep M i = matchingPairRep M j ↔ j = i ∨ j = M i := by
  constructor
  · intro h
    rcases matchingPairRep_eq_or M i with hi | hi <;>
      rcases matchingPairRep_eq_or M j with hj | hj
    · exact Or.inl (hi.symm.trans (h.trans hj)).symm
    · right
      have hij : i = M j := hi.symm.trans (h.trans hj)
      simpa only [M.apply_apply] using (congrArg M hij).symm
    · exact Or.inr (hi.symm.trans (h.trans hj)).symm
    · left
      have hij : M i = M j := hi.symm.trans (h.trans hj)
      exact (M.mate.injective hij).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (matchingPairRep_mate M i).symm

@[simp] theorem componentVertices_pairRep {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) :
    componentVertices M N (matchingPairRep M i) = componentVertices M N i := by
  rcases matchingPairRep_eq_or M i with hi | hi
  · rw [hi]
  · rw [hi]
    exact (componentVertices_eq_of_reachable M N
      (Relation.ReflTransGen.single (Or.inl rfl))).symm

@[simp] theorem matchingKappa_self {n : ℕ} (M : PM n) :
    matchingKappa M M = n := by
  classical
  rw [matchingKappa, ← componentVertices_image_pairReps M M]
  rw [Finset.card_image_of_injOn, M.card_pairReps]
  intro i hi j hj hij
  have h : j = i ∨ j = M i :=
    (reachable_self_iff M i j).mp ((componentVertices_eq_iff M M i j).mp hij)
  rcases h with h | rfl
  · exact h.symm
  · exact False.elim ((M.exactly_one_mem_pairReps i).2 ⟨hi, hj⟩)

theorem matchingKappa_eq_iff {n : ℕ} (M N : PM n) :
    matchingKappa M N = n ↔ M = N := by
  classical
  constructor
  · intro h
    have hcard : (M.pairReps.image (componentVertices M N)).card = M.pairReps.card := by
      rw [componentVertices_image_pairReps, ← matchingKappa, h, M.card_pairReps]
    have hinj := Finset.injOn_of_card_image_eq hcard
    have hmate : ∀ i, N i = M i := by
      intro i
      have heq : matchingPairRep M i = matchingPairRep M (N i) := by
        apply hinj (matchingPairRep_mem M i) (matchingPairRep_mem M (N i))
        rw [componentVertices_pairRep, componentVertices_pairRep]
        exact componentVertices_eq_of_reachable M N
          (Relation.ReflTransGen.single (Or.inr rfl))
      rcases (matchingPairRep_eq_iff M i (N i)).mp heq with hi | hi
      · exact False.elim (N.apply_ne i hi)
      · exact hi
    cases M with
    | mk M hM hMM =>
      cases N with
      | mk N hN hNN =>
        have h : M = N := by
          apply Equiv.ext
          intro i
          exact (hmate i).symm
        cases h
        rfl
  · rintro rfl
    exact matchingKappa_self M

theorem matchingKappa_lt_of_ne {n : ℕ} (M N : PM n) (h : M ≠ N) :
    matchingKappa M N < n := by
  exact (matchingKappa_le M N).lt_of_ne (fun heq => h ((matchingKappa_eq_iff M N).mp heq))

theorem matchingKappa_pos {n : ℕ} (hn : 0 < n) (M N : PM n) :
    0 < matchingKappa M N := by
  classical
  unfold matchingKappa
  apply Finset.card_pos.mpr
  exact ⟨componentVertices M N ⟨0, by omega⟩,
    Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩⟩

theorem pairPartition_ext {n : ℕ} {M N : PM n} (h : ∀ i, M i = N i) : M = N := by
  cases M with
  | mk M hM hMM =>
    cases N with
    | mk N hN hNN =>
      have hMN : M = N := Equiv.ext h
      cases hMN
      rfl

@[simp] theorem transportPairPartition_apply {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (M : PM n) (i : Fin (2 * n)) :
    transportPairPartition g M i = g (M (g.symm i)) := rfl

@[simp] theorem transportPairPartition_one {n : ℕ} (M : PM n) :
    transportPairPartition 1 M = M := by
  apply pairPartition_ext
  intro i
  rfl

@[simp] theorem transportPairPartition_mul {n : ℕ}
    (g h : Equiv.Perm (Fin (2 * n))) (M : PM n) :
    transportPairPartition (g * h) M =
      transportPairPartition g (transportPairPartition h M) := by
  apply pairPartition_ext
  intro i
  rfl

@[simp] theorem matchingAdjacent_transport {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (M N : PM n) (i j : Fin (2 * n)) :
    matchingAdjacent (transportPairPartition g M) (transportPairPartition g N)
      (g i) (g j) ↔ matchingAdjacent M N i j := by
  simp only [matchingAdjacent, transportPairPartition_apply, Equiv.symm_apply_apply,
    g.injective.eq_iff]

theorem reachable_transport_iff {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (M N : PM n) (i j : Fin (2 * n)) :
    Relation.ReflTransGen
      (matchingAdjacent (transportPairPartition g M) (transportPairPartition g N))
      (g i) (g j) ↔ Relation.ReflTransGen (matchingAdjacent M N) i j := by
  constructor
  · intro h
    have hlift := h.lift g.symm (by
      intro a b hab
      exact (matchingAdjacent_transport g M N (g.symm a) (g.symm b)).mp
        (by simpa only [Equiv.apply_symm_apply] using hab))
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hlift
  · intro h
    exact h.lift g (by
      intro a b hab
      exact (matchingAdjacent_transport g M N a b).mpr hab)

theorem componentVertices_transport {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (M N : PM n) (i : Fin (2 * n)) :
    componentVertices (transportPairPartition g M) (transportPairPartition g N)
      (g i) = (componentVertices M N i).image g := by
  classical
  ext j
  constructor
  · intro hj
    refine Finset.mem_image.mpr ⟨g.symm j, ?_, g.apply_symm_apply j⟩
    apply (mem_componentVertices_iff M N i (g.symm j)).mpr
    apply (reachable_transport_iff g M N i (g.symm j)).mp
    simpa only [Equiv.apply_symm_apply] using
      (mem_componentVertices_iff _ _ _ _).mp hj
  · intro hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_componentVertices_iff _ _ _ _).mpr
      ((reachable_transport_iff g M N i k).mpr
        ((mem_componentVertices_iff M N i k).mp hk))

@[simp] theorem matchingKappa_transport {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (M N : PM n) :
    matchingKappa (transportPairPartition g M) (transportPairPartition g N) =
      matchingKappa M N := by
  classical
  have hC :
      Finset.univ.image
        (componentVertices (transportPairPartition g M) (transportPairPartition g N)) =
      (Finset.univ.image (componentVertices M N)).image (Finset.image g) := by
    ext C
    constructor
    · intro h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      refine Finset.mem_image.mpr ⟨componentVertices M N (g.symm i),
        Finset.mem_image.mpr ⟨g.symm i, Finset.mem_univ _, rfl⟩, ?_⟩
      have hcomp := componentVertices_transport g M N (g.symm i)
      simpa only [Equiv.apply_symm_apply] using hcomp.symm
    · intro h
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact Finset.mem_image.mpr
        ⟨g i, Finset.mem_univ _, componentVertices_transport g M N i⟩
  unfold matchingKappa
  rw [hC, Finset.card_image_of_injective _ (Finset.image_injective g.injective)]

/-- Relabeling all vertices permutes the finite matching index set. -/
def matchingRelabelEquiv {n : ℕ} (g : Equiv.Perm (Fin (2 * n))) : PM n ≃ PM n where
  toFun := transportPairPartition g
  invFun := transportPairPartition g⁻¹
  left_inv M := by rw [← transportPairPartition_mul, inv_mul_cancel, transportPairPartition_one]
  right_inv M := by rw [← transportPairPartition_mul, mul_inv_cancel, transportPairPartition_one]

theorem kappa_relative {n : ℕ} (g h : Equiv.Perm (Fin (2 * n))) :
    kappa (g⁻¹ * h) = matchingKappa (transportedPairPartition g)
      (transportedPairPartition h) := by
  unfold kappa transportedPairPartition
  have heq := matchingKappa_transport g (standardPairPartition n)
    (transportPairPartition (g⁻¹ * h) (standardPairPartition n))
  simpa only [← transportPairPartition_mul, mul_inv_cancel_left] using heq.symm

@[simp] theorem orthogonalGram_diag (n : ℕ) (z : ℂ) (M : PM n) :
    orthogonalGram n z M M = z ^ n := by
  simp only [orthogonalGram, matchingKappa_self]

theorem orthogonalGram_isSymm (n : ℕ) (z : ℂ) :
    (orthogonalGram n z).IsSymm := by
  ext M N
  simp only [Matrix.transpose_apply, orthogonalGram, matchingKappa_symm]

theorem orthogonalGram_isHermitian (n : ℕ) (z : ℝ) :
    (orthogonalGram n (z : ℂ)).IsHermitian := by
  ext M N
  simp only [Matrix.conjTranspose_apply, orthogonalGram, matchingKappa_symm,
    map_pow, Complex.star_def, Complex.conj_ofReal]

/-- The identity permutation is the canonical standard matching in every degree. -/
def standardCanonicalMatching (n : ℕ) : PerfectMatching n := by
  refine ⟨1, ?_⟩
  constructor
  · intro i
    change 2 * i.val < 2 * i.val + 1
    omega
  · constructor
    · intro hn
      rfl
    · intro i j hij
      change 2 * i.val < 2 * j.val
      have hijv : i.val < j.val := hij
      omega

@[simp] theorem standardCanonicalMatching_toPerm (n : ℕ) :
    (standardCanonicalMatching n).toPerm = 1 := rfl

theorem canonicalMatching_one_toPerm (M : PerfectMatching 1) : M.toPerm = 1 := by
  have hzero : M.toPerm 0 = 0 := by
    simpa [PerfectMatching.toPerm, leftSlot] using M.property.2.1 (by decide)
  have hone : M.toPerm 1 = 1 := by
    have hne : M.toPerm 1 ≠ 0 := by
      intro h
      have hEq : (1 : Fin 2) = 0 := M.toPerm.injective (h.trans hzero.symm)
      exact (by decide : (1 : Fin 2) ≠ 0) hEq
    apply Fin.ext
    change (M.toPerm 1).val = 1
    have hneval : (M.toPerm 1).val ≠ 0 := by
      intro h
      apply hne
      apply Fin.ext
      change (M.toPerm 1).val = 0
      exact h
    have hlt := (M.toPerm 1).isLt
    omega
  apply Equiv.ext
  intro i
  fin_cases i
  · exact hzero
  · exact hone

instance canonicalMatching_one_subsingleton : Subsingleton (PerfectMatching 1) where
  allEq M N := by
    apply Subtype.ext
    exact (canonicalMatching_one_toPerm M).trans (canonicalMatching_one_toPerm N).symm

instance canonicalMatching_one_unique : Unique (PerfectMatching 1) where
  default := standardCanonicalMatching 1
  uniq M := Subsingleton.elim _ _

@[simp] theorem sum_canonicalMatching_one {α : Type*} [AddCommMonoid α]
    (f : PerfectMatching 1 → α) : ∑ M, f M = f (standardCanonicalMatching 1) := by
  exact Fintype.sum_unique f

@[simp] theorem kappa_one (g : Equiv.Perm (Fin (2 * 1))) : kappa g = 1 := by
  unfold kappa
  have hle := matchingKappa_le (standardPairPartition 1) (transportedPairPartition g)
  have hpos := matchingKappa_pos (by decide : 0 < 1)
    (standardPairPartition 1) (transportedPairPartition g)
  omega

theorem pairPartition_one_toPerm (M : PM 1) :
    M = standardPairPartition 1 := by
  apply (matchingKappa_eq_iff M (standardPairPartition 1)).mp
  have hle := matchingKappa_le M (standardPairPartition 1)
  have hpos := matchingKappa_pos (by decide : 0 < 1) M (standardPairPartition 1)
  omega

instance pairPartition_one_subsingleton : Subsingleton (PM 1) where
  allEq M N := (pairPartition_one_toPerm M).trans (pairPartition_one_toPerm N).symm

instance pairPartition_one_unique : Unique (PM 1) where
  default := standardPairPartition 1
  uniq M := pairPartition_one_toPerm M

end MatsumotoPaper
