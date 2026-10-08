import A4.MatchingGramCanonical
import A4.MatchingGramColoring

/-!
# Positive feature frames for the negative-parameter Gram route

The features are literal oriented symplectic colorings.  The top color layer
has a row separating every matching, so its Gram matrix is positive
definite.  Falling-factorial coefficients are positive in the full required
range `gamma > n - 1`.  Identifying the weighted feature sum with the signed
matching Gram matrix is a separate combinatorial obligation.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def SymplecticColoring (n r : ℕ) :=
  {a : Fin (2 * n) → Fin r × Fin 2 // Function.Surjective (fun i => (a i).1)}

instance symplecticColoring_finite (n r : ℕ) : Finite (SymplecticColoring n r) := by
  unfold SymplecticColoring
  infer_instance

instance symplecticColoring_fintype (n r : ℕ) : Fintype (SymplecticColoring n r) :=
  Fintype.ofFinite _

def matchingSymplecticTensor {n r : ℕ} (M : PM n)
    (a : Fin (2 * n) → Fin r × Fin 2) : ℝ :=
  ∏ i ∈ M.pairReps,
    if (a i).1 = (a (M i)).1 ∧ (a i).2 ≠ (a (M i)).2 then
      if (a i).2 = 0 then 1 else -1
    else 0

def matchingSymplecticFeature (n r : ℕ) : Matrix (SymplecticColoring n r) (PM n) ℝ :=
  fun a M => matchingSymplecticTensor M a.val

def matchingSeparatingColor {n : ℕ} (M : PM n) : Fin (2 * n) → Fin n × Fin 2 :=
  (indexedMatchingEquiv M).symm

@[simp] theorem matchingSeparatingColor_left {n : ℕ} (M : PM n) (i : Fin n) :
    matchingSeparatingColor M (matchingPairOrder M i) = (i, 0) := by
  rw [← indexedMatchingVertex_zero M i]
  change (indexedMatchingEquiv M).symm (indexedMatchingEquiv M (i, 0)) = _
  exact (indexedMatchingEquiv M).symm_apply_apply _

@[simp] theorem matchingSeparatingColor_right {n : ℕ} (M : PM n) (i : Fin n) :
    matchingSeparatingColor M (M (matchingPairOrder M i)) = (i, 1) := by
  rw [← indexedMatchingVertex_one M i]
  change (indexedMatchingEquiv M).symm (indexedMatchingEquiv M (i, 1)) = _
  exact (indexedMatchingEquiv M).symm_apply_apply _

def matchingSeparatingColoring {n : ℕ} (M : PM n) : SymplecticColoring n n :=
  ⟨matchingSeparatingColor M, fun i =>
    ⟨matchingPairOrder M i, congrArg Prod.fst (matchingSeparatingColor_left M i)⟩⟩

@[simp] theorem matchingSymplecticTensor_separating_self {n : ℕ} (M : PM n) :
    matchingSymplecticTensor M (matchingSeparatingColor M) = 1 := by
  classical
  unfold matchingSymplecticTensor
  apply Finset.prod_eq_one
  intro j hj
  obtain ⟨i, rfl⟩ := matchingPairOrder_surjective M hj
  simp only [matchingSeparatingColor_left, matchingSeparatingColor_right]
  norm_num

theorem matchingSeparatingColor_eq_iff {n : ℕ} (M : PM n) (i j : Fin (2 * n)) :
    (matchingSeparatingColor M i).1 = (matchingSeparatingColor M j).1 ↔
      j = i ∨ j = M i := by
  constructor
  · intro h
    obtain ⟨⟨k, b⟩, rfl⟩ := (indexedMatchingEquiv M).surjective i
    obtain ⟨⟨l, c⟩, rfl⟩ := (indexedMatchingEquiv M).surjective j
    have hkl : k = l := by
      simpa only [matchingSeparatingColor, Equiv.symm_apply_apply] using h
    subst l
    fin_cases b <;> fin_cases c
    · exact Or.inl rfl
    · right
      change indexedMatchingVertex M (k, 1) = M (indexedMatchingVertex M (k, 0))
      rw [indexedMatchingVertex_one, indexedMatchingVertex_zero]
    · right
      change indexedMatchingVertex M (k, 0) = M (indexedMatchingVertex M (k, 1))
      rw [indexedMatchingVertex_one, indexedMatchingVertex_zero, M.apply_apply]
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · rfl
    · obtain ⟨⟨k, b⟩, rfl⟩ := (indexedMatchingEquiv M).surjective i
      fin_cases b
      · change (matchingSeparatingColor M (indexedMatchingVertex M (k, 0))).1 =
          (matchingSeparatingColor M (M (indexedMatchingVertex M (k, 0)))).1
        simp only [indexedMatchingVertex_zero, matchingSeparatingColor_left,
          matchingSeparatingColor_right]
      · change (matchingSeparatingColor M (indexedMatchingVertex M (k, 1))).1 =
          (matchingSeparatingColor M (M (indexedMatchingVertex M (k, 1)))).1
        simp only [indexedMatchingVertex_one, M.apply_apply,
          matchingSeparatingColor_left, matchingSeparatingColor_right]

theorem matchingSymplecticTensor_nonzero_color {n r : ℕ} (M : PM n)
    (a : Fin (2 * n) → Fin r × Fin 2)
    (ha : matchingSymplecticTensor M a ≠ 0) (i : Fin (2 * n)) :
    (a (M i)).1 = (a i).1 := by
  classical
  have hp : ∀ j ∈ M.pairReps, (a j).1 = (a (M j)).1 := by
    intro j hj
    have hf := (Finset.prod_ne_zero_iff.mp ha) j hj
    by_contra h
    simp only [h, false_and, if_false] at hf
    exact hf rfl
  rcases (M.exactly_one_mem_pairReps i).1 with hi | hi
  · exact (hp i hi).symm
  · simpa only [M.apply_apply] using hp (M i) hi

theorem matchingSymplecticTensor_separating_ne {n : ℕ} (M N : PM n) (hMN : N ≠ M) :
    matchingSymplecticTensor N (matchingSeparatingColor M) = 0 := by
  by_contra h
  apply hMN
  apply pairPartition_ext
  intro i
  have hcolor := matchingSymplecticTensor_nonzero_color N (matchingSeparatingColor M) h i
  rcases (matchingSeparatingColor_eq_iff M i (N i)).mp hcolor.symm with hi | hi
  · exact False.elim (N.apply_ne i hi)
  · exact hi

@[simp] theorem matchingSymplecticFeature_separating {n : ℕ} (M N : PM n) :
    matchingSymplecticFeature n n (matchingSeparatingColoring M) N =
      if N = M then 1 else 0 := by
  classical
  by_cases h : N = M
  · subst N
    simp only [matchingSymplecticFeature, matchingSeparatingColoring,
      matchingSymplecticTensor_separating_self, if_true]
  · simp only [matchingSymplecticFeature, matchingSeparatingColoring,
      matchingSymplecticTensor_separating_ne M N h, if_neg h]

theorem matchingSymplecticFeature_mulVec_separating {n : ℕ} (x : PM n → ℝ) (M : PM n) :
    (matchingSymplecticFeature n n *ᵥ x) (matchingSeparatingColoring M) = x M := by
  classical
  simp only [Matrix.mulVec, dotProduct, matchingSymplecticFeature_separating,
    ite_mul, one_mul, zero_mul]
  simpa only [Finset.mem_univ, if_true] using Finset.sum_ite_eq' Finset.univ M x

theorem matchingSymplecticFeature_top_injective (n : ℕ) :
    Function.Injective (matchingSymplecticFeature n n).mulVec := by
  intro x y h
  funext M
  have hm := congrFun h (matchingSeparatingColoring M)
  simpa only [matchingSymplecticFeature_mulVec_separating] using hm

theorem matchingSymplecticFeature_top_posDef (n : ℕ) :
    ((matchingSymplecticFeature n n)ᴴ * matchingSymplecticFeature n n).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (matchingSymplecticFeature_top_injective n)

def coloringBinomialWeight (gamma : ℝ) (r : ℕ) : ℝ :=
  (∏ j : Fin r, (gamma - j.val)) / r.factorial

theorem coloringBinomialWeight_pos {n r : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) (hr : r ≤ n) :
    0 < coloringBinomialWeight gamma r := by
  unfold coloringBinomialWeight
  apply div_pos
  · apply Finset.prod_pos
    intro j hj
    have hj : j.val + 1 ≤ n := by omega
    have hjR : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hj
    linarith
  · exact_mod_cast Nat.factorial_pos r

theorem posDef_sum_of_one_posDef {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : κ → Matrix ι ι ℝ) (hA : ∀ k, (A k).PosSemidef)
    (j : κ) (hj : (A j).PosDef) : (∑ k, A k).PosDef := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  apply Matrix.PosDef.posSemidef_add _ hj
  exact Matrix.posSemidef_sum _ (fun k _ => hA k)

def symplecticFeatureExpansion (n : ℕ) (gamma : ℝ) : Matrix (PM n) (PM n) ℝ :=
  ∑ r : Fin (n + 1), coloringBinomialWeight gamma r.val •
    ((matchingSymplecticFeature n r.val)ᴴ * matchingSymplecticFeature n r.val)

theorem symplecticFeatureExpansion_posDef {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) : (symplecticFeatureExpansion n gamma).PosDef := by
  classical
  unfold symplecticFeatureExpansion
  apply posDef_sum_of_one_posDef _
    (fun r => (Matrix.posSemidef_conjTranspose_mul_self _).smul
      (coloringBinomialWeight_pos gamma hgamma (by omega)).le)
    (⟨n, by omega⟩ : Fin (n + 1))
  exact (matchingSymplecticFeature_top_posDef n).smul
    (coloringBinomialWeight_pos gamma hgamma (le_refl n))

def matchingOrientation {n : ℕ} (M : PM n) : ℝ :=
  ((Equiv.Perm.sign (canonicalMatchingPermutation M) : ℤˣ) : ℤ)

def realOrthogonalGram (n : ℕ) (z : ℝ) : Matrix (PM n) (PM n) ℝ :=
  fun M N => z ^ matchingKappa M N

def signedNegativeOrthogonalGram (n : ℕ) (gamma : ℝ) : Matrix (PM n) (PM n) ℝ :=
  fun M N => (-1 : ℝ) ^ n * matchingOrientation M * matchingOrientation N *
    (-2 * gamma) ^ matchingKappa M N

theorem signedNegativeOrthogonalGram_eq_diagonal_conjugation (n : ℕ) (gamma : ℝ) :
    signedNegativeOrthogonalGram n gamma =
      Matrix.diagonal (matchingOrientation (n := n)) *
        ((-1 : ℝ) ^ n • realOrthogonalGram n (-2 * gamma)) *
          Matrix.diagonal (matchingOrientation (n := n)) := by
  classical
  ext M N
  simp only [signedNegativeOrthogonalGram, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul, realOrthogonalGram]
  ring

theorem realOrthogonalGram_map_complex (n : ℕ) (z : ℝ) :
    (realOrthogonalGram n z).map Complex.ofRealHom = orthogonalGram n (z : ℂ) := by
  ext M N
  change ((z ^ matchingKappa M N : ℝ) : ℂ) = (z : ℂ) ^ matchingKappa M N
  exact Complex.ofReal_pow _ _

/-- The missing signed expansion identity suffices for the exact required Gram nonsingularity. -/
theorem orthogonalGram_isUnit_of_symplecticFeatureExpansion {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma)
    (hexpansion : symplecticFeatureExpansion n gamma = signedNegativeOrthogonalGram n gamma) :
    IsUnit (orthogonalGram n (-2 * (gamma : ℂ))).det := by
  classical
  have hpos : (signedNegativeOrthogonalGram n gamma).PosDef := by
    rw [← hexpansion]
    exact symplecticFeatureExpansion_posDef gamma hgamma
  have hdet : (realOrthogonalGram n (-2 * gamma)).det ≠ 0 := by
    intro hzero
    apply ne_of_gt hpos.det_pos
    rw [signedNegativeOrthogonalGram_eq_diagonal_conjugation,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, hzero]
    ring
  have hmap := Complex.ofRealHom.map_det (realOrthogonalGram n (-2 * gamma))
  change (((realOrthogonalGram n (-2 * gamma)).det : ℝ) : ℂ) =
    ((realOrthogonalGram n (-2 * gamma)).map Complex.ofRealHom).det at hmap
  rw [realOrthogonalGram_map_complex] at hmap
  have harg : ((-2 * gamma : ℝ) : ℂ) = -2 * (gamma : ℂ) := by push_cast; rfl
  rw [harg] at hmap
  have hgram : (orthogonalGram n (-2 * (gamma : ℂ))).det ≠ 0 := by
    have hcast : ((realOrthogonalGram n (-2 * gamma)).det : ℂ) ≠ 0 := by
      exact_mod_cast hdet
    rwa [← hmap]
  exact isUnit_iff_ne_zero.mpr hgram

end MatsumotoPaper
