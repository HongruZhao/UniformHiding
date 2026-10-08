import A4.MatchingGramSymplectic
import Mathlib.Algebra.Polynomial.Roots

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def coloringBinomialPolynomial (r : ℕ) : Polynomial ℝ :=
  Polynomial.C ((r.factorial : ℝ)⁻¹) *
    ∏ j : Fin r, (Polynomial.X - Polynomial.C (j.val : ℝ))

theorem eval_coloringBinomialPolynomial (r : ℕ) (gamma : ℝ) :
    (coloringBinomialPolynomial r).eval gamma = coloringBinomialWeight gamma r := by
  simp only [coloringBinomialPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, coloringBinomialWeight]
  ring

theorem natDegree_coloringBinomialPolynomial_le (r : ℕ) :
    (coloringBinomialPolynomial r).natDegree ≤ r := by
  unfold coloringBinomialPolynomial
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have h := Polynomial.natDegree_prod_le (s := Finset.univ)
    (f := fun j : Fin r ↦ Polynomial.X - Polynomial.C (j.val : ℝ))
  apply h.trans
  calc
    _ ≤ ∑ _ : Fin r, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [sub_eq_add_neg]
      apply Polynomial.natDegree_add_le_of_degree_le <;> simp
    _ = r := by simp

def symplecticFeatureEntryPolynomial {n : ℕ} (M N : PM n) : Polynomial ℝ :=
  ∑ r : Fin (n + 1),
    coloringBinomialPolynomial r.val *
      Polynomial.C (((matchingSymplecticFeature n r.val)ᴴ *
        matchingSymplecticFeature n r.val) M N)

theorem eval_symplecticFeatureEntryPolynomial {n : ℕ} (M N : PM n) (gamma : ℝ) :
    (symplecticFeatureEntryPolynomial M N).eval gamma =
      symplecticFeatureExpansion n gamma M N := by
  simp only [symplecticFeatureEntryPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, eval_coloringBinomialPolynomial]
  simp only [symplecticFeatureExpansion, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]

theorem natDegree_symplecticFeatureEntryPolynomial_le {n : ℕ} (M N : PM n) :
    (symplecticFeatureEntryPolynomial M N).natDegree ≤ n := by
  unfold symplecticFeatureEntryPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r _
  exact (Polynomial.natDegree_mul_C_le _ _).trans
    ((natDegree_coloringBinomialPolynomial_le r.val).trans (by omega))

def signedNegativeGramEntryPolynomial {n : ℕ} (M N : PM n) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ) ^ n * matchingOrientation M * matchingOrientation N) *
    (Polynomial.C (-2) * Polynomial.X) ^ matchingKappa M N

theorem eval_signedNegativeGramEntryPolynomial {n : ℕ} (M N : PM n) (gamma : ℝ) :
    (signedNegativeGramEntryPolynomial M N).eval gamma =
      signedNegativeOrthogonalGram n gamma M N := by
  simp only [signedNegativeGramEntryPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, signedNegativeOrthogonalGram]

theorem natDegree_signedNegativeGramEntryPolynomial_le {n : ℕ} (M N : PM n) :
    (signedNegativeGramEntryPolynomial M N).natDegree ≤ n := by
  unfold signedNegativeGramEntryPolynomial
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have hbase : (Polynomial.C (-2 : ℝ) * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hpow := Polynomial.natDegree_pow_le_of_le (matchingKappa M N) hbase
  simpa using hpow.trans (by simpa using matchingKappa_le M N)

/-- Exact finite polynomial interpolation extends the discrete symplectic
color identity to every real parameter. The discrete equality is the only
remaining combinatorial premise of this bridge. -/
theorem symplecticFeatureExpansion_eq_of_samples (n : ℕ)
    (sample : Fin (n + 1) → ℝ) (hinj : Function.Injective sample)
    (hsample : ∀ i, symplecticFeatureExpansion n (sample i) =
      signedNegativeOrthogonalGram n (sample i)) (gamma : ℝ) :
    symplecticFeatureExpansion n gamma = signedNegativeOrthogonalGram n gamma := by
  ext M N
  have hpoly : symplecticFeatureEntryPolynomial M N =
      signedNegativeGramEntryPolynomial M N := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj
    · intro i
      rw [eval_symplecticFeatureEntryPolynomial, eval_signedNegativeGramEntryPolynomial,
        hsample i]
    · simpa using Nat.lt_succ_of_le (max_le
        (natDegree_symplecticFeatureEntryPolynomial_le M N)
        (natDegree_signedNegativeGramEntryPolynomial_le M N))
  have h := congrArg (fun P : Polynomial ℝ ↦ P.eval gamma) hpoly
  simpa only [eval_symplecticFeatureEntryPolynomial,
    eval_signedNegativeGramEntryPolynomial] using h

/-- Integer color identities above degree `n` suffice for the complete
real-parameter expansion and consequently its sharp positivity range. -/
theorem symplecticFeatureExpansion_eq_of_nat (n : ℕ)
    (hnat : ∀ k : ℕ, n ≤ k →
      symplecticFeatureExpansion n (k : ℝ) = signedNegativeOrthogonalGram n (k : ℝ))
    (gamma : ℝ) :
    symplecticFeatureExpansion n gamma = signedNegativeOrthogonalGram n gamma := by
  apply symplecticFeatureExpansion_eq_of_samples n
    (fun i : Fin (n + 1) ↦ ((n + i.val : ℕ) : ℝ))
  · intro i j h
    change ((n + i.val : ℕ) : ℝ) = ((n + j.val : ℕ) : ℝ) at h
    have hnat : n + i.val = n + j.val := by exact_mod_cast h
    exact Fin.ext (Nat.add_left_cancel hnat)
  · intro i
    exact hnat (n + i.val) (by omega)

end MatsumotoPaper
