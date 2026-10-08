import A4.MatchingGramSymplecticContraction
import A4.MatchingGramPolynomialExtension

/-!
# The unconditional signed negative matching Gram expansion

Exact finite-color contractions and exact used-color counting prove the
identity at every natural color parameter above the degree.  Polynomial
interpolation then proves it for every real parameter.  Positive feature
weights give the full `gamma > n - 1` nonsingularity theorem.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem symplecticFeatureExpansion_nat (n k : ℕ) (hk : n ≤ k) :
    symplecticFeatureExpansion n (k : ℝ) = signedNegativeOrthogonalGram n (k : ℝ) := by
  classical
  ext M N
  have hcount := pow_card_eq_sum_surjective_ranks_bounded
    (α := MatchingComponent M N)
    (show Fintype.card (MatchingComponent M N) ≤ n by
      rw [card_matchingComponent]; exact matchingKappa_le M N) hk
  rw [card_matchingComponent] at hcount
  have hcountR : (k : ℝ) ^ matchingKappa M N =
      ∑ r : Fin (n + 1), (k.choose r.val : ℝ) *
        (Fintype.card (SurjectiveFiniteMap (MatchingComponent M N) (Fin r.val)) : ℝ) := by
    exact_mod_cast hcount
  calc
    _ = ∑ r : Fin (n + 1), (k.choose r.val : ℝ) *
        ((matchingOrientation M * matchingOrientation N *
          (-1 : ℝ) ^ (n + matchingKappa M N)) *
          (2 : ℝ) ^ matchingKappa M N *
          (Fintype.card (SurjectiveFiniteMap (MatchingComponent M N) (Fin r.val)) : ℝ)) := by
      simp only [symplecticFeatureExpansion, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, coloringBinomialWeight_nat, matchingSymplecticFeature_gram_entry]
    _ = (matchingOrientation M * matchingOrientation N *
        (-1 : ℝ) ^ (n + matchingKappa M N)) * (2 : ℝ) ^ matchingKappa M N *
        ∑ r : Fin (n + 1), (k.choose r.val : ℝ) *
          (Fintype.card (SurjectiveFiniteMap (MatchingComponent M N) (Fin r.val)) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = (matchingOrientation M * matchingOrientation N *
        (-1 : ℝ) ^ (n + matchingKappa M N)) * (2 : ℝ) ^ matchingKappa M N *
        (k : ℝ) ^ matchingKappa M N := by rw [← hcountR]
    _ = signedNegativeOrthogonalGram n (k : ℝ) M N := by
      unfold signedNegativeOrthogonalGram
      have hpow : (-2 * (k : ℝ)) ^ matchingKappa M N =
          (-1 : ℝ) ^ matchingKappa M N * (2 : ℝ) ^ matchingKappa M N *
            (k : ℝ) ^ matchingKappa M N := by
        calc
          _ = ((-1 : ℝ) * 2 * (k : ℝ)) ^ matchingKappa M N := by congr 1; ring
          _ = _ := by rw [mul_pow, mul_pow]
      rw [pow_add, hpow]
      ring

theorem symplecticFeatureExpansion_eq (n : ℕ) (gamma : ℝ) :
    symplecticFeatureExpansion n gamma = signedNegativeOrthogonalGram n gamma :=
  symplecticFeatureExpansion_eq_of_nat n (fun k hk => symplecticFeatureExpansion_nat n k hk) gamma

theorem signedNegativeOrthogonalGram_posDef {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) : (signedNegativeOrthogonalGram n gamma).PosDef := by
  rw [← symplecticFeatureExpansion_eq n gamma]
  exact symplecticFeatureExpansion_posDef gamma hgamma

theorem orthogonalGram_isUnit_det_negative {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) :
    IsUnit (orthogonalGram n (-2 * (gamma : ℂ))).det :=
  orthogonalGram_isUnit_of_symplecticFeatureExpansion gamma hgamma
    (symplecticFeatureExpansion_eq n gamma)

end MatsumotoPaper
