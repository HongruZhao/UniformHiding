import Mathlib

open scoped BigOperators
open Matrix Polynomial

noncomputable section
namespace A3Research

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The polynomial of a finite real root list, interpreted over an RCLike field. -/
def realRootPolynomial {r : ℕ} (lambda : Fin r → ℝ) : Polynomial 𝕜 :=
  ∏ i, (X - C (RCLike.ofReal (lambda i)))

theorem realRootPolynomial_roots_re {r : ℕ} (lambda : Fin r → ℝ) :
    ((realRootPolynomial (𝕜 := 𝕜) lambda).roots.map RCLike.re) =
      Multiset.map lambda Finset.univ.val := by
  unfold realRootPolynomial
  rw [Polynomial.roots_prod]
  · simp [Function.comp_def]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem realRootPolynomial_sort_roots {r : ℕ} (lambda : Fin r → ℝ)
    (hlambda : Antitone lambda) :
    ((realRootPolynomial (𝕜 := 𝕜) lambda).roots.map RCLike.re).sort (· ≥ ·) =
      List.ofFn lambda := by
  rw [realRootPolynomial_roots_re, Fin.univ_val_map, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact hlambda.sortedGE_ofFn

theorem realRootPolynomial_injective_on_antitone {r : ℕ}
    {lambda mu : Fin r → ℝ} (hlambda : Antitone lambda) (hmu : Antitone mu)
    (hpoly : realRootPolynomial (𝕜 := 𝕜) lambda = realRootPolynomial mu) :
    lambda = mu := by
  have h := congrArg (fun p : Polynomial 𝕜 ↦ (p.roots.map RCLike.re).sort (· ≥ ·)) hpoly
  rw [realRootPolynomial_sort_roots lambda hlambda,
    realRootPolynomial_sort_roots mu hmu] at h
  simpa only [List.ofFn_inj] using h

theorem charpoly_eq_realRootPolynomial_eigenvalues₀ {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    A.charpoly = realRootPolynomial hA.eigenvalues₀ := by
  rw [hA.charpoly_eq]
  unfold realRootPolynomial
  simp only [Matrix.IsHermitian.eigenvalues]
  exact Equiv.prod_comp
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun i ↦ (X : Polynomial 𝕜) - C (RCLike.ofReal (hA.eigenvalues₀ i)))

end A3Research
