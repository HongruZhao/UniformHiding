import A2.SpectrumRoots

open scoped BigOperators
open Matrix Polynomial

noncomputable section
namespace A2Research

theorem exists_perm_of_multiset_map_univ_eq {r : ℕ}
    {f g : Fin r → ℝ}
    (hmap : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ sigma : Equiv.Perm (Fin r), f = g ∘ sigma := by
  classical
  have hfiber (y : ℝ) :
      Fintype.card {i : Fin r // f i = y} = Fintype.card {i : Fin r // g i = y} := by
    have hc := congrArg (Multiset.count y) hmap
    simpa only [Multiset.count_map, ← Finset.filter_val, Finset.card_def,
      Fintype.card_subtype, eq_comm] using hc
  let e (y : ℝ) : {i : Fin r // f i = y} ≃ {i : Fin r // g i = y} :=
    Fintype.equivOfCardEq (hfiber y)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map e i).symm

variable {𝕜 : Type*} [RCLike 𝕜]

theorem charpoly_eq_realRootPolynomial_eigenvalues {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian) :
    A.charpoly = realRootPolynomial hA.eigenvalues :=
  hA.charpoly_eq

theorem eigenvalues_permutation_of_charpoly_eq {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (lambda : Fin N → ℝ) (hpoly : A.charpoly = realRootPolynomial lambda) :
    ∃ sigma : Equiv.Perm (Fin N), hA.eigenvalues = lambda ∘ sigma := by
  have hroots := congrArg (fun p : Polynomial 𝕜 ↦ p.roots.map RCLike.re) hpoly
  rw [realRootPolynomial_roots_re] at hroots
  have hmap : Multiset.map hA.eigenvalues Finset.univ.val =
      Multiset.map lambda Finset.univ.val := by
    simpa [hA.roots_charpoly_eq_eigenvalues, Function.comp_def] using hroots
  exact exists_perm_of_multiset_map_univ_eq hmap

theorem charpoly_unitary_conjugation {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) 𝕜) (A : Matrix (Fin N) (Fin N) 𝕜) :
    ((U : Matrix (Fin N) (Fin N) 𝕜) * A * star (U : Matrix (Fin N) (Fin N) 𝕜)).charpoly =
      A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

theorem eigenvalues_permutation_of_unitary_diagonalization {N : ℕ}
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup (Fin N) 𝕜) (lambda : Fin N → ℝ)
    (hdiag : A = (U : Matrix (Fin N) (Fin N) 𝕜) *
      Matrix.diagonal (RCLike.ofReal ∘ lambda) * star (U : Matrix (Fin N) (Fin N) 𝕜)) :
    ∃ sigma : Equiv.Perm (Fin N), hA.eigenvalues = lambda ∘ sigma := by
  apply eigenvalues_permutation_of_charpoly_eq hA lambda
  rw [hdiag, charpoly_unitary_conjugation, Matrix.charpoly_diagonal]
  rfl

end A2Research

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem canonicalGapSquaredSpectrum_permutation_of_gap_diagonalization {N : ℕ}
    (C : ConcreteMatrixState N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ)
    (hdiag : coeHermitianGap C = (U : ConcreteMatrixState N) *
      Matrix.diagonal (fun i ↦ ((1 - lambda i : ℝ) : ℂ)) *
        star (U : ConcreteMatrixState N)) :
    ∃ sigma : Equiv.Perm (Fin N), canonicalGapSquaredSpectrum N C = lambda ∘ sigma := by
  obtain ⟨sigma, hsigma⟩ := A2Research.eigenvalues_permutation_of_unitary_diagonalization
    (coeHermitianGap_isHermitian C) U (fun i ↦ 1 - lambda i) hdiag
  refine ⟨sigma, ?_⟩
  funext i
  simp [canonicalGapSquaredSpectrum, hsigma, Function.comp_def]

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
