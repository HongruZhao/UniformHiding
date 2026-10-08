import A2.Target
import A2.SpectrumTakagi

noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem canonicalGapSquaredSpectrum_permutation_of_sqrt_unitary_congruence {N : ℕ}
    (C : ConcreteMatrixState N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)
    (hC : C = (U : ConcreteMatrixState N) *
      Matrix.diagonal (fun i ↦ (Real.sqrt (lambda i) : ℂ)) *
        (U : ConcreteMatrixState N).transpose) :
    ∃ sigma : Equiv.Perm (Fin N), canonicalGapSquaredSpectrum N C = lambda ∘ sigma := by
  obtain ⟨sigma, hsigma⟩ := canonicalGapSquaredSpectrum_permutation_of_unitary_congruence
    C U (fun i ↦ Real.sqrt (lambda i)) hC
  have hsquare : (fun i ↦ Real.sqrt (lambda i) ^ 2) = lambda :=
    funext fun i ↦ Real.sq_sqrt (hlambda i)
  exact ⟨sigma, hsquare ▸ hsigma⟩

theorem permutationInvariantSpectralTest_eq_of_unitary_congruence {N : ℕ} {γ : Type}
    (F : (Fin N → ℝ) → γ) (hF : IsPermutationInvariantSpectralTest F)
    (C : ConcreteMatrixState N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (r : Fin N → ℝ)
    (hC : C = (U : ConcreteMatrixState N) *
      Matrix.diagonal (fun i ↦ (r i : ℂ)) * (U : ConcreteMatrixState N).transpose) :
    F (canonicalGapSquaredSpectrum N C) = F (fun i ↦ r i ^ 2) := by
  obtain ⟨sigma, hsigma⟩ := canonicalGapSquaredSpectrum_permutation_of_unitary_congruence C U r hC
  rw [hsigma]
  exact hF sigma (fun i ↦ r i ^ 2)

theorem permutationInvariantSpectralTest_eq_of_sqrt_unitary_congruence {N : ℕ} {γ : Type}
    (F : (Fin N → ℝ) → γ) (hF : IsPermutationInvariantSpectralTest F)
    (C : ConcreteMatrixState N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)
    (hC : C = (U : ConcreteMatrixState N) *
      Matrix.diagonal (fun i ↦ (Real.sqrt (lambda i) : ℂ)) *
        (U : ConcreteMatrixState N).transpose) :
    F (canonicalGapSquaredSpectrum N C) = F lambda := by
  obtain ⟨sigma, hsigma⟩ := canonicalGapSquaredSpectrum_permutation_of_sqrt_unitary_congruence
    C U lambda hlambda hC
  rw [hsigma]
  exact hF sigma lambda

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
