import A2.SpectrumTakagiStabilizer

open scoped Matrix

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiPermutationUnitary {N : ℕ} (sigma : Equiv.Perm (Fin N)) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨sigma.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp⟩

theorem takagiPermutation_congruence_diagonal {N : ℕ}
    (sigma : Equiv.Perm (Fin N)) (r : Fin N → ℂ) :
    (takagiPermutationUnitary sigma : Matrix (Fin N) (Fin N) ℂ) *
        Matrix.diagonal r *
          (takagiPermutationUnitary sigma : Matrix (Fin N) (Fin N) ℂ).transpose =
      Matrix.diagonal (r ∘ sigma) := by
  change sigma.permMatrix ℂ * Matrix.diagonal r * (sigma.permMatrix ℂ).transpose = _
  rw [Matrix.transpose_permMatrix]
  change sigma.toPEquiv.toMatrix * Matrix.diagonal r * sigma.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp, Equiv.symm_symm] using
    Matrix.submatrix_diagonal_equiv r sigma

theorem takagiOrbit_permutationUnitary {N : ℕ}
    (sigma : Equiv.Perm (Fin N)) (lambda : Fin N → ℝ) :
    takagiOrbit (takagiPermutationUnitary sigma) lambda =
      Matrix.diagonal (fun i => (Real.sqrt ((lambda ∘ sigma) i) : ℂ)) := by
  exact takagiPermutation_congruence_diagonal sigma _

theorem takagiOrbit_mul_permutation {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (sigma : Equiv.Perm (Fin N))
    (lambda : Fin N → ℝ) :
    takagiOrbit (U * takagiPermutationUnitary sigma) lambda =
      takagiOrbit U (lambda ∘ sigma) := by
  rw [takagiOrbit_mul, takagiOrbit_permutationUnitary]
  rfl

theorem IsRegularTakagiSpectrum.comp_perm {N : ℕ} {lambda : Fin N → ℝ}
    (hlambda : IsRegularTakagiSpectrum lambda) (sigma : Equiv.Perm (Fin N)) :
    IsRegularTakagiSpectrum (lambda ∘ sigma) :=
  ⟨fun i => hlambda.1 (sigma i), hlambda.2.comp sigma.injective⟩

theorem takagiOrbit_eq_spectrum_permutation {N : ℕ}
    (U V : Matrix.unitaryGroup (Fin N) ℂ) (lambda mu : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) (hmu : IsRegularTakagiSpectrum mu)
    (h : takagiOrbit V mu = takagiOrbit U lambda) :
    ∃! sigma : Equiv.Perm (Fin N), mu = lambda ∘ sigma := by
  obtain ⟨a, ha⟩ := canonicalGapSquaredSpectrum_permutation_of_sqrt_unitary_congruence
    (takagiOrbit U lambda) U lambda (fun i => le_of_lt (hlambda.1 i)) rfl
  obtain ⟨b, hb⟩ := canonicalGapSquaredSpectrum_permutation_of_sqrt_unitary_congruence
    (takagiOrbit V mu) V mu (fun i => le_of_lt (hmu.1 i)) rfl
  rw [h] at hb
  have hab : mu ∘ b = lambda ∘ a := hb.symm.trans ha
  let sigma : Equiv.Perm (Fin N) := b.symm.trans a
  have hsigma : mu = lambda ∘ sigma := by
    funext i
    simpa only [sigma, Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply] using
      congrFun hab (b.symm i)
  refine ⟨sigma, hsigma, ?_⟩
  intro tau htau
  apply Equiv.ext
  intro i
  exact hlambda.2 (congrFun (htau.symm.trans hsigma) i)

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
