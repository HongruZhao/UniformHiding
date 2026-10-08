import A2.SpectrumMeasurable

open Matrix Set
open scoped Pointwise ComplexOrder MatrixOrder

noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Every literal squared-gap coordinate belongs to the real Gram spectrum. -/
theorem canonicalGapSquaredSpectrum_mem_gram_spectrum {N : ℕ}
    (C : ConcreteMatrixState N) (i : Fin N) :
    canonicalGapSquaredSpectrum N C i ∈ spectrum ℝ (C.conjTranspose * C) := by
  have heig := (coeHermitianGap_isHermitian C).eigenvalues_mem_spectrum_real i
  have hgram : C.conjTranspose * C = 1 - coeHermitianGap C := by
    unfold coeHermitianGap
    abel
  have hspec : spectrum ℝ (1 - coeHermitianGap C) =
      ({1} : Set ℝ) - spectrum ℝ (coeHermitianGap C) := by
    simpa only [map_one] using (spectrum.singleton_sub_eq (coeHermitianGap C) (1 : ℝ)).symm
  change 1 - (coeHermitianGap_isHermitian C).eigenvalues i ∈ _
  rw [hgram, hspec]
  exact Set.sub_mem_sub (by simp) heig

theorem canonicalGapSquaredSpectrum_nonneg {N : ℕ}
    (C : ConcreteMatrixState N) (i : Fin N) :
    0 ≤ canonicalGapSquaredSpectrum N C i := by
  have hmem := canonicalGapSquaredSpectrum_mem_gram_spectrum C i
  rw [(Matrix.isHermitian_conjTranspose_mul_self C).spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨j, hj⟩ := hmem
  rw [← hj]
  exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg C j

theorem canonicalGapSquaredSpectrum_pos_of_det_ne_zero {N : ℕ}
    (C : ConcreteMatrixState N) (hdet : C.det ≠ 0) (i : Fin N) :
    0 < canonicalGapSquaredSpectrum N C i := by
  have hunit : IsUnit C := C.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  have hpos : (C.conjTranspose * C).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self C (Matrix.mulVec_injective_of_isUnit hunit)
  have hmem := canonicalGapSquaredSpectrum_mem_gram_spectrum C i
  rw [hpos.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨j, hj⟩ := hmem
  rw [← hj]
  exact hpos.eigenvalues_pos j

theorem canonicalGapSquaredSpectrum_mem_openPositiveOrthant_of_det_ne_zero {N : ℕ}
    (C : ConcreteMatrixState N) (hdet : C.det ≠ 0) :
    canonicalGapSquaredSpectrum N C ∈ H6CoordinateAlgebra.openPositiveOrthant N :=
  canonicalGapSquaredSpectrum_pos_of_det_ne_zero C hdet

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
