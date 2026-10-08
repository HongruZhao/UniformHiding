import A2.SpectrumPermutation

open Matrix

noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The Hermitian gap of a supplied real diagonal unitary congruence. -/
theorem coeHermitianGap_diagonalization_of_unitary_congruence {N : ℕ}
    (C : ConcreteMatrixState N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (r : Fin N → ℝ)
    (hC : C = (U : ConcreteMatrixState N) *
      Matrix.diagonal (fun i ↦ (r i : ℂ)) * (U : ConcreteMatrixState N).transpose) :
    coeHermitianGap C =
      (star (Matrix.UnitaryGroup.transpose U) : ConcreteMatrixState N) *
        Matrix.diagonal (fun i ↦ ((1 - r i ^ 2 : ℝ) : ℂ)) *
          star (star (Matrix.UnitaryGroup.transpose U) : ConcreteMatrixState N) := by
  let D : ConcreteMatrixState N := Matrix.diagonal (fun i ↦ (r i : ℂ))
  let T : Matrix.unitaryGroup (Fin N) ℂ := Matrix.UnitaryGroup.transpose U
  have hC' : C = (U : ConcreteMatrixState N) * D * (T : ConcreteMatrixState N) := hC
  have hD : star D = D := by simp [D, Matrix.star_eq_conjTranspose]
  have hgram : star C * C =
      star (T : ConcreteMatrixState N) * (D * D) * (T : ConcreteMatrixState N) := by
    rw [hC']
    calc
      _ = star (T : ConcreteMatrixState N) * D *
          (star (U : ConcreteMatrixState N) * (U : ConcreteMatrixState N)) *
            D * (T : ConcreteMatrixState N) := by
        simp only [star_mul, hD, mul_assoc]
      _ = star (T : ConcreteMatrixState N) * (D * D) * (T : ConcreteMatrixState N) := by
        rw [Unitary.coe_star_mul_self]
        simp only [mul_one, mul_assoc]
  have hDsq : D * D = Matrix.diagonal (fun i ↦ ((r i ^ 2 : ℝ) : ℂ)) := by
    simp [D, Matrix.diagonal_mul_diagonal, pow_two]
  have hDgap : 1 - D * D = Matrix.diagonal (fun i ↦ ((1 - r i ^ 2 : ℝ) : ℂ)) := by
    rw [hDsq, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp
  have hgap : coeHermitianGap C =
      star (T : ConcreteMatrixState N) *
        Matrix.diagonal (fun i ↦ ((1 - r i ^ 2 : ℝ) : ℂ)) *
          (T : ConcreteMatrixState N) := by
    unfold coeHermitianGap
    change 1 - star C * C = _
    rw [hgram, ← hDgap]
    simp only [mul_sub, sub_mul, mul_one, Unitary.coe_star_mul_self]
  simpa only [Unitary.coe_star, star_star] using hgap

/-- The paper's canonical spectrum agrees up to permutation with the
squared entries of any supplied real Takagi diagonal. -/
theorem canonicalGapSquaredSpectrum_permutation_of_unitary_congruence {N : ℕ}
    (C : ConcreteMatrixState N) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (r : Fin N → ℝ)
    (hC : C = (U : ConcreteMatrixState N) *
      Matrix.diagonal (fun i ↦ (r i : ℂ)) * (U : ConcreteMatrixState N).transpose) :
    ∃ sigma : Equiv.Perm (Fin N),
      canonicalGapSquaredSpectrum N C = (fun i ↦ r i ^ 2) ∘ sigma :=
  canonicalGapSquaredSpectrum_permutation_of_gap_diagonalization C
    (star (Matrix.UnitaryGroup.transpose U)) (fun i ↦ r i ^ 2)
    (coeHermitianGap_diagonalization_of_unitary_congruence C U r hC)

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
