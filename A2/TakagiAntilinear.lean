import A2.TakagiOrbit

open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiConjugateAction {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin N → ℂ) : Fin N → ℂ := C *ᵥ star v

theorem takagiConjugateAction_add {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (v w : Fin N → ℂ) :
    takagiConjugateAction C (v + w) = takagiConjugateAction C v + takagiConjugateAction C w := by
  simp [takagiConjugateAction, Matrix.mulVec_add]

theorem takagiConjugateAction_smul {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (a : ℂ) (v : Fin N → ℂ) :
    takagiConjugateAction C (a • v) = star a • takagiConjugateAction C v := by
  simp [takagiConjugateAction, Matrix.mulVec_smul, star_smul]

theorem takagiConjugateAction_real_smul {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (a : ℝ) (v : Fin N → ℂ) :
    takagiConjugateAction C (a • v) = a • takagiConjugateAction C v := by
  simp [takagiConjugateAction, Matrix.mulVec_smul, star_smul]

theorem star_takagiConjugateAction {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : C.transpose = C) (v : Fin N → ℂ) :
    star (takagiConjugateAction C v) = C.conjTranspose *ᵥ v := by
  ext i
  simp only [takagiConjugateAction, Matrix.mulVec, dotProduct, Pi.star_apply,
    star_sum, star_mul, star_star, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : C i j = C j i :=
    (congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hC).symm
  rw [hij]
  ring

theorem takagiConjugateAction_square {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : C.transpose = C) (v : Fin N → ℂ) :
    takagiConjugateAction C (takagiConjugateAction C v) = (C * C.conjTranspose) *ᵥ v := by
  change C *ᵥ star (takagiConjugateAction C v) = _
  rw [star_takagiConjugateAction C hC, Matrix.mulVec_mulVec]

theorem takagiConjugateAction_dot_symmetry {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : C.transpose = C) (v w : Fin N → ℂ) :
    star (takagiConjugateAction C v) ⬝ᵥ w = star (takagiConjugateAction C w) ⬝ᵥ v := by
  rw [star_takagiConjugateAction C hC, star_takagiConjugateAction C hC]
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : C i j = C j i :=
    (congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hC).symm
  rw [hij]
  ring

theorem takagiConjugateAction_eq_zero_of_square_zero {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.transpose = C) (v : Fin N → ℂ)
    (hv : takagiConjugateAction C (takagiConjugateAction C v) = 0) :
    takagiConjugateAction C v = 0 := by
  apply dotProduct_star_self_eq_zero.mp
  rw [takagiConjugateAction_dot_symmetry C hC, hv, star_zero, zero_dotProduct]

/-- A nonzero eigenvector of the square of the conjugate action yields a
nonzero Takagi vector, including the zero singular value. -/
theorem exists_takagiVector_of_square_eigenvector {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.transpose = C)
    (v : Fin N → ℂ) (hv : v ≠ 0) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (heigen : takagiConjugateAction C (takagiConjugateAction C v) = lambda • v) :
    ∃ u : Fin N → ℂ, u ≠ 0 ∧ takagiConjugateAction C u = Real.sqrt lambda • u := by
  by_cases hz : lambda = 0
  · subst lambda
    refine ⟨v, hv, ?_⟩
    simpa using takagiConjugateAction_eq_zero_of_square_zero C hC v (by simpa using heigen)
  · let r := Real.sqrt lambda
    have hr : r ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hlambda (Ne.symm hz))).ne'
    have hrsq : r ^ 2 = lambda := Real.sq_sqrt hlambda
    let w : Fin N → ℂ := v + r⁻¹ • takagiConjugateAction C v
    have hw : takagiConjugateAction C w = r • w := by
      change takagiConjugateAction C (v + r⁻¹ • takagiConjugateAction C v) =
        r • (v + r⁻¹ • takagiConjugateAction C v)
      rw [takagiConjugateAction_add, takagiConjugateAction_real_smul, heigen]
      have hinv : r⁻¹ * lambda = r := by rw [← hrsq]; field_simp
      rw [smul_smul, hinv, smul_add, smul_smul, mul_inv_cancel₀ hr, one_smul]
      exact add_comm _ _
    by_cases hw0 : w = 0
    · have hTv : takagiConjugateAction C v = -(r • v) := by
        have hwi := congrArg (fun z : Fin N → ℂ => r • z) hw0
        change r • (v + r⁻¹ • takagiConjugateAction C v) = r • (0 : Fin N → ℂ) at hwi
        rw [smul_add, smul_smul, mul_inv_cancel₀ hr, one_smul, smul_zero] at hwi
        exact eq_neg_of_add_eq_zero_right hwi
      refine ⟨Complex.I • v, ?_, ?_⟩
      · exact smul_ne_zero Complex.I_ne_zero hv
      · rw [takagiConjugateAction_smul, hTv]
        ext i
        simp [Complex.star_def, Complex.real_smul]
        ring
    · exact ⟨w, hw0, hw⟩

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
