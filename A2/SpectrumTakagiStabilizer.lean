import A2.TakagiOrbit
import A2.SpectrumInvariant

open scoped Matrix

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

abbrev TakagiSigns (N : ℕ) := Fin N → Bool

def takagiSignValue {N : ℕ} (epsilon : TakagiSigns N) (i : Fin N) : ℂ :=
  if epsilon i then -1 else 1

def takagiSignUnitary {N : ℕ} (epsilon : TakagiSigns N) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨Matrix.diagonal (takagiSignValue epsilon), by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    cases h : epsilon i <;> simp [takagiSignValue, h]⟩

theorem takagiSignUnitary_injective {N : ℕ} :
    Function.Injective (takagiSignUnitary : TakagiSigns N → _) := by
  intro epsilon eta h
  funext i
  have hi := congrArg (fun U : Matrix.unitaryGroup (Fin N) ℂ => U i i) h
  have hi' : takagiSignValue epsilon i = takagiSignValue eta i := by
    simpa only [takagiSignUnitary, Matrix.diagonal_apply_eq] using hi
  cases he : epsilon i <;> cases hf : eta i <;>
    simp [takagiSignValue, he, hf] at hi' ⊢
  all_goals norm_num at hi'

theorem takagiOrbit_mul {N : ℕ}
    (U V : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    takagiOrbit (U * V) lambda =
      (U : Matrix (Fin N) (Fin N) ℂ) * takagiOrbit V lambda *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose := by
  simp [takagiOrbit, Matrix.transpose_mul, Matrix.mul_assoc]

theorem takagiOrbit_signUnitary {N : ℕ}
    (epsilon : TakagiSigns N) (lambda : Fin N → ℝ) :
    takagiOrbit (takagiSignUnitary epsilon) lambda =
      Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ)) := by
  simp only [takagiOrbit, takagiSignUnitary, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  cases h : epsilon i <;> simp [takagiSignValue, h]

theorem takagiOrbit_mul_sign {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (epsilon : TakagiSigns N)
    (lambda : Fin N → ℝ) :
    takagiOrbit (U * takagiSignUnitary epsilon) lambda = takagiOrbit U lambda := by
  rw [takagiOrbit_mul, takagiOrbit_signUnitary]
  rfl

theorem takagiOrbit_mul_conjTranspose {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) :
    takagiOrbit U lambda * (takagiOrbit U lambda).conjTranspose =
      (U : Matrix (Fin N) (Fin N) ℂ) *
        Matrix.diagonal (fun i => (lambda i : ℂ)) *
          star (U : Matrix (Fin N) (Fin N) ℂ) := by
  let D : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ))
  let T := Matrix.UnitaryGroup.transpose U
  have hD : star D = D := by simp [D, Matrix.star_eq_conjTranspose]
  have hDsq : D * D = Matrix.diagonal (fun i => (lambda i : ℂ)) := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    exact Real.mul_self_sqrt (hlambda i)
  change ((U : Matrix (Fin N) (Fin N) ℂ) * D * (T : Matrix (Fin N) (Fin N) ℂ)) *
    star ((U : Matrix (Fin N) (Fin N) ℂ) * D * (T : Matrix (Fin N) (Fin N) ℂ)) = _
  calc
    _ = (U : Matrix (Fin N) (Fin N) ℂ) * D *
        ((T : Matrix (Fin N) (Fin N) ℂ) * star (T : Matrix (Fin N) (Fin N) ℂ)) *
          D * star (U : Matrix (Fin N) (Fin N) ℂ) := by
      simp only [star_mul, hD, Matrix.mul_assoc]
    _ = (U : Matrix (Fin N) (Fin N) ℂ) * (D * D) *
        star (U : Matrix (Fin N) (Fin N) ℂ) := by
      rw [T.property.2]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hDsq]

theorem takagiStabilizer_commutes_squaredDiagonal {N : ℕ}
    (P : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (hP : takagiOrbit P lambda =
      Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ))) :
    Commute (P : Matrix (Fin N) (Fin N) ℂ)
      (Matrix.diagonal (fun i => (lambda i : ℂ))) := by
  apply (commute_unitary_iff_star_right_conjugate P.property).mpr
  rw [← takagiOrbit_mul_conjTranspose P lambda hlambda, hP]
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  congr 1
  funext i
  norm_cast
  exact Real.mul_self_sqrt (hlambda i)

theorem takagiStabilizer_offDiagonal_zero {N : ℕ}
    (P : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda)
    (hP : takagiOrbit P lambda =
      Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ)))
    (i j : Fin N) (hij : i ≠ j) : P i j = 0 := by
  have hcomm := takagiStabilizer_commutes_squaredDiagonal P lambda
    (fun i => le_of_lt (hlambda.1 i)) hP
  have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A i j) hcomm.eq
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hneq : (lambda j : ℂ) ≠ (lambda i : ℂ) := by
    intro h
    exact hij (hlambda.2 (Complex.ofReal_injective h)).symm
  have hz : P i j * ((lambda j : ℂ) - (lambda i : ℂ)) = 0 := by
    rw [mul_sub, he, mul_comm]
    exact sub_self _
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hneq)

theorem takagiStabilizer_eq_diagonal {N : ℕ}
    (P : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda)
    (hP : takagiOrbit P lambda =
      Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ))) :
    (P : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal (fun i => P i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [takagiStabilizer_offDiagonal_zero P lambda hlambda hP i j hij]
    simp [Matrix.diagonal_apply, hij]

theorem takagiStabilizer_diagonal_sq {N : ℕ}
    (P : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda)
    (hP : takagiOrbit P lambda =
      Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ))) (i : Fin N) :
    P i i ^ 2 = 1 := by
  have hdiag := takagiStabilizer_eq_diagonal P lambda hlambda hP
  have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A i i) hP
  simp only [takagiOrbit] at he
  rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at he
  have hs : (Real.sqrt (lambda i) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (hlambda.1 i))
  apply (mul_right_cancel₀ hs)
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using he

theorem takagiStabilizer_exists_unique_sign {N : ℕ}
    (P : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda)
    (hP : takagiOrbit P lambda =
      Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ))) :
    ∃! epsilon : TakagiSigns N, P = takagiSignUnitary epsilon := by
  let epsilon : TakagiSigns N := fun i => decide (P i i = -1)
  have hsign : ∀ i, P i i = takagiSignValue epsilon i := by
    intro i
    have hi : P i i = 1 ∨ P i i = -1 := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      simpa using takagiStabilizer_diagonal_sq P lambda hlambda hP i
    rcases hi with hi | hi <;> simp [takagiSignValue, epsilon, hi]
  have he : P = takagiSignUnitary epsilon := by
    apply Subtype.ext
    rw [takagiStabilizer_eq_diagonal P lambda hlambda hP]
    change Matrix.diagonal (fun i => P i i) = Matrix.diagonal (takagiSignValue epsilon)
    congr 1
    exact funext hsign
  refine ⟨epsilon, he, ?_⟩
  intro eta heta
  exact takagiSignUnitary_injective (heta.symm.trans he)

theorem takagiOrbit_eq_iff_exists_unique_sign {N : ℕ}
    (U V : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) :
    takagiOrbit V lambda = takagiOrbit U lambda ↔
      ∃! epsilon : TakagiSigns N, V = U * takagiSignUnitary epsilon := by
  constructor
  · intro h
    have hP : takagiOrbit (star U * V) lambda =
        Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ)) := by
      rw [takagiOrbit_mul, h, ← takagiOrbit_mul]
      simp [takagiOrbit]
    obtain ⟨epsilon, he, huniq⟩ :=
      takagiStabilizer_exists_unique_sign (star U * V) lambda hlambda hP
    refine ⟨epsilon, ?_, ?_⟩
    · calc
        V = U * (star U * V) := by simp [← mul_assoc]
        _ = _ := by rw [he]
    · intro eta heta
      apply huniq eta
      rw [heta]
      simp [← mul_assoc]
  · rintro ⟨epsilon, he, _⟩
    rw [he, takagiOrbit_mul_sign]

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
