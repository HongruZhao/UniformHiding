import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A3_ProjectSourceBridge
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_BetaJacobiBetaPrimeTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_MuirheadOrderedConditional

/-!
# H6 A3 full-rank GSVD quotient-spectrum bridge

This theorem-only module proves the deterministic algebra missing between the
literal Edelman--Sutton Jacobi matrix and the matrix beta-prime quotient.  It
uses no scientific declaration beyond the separately approved A3 source law
imported by the surrounding project modules.
-/

open scoped BigOperators MatrixOrder ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra

theorem edelmanSuttonFirstGram_posSemidef
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonFirstGram omega).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self omega.1

theorem edelmanSuttonSecondGram_posSemidef
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonSecondGram omega).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self omega.2

theorem edelmanSuttonTotalGram_posSemidef
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonFirstGram omega +
      edelmanSuttonSecondGram omega).PosSemidef := by
  exact (edelmanSuttonFirstGram_posSemidef omega).add
    (edelmanSuttonSecondGram_posSemidef omega)

theorem edelmanSuttonTotalGramSqrt_isHermitian
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonTotalGramSqrt omega).IsHermitian := by
  exact (CFC.sqrt_nonneg
    (edelmanSuttonFirstGram omega +
      edelmanSuttonSecondGram omega)).isSelfAdjoint

theorem edelmanSuttonTotalGramSqrt_square
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    edelmanSuttonFirstGram omega + edelmanSuttonSecondGram omega =
      edelmanSuttonTotalGramSqrt omega *
        edelmanSuttonTotalGramSqrt omega := by
  symm
  exact CFC.sqrt_mul_sqrt_self
    (edelmanSuttonFirstGram omega + edelmanSuttonSecondGram omega)
    (edelmanSuttonTotalGram_posSemidef omega).nonneg

theorem edelmanSuttonJacobiMatrix_eq_inverse_mul_firstGram_mul_inverse
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    edelmanSuttonJacobiMatrix omega =
      (edelmanSuttonTotalGramSqrt omega)⁻¹ *
        edelmanSuttonFirstGram omega *
          (edelmanSuttonTotalGramSqrt omega)⁻¹ := by
  unfold edelmanSuttonJacobiMatrix
  rw [(edelmanSuttonTotalGramSqrt_isHermitian omega).inv.eq]

theorem edelmanSuttonJacobiMatrix_posSemidef
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonJacobiMatrix omega).PosSemidef := by
  rw [edelmanSuttonJacobiMatrix_eq_inverse_mul_firstGram_mul_inverse]
  simpa only [(edelmanSuttonTotalGramSqrt_isHermitian omega).inv.eq] using
    (edelmanSuttonFirstGram_posSemidef omega).mul_mul_conjTranspose_same
      ((edelmanSuttonTotalGramSqrt omega)⁻¹)

theorem edelmanSutton_c_i_sq
    {n a b : ℕ} (beta : ℝ)
    (omega : EdelmanSuttonGaussianPair n a b) (i : Fin n) :
    (edelmanSutton_c_i n a b beta omega i) ^ 2 =
      (edelmanSuttonJacobiMatrix_isHermitian omega).eigenvalues i := by
  unfold edelmanSutton_c_i
  exact Real.sq_sqrt
    ((edelmanSuttonJacobiMatrix_posSemidef omega).eigenvalues_nonneg i)

theorem edelmanSuttonTotalGramSqrt_det_isUnit_of_secondGram
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b)
    (hBdet : IsUnit (edelmanSuttonSecondGram omega).det) :
    IsUnit (edelmanSuttonTotalGramSqrt omega).det := by
  have hBunit : IsUnit (edelmanSuttonSecondGram omega) :=
    (Matrix.isUnit_iff_isUnit_det
      (edelmanSuttonSecondGram omega)).mpr hBdet
  have hBpos : (edelmanSuttonSecondGram omega).PosDef :=
    (edelmanSuttonSecondGram_posSemidef omega).posDef_iff_isUnit.mpr hBunit
  have hTpos :
      (edelmanSuttonFirstGram omega +
        edelmanSuttonSecondGram omega).PosDef :=
    Matrix.PosDef.posSemidef_add
      (edelmanSuttonFirstGram_posSemidef omega) hBpos
  have hTunit : IsUnit
      (edelmanSuttonFirstGram omega +
        edelmanSuttonSecondGram omega) :=
    hTpos.posSemidef.posDef_iff_isUnit.mp hTpos
  have hSunit : IsUnit (edelmanSuttonTotalGramSqrt omega) := by
    apply (CFC.isUnit_sqrt_iff
      (edelmanSuttonFirstGram omega +
        edelmanSuttonSecondGram omega)
          hTpos.posSemidef.nonneg).mpr
    exact hTunit
  exact (Matrix.isUnit_iff_isUnit_det
    (edelmanSuttonTotalGramSqrt omega)).mp hSunit

theorem edelmanSuttonFirstGram_eq_sqrt_mul_jacobi_mul_sqrt
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b)
    (hS : IsUnit (edelmanSuttonTotalGramSqrt omega).det) :
    edelmanSuttonFirstGram omega =
      edelmanSuttonTotalGramSqrt omega *
        edelmanSuttonJacobiMatrix omega *
          edelmanSuttonTotalGramSqrt omega := by
  rw [edelmanSuttonJacobiMatrix_eq_inverse_mul_firstGram_mul_inverse]
  symm
  calc
    edelmanSuttonTotalGramSqrt omega *
          ((edelmanSuttonTotalGramSqrt omega)⁻¹ *
            edelmanSuttonFirstGram omega *
              (edelmanSuttonTotalGramSqrt omega)⁻¹) *
        edelmanSuttonTotalGramSqrt omega =
      (edelmanSuttonTotalGramSqrt omega *
          (edelmanSuttonTotalGramSqrt omega)⁻¹) *
        edelmanSuttonFirstGram omega *
          ((edelmanSuttonTotalGramSqrt omega)⁻¹ *
            edelmanSuttonTotalGramSqrt omega) := by
        noncomm_ring
    _ = edelmanSuttonFirstGram omega := by
      rw [Matrix.mul_nonsing_inv _ hS, Matrix.nonsing_inv_mul _ hS]
      simp

theorem edelmanSuttonSecondGram_eq_sqrt_mul_one_sub_jacobi_mul_sqrt
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b)
    (hS : IsUnit (edelmanSuttonTotalGramSqrt omega).det) :
    edelmanSuttonSecondGram omega =
      edelmanSuttonTotalGramSqrt omega *
        (1 - edelmanSuttonJacobiMatrix omega) *
          edelmanSuttonTotalGramSqrt omega := by
  have hA := edelmanSuttonFirstGram_eq_sqrt_mul_jacobi_mul_sqrt omega hS
  have hT := edelmanSuttonTotalGramSqrt_square omega
  calc
    edelmanSuttonSecondGram omega =
        (edelmanSuttonFirstGram omega +
          edelmanSuttonSecondGram omega) -
            edelmanSuttonFirstGram omega := by abel
    _ = edelmanSuttonTotalGramSqrt omega *
          edelmanSuttonTotalGramSqrt omega -
            edelmanSuttonFirstGram omega := by rw [hT]
    _ = edelmanSuttonTotalGramSqrt omega *
          edelmanSuttonTotalGramSqrt omega -
        edelmanSuttonTotalGramSqrt omega *
          edelmanSuttonJacobiMatrix omega *
            edelmanSuttonTotalGramSqrt omega := by rw [hA]
    _ = edelmanSuttonTotalGramSqrt omega *
        (1 - edelmanSuttonJacobiMatrix omega) *
          edelmanSuttonTotalGramSqrt omega := by noncomm_ring

def edelmanSuttonJacobiOddsMatrix
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 - edelmanSuttonJacobiMatrix omega)⁻¹ *
    edelmanSuttonJacobiMatrix omega

theorem inverse_common_congruence_ratio
    {n : ℕ} {S A B J : Matrix (Fin n) (Fin n) ℂ}
    (hS : IsUnit S.det)
    (hA : A = S * J * S)
    (hB : B = S * (1 - J) * S) :
    B⁻¹ * A = S⁻¹ * ((1 - J)⁻¹ * J) * S := by
  rw [hA, hB]
  letI := Matrix.invertibleOfIsUnitDet S hS
  simp only [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible,
    Matrix.mul_assoc]
  have hcancel : S⁻¹ * (S * (J * S)) = J * S := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, one_mul]
  rw [hcancel]

theorem edelmanSutton_fullRank_ratio_eq_inverse_conjugate_odds
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b)
    (hBdet : IsUnit (edelmanSuttonSecondGram omega).det) :
    (edelmanSuttonSecondGram omega)⁻¹ *
        edelmanSuttonFirstGram omega =
      (edelmanSuttonTotalGramSqrt omega)⁻¹ *
        edelmanSuttonJacobiOddsMatrix omega *
          edelmanSuttonTotalGramSqrt omega := by
  have hS :=
    edelmanSuttonTotalGramSqrt_det_isUnit_of_secondGram omega hBdet
  exact inverse_common_congruence_ratio hS
    (edelmanSuttonFirstGram_eq_sqrt_mul_jacobi_mul_sqrt omega hS)
    (edelmanSuttonSecondGram_eq_sqrt_mul_one_sub_jacobi_mul_sqrt omega hS)

theorem inverse_conjugate_pow_complex
    {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (hS : IsUnit S.det) :
    (S⁻¹ * X * S) ^ m = S⁻¹ * X ^ m * S := by
  have hconj : SemiconjBy S (S⁻¹ * X * S) X := by
    unfold SemiconjBy
    calc
      S * (S⁻¹ * X * S) = (S * S⁻¹) * X * S := by
        simp only [Matrix.mul_assoc]
      _ = X * S := by rw [Matrix.mul_nonsing_inv S hS, one_mul]
  have hpow := hconj.pow_right m
  calc
    (S⁻¹ * X * S) ^ m =
        S⁻¹ * (S * (S⁻¹ * X * S) ^ m) := by
      rw [Matrix.nonsing_inv_mul_cancel_left S _ hS]
    _ = S⁻¹ * (X ^ m * S) := by rw [hpow.eq]
    _ = S⁻¹ * X ^ m * S := by rw [Matrix.mul_assoc]

theorem trace_inverse_conjugate_pow_complex
    {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (hS : IsUnit S.det) :
    Matrix.trace ((S⁻¹ * X * S) ^ m) = Matrix.trace (X ^ m) := by
  rw [inverse_conjugate_pow_complex S X m hS]
  calc
    Matrix.trace (S⁻¹ * X ^ m * S) =
        Matrix.trace (S * (S⁻¹ * X ^ m)) := by
      rw [Matrix.trace_mul_cycle]
      congr 1
      noncomm_ring
    _ = Matrix.trace ((S * S⁻¹) * X ^ m) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (X ^ m) := by
      rw [Matrix.mul_nonsing_inv S hS, one_mul]

theorem jacobiOdds_inverse_conjugate
    {n : ℕ} (S D : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S.det) :
    (1 - S⁻¹ * D * S)⁻¹ * (S⁻¹ * D * S) =
      S⁻¹ * ((1 - D)⁻¹ * D) * S := by
  have hsub :
      1 - S⁻¹ * D * S = S⁻¹ * (1 - D) * S := by
    calc
      1 - S⁻¹ * D * S =
          S⁻¹ * S - S⁻¹ * D * S := by
        rw [Matrix.nonsing_inv_mul S hS]
      _ = S⁻¹ * (1 - D) * S := by noncomm_ring
  rw [hsub]
  letI := Matrix.invertibleOfIsUnitDet S hS
  simp only [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible,
    Matrix.mul_assoc]
  have hcancel : S * (S⁻¹ * (D * S)) = D * S := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hS, one_mul]
  rw [hcancel]

theorem trace_diagonal_jacobiOdds_pow
    {n : ℕ} (lambda : Fin n → ℝ)
    (hne : ∀ i, (1 - (lambda i : ℂ)) ≠ 0) (m : ℕ) :
    Matrix.trace
        ((((1 : Matrix (Fin n) (Fin n) ℂ) -
          Matrix.diagonal (RCLike.ofReal ∘ lambda))⁻¹ *
            Matrix.diagonal (RCLike.ofReal ∘ lambda)) ^ m) =
      ∑ i : Fin n, ((betaPrimeForward (lambda i) : ℂ) ^ m) := by
  classical
  have hsub :
      (1 : Matrix (Fin n) (Fin n) ℂ) -
          Matrix.diagonal (RCLike.ofReal ∘ lambda) =
        Matrix.diagonal (fun i ↦ (1 - lambda i : ℝ) : Fin n → ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply, Matrix.diagonal, hij]
  have hinv :
      (Matrix.diagonal (fun i ↦ (1 - lambda i : ℝ) : Fin n → ℂ))⁻¹ =
        Matrix.diagonal (fun i ↦ (1 - (lambda i : ℂ))⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hne]
    · simp [Matrix.one_apply, Matrix.diagonal, hij]
  rw [hsub, hinv]
  simp [Matrix.diagonal_pow, betaPrimeForward, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i hi
  change (((1 - (lambda i : ℂ))⁻¹ * (lambda i : ℂ)) ^ m) =
    (((lambda i : ℂ) * (1 - (lambda i : ℂ))⁻¹) ^ m)
  rw [mul_comm]

theorem trace_edelmanSuttonJacobiOdds_pow
    {n a b : ℕ} (beta : ℝ)
    (omega : EdelmanSuttonGaussianPair n a b)
    (hOneSubDet : IsUnit
      (1 - edelmanSuttonJacobiMatrix omega).det)
    (m : ℕ) :
    Matrix.trace ((edelmanSuttonJacobiOddsMatrix omega) ^ m) =
      ∑ i : Fin n,
        ((betaPrimeForward
          ((edelmanSutton_c_i n a b beta omega i) ^ 2) : ℂ) ^ m) := by
  let hJ := edelmanSuttonJacobiMatrix_isHermitian omega
  let U := hJ.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hJ.eigenvalues)
  have hSinv : (star (U : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
      (U : Matrix (Fin n) (Fin n) ℂ) := by
    exact Matrix.inv_eq_left_inv (Unitary.coe_mul_star_self U)
  have hSunit : IsUnit (star (U : Matrix (Fin n) (Fin n) ℂ)) := by
    simpa only [Unitary.coe_star] using
      (Unitary.isUnit_coe (U := star U))
  have hSdet : IsUnit (star (U : Matrix (Fin n) (Fin n) ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSunit
  have hspec : edelmanSuttonJacobiMatrix omega =
      (star (U : Matrix (Fin n) (Fin n) ℂ))⁻¹ * D *
        star (U : Matrix (Fin n) (Fin n) ℂ) := by
    simpa only [D, U, hSinv, Unitary.conjStarAlgAut_apply] using
      hJ.spectral_theorem
  have hsub :
      1 - edelmanSuttonJacobiMatrix omega =
        (star (U : Matrix (Fin n) (Fin n) ℂ))⁻¹ *
          (1 - D) * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hspec]
    calc
      1 - (star (U : Matrix (Fin n) (Fin n) ℂ))⁻¹ * D * star U =
          (star (U : Matrix (Fin n) (Fin n) ℂ))⁻¹ * star U -
            (star (U : Matrix (Fin n) (Fin n) ℂ))⁻¹ * D * star U := by
        rw [hSinv, Unitary.coe_mul_star_self]
      _ = (star (U : Matrix (Fin n) (Fin n) ℂ))⁻¹ *
          (1 - D) * star U := by noncomm_ring
  have hDdet : IsUnit (1 - D).det := by
    rw [hsub, Matrix.det_mul, Matrix.det_mul] at hOneSubDet
    exact (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hOneSubDet).1).2
  have hDunit : IsUnit (1 - D) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hDdet
  have hdiag :
      (1 - D : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun i ↦ (1 - hJ.eigenvalues i : ℝ) : Fin n → ℂ) := by
    dsimp [D]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply, Matrix.diagonal, hij]
  have hfunUnit : IsUnit
      (fun i ↦ (1 - hJ.eigenvalues i : ℝ) : Fin n → ℂ) := by
    apply Matrix.isUnit_diagonal.mp
    rw [← hdiag]
    exact hDunit
  have hne : ∀ i, (1 - (hJ.eigenvalues i : ℂ)) ≠ 0 := by
    intro i
    simpa using (hfunUnit.apply i).ne_zero
  unfold edelmanSuttonJacobiOddsMatrix
  rw [hspec, jacobiOdds_inverse_conjugate _ _ hSdet]
  rw [trace_inverse_conjugate_pow_complex _ _ m hSdet]
  rw [trace_diagonal_jacobiOdds_pow hJ.eigenvalues hne m]
  apply Finset.sum_congr rfl
  intro i hi
  rw [edelmanSutton_c_i_sq beta omega i]

/-- Full-rank GSVD quotient-spectrum identity in literal paper variables. -/
theorem edelmanSutton_fullRank_quotient_trace_pow_eq_odds
    {n a b : ℕ} (beta : ℝ)
    (omega : EdelmanSuttonGaussianPair n a b)
    (hBdet : IsUnit (edelmanSuttonSecondGram omega).det)
    (m : ℕ) :
    Matrix.trace
        (((edelmanSuttonSecondGram omega)⁻¹ *
          edelmanSuttonFirstGram omega) ^ m) =
      ∑ i : Fin n,
        ((betaPrimeForward
          ((edelmanSutton_c_i n a b beta omega i) ^ 2) : ℂ) ^ m) := by
  have hS :=
    edelmanSuttonTotalGramSqrt_det_isUnit_of_secondGram omega hBdet
  have hBfac :=
    edelmanSuttonSecondGram_eq_sqrt_mul_one_sub_jacobi_mul_sqrt omega hS
  have hOneSubDet : IsUnit
      (1 - edelmanSuttonJacobiMatrix omega).det := by
    have hBdet' := hBdet
    rw [hBfac, Matrix.det_mul, Matrix.det_mul] at hBdet'
    exact (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hBdet').1).2
  rw [edelmanSutton_fullRank_ratio_eq_inverse_conjugate_odds omega hBdet]
  rw [trace_inverse_conjugate_pow_complex _ _ m hS]
  exact trace_edelmanSuttonJacobiOdds_pow beta omega hOneSubDet m

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
