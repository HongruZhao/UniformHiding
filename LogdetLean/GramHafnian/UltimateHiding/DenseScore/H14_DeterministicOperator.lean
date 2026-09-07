import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_Proof
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteOrbitalEventGeometry
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# H14 deterministic operator estimate

This file supplies the concrete matrix/operator layer behind the H14
pointwise majorant.  It is independent of every probability or inverse-
Wishart moment estimate.

The matrix called `h14ConcreteXHYMatrix` is the literal operator paired with
the centered direction in the second score.  The factor `2` is included so
that

`h14CenteredSandwichSecondScore = -2 Re Tr(Q_v XHY)`.

The proof records, separately:

* the operational trace-norm estimate `||Q_v||_1 <= 2`, expressed by its
  dual trace-pairing inequality;
* `||Q_v||_op <= 1` and `||Q_v.transpose||_op <= 1`;
* `||Y||_op <= sqrt (Re Tr(Y^2))` for Hermitian `Y`;
* `||h14ConcreteXHYMatrix||_op <= 4 y u`;
* the requested pointwise score bound with
  `y = sqrt (concreteCOETraceTwo N K A)`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder
open scoped Matrix.Norms.L2Operator
open scoped InnerProductSpace

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open Matrix Unitary
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-! ## Euclidean operator-norm trace pairing -/

/-- The coordinate projective trace pairing is the Euclidean Rayleigh
pairing of the corresponding matrix operator. -/
theorem complexProjectiveTracePair_eq_euclideanInner_h14
    {N : ℕ} (v : ComplexUnitSphere N) (X : ConcreteMatrixState N) :
    complexProjectiveTracePair v X =
      ⟪v.1, ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) X) v.1⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM]
  unfold complexProjectiveTracePair complexRankOneProjection
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (v.1 j * star (v.1 i)) (X i j), ← mul_assoc]
  simp only [Pi.star_apply]

/-- A unit-vector Rayleigh pairing is bounded by the Euclidean operator
norm, without any self-adjointness assumption on the matrix. -/
theorem norm_euclideanInner_matrix_le_l2_opNorm_h14
    {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) (X : ConcreteMatrixState N)
    (hx : ‖x‖ = 1) :
    ‖⟪x, ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) X) x⟫_ℂ‖ ≤ ‖X‖ := by
  calc
    ‖⟪x, ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) X) x⟫_ℂ‖ ≤
        ‖x‖ * ‖((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) X) x‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x‖ *
        (‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) X‖ * ‖x‖) := by
      gcongr
      exact (((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) X).le_opNorm x)
    _ = ‖X‖ := by rw [hx, Matrix.l2_opNorm_toEuclideanCLM]; ring

/-- The uncentered projective trace pairing has dual norm at most one. -/
theorem norm_complexProjectiveTracePair_le_l2_opNorm_h14
    {N : ℕ} (v : ComplexUnitSphere N) (X : ConcreteMatrixState N) :
    ‖complexProjectiveTracePair v X‖ ≤ ‖X‖ := by
  rw [complexProjectiveTracePair_eq_euclideanInner_h14]
  apply norm_euclideanInner_matrix_le_l2_opNorm_h14
  exact mem_sphere_zero_iff_norm.mp v.2

/-- Every diagonal entry is bounded by the Euclidean operator norm. -/
theorem norm_matrix_diagonal_entry_le_l2_opNorm_h14
    {N : ℕ} (X : ConcreteMatrixState N) (i : Fin N) :
    ‖X i i‖ ≤ ‖X‖ := by
  let e : EuclideanSpace ℂ (Fin N) :=
    WithLp.toLp 2 (Pi.single i (1 : ℂ))
  have he : ‖e‖ = 1 := by
    simp [e, PiLp.norm_single]
  have hinner := norm_euclideanInner_matrix_le_l2_opNorm_h14 e X he
  have hcoord :
      ⟪e, ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)) X) e⟫_ℂ = X i i := by
    classical
    simp [e, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanCLM, dotProduct, Matrix.mulVec,
      Pi.single_apply, eq_comm]
  simpa only [hcoord] using hinner

/-- The trace is bounded by dimension times the Euclidean operator norm. -/
theorem norm_trace_le_card_mul_l2_opNorm_h14
    {N : ℕ} (X : ConcreteMatrixState N) :
    ‖Matrix.trace X‖ ≤ (N : ℝ) * ‖X‖ := by
  rw [Matrix.trace]
  calc
    ‖∑ i, X i i‖ ≤ ∑ i, ‖X i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ‖X‖ := by
      exact Finset.sum_le_sum fun i _ ↦
        norm_matrix_diagonal_entry_le_l2_opNorm_h14 X i
    _ = (N : ℝ) * ‖X‖ := by simp

/-- Operational form of `||Q_v||_1 <= 2`: the trace pairing against every
matrix is bounded by twice its Euclidean operator norm.  This is the exact
dual-norm statement used below, so no opaque nuclear-norm API is required. -/
theorem concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (X : ConcreteMatrixState N) :
    ‖Matrix.trace (concreteCenteredOrbitalDirection N v * X)‖ ≤
      2 * ‖X‖ := by
  rw [trace_concreteCenteredOrbitalDirection_mul]
  unfold complexCenteredProjectiveTracePair
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hPair := norm_complexProjectiveTracePair_le_l2_opNorm_h14 v X
  have hTrace := norm_trace_le_card_mul_l2_opNorm_h14 X
  have hcoef :
      ‖(((((N : ℝ)⁻¹ : ℝ) : ℂ)) * Matrix.trace X)‖ ≤ ‖X‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hNpos)]
    calc
      (N : ℝ)⁻¹ * ‖Matrix.trace X‖ ≤
          (N : ℝ)⁻¹ * ((N : ℝ) * ‖X‖) :=
        mul_le_mul_of_nonneg_left hTrace (inv_nonneg.mpr hNpos.le)
      _ = ‖X‖ := by field_simp
  calc
    ‖complexProjectiveTracePair v X -
        (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace X‖ ≤
        ‖complexProjectiveTracePair v X‖ +
          ‖((((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace X)‖ :=
      norm_sub_le _ _
    _ ≤ ‖X‖ + ‖X‖ := add_le_add hPair hcoef
    _ = 2 * ‖X‖ := by ring

/-- Real-part corollary of the operational trace-one bound. -/
theorem abs_re_trace_centeredDirection_mul_le_two_h14
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (X : ConcreteMatrixState N) :
    |(Matrix.trace (concreteCenteredOrbitalDirection N v * X)).re| ≤
      2 * ‖X‖ :=
  (Complex.abs_re_le_norm _).trans
    (concreteCenteredOrbitalDirection_traceOne_dual_le_two_h14 hN v X)

/-! ## Operator norm of the centered direction -/

/-- A Hermitian idempotent has Euclidean operator norm at most one. -/
theorem l2_opNorm_le_one_of_isHermitian_idempotent_h14
    {N : ℕ} (P : ConcreteMatrixState N) (hPherm : P.IsHermitian)
    (hPidem : P * P = P) :
    ‖P‖ ≤ 1 := by
  have hsquare : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self P, hPherm.eq, hPidem]
  nlinarith [norm_nonneg P]

/-- For dimension at least two, centering a Hermitian idempotent by `I/N`
has Euclidean operator norm at most one. -/
theorem l2_opNorm_idempotent_sub_invCard_one_le_one_h14
    {N : ℕ} (hNtwo : 2 ≤ N) (P : ConcreteMatrixState N)
    (hPherm : P.IsHermitian) (hPidem : P * P = P) :
    ‖P - ((((N : ℝ)⁻¹ : ℝ) : ℂ) •
        (1 : ConcreteMatrixState N))‖ ≤ 1 := by
  let a : ℝ := (N : ℝ)⁻¹
  let Q : ConcreteMatrixState N :=
    P - (((a : ℝ) : ℂ) • (1 : ConcreteMatrixState N))
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hNtwo
  have hNpos : (0 : ℝ) < N := by linarith
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have ha0 : 0 ≤ a := inv_nonneg.mpr hNpos.le
  have haha : a ≤ 1 / 2 := by
    dsimp only [a]
    simpa only [one_div] using
      (inv_le_inv₀ hNpos (by norm_num : (0 : ℝ) < 2)).mpr hNreal
  have hPnorm : ‖P‖ ≤ 1 :=
    l2_opNorm_le_one_of_isHermitian_idempotent_h14 P hPherm hPidem
  have hQherm : Q.IsHermitian := by
    dsimp only [Q]
    apply hPherm.sub
    apply Matrix.isHermitian_one.smul
    simp [IsSelfAdjoint]
  have hQsq : Q * Q =
      ((((1 - 2 * a : ℝ) : ℂ)) • P) +
        ((((a ^ 2 : ℝ) : ℂ)) • (1 : ConcreteMatrixState N)) := by
    dsimp only [Q]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hPidem,
      smul_smul]
    module
  have hcoef0 : 0 ≤ 1 - 2 * a := by linarith
  have hcoefNorm : ‖(((1 - 2 * a : ℝ) : ℂ))‖ = 1 - 2 * a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
  have haSqNorm : ‖(((a ^ 2 : ℝ) : ℂ))‖ = a ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  have hQsqNorm : ‖Q * Q‖ ≤ 1 := by
    rw [hQsq]
    calc
      ‖(((1 - 2 * a : ℝ) : ℂ) • P) +
          (((a ^ 2 : ℝ) : ℂ) • (1 : ConcreteMatrixState N))‖ ≤
          ‖(((1 - 2 * a : ℝ) : ℂ) • P)‖ +
            ‖(((a ^ 2 : ℝ) : ℂ) • (1 : ConcreteMatrixState N))‖ :=
        norm_add_le _ _
      _ = (1 - 2 * a) * ‖P‖ + a ^ 2 := by
        rw [norm_smul, norm_smul, hcoefNorm, haSqNorm,
          CStarRing.norm_one, mul_one]
      _ ≤ (1 - 2 * a) * 1 + a ^ 2 := by
        gcongr
      _ ≤ 1 := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr haha)]
  have hnormsq : ‖Q‖ * ‖Q‖ = ‖Q * Q‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self Q, hQherm.eq]
  have hQsquared : ‖Q‖ ^ 2 ≤ 1 := by
    rw [pow_two, hnormsq]
    exact hQsqNorm
  have hQnonneg : 0 ≤ ‖Q‖ := norm_nonneg Q
  have : ‖Q‖ ≤ 1 := by nlinarith
  simpa only [Q, a] using this

/-- The actual centered projective direction has operator norm at most one. -/
theorem concreteCenteredOrbitalDirection_l2_opNorm_le_one_h14
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    ‖concreteCenteredOrbitalDirection N v‖ ≤ 1 := by
  rcases hN.eq_or_lt with hNone | hNlt
  · subst N
    rw [concreteCenteredOrbitalDirection_fin_one_eq_zero]
    simp
  · have hNtwo : 2 ≤ N := by omega
    unfold concreteCenteredOrbitalDirection
    exact l2_opNorm_idempotent_sub_invCard_one_le_one_h14 hNtwo
      (complexRankOneProjection v)
      (by
        rw [Matrix.IsHermitian]
        ext i j
        simp [Matrix.conjTranspose_apply, complexRankOneProjection]
        ring)
      (complexRankOneProjection_mul_self v)

/-- The transpose centered direction obeys the same operator-norm bound. -/
theorem concreteCenteredOrbitalDirection_transpose_l2_opNorm_le_one_h14
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    ‖(concreteCenteredOrbitalDirection N v).transpose‖ ≤ 1 := by
  rcases hN.eq_or_lt with hNone | hNlt
  · subst N
    rw [concreteCenteredOrbitalDirection_fin_one_eq_zero,
      Matrix.transpose_zero]
    simp
  · have hNtwo : 2 ≤ N := by omega
    rw [concreteCenteredOrbitalDirection, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one]
    apply l2_opNorm_idempotent_sub_invCard_one_le_one_h14 hNtwo
    · exact (by
        rw [Matrix.IsHermitian]
        ext i j
        simp [Matrix.conjTranspose_apply, complexRankOneProjection]
        ring : (complexRankOneProjection v).IsHermitian).transpose
    · rw [← Matrix.transpose_mul, complexRankOneProjection_mul_self]

/-! ## Hermitian trace-square control -/

/-- The Euclidean operator norm of a Hermitian matrix is bounded by its
Hilbert--Schmidt norm, here written as `sqrt (Re Tr(Y^2))`. -/
theorem hermitian_l2_opNorm_le_sqrt_trace_mul_self_re_h14
    {N : ℕ} (hN : 1 ≤ N) (Y : ConcreteMatrixState N)
    (hY : Y.IsHermitian) :
    ‖Y‖ ≤ Real.sqrt (Matrix.trace (Y * Y)).re := by
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  let U := hY.eigenvectorUnitary
  let lambda : Fin N → ℝ := hY.eigenvalues
  let D : ConcreteMatrixState N :=
    Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ))
  have htraceComplex : Matrix.trace (Y * Y) =
      ∑ i, (((lambda i : ℝ) : ℂ) ^ 2) := by
    have hspectral := hY.spectral_theorem
    rw [← pow_two]
    conv_lhs => rw [hspectral]
    rw [← map_pow]
    rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  have htraceReal : (Matrix.trace (Y * Y)).re =
      ∑ i, lambda i ^ 2 := by
    rw [htraceComplex, Complex.re_sum]
    norm_cast
  have hdiag : ‖D‖ ≤ Real.sqrt (Matrix.trace (Y * Y)).re := by
    rw [show D = Matrix.diagonal
        (fun i ↦ ((lambda i : ℝ) : ℂ)) by rfl,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [htraceReal]
    have hi : lambda i ^ 2 ≤ ∑ j, lambda j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (lambda j))
        (Finset.mem_univ i)
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hi
  have hnormDiagonal : ‖Y‖ = ‖D‖ := by
    have hspectral := hY.spectral_theorem
    rw [hspectral]
    change ‖conjStarAlgAut ℂ (ConcreteMatrixState N) U D‖ = ‖D‖
    rw [conjStarAlgAut_apply]
    calc
      ‖(U : ConcreteMatrixState N) * D * star (U : ConcreteMatrixState N)‖ =
          ‖(U : ConcreteMatrixState N) * D *
            ((star U : Matrix.unitaryGroup (Fin N) ℂ) :
              ConcreteMatrixState N)‖ := by rw [Unitary.coe_star]
      _ = ‖(U : ConcreteMatrixState N) * D‖ :=
        CStarRing.norm_mul_coe_unitary _ (star U)
      _ = ‖D‖ := CStarRing.norm_coe_unitary_mul U D
  rw [hnormDiagonal]
  exact hdiag

/-- Concrete specialization of the preceding spectral estimate. -/
theorem concreteCOEY_l2_opNorm_le_sqrt_traceTwo_h14
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ‖concreteCOEY N K A‖ ≤
      Real.sqrt (concreteCOETraceTwo N K A) := by
  change ‖concreteCOEY N K A‖ ≤
    Real.sqrt (Matrix.trace
      (concreteCOEY N K A * concreteCOEY N K A)).re
  exact hermitian_l2_opNorm_le_sqrt_trace_mul_self_re_h14 hN _
    (concreteCOEY_isHermitian_of_support A hsupport)

/-! ## The concrete `W`, `R`, and `X_HY` model -/

/-- The support matrix `W=I+Y/c` obeys the elementary operator-norm
estimate `||W|| <= 1+y/c`. -/
theorem concreteCOEWMatrix_l2_opNorm_le_h14
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    {y : ℝ} (hc : 0 < concreteCOEExponent N K)
    (hY : ‖concreteCOEY N K A‖ ≤ y) :
    ‖concreteCOEWMatrix N K A‖ ≤
      1 + y / concreteCOEExponent N K := by
  letI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  let c := concreteCOEExponent N K
  have hcInv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hcoef : ‖(((c⁻¹ : ℝ) : ℂ))‖ = c⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcInv]
  unfold concreteCOEWMatrix
  change ‖1 + (((c⁻¹ : ℝ) : ℂ)) • concreteCOEY N K A‖ ≤
    1 + y / c
  calc
    ‖1 + (((c⁻¹ : ℝ) : ℂ)) • concreteCOEY N K A‖ ≤
        ‖(1 : ConcreteMatrixState N)‖ +
          ‖(((c⁻¹ : ℝ) : ℂ)) • concreteCOEY N K A‖ :=
      norm_add_le _ _
    _ = 1 + c⁻¹ * ‖concreteCOEY N K A‖ := by
      rw [CStarRing.norm_one, norm_smul, hcoef]
    _ ≤ 1 + c⁻¹ * y := by
      gcongr
    _ = 1 + y / c := by rw [div_eq_mul_inv, mul_comm]

/-- The support Gram identity controls the squared operator norm of `R`. -/
theorem concreteCOERMatrix_l2_opNorm_sq_le_h14
    {N K : ℕ} (A : ConcreteMatrixState N) {y u : ℝ}
    (hc : 0 < concreteCOEExponent N K)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hY : ‖concreteCOEY N K A‖ ≤ y)
    (hW : ‖concreteCOEWMatrix N K A‖ ≤ u) :
    ‖concreteCOERMatrix N K A‖ ^ 2 ≤ y * u := by
  let R := concreteCOERMatrix N K A
  let Y := concreteCOEY N K A
  let W := concreteCOEWMatrix N K A
  have hGram : R * R.conjTranspose = Y * W := by
    simpa only [R, Y, W] using
      concreteCOERMatrix_mul_conjTranspose_eq_Y_mul_W A hc hsupport
  have hRstar : ‖R.conjTranspose‖ = ‖R‖ :=
    Matrix.l2_opNorm_conjTranspose R
  have hRRnorm : ‖R‖ ^ 2 = ‖R * R.conjTranspose‖ := by
    calc
      ‖R‖ ^ 2 = ‖R.conjTranspose‖ * ‖R.conjTranspose‖ := by
        rw [hRstar]
        ring
      _ = ‖R.conjTranspose.conjTranspose * R.conjTranspose‖ := by
        rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖R * R.conjTranspose‖ := by simp
  rw [hRRnorm, hGram]
  calc
    ‖Y * W‖ ≤ ‖Y‖ * ‖W‖ := Matrix.l2_opNorm_mul Y W
    _ ≤ y * u := mul_le_mul hY hW (norm_nonneg W) hy

/-- The literal matrix paired with `Q_v` in the second score.  It is the
concrete `X_H Y` model after collecting the two sandwich terms. -/
def h14ConcreteXHYMatrix (N K : ℕ) (A : ConcreteMatrixState N)
    (v : ComplexUnitSphere N) : ConcreteMatrixState N :=
  (2 : ℂ) •
    (concreteCOEWMatrix N K A * concreteCenteredOrbitalDirection N v *
        concreteCOEY N K A +
      concreteCOERMatrix N K A *
        (concreteCenteredOrbitalDirection N v).transpose *
          (concreteCOERMatrix N K A).conjTranspose)

/-- `||X_H Y||_op <= 4 y u`, with every factor assumption exposed. -/
theorem h14ConcreteXHYMatrix_l2_opNorm_le_four_h14
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (v : ComplexUnitSphere N) {y u : ℝ}
    (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hY : ‖concreteCOEY N K A‖ ≤ y)
    (hW : ‖concreteCOEWMatrix N K A‖ ≤ u)
    (hR : ‖concreteCOERMatrix N K A‖ ^ 2 ≤ y * u) :
    ‖h14ConcreteXHYMatrix N K A v‖ ≤ 4 * y * u := by
  let Q := concreteCenteredOrbitalDirection N v
  let W := concreteCOEWMatrix N K A
  let Y := concreteCOEY N K A
  let R := concreteCOERMatrix N K A
  have hQ : ‖Q‖ ≤ 1 := by
    simpa only [Q] using
      concreteCenteredOrbitalDirection_l2_opNorm_le_one_h14 hN v
  have hQt : ‖Q.transpose‖ ≤ 1 := by
    simpa only [Q] using
      concreteCenteredOrbitalDirection_transpose_l2_opNorm_le_one_h14 hN v
  have hFirst : ‖W * Q * Y‖ ≤ u * y := by
    calc
      ‖W * Q * Y‖ ≤ ‖W * Q‖ * ‖Y‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖W‖ * ‖Q‖) * ‖Y‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul W Q
      _ ≤ (u * 1) * y := by
        gcongr
      _ = u * y := by ring
  have hRstar : ‖R.conjTranspose‖ = ‖R‖ :=
    Matrix.l2_opNorm_conjTranspose R
  have hSecond : ‖R * Q.transpose * R.conjTranspose‖ ≤ y * u := by
    calc
      ‖R * Q.transpose * R.conjTranspose‖ ≤
          ‖R * Q.transpose‖ * ‖R.conjTranspose‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖R‖ * ‖Q.transpose‖) * ‖R‖ := by
        rw [hRstar]
        gcongr
        exact Matrix.l2_opNorm_mul R Q.transpose
      _ ≤ (‖R‖ * 1) * ‖R‖ := by gcongr
      _ = ‖R‖ ^ 2 := by ring
      _ ≤ y * u := hR
  unfold h14ConcreteXHYMatrix
  change ‖(2 : ℂ) • (W * Q * Y + R * Q.transpose * R.conjTranspose)‖ ≤
    4 * y * u
  rw [norm_smul]
  norm_num
  calc
    2 * ‖W * Q * Y + R * Q.transpose * R.conjTranspose‖ ≤
        2 * (‖W * Q * Y‖ + ‖R * Q.transpose * R.conjTranspose‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ 2 * (u * y + y * u) := by gcongr
    _ = 4 * y * u := by ring

/-! ## Exact trace bookkeeping for the score -/

theorem concreteCenteredOrbitalDirection_apply_eq_projection_h14
    {N : ℕ} (v : ComplexUnitSphere N) (i j : Fin N) :
    concreteCenteredOrbitalDirection N v i j =
      complexCenteredRankOneProjection N v i j := by
  simp [concreteCenteredOrbitalDirection, complexCenteredRankOneProjection,
    complexRankOneProjection, Matrix.one_apply]

/-- Public coordinate verification of
`Tr(Q_v W Q_v Y)=complexCenteredProjectiveSandwich v W Y`. -/
theorem trace_centered_sandwich_eq_h14
    {N : ℕ} (v : ComplexUnitSphere N)
    (W Y : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * W *
          concreteCenteredOrbitalDirection N v * Y) =
      complexCenteredProjectiveSandwich v W Y := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    concreteCenteredOrbitalDirection_apply_eq_projection_h14,
    complexCenteredProjectiveSandwich]
  apply Finset.sum_congr rfl
  intro a _
  have hexpand (d : Fin N) :
      (∑ c, (∑ b, complexCenteredRankOneProjection N v a b * W b c) *
          complexCenteredRankOneProjection N v c d) * Y d a =
        ∑ c, ∑ b, complexCenteredRankOneProjection N v a b * W b c *
          complexCenteredRankOneProjection N v c d * Y d a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [hexpand]
  let f : Fin N → Fin N → Fin N → ℂ := fun b c d ↦
    complexCenteredRankOneProjection N v a b * W b c *
      complexCenteredRankOneProjection N v c d * Y d a
  change (∑ d, ∑ c, ∑ b, f b c d) = ∑ b, ∑ c, ∑ d, f b c d
  calc
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ c, ∑ d, ∑ b, f b c d :=
      Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ d, f b c d := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, f b c d := Finset.sum_comm

/-- Public coordinate verification of
`Tr(Q_v R Q_v.transpose R†)=complexCenteredProjectiveConjugateSandwich v R`. -/
theorem trace_centered_conjugate_sandwich_eq_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * R *
          (concreteCenteredOrbitalDirection N v).transpose *
            R.conjTranspose) =
      complexCenteredProjectiveConjugateSandwich v R := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    concreteCenteredOrbitalDirection_apply_eq_projection_h14,
    complexCenteredProjectiveConjugateSandwich, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hexpand (d : Fin N) :
      (∑ c, (∑ b, complexCenteredRankOneProjection N v a b * R b c) *
          complexCenteredRankOneProjection N v d c) * star (R a d) =
        ∑ c, ∑ b, complexCenteredRankOneProjection N v a b * R b c *
          complexCenteredRankOneProjection N v d c * star (R a d) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [hexpand]
  let f : Fin N → Fin N → Fin N → ℂ := fun b c d ↦
    complexCenteredRankOneProjection N v a b * R b c *
      complexCenteredRankOneProjection N v d c * star (R a d)
  change (∑ d, ∑ c, ∑ b, f b c d) = ∑ b, ∑ c, ∑ d, f b c d
  calc
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ c, ∑ d, ∑ b, f b c d :=
      Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ d, f b c d := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, f b c d := Finset.sum_comm

/-- Exact concrete operator model for the already-proved two-sandwich score
expansion. -/
theorem h14CenteredSandwichSecondScore_eq_neg_two_re_trace_XHY_h14
    {N K : ℕ} (A : ConcreteMatrixState N) (v : ComplexUnitSphere N) :
    h14CenteredSandwichSecondScore N K A v =
      -2 * (Matrix.trace
        (concreteCenteredOrbitalDirection N v *
          h14ConcreteXHYMatrix N K A v)).re := by
  let Q := concreteCenteredOrbitalDirection N v
  let W := concreteCOEWMatrix N K A
  let Y := concreteCOEY N K A
  let R := concreteCOERMatrix N K A
  have hmulFirst : Q * (W * Q * Y) = Q * W * Q * Y := by
    noncomm_ring
  have hmulSecond : Q * (R * Q.transpose * R.conjTranspose) =
      Q * R * Q.transpose * R.conjTranspose := by
    noncomm_ring
  have htrace : Matrix.trace (Q * h14ConcreteXHYMatrix N K A v) =
      2 * (complexCenteredProjectiveSandwich v W Y +
        complexCenteredProjectiveConjugateSandwich v R) := by
    unfold h14ConcreteXHYMatrix
    change Matrix.trace
      (Q * ((2 : ℂ) • (W * Q * Y + R * Q.transpose * R.conjTranspose))) = _
    rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add,
      Matrix.trace_add, hmulFirst, hmulSecond,
      trace_centered_sandwich_eq_h14,
      trace_centered_conjugate_sandwich_eq_h14]
    rfl
  unfold h14CenteredSandwichSecondScore
  rw [show concreteCenteredOrbitalDirection N v = Q by rfl, htrace]
  simp [Complex.mul_re]
  ring

/-! ## Closed deterministic H14 majorant -/

/-- The requested deterministic pointwise estimate.  It uses only the
concrete support algebra, Euclidean operator norms, and the exact score
identity above. -/
theorem h14CenteredSandwichSecondScore_abs_le_traceTwo_majorant_h14
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (_hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    |h14CenteredSandwichSecondScore N K A v| ≤
      16 * Real.sqrt (concreteCOETraceTwo N K A) *
        (1 + Real.sqrt (concreteCOETraceTwo N K A) /
          concreteCOEExponent N K) := by
  let c : ℝ := concreteCOEExponent N K
  let y : ℝ := Real.sqrt (concreteCOETraceTwo N K A)
  let u : ℝ := 1 + y / c
  let XHY := h14ConcreteXHYMatrix N K A v
  have hc : 0 < c := by
    dsimp only [c, concreteCOEExponent]
    have hgapR : (2 : ℝ) * (N : ℝ) + 8 ≤ (K : ℝ) := by
      exact_mod_cast hgap
    linarith
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hu : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hY : ‖concreteCOEY N K A‖ ≤ y := by
    simpa only [y] using
      concreteCOEY_l2_opNorm_le_sqrt_traceTwo_h14 hN A hsupport
  have hW : ‖concreteCOEWMatrix N K A‖ ≤ u := by
    simpa only [u, y, c] using
      concreteCOEWMatrix_l2_opNorm_le_h14 hN A hc hY
  have hR : ‖concreteCOERMatrix N K A‖ ^ 2 ≤ y * u := by
    exact concreteCOERMatrix_l2_opNorm_sq_le_h14 A hc hsupport
      hy hu hY hW
  have hXHY : ‖XHY‖ ≤ 4 * y * u := by
    simpa only [XHY] using
      h14ConcreteXHYMatrix_l2_opNorm_le_four_h14
        hN A v hy hu hY hW hR
  have hpair :
      |(Matrix.trace
        (concreteCenteredOrbitalDirection N v * XHY)).re| ≤
          2 * ‖XHY‖ :=
    abs_re_trace_centeredDirection_mul_le_two_h14 hN v XHY
  rw [h14CenteredSandwichSecondScore_eq_neg_two_re_trace_XHY_h14]
  change |-2 * (Matrix.trace
    (concreteCenteredOrbitalDirection N v * XHY)).re| ≤ _
  calc
    |-2 * (Matrix.trace
        (concreteCenteredOrbitalDirection N v * XHY)).re| =
        2 * |(Matrix.trace
          (concreteCenteredOrbitalDirection N v * XHY)).re| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * (2 * ‖XHY‖) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * (2 * (4 * y * u)) := by gcongr
    _ = 16 * Real.sqrt (concreteCOETraceTwo N K A) *
        (1 + Real.sqrt (concreteCOETraceTwo N K A) /
          concreteCOEExponent N K) := by
      dsimp only [y, u, c]
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
