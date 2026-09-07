import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19NormalizerLimit
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19ScalarLimits
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19GaussianDensity

/-!
# Pointwise Jiang-density limit for H19

This module proves the elementary finite-dimensional analytic facts needed to
turn Jiang's literal corner density into a direct total-variation limit.  It
contains no additional random-matrix input.
-/

open Filter MeasureTheory Matrix
open scoped BigOperators ComplexOrder ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

/-- For a fixed Hermitian matrix, `I - A/M` is positive semidefinite for all
sufficiently large natural `M`. -/
theorem eventually_posSemidef_one_sub_nat_inv_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∀ᶠ M : ℕ in atTop,
      (1 - (((M : ℝ)⁻¹ : ℝ) : ℂ) • A).PosSemidef := by
  have hbound : ∀ᶠ M : ℕ in atTop,
      ∀ i : n, hA.eigenvalues i ≤ (M : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    exact tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (hA.eigenvalues i))
  filter_upwards [hbound, eventually_ne_atTop 0] with M hMb hM0
  have hMr : (0 : ℝ) < M := by exact_mod_cast (Nat.pos_of_ne_zero hM0)
  let U : Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary
  let D : Matrix n n ℂ :=
    Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  let r : ℂ := (((M : ℝ)⁻¹ : ℝ) : ℂ)
  have haffine :
      1 - r • ((U : Matrix n n ℂ) * D *
        star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * (1 - r • D) *
        star (U : Matrix n n ℂ) := by
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, mul_assoc, Unitary.coe_mul_star_self]
  have hdiag : 1 - r • D = Matrix.diagonal
      (fun i : n => ((1 - hA.eigenvalues i / (M : ℝ) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, r, Function.comp_def, div_eq_mul_inv, mul_comm]
    · simp [D, r, Matrix.one_apply, hij, Function.comp_def]
  have hdiagPSD : (1 - r • D).PosSemidef := by
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast (sub_nonneg.mpr (div_le_one hMr |>.2 (hMb i)))
  rw [hA.spectral_theorem]
  change (1 - r • ((U : Matrix n n ℂ) * D *
    star (U : Matrix n n ℂ))).PosSemidef
  rw [haffine]
  simpa only [Matrix.star_eq_conjTranspose] using
    hdiagPSD.mul_mul_conjTranspose_same (U : Matrix n n ℂ)

/-- Entrywise inverse-square-root scaling turns the Gram matrix into
`M⁻¹ Zᴴ Z`. -/
theorem conjTranspose_invSqrt_smul_mul_self
    {M K N : ℕ} (hM : 0 < M)
    (Z : Matrix (Fin K) (Fin N) ℂ) :
    (((Real.sqrt (M : ℝ))⁻¹ • Z).conjTranspose *
        ((Real.sqrt (M : ℝ))⁻¹ • Z)) =
      ((((M : ℝ)⁻¹ : ℝ) : ℂ)) • (Z.conjTranspose * Z) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : (Real.sqrt (M : ℝ)) ^ 2 = (M : ℝ) :=
    Real.sq_sqrt hMr.le
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  congr 1
  have hs0 : Real.sqrt (M : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hMr)
  simp only [star_trivial, Complex.ofReal_re]
  field_simp [hs0]
  nlinarith

/-- Jiang's quadratic-form support predicate is exactly positive
semidefiniteness of the matrix-ball complement. -/
theorem jiangUnscaledTallHaarCornerSupport_iff_posSemidef
    {K N : ℕ} (X : Matrix (Fin K) (Fin N) ℂ) :
    jiangUnscaledTallHaarCornerSupport X ↔
      (1 - X.conjTranspose * X).PosSemidef := by
  have hHerm : (1 - X.conjTranspose * X).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self X)
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v ↦ ?_
    rw [RCLike.nonneg_iff]
    exact ⟨h v, hHerm.im_star_dotProduct_mulVec_self v⟩
  · intro h v
    exact h.re_dotProduct_nonneg v

/-- A fixed scaled matrix lies in Jiang's rescaled support for all large
ambient dimensions. -/
theorem eventually_jiangUnscaledTallHaarCornerSupport_invSqrt_smul
    {K N : ℕ} (Z : Matrix (Fin K) (Fin N) ℂ) :
    ∀ᶠ M : ℕ in atTop,
      jiangUnscaledTallHaarCornerSupport
        ((Real.sqrt (M : ℝ))⁻¹ • Z) := by
  let A : Matrix (Fin N) (Fin N) ℂ := Z.conjTranspose * Z
  have hA : A.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self Z
  have hpsd := eventually_posSemidef_one_sub_nat_inv_smul A hA
  filter_upwards [hpsd, eventually_ne_atTop 0] with M hPSD hM0
  rw [jiangUnscaledTallHaarCornerSupport_iff_posSemidef,
    conjTranspose_invSqrt_smul_mul_self (Nat.pos_of_ne_zero hM0) Z]
  exact hPSD

/-! ## Real densities and their pointwise limit -/

/-- Real-valued version of the transported Jiang density.  The following
lemma proves that `ENNReal.ofReal` of this function is exactly the measure
density already obtained from the raw source axiom. -/
def jiangSqrtScaledTallHaarCornerRealPDF (M K N : ℕ)
    (Z : Matrix (Fin K) (Fin N) ℂ) : ℝ :=
  ((M : ℝ)⁻¹) ^ (K * N) *
    @ite ℝ (jiangUnscaledTallHaarCornerSupport
        ((Real.sqrt (M : ℝ))⁻¹ • Z))
      (Classical.propDecidable _) (
      jiangUnscaledTallHaarCornerNormalizer M K N *
        (Matrix.det
          (1 - (((Real.sqrt (M : ℝ))⁻¹ • Z).conjTranspose *
            ((Real.sqrt (M : ℝ))⁻¹ • Z)))).re ^ (M - K - N))
      0

/-- The limiting standard complex-Gaussian density, in radial Gram form. -/
def standardComplexGaussianTallRealPDF (K N : ℕ)
    (Z : Matrix (Fin K) (Fin N) ℂ) : ℝ :=
  (Real.pi ^ (K * N))⁻¹ *
    Real.exp (-(Matrix.trace (Z.conjTranspose * Z)).re)

theorem jiangSqrtScaledTallHaarCornerPDF_eq_ofReal
    (M K N : ℕ) (Z : Matrix (Fin K) (Fin N) ℂ) :
    jiangSqrtScaledTallHaarCornerPDF M K N Z =
      ENNReal.ofReal (jiangSqrtScaledTallHaarCornerRealPDF M K N Z) := by
  have hjac : 0 ≤ ((M : ℝ)⁻¹) ^ (K * N) := by positivity
  by_cases hsupport : jiangUnscaledTallHaarCornerSupport
      ((Real.sqrt (M : ℝ))⁻¹ • Z)
  · simp [jiangSqrtScaledTallHaarCornerPDF,
      jiangUnscaledTallHaarCornerPDF,
      jiangSqrtScaledTallHaarCornerRealPDF, hsupport,
      ENNReal.ofReal_mul hjac]
  · simp [jiangSqrtScaledTallHaarCornerPDF,
      jiangUnscaledTallHaarCornerPDF,
      jiangSqrtScaledTallHaarCornerRealPDF, hsupport]

theorem jiangUnscaledTallHaarCornerNormalizer_nonneg (M K N : ℕ) :
    0 ≤ jiangUnscaledTallHaarCornerNormalizer M K N := by
  unfold jiangUnscaledTallHaarCornerNormalizer
  positivity

theorem jiangSqrtScaledTallHaarCornerRealPDF_nonneg
    (M K N : ℕ) (Z : Matrix (Fin K) (Fin N) ℂ) :
    0 ≤ jiangSqrtScaledTallHaarCornerRealPDF M K N Z := by
  unfold jiangSqrtScaledTallHaarCornerRealPDF
  apply mul_nonneg (by positivity)
  split_ifs with hsupport
  · apply mul_nonneg
      (jiangUnscaledTallHaarCornerNormalizer_nonneg M K N)
    apply pow_nonneg
    have hPSD :=
      (jiangUnscaledTallHaarCornerSupport_iff_posSemidef _).mp hsupport
    exact (RCLike.nonneg_iff.mp hPSD.det_nonneg).1
  · exact le_rfl

theorem standardComplexGaussianTallRealPDF_nonneg
    (K N : ℕ) (Z : Matrix (Fin K) (Fin N) ℂ) :
    0 ≤ standardComplexGaussianTallRealPDF K N Z := by
  unfold standardComplexGaussianTallRealPDF
  positivity

theorem trace_conjTranspose_mul_self_re_eq_sum_norm_sq
    {K N : ℕ} (Z : Matrix (Fin K) (Fin N) ℂ) :
    (Matrix.trace (Z.conjTranspose * Z)).re =
      ∑ i : Fin K, ∑ j : Fin N, ‖Z i j‖ ^ 2 := by
  rw [Matrix.trace, Complex.re_sum]
  change (∑ j : Fin N,
      ((∑ i : Fin K, star (Z i j) * Z i j : ℂ)).re) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp [Complex.sq_norm, Complex.normSq_apply]

theorem standardComplexGaussianRectangularDensityReal_eq_radial
    (K N : ℕ) (Z : Matrix (Fin K) (Fin N) ℂ) :
    standardComplexGaussianRectangularDensityReal K N Z =
      standardComplexGaussianTallRealPDF K N Z := by
  unfold standardComplexGaussianRectangularDensityReal
    standardComplexGaussianTallRealPDF
  rw [trace_conjTranspose_mul_self_re_eq_sum_norm_sq Z]

theorem measurable_jiangSqrtScaledTallHaarCornerRealPDF
    (M K N : ℕ) :
    Measurable (jiangSqrtScaledTallHaarCornerRealPDF M K N) := by
  have hfun : jiangSqrtScaledTallHaarCornerRealPDF M K N =
      fun Z ↦ (jiangSqrtScaledTallHaarCornerPDF M K N Z).toReal := by
    funext Z
    rw [jiangSqrtScaledTallHaarCornerPDF_eq_ofReal]
    exact (ENNReal.toReal_ofReal
      (jiangSqrtScaledTallHaarCornerRealPDF_nonneg M K N Z)).symm
  rw [hfun]
  exact (measurable_jiangSqrtScaledTallHaarCornerPDF M K N).ennreal_toReal

theorem measurable_standardComplexGaussianTallRealPDF (K N : ℕ) :
    Measurable (standardComplexGaussianTallRealPDF K N) := by
  have hfun : standardComplexGaussianTallRealPDF K N =
      fun Z : Matrix (Fin K) (Fin N) ℂ ↦
        (Real.pi ^ (K * N))⁻¹ *
          Real.exp (-∑ i : Fin K, ∑ j : Fin N, ‖Z i j‖ ^ 2) := by
    funext Z
    unfold standardComplexGaussianTallRealPDF
    rw [trace_conjTranspose_mul_self_re_eq_sum_norm_sq Z]
  rw [hfun]
  fun_prop

/-- The Gaussian reference law expressed with the same radial real density. -/
theorem standardGaussianBlockLaw_eq_withDensity_ofReal_H19 (K N : ℕ) :
    standardGaussianBlockLaw K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (fun Z ↦ ENNReal.ofReal
          (standardComplexGaussianTallRealPDF K N Z)) := by
  rw [standardGaussianBlockLaw_eq_withDensity_H19]
  congr 1
  funext Z
  unfold standardComplexGaussianRectangularPDF
  rw [standardComplexGaussianRectangularDensityReal_eq_radial]

theorem jiangSqrtScaledTallHaarCornerLaw_isProbability
    {M K N : ℕ} (hM : 0 < M) (hKM : K ≤ M) (hNM : N ≤ M) :
    IsProbabilityMeasure (jiangSqrtScaledTallHaarCornerLaw M K N) := by
  rw [jiangSqrtScaledTallHaarCornerLaw,
    jiangUnscaledTallHaarCornerLaw, dif_pos ⟨hKM, hNM⟩]
  letI : IsProbabilityMeasure (unitaryHaarProbabilityMeasure M) :=
    unitaryHaarProbabilityMeasure_isProbability M
  haveI : IsProbabilityMeasure
      (Measure.map (jiangUnscaledTallHaarCornerMatrix hKM hNM)
        (unitaryHaarProbabilityMeasure M)) :=
    Measure.isProbabilityMeasure_map
      (measurable_jiangUnscaledTallHaarCornerMatrix hKM hNM).aemeasurable
  change IsProbabilityMeasure
    (Measure.map (rectangularSqrtScaleMeasurableEquiv M K N hM)
      (Measure.map (jiangUnscaledTallHaarCornerMatrix hKM hNM)
        (unitaryHaarProbabilityMeasure M)))
  exact Measure.isProbabilityMeasure_map
    (rectangularSqrtScaleMeasurableEquiv M K N hM).measurable.aemeasurable

/-- For each fixed rectangular matrix, Jiang's scaled density converges to
the standard complex-Gaussian radial density. -/
theorem tendsto_jiangSqrtScaledTallHaarCornerRealPDF
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (Z : Matrix (Fin K) (Fin N) ℂ) :
    Tendsto
      (fun M : ℕ ↦ jiangSqrtScaledTallHaarCornerRealPDF M K N Z)
      atTop (nhds (standardComplexGaussianTallRealPDF K N Z)) := by
  let A : Matrix (Fin N) (Fin N) ℂ := Z.conjTranspose * Z
  have hA : A.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self Z
  have hcoeff :=
    tendsto_jiangUnscaledTallHaarCornerNormalizer_mul_inv_pow
      hN hK hNK
  have hdet := tendsto_hermitian_det_one_sub_div_pow_sub_exp
    A hA (K + N)
  have hprod := hcoeff.mul hdet
  have hsupp :=
    eventually_jiangUnscaledTallHaarCornerSupport_invSqrt_smul Z
  apply hprod.congr'
  filter_upwards [hsupp, eventually_ne_atTop 0] with M hsupport hM0
  have hM : 0 < M := Nat.pos_of_ne_zero hM0
  rw [jiangSqrtScaledTallHaarCornerRealPDF]
  simp only [if_pos hsupport]
  rw [conjTranspose_invSqrt_smul_mul_self hM Z, Nat.sub_sub]
  simp only [A, Nat.cast_ofNat, Complex.natCast_re]
  rw [inv_pow]
  have hcast : (M : ℂ)⁻¹ = ((((M : ℝ)⁻¹ : ℝ) : ℂ)) := by
    simpa using (Complex.ofReal_inv (M : ℝ)).symm
  rw [hcast]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
