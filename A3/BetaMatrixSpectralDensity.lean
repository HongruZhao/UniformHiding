import A3.HermitianWeylBetaKernel
import A3.BetaMatrixKernel

open MeasureTheory MeasureTheory.Measure Set Matrix
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ENNReal ComplexOrder MatrixOrder Matrix.Norms.Elementwise

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

theorem hermitianOrbitMatrix_complement (U : Matrix.unitaryGroup (Fin n) K)
    (lambda : Fin n → ℝ) :
    hermitianOrbitMatrix U (fun i ↦ 1 - lambda i) = 1 - hermitianOrbitMatrix U lambda := by
  unfold hermitianOrbitMatrix
  have hdiag : Matrix.diagonal (fun i ↦ ((1 - lambda i : ℝ) : K)) =
      1 - Matrix.diagonal (fun i ↦ (lambda i : K)) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp only [RCLike.ofReal_sub, RCLike.ofReal_one]
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  have hu : U.val * U.val.conjTranspose = 1 := U.property.2
  rw [hu]

theorem hermitianComplementCoordinates_orbit (U : Matrix.unitaryGroup (Fin n) K)
    (lambda : Fin n → ℝ) :
    hermitianComplementCoordinates (hermitianOrbitCoordinates U lambda) =
      hermitianOrbitCoordinates U (fun i ↦ 1 - lambda i) := by
  unfold hermitianComplementCoordinates
  rw [hermitianOrbitCoordinates_reconstruct, ← hermitianOrbitMatrix_complement]
  rfl

theorem canonicalHermitianSpectrum_complement_permutation (x : HermitianCoordinates n K) :
    ∃ sigma : Equiv.Perm (Fin n),
      canonicalHermitianSpectrum (hermitianComplementCoordinates x) =
        (fun i ↦ 1 - canonicalHermitianSpectrum x i) ∘ sigma := by
  let U := (hermitianMatrixOfCoordinates_isHermitian x).eigenvectorUnitary
  have hc : hermitianComplementCoordinates x =
      hermitianOrbitCoordinates U (fun i ↦ 1 - canonicalHermitianSpectrum x i) := by
    conv_lhs => rw [hermitianCoordinates_spectral_representation x]
    exact hermitianComplementCoordinates_orbit U _
  rw [hc]
  exact canonicalHermitianSpectrum_orbit_permutation U _

theorem hermitianOrbitMatrix_posDef_iff (U : Matrix.unitaryGroup (Fin n) K)
    (lambda : Fin n → ℝ) :
    (hermitianOrbitMatrix U lambda).PosDef ↔ ∀ i, 0 < lambda i := by
  unfold hermitianOrbitMatrix
  rw [← Matrix.star_eq_conjTranspose, Unitary.isUnit_coe.posDef_star_right_conjugate_iff,
    Matrix.posDef_diagonal_iff]
  simp only [RCLike.ofReal_pos]

/-- The actual matrix-beta support is exactly the full scalar open cube. -/
theorem mem_hermitianBetaDomain_iff_spectrum_cube (x : HermitianCoordinates n K) :
    x ∈ hermitianBetaDomain n K ↔ canonicalHermitianSpectrum x ∈ betaJacobiOpenCube n := by
  let U := (hermitianMatrixOfCoordinates_isHermitian x).eigenvectorUnitary
  have hM : hermitianMatrixOfCoordinates x =
      hermitianOrbitMatrix U (canonicalHermitianSpectrum x) := by
    have hc := congrArg hermitianMatrixOfCoordinates (hermitianCoordinates_spectral_representation x)
    simpa only [hermitianOrbitCoordinates_reconstruct] using hc
  change (hermitianMatrixOfCoordinates x).PosDef ∧
      (1 - hermitianMatrixOfCoordinates x).PosDef ↔
    ∀ i, canonicalHermitianSpectrum x i ∈ Ioo 0 1
  rw [hM, ← hermitianOrbitMatrix_complement,
    hermitianOrbitMatrix_posDef_iff, hermitianOrbitMatrix_posDef_iff]
  constructor
  · intro h i
    exact ⟨h.1 i, (sub_pos.mp (h.2 i))⟩
  · intro h
    exact ⟨fun i ↦ (h i).1, fun i ↦ sub_pos.mpr (h i).2⟩

theorem wishartDetReal_eq_prod_spectrum (x : HermitianCoordinates n K) :
    wishartDetReal x = ∏ i, canonicalHermitianSpectrum x i := by
  have he : (hermitianMatrixOfCoordinates x).det =
      ((∏ i, canonicalHermitianSpectrum x i : ℝ) : K) := by
    rw [(hermitianMatrixOfCoordinates_isHermitian x).det_eq_prod_eigenvalues]
    exact (map_prod (algebraMap ℝ K) _ _).symm
  change RCLike.re (hermitianMatrixOfCoordinates x).det = _
  rw [he, RCLike.ofReal_re]

theorem wishartDetReal_complement_eq_prod_spectrum (x : HermitianCoordinates n K) :
    wishartDetReal (hermitianComplementCoordinates x) =
      ∏ i, (1 - canonicalHermitianSpectrum x i) := by
  rw [wishartDetReal_eq_prod_spectrum]
  obtain ⟨sigma, hsigma⟩ := canonicalHermitianSpectrum_complement_permutation x
  rw [hsigma]
  exact Equiv.prod_comp sigma (fun i ↦ 1 - canonicalHermitianSpectrum x i)

theorem betaMatrix_shape_exponent (n : ℕ) (K : Type*) [RCLike K] (a : ℝ) :
    (Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2 - wishartHermitianKappa n K =
      (Module.finrank ℝ K : ℝ) * (a + 1) / 2 - 1 := by
  unfold wishartHermitianKappa
  ring

theorem betaMatrixKernel_of_spectrum (a b : ℝ) (x : HermitianCoordinates n K) :
    betaMatrixKernel n K ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2)
      ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + b) / 2) x =
      (∏ i, canonicalHermitianSpectrum x i) ^
          ((Module.finrank ℝ K : ℝ) * (a + 1) / 2 - 1) *
        (∏ i, (1 - canonicalHermitianSpectrum x i)) ^
          ((Module.finrank ℝ K : ℝ) * (b + 1) / 2 - 1) := by
  rw [betaMatrixKernel, wishartDetReal_eq_prod_spectrum,
    wishartDetReal_complement_eq_prod_spectrum, betaMatrix_shape_exponent,
    betaMatrix_shape_exponent]

theorem ofReal_betaMatrixKernel_eq_endpoint (a b : ℝ) (x : HermitianCoordinates n K)
    (hx : x ∈ hermitianBetaDomain n K) :
    ENNReal.ofReal (betaMatrixKernel n K ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2)
      ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + b) / 2) x) =
        hermitianBetaEndpointDensity n a b (Module.finrank ℝ K) (canonicalHermitianSpectrum x) := by
  have hcube := (mem_hermitianBetaDomain_iff_spectrum_cube x).mp hx
  rw [betaMatrixKernel_of_spectrum,
    ← Real.finsetProd_rpow Finset.univ _ (fun i _ ↦ (hcube i).1.le) _,
    ← Real.finsetProd_rpow Finset.univ _ (fun i _ ↦ (sub_pos.mpr (hcube i).2).le) _,
    ← Finset.prod_mul_distrib,
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦
      mul_nonneg (Real.rpow_nonneg (hcube i).1.le _) (Real.rpow_nonneg
        (sub_pos.mpr (hcube i).2).le _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hcube i).1.le _),
    ← ENNReal.ofReal_rpow_of_pos (hcube i).1,
    ← ENNReal.ofReal_rpow_of_pos (sub_pos.mpr (hcube i).2)]
  rfl

/-- The literal matrix-beta density is exactly the measurable symmetric
spectral weight used in the proved weighted Weyl law. -/
theorem betaMatrixDensity_eq_spectral_weight (a b : ℝ) (x : HermitianCoordinates n K) :
    betaMatrixDensity n K ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2)
      ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + b) / 2) x =
        hermitianBetaSpectralWeight n a b (Module.finrank ℝ K) (canonicalHermitianSpectrum x) := by
  classical
  unfold betaMatrixDensity hermitianBetaSpectralWeight
  by_cases hx : x ∈ hermitianBetaDomain n K
  · rw [if_pos hx, indicator_of_mem ((mem_hermitianBetaDomain_iff_spectrum_cube x).mp hx)]
    exact ofReal_betaMatrixKernel_eq_endpoint a b x hx
  · rw [if_neg hx, indicator_of_notMem (fun hc ↦ hx
      ((mem_hermitianBetaDomain_iff_spectrum_cube x).mpr hc))]

theorem betaMatrixRawMeasure_eq_spectral_density
    [MeasureSpace K] [BorelSpace K] (a b : ℝ) :
    betaMatrixRawMeasure n K ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2)
      ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + b) / 2) =
      (hermitianCoordinateVolume n K).withDensity
        (hermitianBetaSpectralWeight n a b (Module.finrank ℝ K) ∘ canonicalHermitianSpectrum) := by
  unfold betaMatrixRawMeasure
  congr 1
  funext x
  exact betaMatrixDensity_eq_spectral_weight a b x

/-- The full literal beta-matrix spectral law, including its actual matrix
support and determinant powers, maps to the paper's raw beta-Jacobi law. -/
theorem betaMatrixRawMeasure_symmetric_test_law
    [MeasureSpace K] [BorelSpace K] [PolishSpace K]
    [IsAddHaarMeasure (volume : Measure K)]
    (a b : ℝ) {Y : Type} [MeasurableSpace Y] (F : (Fin n → ℝ) → Y)
    (hF : Measurable F) (hperm : IsA2SymmetricTest F) :
    Measure.map (F ∘ canonicalHermitianSpectrum)
      (betaMatrixRawMeasure n K ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2)
        ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + b) / 2)) =
      ((hermitianWeylSymmetricIntegrationLaw n K).orbitConstant : ℝ≥0∞) •
        Measure.map F (betaJacobiRawMeasure n a b (Module.finrank ℝ K)) := by
  rw [betaMatrixRawMeasure_eq_spectral_density a b]
  exact hermitianWeyl_map_beta_spectral_density a b F hF hperm

end A3Research
