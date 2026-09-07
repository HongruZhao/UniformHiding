import LogdetLean.GramHafnian.SymmetricGaussianHafnian.ScalarGaussianFactor
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LocalCofactorCompression

/-!
# The literal complex scalar-plus-bilinear conditional kernel

The Gaussian variables here are exactly one standard circular scalar and
two independent standard circular vectors.  No hafnian law is encoded in
their definition.  When the literal cofactor expansion supplies `ell`, `M`,
and `q`, these lemmas discharge the realification, scalar integration,
integrability, and weighted two-endpoint comparison.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1200000

/-- The exact real operator of a complex transpose-bilinear form. -/
def complexBilinearPhaseOperator {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) :
    CofactorRealSpace k →L[ℝ] CofactorRealSpace k :=
  (Matrix.toEuclideanLin (cofactorBilinearPhaseMatrix 1 M)).toContinuousLinearMap

/-- The common real endpoint map associated with the cofactor vector `q`. -/
def complexLinearPhaseOperator {k : ℕ} (q : Fin k → ℂ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] CofactorRealSpace k :=
  (Matrix.toEuclideanLin (cofactorLinearPhaseMatrix q)).toContinuousLinearMap

/-- Conditional phase after the scalar edge has been separated off. -/
def complexBilinearPhase {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ)
    (q : Fin k → ℂ) (a b : ℂ) (X Y : Fin k → ℂ) : ℝ :=
  (transposeBilinear X M Y + a * transposeDot Y q + b * transposeDot X q).re

/-- Exact realification of the complex scalar coefficients and bilinear
matrix, including the `sqrt 2` normalization of Gaussian real coordinates. -/
theorem complexBilinearPhase_eq_real
    {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (q : Fin k → ℂ)
    (a b : ℂ) (X Y : Fin k → ℂ) :
    complexBilinearPhase M q a b X Y =
      inner ℝ (complexRealificationEuclidean X)
        (complexBilinearPhaseOperator M (complexRealificationEuclidean Y)) +
      inner ℝ (complexRealificationEuclidean X)
        (complexLinearPhaseOperator q (complexPhaseCoordinatesEuclidean b)) +
      inner ℝ (complexRealificationEuclidean Y)
        (complexLinearPhaseOperator q (complexPhaseCoordinatesEuclidean a)) := by
  have hbil := complex_bilinear_phase_realification (1 : ℂ) X M Y
  simp only [one_mul] at hbil
  have hT : inner ℝ (complexRealificationEuclidean X)
      (complexBilinearPhaseOperator M (complexRealificationEuclidean Y)) =
      realTransposeBilinearPhase (complexRealification X)
        (cofactorBilinearPhaseMatrix 1 M) (complexRealification Y) :=
    inner_toEuclideanLin_eq_realTransposeBilinearPhase _ _ _
  have hL (Z : Fin k → ℂ) (c : ℂ) :
      inner ℝ (complexRealificationEuclidean Z)
        (complexLinearPhaseOperator q (complexPhaseCoordinatesEuclidean c)) =
      realTransposeLinearPhase (complexRealification Z)
        (cofactorLinearPhaseMatrix q) (complexPhaseCoordinates c) :=
    inner_toEuclideanLin_eq_realTransposeBilinearPhase _ _ _
  rw [hT, hL, hL]
  unfold complexBilinearPhase
  rw [Complex.add_re, Complex.add_re, hbil,
    complex_linear_phase_realification, complex_linear_phase_realification]
  ring

/-- Literal integral over the two independently exposed circular vectors. -/
def complexBilinearKernel {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ)
    (q : Fin k → ℂ) (a b : ℂ) : ℂ :=
  ∫ p : (Fin k → ℂ) × (Fin k → ℂ),
    Complex.exp (((complexBilinearPhase M q a b p.1 p.2 : ℝ) : ℂ) * Complex.I)
    ∂((circularGaussianVector k).prod (circularGaussianVector k))

/-- Two independent circular Gaussian vectors transport exactly to the
standard real Gaussian bilinear kernel. -/
theorem complexBilinearKernel_eq_bilinearGaussianIntegral
    {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (q : Fin k → ℂ) (a b : ℂ) :
    complexBilinearKernel M q a b =
      bilinearGaussianIntegral (complexBilinearPhaseOperator M)
        (complexLinearPhaseOperator q)
        (complexPhaseCoordinatesEuclidean a) (complexPhaseCoordinatesEuclidean b) := by
  let rho : ((Fin k → ℂ) × (Fin k → ℂ)) →
      (CofactorRealSpace k × CofactorRealSpace k) :=
    fun p ↦ (complexRealificationEuclidean p.1, complexRealificationEuclidean p.2)
  let kernel : CofactorRealSpace k × CofactorRealSpace k → ℂ := fun p ↦
    Complex.exp (((inner ℝ p.1 (complexBilinearPhaseOperator M p.2) +
      inner ℝ p.1 (complexLinearPhaseOperator q (complexPhaseCoordinatesEuclidean b)) +
      inner ℝ p.2 (complexLinearPhaseOperator q (complexPhaseCoordinatesEuclidean a)) : ℝ)
      : ℂ) * Complex.I)
  have hrho : MeasurePreserving rho
      ((circularGaussianVector k).prod (circularGaussianVector k))
      ((stdGaussian (CofactorRealSpace k)).prod (stdGaussian (CofactorRealSpace k))) := by
    have hp := (measurePreserving_complexRealificationEuclidean k).prod
      (measurePreserving_complexRealificationEuclidean k)
    refine hp.congr (by fun_prop) ?_
    filter_upwards [] with p
    rfl
  have htransport :
      (∫ p : (Fin k → ℂ) × (Fin k → ℂ), kernel (rho p)
        ∂((circularGaussianVector k).prod (circularGaussianVector k))) =
      ∫ p, kernel p
        ∂((stdGaussian (CofactorRealSpace k)).prod (stdGaussian (CofactorRealSpace k))) := by
    rw [← hrho.map_eq]
    symm
    exact integral_map hrho.measurable.aemeasurable
      (by fun_prop : Continuous kernel).aestronglyMeasurable
  unfold complexBilinearKernel bilinearGaussianIntegral
  rw [← htransport]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [complexBilinearPhase_eq_real]

/-- The exposed sample space consists of the shared edge and two vectors. -/
abbrev ComplexExposedSample (k : ℕ) :=
  ℂ × ((Fin k → ℂ) × (Fin k → ℂ))

/-- Literal independent Gaussian law on the exposed sample space. -/
def complexExposedMeasure (k : ℕ) : Measure (ComplexExposedSample k) :=
  circularGaussian.prod ((circularGaussianVector k).prod (circularGaussianVector k))

instance (k : ℕ) : IsProbabilityMeasure (complexExposedMeasure k) := by
  unfold complexExposedMeasure
  infer_instance

/-- Literal scalar-plus-bilinear complex Gaussian conditional kernel. -/
def complexConditionalKernel {k : ℕ} (ell : ℂ)
    (M : Matrix (Fin k) (Fin k) ℂ) (q : Fin k → ℂ) (a b : ℂ) : ℂ :=
  ∫ p : ComplexExposedSample k,
    Complex.exp (((((p.1 * ell).re +
      complexBilinearPhase M q a b p.2.1 p.2.2) : ℝ) : ℂ) * Complex.I)
    ∂complexExposedMeasure k

/-- The extra scalar edge gives exactly the positive weight; the two
remaining vectors give exactly the already verified bilinear kernel. -/
theorem complexConditionalKernel_eq_weightedBilinearGaussianIntegral
    {k : ℕ} (ell : ℂ) (M : Matrix (Fin k) (Fin k) ℂ)
    (q : Fin k → ℂ) (a b : ℂ) :
    complexConditionalKernel ell M q a b =
      weightedBilinearGaussianIntegral (scalarGaussianWeight ell)
        (complexBilinearPhaseOperator M) (complexLinearPhaseOperator q)
        (complexPhaseCoordinatesEuclidean a) (complexPhaseCoordinatesEuclidean b) := by
  unfold complexConditionalKernel complexExposedMeasure
  rw [integral_independent_scalarGaussian_phase
    ((circularGaussianVector k).prod (circularGaussianVector k)) ell
    (fun p : (Fin k → ℂ) × (Fin k → ℂ) ↦ complexBilinearPhase M q a b p.1 p.2)]
  change (scalarGaussianWeight ell : ℂ) * complexBilinearKernel M q a b = _
  rw [complexBilinearKernel_eq_bilinearGaussianIntegral]
  rfl

/-- Every measurable background family of these literal conditional
kernels is integrable under a finite measure, by the unit modulus of the
unintegrated characteristic phase. -/
theorem integrable_complexConditionalKernel_background
    {Omega : Type*} [MeasurableSpace Omega] {k : ℕ}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (ell : Omega → ℂ) (M : Omega → Matrix (Fin k) (Fin k) ℂ)
    (q : Omega → (Fin k → ℂ))
    (hell : Measurable ell) (hM : ∀ i j, Measurable (fun omega ↦ M omega i j))
    (hq : Measurable q)
    (a b : ℂ) :
    Integrable (fun omega ↦ complexConditionalKernel (ell omega) (M omega) (q omega) a b)
      mu := by
  let f : Omega × ComplexExposedSample k → ℂ := fun p ↦
    Complex.exp (((((p.2.1 * ell p.1).re +
      complexBilinearPhase (M p.1) (q p.1) a b p.2.2.1 p.2.2.2) : ℝ) : ℂ) * Complex.I)
  have hfmeas : Measurable f := by
    unfold f complexBilinearPhase transposeBilinear transposeDot
    fun_prop
  have hf : Integrable f (mu.prod (complexExposedMeasure k)) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable 1
    filter_upwards [] with p
    unfold f
    rw [Complex.norm_exp]
    simp
  exact hf.integral_prod_left

/-- Fully instantiated complex Gaussian two-endpoint comparison.  The
only background hypotheses are elementary measurability; no compression,
positivity, integrability, or distributional claim is taken as an input. -/
theorem norm_integral_complexConditionalKernel_sqrt_le_max
    {Omega : Type*} [MeasurableSpace Omega] {k : ℕ}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (ell : Omega → ℂ) (M : Omega → Matrix (Fin k) (Fin k) ℂ)
    (q : Omega → (Fin k → ℂ))
    (hell : Measurable ell) (hM : ∀ i j, Measurable (fun omega ↦ M omega i j))
    (hq : Measurable q)
    (a b : ℂ) {theta : ℝ} (htheta : 0 < theta) (htheta_one : theta < 1) :
    ‖∫ omega, complexConditionalKernel (ell omega) (M omega) (q omega)
      (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b) ∂mu‖ ≤
      max
        ‖∫ omega, complexConditionalKernel (ell omega) (M omega) (q omega) a 0 ∂mu‖
        ‖∫ omega, complexConditionalKernel (ell omega) (M omega) (q omega) 0 b ∂mu‖ := by
  have hint := integrable_complexConditionalKernel_background mu ell M q hell hM hq
    (Real.sqrt theta • a) (Real.sqrt (1 - theta) • b)
  have hleft := integrable_complexConditionalKernel_background mu ell M q hell hM hq a 0
  have hright := integrable_complexConditionalKernel_background mu ell M q hell hM hq 0 b
  simp only [complexConditionalKernel_eq_weightedBilinearGaussianIntegral,
    complexPhaseCoordinatesEuclidean_real_smul,
    complexPhaseCoordinatesEuclidean_zero] at hint hleft hright ⊢
  exact norm_integral_weightedBilinearGaussianIntegral_sqrt_le_max mu
    (fun omega ↦ scalarGaussianWeight (ell omega))
    (fun omega ↦ scalarGaussianWeight_pos (ell omega))
    (fun omega ↦ complexBilinearPhaseOperator (M omega))
    (fun omega ↦ complexLinearPhaseOperator (q omega))
    (complexPhaseCoordinatesEuclidean a) (complexPhaseCoordinatesEuclidean b)
    htheta htheta_one hint hleft hright

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
