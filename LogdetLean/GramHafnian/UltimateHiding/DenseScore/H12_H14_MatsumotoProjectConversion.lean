import LogdetLean.GramHafnian.UltimateHiding.DenseScore.BetaPrimeMeanInternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_CenteredEllTwoProjectiveCancellationConditional
import Mathlib.Tactic

/-!
# Matsumoto paper parameters to the H12/H14 denominator model

This module contains only the deterministic scale, shape, index, moment, and
projective-cancellation conversion.  It declares no literature atom.  The
approved A4 theorem must be imported from the campaign trust-base module once
that module exposes an actual Lean declaration; the currently supplied
register keeps A4 only in a comment.  The theorem-only
`H12H14MatsumotoIdentityTraceFourMoment` package below is therefore the exact
identity-scale output boundary that a future literal `d,n,beta,gamma,sigma,g,m`
A4 specialization must prove.  It is not an axiom or an endpoint contract.

The false raw `O(N^2)` trace-two mean majorant is not imported.  The centered
`ell_2` representation and trace-zero fourth-moment identity are exposed before
any absolute value or probability estimate.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.Dense

/-! ## Literal Wishart scale and paper parameter conversion -/

/-- Scalar multiplication on the real denominator-matrix space. -/
def h12h14RealWishartScale (d : ℕ) (a : ℝ) :
    Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ :=
  fun W ↦ a • W

theorem measurable_h12h14RealWishartScale (d : ℕ) (a : ℝ) :
    Measurable (h12h14RealWishartScale d a) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [h12h14RealWishartScale, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul
    ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- Matsumoto's integer-shape `W_d(beta, I; R)` realization, with
`beta = k / 2` and entry variance `1/2`. -/
def h12h14MatsumotoIdentityWishartLaw (k d : ℕ) :
    Measure (Matrix (Fin d) (Fin d) ℝ) :=
  Measure.map
    (realWishartGram : Matrix (Fin k) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ)
    (halfGaussianMatrix k d)

/-- The project denominator Wishart law, whose source entries have variance
one and hence corresponds to Matsumoto scale `sigma = 2 I`. -/
def h12h14ProjectStandardWishartLaw (k d : ℕ) :
    Measure (Matrix (Fin d) (Fin d) ℝ) :=
  Measure.map
    (realWishartGram : Matrix (Fin k) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ)
    (standardRealGaussianMatrixMeasure k d)

/-- Exact paper-scale conversion `W_d(k/2, I; R) = (W ↦ W/2)_#
W_d(k/2, 2I; R)`. -/
theorem h12h14_matsumotoIdentityLaw_eq_halfScale_projectLaw (k d : ℕ) :
    h12h14MatsumotoIdentityWishartLaw k d =
      Measure.map (h12h14RealWishartScale d (1 / 2 : ℝ))
        (h12h14ProjectStandardWishartLaw k d) := by
  unfold h12h14MatsumotoIdentityWishartLaw h12h14ProjectStandardWishartLaw
  rw [← map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure k d]
  rw [Measure.map_map
    (measurable_realWishartGram_genericSteinHaff
      (k := Fin k) (p := Fin d))
    (measurable_invSqrtTwoScaleMatrix k d)]
  rw [Measure.map_map
    (measurable_h12h14RealWishartScale d (1 / 2 : ℝ))
    (measurable_realWishartGram_genericSteinHaff
      (k := Fin k) (p := Fin d))]
  apply Measure.map_congr
  filter_upwards [] with R
  simpa only [Function.comp_apply, h12h14RealWishartScale] using
    realWishartGram_invSqrtTwoScaleMatrix k d R

/-- The inverse scale direction used after specializing A4. -/
theorem h12h14_projectLaw_eq_sigmaTwo_pushforward (k d : ℕ) :
    h12h14ProjectStandardWishartLaw k d =
      Measure.map (h12h14RealWishartScale d 2)
        (h12h14MatsumotoIdentityWishartLaw k d) := by
  rw [h12h14_matsumotoIdentityLaw_eq_halfScale_projectLaw]
  unfold h12h14ProjectStandardWishartLaw
  rw [Measure.map_map
    (measurable_h12h14RealWishartScale d 2)
    (measurable_h12h14RealWishartScale d (1 / 2 : ℝ))]
  have hfun :
      h12h14RealWishartScale d 2 ∘
          h12h14RealWishartScale d (1 / 2 : ℝ) = id := by
    funext W
    ext i j
    simp [h12h14RealWishartScale, Function.comp_apply]
  rw [hfun, Measure.map_id]

/-- Matsumoto's literal integer-shape paper variable `beta = k/2`. -/
def h12h14MatsumotoBeta (k : ℕ) : ℝ :=
  (k : ℝ) / 2

/-- Matsumoto's literal paper variable `gamma = beta - (d+1)/2`. -/
def h12h14MatsumotoGamma (d : ℕ) (beta : ℝ) : ℝ :=
  beta - ((d : ℝ) + 1) / 2

/-- Project substitution `d=N`, `k=K-N`, and
`gamma=(K-2N-1)/2`. -/
theorem h12h14_projectDenominator_gamma_eq
    {N K : ℕ} (hNK : N ≤ K) :
    h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)) =
      ((K : ℝ) - 2 * (N : ℝ) - 1) / 2 := by
  unfold h12h14MatsumotoGamma h12h14MatsumotoBeta
  rw [Nat.cast_sub hNK]
  ring

/-- The same project substitution, now stated against the literal project
exponent `c = K - 2N - 1`.  This is a theorem rather than part of A4. -/
theorem h12h14_projectDenominator_gamma_eq_half_concreteCOEExponent
    {N K : ℕ} (hNK : N ≤ K) :
    h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)) =
      concreteCOEExponent N K / 2 := by
  rw [h12h14_projectDenominator_gamma_eq hNK]
  rfl

/-- Exact pointwise scalar conversion `2 * gamma = c`. -/
theorem h12h14_two_mul_projectDenominator_gamma_eq_concreteCOEExponent
    {N K : ℕ} (hNK : N ≤ K) :
    2 * h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)) =
      concreteCOEExponent N K := by
  rw [h12h14_projectDenominator_gamma_eq_half_concreteCOEExponent hNK]
  ring

/-- Matsumoto's side condition `n-1 < gamma`, uniformly for the H12/H14
specializations `n ≤ 4`. -/
theorem h12h14_projectDenominator_gamma_gt_order_sub_one
    {N K n : ℕ} (hgap : 2 * N + 8 ≤ K) (hn : n ≤ 4) :
    (n : ℝ) - 1 <
      h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)) := by
  rw [h12h14_projectDenominator_gamma_eq (by omega : N ≤ K)]
  have hgapR : (2 : ℝ) * (N : ℝ) + 8 ≤ (K : ℝ) := by
    exact_mod_cast hgap
  have hnR : (n : ℝ) ≤ 4 := by
    exact_mod_cast hn
  linarith

/-- The paper entry-index family and the project entry-index family are
literally the same after `d=N`; this theorem keeps that substitution explicit. -/
theorem h12h14_projectEntryIndices_eq
    {N n : ℕ} (indices : Fin (2 * n) → Fin N) :
    (fun r : Fin (2 * n) ↦ indices r) = indices := rfl

/-! ## Exact inverse-Wishart fourth-moment conversion -/

/-- Matsumoto identity-scale inverse matrix `gamma W^{-1}`.  Its arguments are
paper-side dimension/row/shape variables, not project aliases. -/
def h12h14MatsumotoIdentityScaledInverseMatrix
    (d k : ℕ) (gamma : ℝ)
    (R : Matrix (Fin k) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  gamma • (realWishartGram R)⁻¹

/-- The project denominator matrix `c W^{-1}`. -/
def h12h14ProjectScaledInverseMatrix
    (N K : ℕ) (R : Matrix (Fin (K - N)) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  concreteCOEExponent N K • (realWishartGram R)⁻¹

/-- The project denominator is exactly `2 * gamma` times the inverse Gram
matrix.  The A4 paper-to-project scalar substitution is explicit here. -/
theorem h12h14_projectScaledInverseMatrix_eq_twoGamma
    {N K : ℕ} (hNK : N ≤ K)
    (R : Matrix (Fin (K - N)) (Fin N) ℝ) :
    h12h14ProjectScaledInverseMatrix N K R =
      (2 * h12h14MatsumotoGamma N
        (h12h14MatsumotoBeta (K - N))) • (realWishartGram R)⁻¹ := by
  unfold h12h14ProjectScaledInverseMatrix
  rw [h12h14_two_mul_projectDenominator_gamma_eq_concreteCOEExponent hNK]

/-- Paper-side order-four observable `Tr((gamma W^{-1})^4)`. -/
def h12h14MatsumotoIdentityScaledInverseTraceFour
    (d k : ℕ) (gamma : ℝ)
    (R : Matrix (Fin k) (Fin d) ℝ) : ℝ :=
  Matrix.trace ((h12h14MatsumotoIdentityScaledInverseMatrix d k gamma R) ^ 4)

/-- Project-side order-four observable `Tr((c W^{-1})^4)`. -/
def h12h14ProjectScaledInverseTraceFour
    (N K : ℕ) (R : Matrix (Fin (K - N)) (Fin N) ℝ) : ℝ :=
  Matrix.trace ((h12h14ProjectScaledInverseMatrix N K R) ^ 4)

private theorem measurable_h12h14RealMatrix_mul
    {X n : Type*} [MeasurableSpace X] [Fintype n]
    {A B : X → Matrix n n ℝ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x * B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ ↦
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

private theorem measurable_h12h14RealMatrix_pow
    {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
    {A : X → Matrix n n ℝ} (hA : Measurable A) :
    ∀ r : ℕ, Measurable (fun x ↦ (A x) ^ r)
  | 0 => by
      simpa using
        (measurable_const : Measurable (fun _ : X ↦ (1 : Matrix n n ℝ)))
  | r + 1 => by
      simpa only [pow_succ] using
        measurable_h12h14RealMatrix_mul
          (measurable_h12h14RealMatrix_pow hA r) hA

private theorem measurable_h12h14RealMatrix_trace
    {X n : Type*} [MeasurableSpace X] [Fintype n]
    {A : X → Matrix n n ℝ} (hA : Measurable A) :
    Measurable (fun x ↦ Matrix.trace (A x)) := by
  unfold Matrix.trace
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hA)

theorem measurable_h12h14MatsumotoIdentityScaledInverseTraceFour
    (d k : ℕ) (gamma : ℝ) :
    Measurable (h12h14MatsumotoIdentityScaledInverseTraceFour d k gamma) := by
  have hinv : Measurable
      (fun R : Matrix (Fin k) (Fin d) ℝ ↦ (realWishartGram R)⁻¹) :=
    measurable_nonsingInv_realWishartGram_matrix
  have hscaled : Measurable
      (fun R : Matrix (Fin k) (Fin d) ℝ ↦
        gamma • (realWishartGram R)⁻¹) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact measurable_const.mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hinv))
  exact measurable_h12h14RealMatrix_trace
    (measurable_h12h14RealMatrix_pow hscaled 4)

/-- Pointwise equality of the paper identity-scale order-four observable and
the project observable after the Gaussian `1/sqrt 2` scale map. -/
theorem h12h14_matsumotoIdentityScaledInverseTraceFour_invSqrtTwoScaleMatrix
    {N K : ℕ} (hNK : N ≤ K)
    (R : Matrix (Fin (K - N)) (Fin N) ℝ)
    (hunit : IsUnit (realWishartGram R).det) :
    h12h14MatsumotoIdentityScaledInverseTraceFour N (K - N)
        (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)))
        (invSqrtTwoScaleMatrix (K - N) N R) =
      h12h14ProjectScaledInverseTraceFour N K R := by
  have hinv :
      (realWishartGram (invSqrtTwoScaleMatrix (K - N) N R))⁻¹ =
        (2 : ℝ) • (realWishartGram R)⁻¹ := by
    rw [realWishartGram_invSqrtTwoScaleMatrix]
    letI : Invertible (1 / 2 : ℝ) :=
      invertibleOfNonzero (by norm_num)
    rw [Matrix.inv_smul (A := realWishartGram R) (1 / 2 : ℝ) hunit]
    change (⅟ (1 / 2 : ℝ)) • (realWishartGram R)⁻¹ =
      (2 : ℝ) • (realWishartGram R)⁻¹
    norm_num
  have hgamma :
      h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)) * 2 =
        concreteCOEExponent N K := by
    rw [mul_comm]
    exact h12h14_two_mul_projectDenominator_gamma_eq_concreteCOEExponent hNK
  unfold h12h14MatsumotoIdentityScaledInverseTraceFour
    h12h14MatsumotoIdentityScaledInverseMatrix
    h12h14ProjectScaledInverseTraceFour h12h14ProjectScaledInverseMatrix
  rw [hinv, smul_smul, hgamma]

/-- Exact equality between the identity-scale A4 order-four integral and the
project variance-one denominator integral.  This is proved before consuming
any A4 moment formula and before taking absolute values. -/
theorem h12h14_matsumotoIdentityScaledInverseTraceFour_integral_eq_project
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        h12h14MatsumotoIdentityScaledInverseTraceFour N (K - N)
          (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N))) R
          ∂halfGaussianMatrix (K - N) N) =
      ∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        h12h14ProjectScaledInverseTraceFour N K R
          ∂standardRealGaussianMatrixMeasure (K - N) N := by
  let f := h12h14MatsumotoIdentityScaledInverseTraceFour N (K - N)
    (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)))
  have hf : Measurable f :=
    measurable_h12h14MatsumotoIdentityScaledInverseTraceFour N (K - N)
      (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)))
  have hunit :=
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
      (k := K - N) (p := N) (by omega)
  calc
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ, f R
        ∂halfGaussianMatrix (K - N) N) =
      ∫ R, f R
        ∂Measure.map (invSqrtTwoScaleMatrix (K - N) N)
          (standardRealGaussianMatrixMeasure (K - N) N) := by
        rw [map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure]
    _ = ∫ R, f (invSqrtTwoScaleMatrix (K - N) N R)
        ∂standardRealGaussianMatrixMeasure (K - N) N := by
      rw [integral_map (measurable_invSqrtTwoScaleMatrix (K - N) N).aemeasurable
        hf.aestronglyMeasurable]
    _ = ∫ R, h12h14ProjectScaledInverseTraceFour N K R
        ∂standardRealGaussianMatrixMeasure (K - N) N := by
      apply integral_congr_ae
      filter_upwards [hunit] with R hR
      exact
        h12h14_matsumotoIdentityScaledInverseTraceFour_invSqrtTwoScaleMatrix
          (by omega) R hR

/-- Integrability crosses the exact Wishart scale conversion in the same
direction as the moment identity. -/
theorem h12h14_integrable_projectScaledInverseTraceFour_of_matsumotoIdentity
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (hA4 : Integrable
      (h12h14MatsumotoIdentityScaledInverseTraceFour N (K - N)
        (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N))))
      (halfGaussianMatrix (K - N) N)) :
    Integrable (h12h14ProjectScaledInverseTraceFour N K)
      (standardRealGaussianMatrixMeasure (K - N) N) := by
  let e := invSqrtTwoScaleMatrix (K - N) N
  have hmp : MeasurePreserving e
      (standardRealGaussianMatrixMeasure (K - N) N)
      (halfGaussianMatrix (K - N) N) :=
    ⟨measurable_invSqrtTwoScaleMatrix (K - N) N,
      map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure (K - N) N⟩
  have hcomp := hmp.integrable_comp_of_integrable hA4
  apply hcomp.congr
  filter_upwards [
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
      (k := K - N) (p := N) (by omega)] with R hR
  exact h12h14_matsumotoIdentityScaledInverseTraceFour_invSqrtTwoScaleMatrix
    (by omega) R hR

/-- The exact identity-scale trace-four output needed from the literal A4
specialization.  This is an ordinary proposition-valued structure, not a new
scientific axiom. -/
structure H12H14MatsumotoIdentityTraceFourMoment
    (d k : ℕ) (gamma value : ℝ) : Prop where
  integrable : Integrable
    (h12h14MatsumotoIdentityScaledInverseTraceFour d k gamma)
    (halfGaussianMatrix k d)
  integral_eq :
    (∫ R : Matrix (Fin k) (Fin d) ℝ,
      h12h14MatsumotoIdentityScaledInverseTraceFour d k gamma R
        ∂halfGaussianMatrix k d) = value

/-- Every paper-to-project operation is discharged here as a theorem: law
scale, `gamma=c/2`, pointwise inverse scale, integral equality, and
integrability transport. -/
theorem h12h14_projectTraceFourMoment_of_matsumotoIdentity
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) {value : ℝ}
    (hA4 : H12H14MatsumotoIdentityTraceFourMoment N (K - N)
      (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N))) value) :
    Integrable (h12h14ProjectScaledInverseTraceFour N K)
        (standardRealGaussianMatrixMeasure (K - N) N) ∧
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        h12h14ProjectScaledInverseTraceFour N K R
          ∂standardRealGaussianMatrixMeasure (K - N) N) = value := by
  constructor
  · exact h12h14_integrable_projectScaledInverseTraceFour_of_matsumotoIdentity
      hgap hA4.integrable
  · rw [← h12h14_matsumotoIdentityScaledInverseTraceFour_integral_eq_project hgap,
      hA4.integral_eq]

/-! ## Centered score and projective cancellation before absolute values -/

/-- Re-export of the exact centered `ell_2` representation at the A4 adapter
boundary, before any absolute value. -/
theorem h12h14_centeredEllTwo_before_abs
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 2 N K (A, v) =
      -4 *
        ((complexCenteredProjectiveSandwich v
            (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re +
          (complexCenteredProjectiveConjugateSandwich v
            (concreteCOERMatrix N K A)).re) :=
  concreteCenteredEll_two_eq_projectiveSandwiches_h14_internal
    hN hgap A v hsymm hsupport

/-- Exact trace-zero projective fourth moment at the adapter boundary.  The
scalar mode has been cancelled in the equality itself, before absolute values. -/
theorem h12h14_projectiveTraceZero_fourth_before_abs
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveTracePair v A ^ 4
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ : ℝ) : ℂ) *
        (3 * Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A) ^ 2 +
          6 * Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A)) :=
  integral_complexCenteredProjectiveTracePair_fourth_eq_traceZero_h14 hN A

/-- Complexification of the same project denominator matrix used in the A4
moment conversion. -/
def h12h14ComplexProjectScaledInverseMatrix
    (N K : ℕ) (R : Matrix (Fin (K - N)) (Fin N) ℝ) :
    ConcreteMatrixState N :=
  fun i j ↦ (h12h14ProjectScaledInverseMatrix N K R i j : ℂ)

/-- Exact trace-zero projective fourth package, still before absolute values. -/
def H12H14ProjectiveTraceZeroFourthPackage
    {N : ℕ} (A : ConcreteMatrixState N) : Prop :=
  Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v A ^ 4)
      (complexUnitSphereProbabilityMeasure N) ∧
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveTracePair v A ^ 4
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ : ℝ) : ℂ) *
        (3 * Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A) ^ 2 +
          6 * Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A))

/-- Smallest H12/H14 moment/cancellation bridge.  A literal A4 trace-four
output is transported to the project denominator, and the same denominator
matrix receives exact trace-zero complex-projective cancellation before any
absolute value.  This theorem is below both frozen endpoints. -/
theorem h12h14_matsumotoTraceFour_projectiveCancellationBridge
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) {value : ℝ}
    (hA4 : H12H14MatsumotoIdentityTraceFourMoment N (K - N)
      (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N))) value) :
    (Integrable (h12h14ProjectScaledInverseTraceFour N K)
        (standardRealGaussianMatrixMeasure (K - N) N) ∧
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        h12h14ProjectScaledInverseTraceFour N K R
          ∂standardRealGaussianMatrixMeasure (K - N) N) = value) ∧
      ∀ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        H12H14ProjectiveTraceZeroFourthPackage
          (h12h14ComplexProjectScaledInverseMatrix N K R) := by
  refine ⟨h12h14_projectTraceFourMoment_of_matsumotoIdentity hgap hA4, ?_⟩
  intro R
  constructor
  · exact integrable_complexCenteredProjectiveTracePair_fourth_h14 hN _
  · exact h12h14_projectiveTraceZero_fourth_before_abs hN _

#print axioms h12h14_matsumotoIdentityLaw_eq_halfScale_projectLaw
#print axioms h12h14_projectLaw_eq_sigmaTwo_pushforward
#print axioms h12h14_projectDenominator_gamma_eq
#print axioms h12h14_projectDenominator_gamma_eq_half_concreteCOEExponent
#print axioms h12h14_two_mul_projectDenominator_gamma_eq_concreteCOEExponent
#print axioms h12h14_projectDenominator_gamma_gt_order_sub_one
#print axioms h12h14_projectEntryIndices_eq
#print axioms h12h14_projectScaledInverseMatrix_eq_twoGamma
#print axioms h12h14_matsumotoIdentityScaledInverseTraceFour_invSqrtTwoScaleMatrix
#print axioms h12h14_matsumotoIdentityScaledInverseTraceFour_integral_eq_project
#print axioms h12h14_integrable_projectScaledInverseTraceFour_of_matsumotoIdentity
#print axioms h12h14_projectTraceFourMoment_of_matsumotoIdentity
#print axioms h12h14_centeredEllTwo_before_abs
#print axioms h12h14_projectiveTraceZero_fourth_before_abs
#print axioms h12h14_matsumotoTraceFour_projectiveCancellationBridge

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
