import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19DensityLimit
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangDensityProved
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19MatrixBetaDefinitions
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19LogDetSecondOrder
import LogdetLean.GramHafnian.UltimateHiding.Sparse.BinaryPinsker
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Quantitative consequences of Jiang's raw Haar-corner density

This source-pruned release uses the internally proved strict-size Lebesgue
density in `H19JiangDensityProved`.  The first section is a generic
measure-theoretic adapter: two finite real densities with respect to one
sigma-finite measure, with a strictly positive reference density, determine
their absolute continuity relation and log-likelihood ratio.  Thus no
Radon--Nikodym or likelihood identity is postulated for H19.
-/

open MeasureTheory
open scoped ENNReal BigOperators ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

/-! ## A generic common-density likelihood adapter -/

theorem withDensity_ofReal_absolutelyContinuous
    {alpha : Type*} [MeasurableSpace alpha]
    (lambda : Measure alpha) [SigmaFinite lambda]
    (f g : alpha -> Real)
    (hf : Measurable f) (hg : Measurable g)
    (_hf_nonneg : forall x, 0 <= f x) (hg_pos : forall x, 0 < g x) :
    lambda.withDensity (fun x => ENNReal.ofReal (f x)) ≪
      lambda.withDensity (fun x => ENNReal.ofReal (g x)) := by
  have hleft :
      lambda.withDensity (fun x => ENNReal.ofReal (f x)) ≪ lambda :=
    withDensity_absolutelyContinuous lambda _
  have hright : lambda ≪
      lambda.withDensity (fun x => ENNReal.ofReal (g x)) := by
    apply withDensity_absolutelyContinuous'
    · exact hg.ennreal_ofReal.aemeasurable
    · exact ae_of_all lambda fun x =>
        ENNReal.ofReal_ne_zero_iff.mpr (hg_pos x)
  exact hleft.trans hright

theorem rnDeriv_withDensity_ofReal_common
    {alpha : Type*} [MeasurableSpace alpha]
    (lambda : Measure alpha) [SigmaFinite lambda]
    (f g : alpha -> Real)
    (hf : Measurable f) (hg : Measurable g)
    (hf_nonneg : forall x, 0 <= f x) (hg_pos : forall x, 0 < g x) :
    (lambda.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv
        (lambda.withDensity (fun x => ENNReal.ofReal (g x))) =ᵐ[
      lambda.withDensity (fun x => ENNReal.ofReal (f x))]
        (fun x => ENNReal.ofReal (f x / g x)) :=
        by
          apply (withDensity_absolutelyContinuous lambda
            (fun x => ENNReal.ofReal (f x))).ae_eq
          have hgnezero : ∀ᵐ x ∂lambda,
              ENNReal.ofReal (g x) ≠ 0 :=
            ae_of_all lambda fun x =>
              ENNReal.ofReal_ne_zero_iff.mpr (hg_pos x)
          have hgnetop : ∀ᵐ x ∂lambda,
              ENNReal.ofReal (g x) ≠ ∞ :=
            ae_of_all lambda fun _ => ENNReal.ofReal_ne_top
          have hright := Measure.rnDeriv_withDensity_right
            (lambda.withDensity (fun x => ENNReal.ofReal (f x))) lambda
            hg.ennreal_ofReal.aemeasurable hgnezero hgnetop
          have hleft := Measure.rnDeriv_withDensity lambda
            hf.ennreal_ofReal
          filter_upwards [hright, hleft] with x hxright hxleft
          rw [hxright, hxleft]
          rw [ENNReal.ofReal_div_of_pos (hg_pos x)]
          simp [div_eq_mul_inv, mul_comm]

theorem llr_withDensity_ofReal_common
    {alpha : Type*} [MeasurableSpace alpha]
    (lambda : Measure alpha) [SigmaFinite lambda]
    (f g : alpha -> Real)
    (hf : Measurable f) (hg : Measurable g)
    (hf_nonneg : forall x, 0 <= f x) (hg_pos : forall x, 0 < g x) :
    llr (lambda.withDensity (fun x => ENNReal.ofReal (f x)))
        (lambda.withDensity (fun x => ENNReal.ofReal (g x))) =ᵐ[
      lambda.withDensity (fun x => ENNReal.ofReal (f x))]
        (fun x => Real.log (f x / g x)) := by
  have hrn := rnDeriv_withDensity_ofReal_common lambda f g hf hg
    hf_nonneg hg_pos
  filter_upwards [hrn] with x hx
  rw [llr, hx, ENNReal.toReal_ofReal]
  exact div_nonneg (hf_nonneg x) (le_of_lt (hg_pos x))

/-- A common-density likelihood is integrable as soon as its positive part
has an integrable upper envelope.  The negative part needs no tail estimate:
for `0 < r ≤ 1`, the elementary bound `r * |log r| < 1` transports it to
the reference density `g`. -/
theorem integrable_log_densityRatio_of_integrable_upper
    {alpha : Type*} [MeasurableSpace alpha]
    (lambda : Measure alpha)
    (f g B : alpha → Real)
    (hf : Measurable f) (hg : Measurable g) (hBmeas : Measurable B)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_pos : ∀ x, 0 < g x)
    (hB_nonneg : ∀ x, 0 ≤ B x)
    (hg_integrable : Integrable g lambda)
    (hB_integrable : Integrable B
      (lambda.withDensity (fun x ↦ ENNReal.ofReal (f x))))
    (hupper : ∀ x, f x ≠ 0 → Real.log (f x / g x) ≤ B x) :
    Integrable (fun x ↦ Real.log (f x / g x))
      (lambda.withDensity (fun x ↦ ENNReal.ofReal (f x))) := by
  let mu := lambda.withDensity (fun x ↦ ENNReal.ofReal (f x))
  have hquot_integrable : Integrable (fun x ↦ g x / f x) mu := by
    dsimp only [mu]
    rw [integrable_withDensity_iff hf.ennreal_ofReal
      (ae_of_all lambda fun _ ↦ ENNReal.ofReal_lt_top)]
    apply hg_integrable.mono
    · exact ((hg.div hf).mul
          (hf.ennreal_ofReal.ennreal_toReal)).aestronglyMeasurable
    · filter_upwards with x
      rw [ENNReal.toReal_ofReal (hf_nonneg x)]
      by_cases hfx : f x = 0
      · simp [hfx]
      · rw [div_mul_cancel₀ _ hfx]
  apply Integrable.mono' (hB_integrable.add hquot_integrable)
    ((hf.div hg).log.aestronglyMeasurable)
  refine (ae_withDensity_iff hf.ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hfx_ofReal
  have hfx_pos : 0 < f x :=
    ENNReal.ofReal_ne_zero_iff.mp hfx_ofReal
  have hfx : f x ≠ 0 := hfx_pos.ne'
  have hr : 0 < f x / g x := div_pos hfx_pos (hg_pos x)
  have hquot_nonneg : 0 ≤ g x / f x :=
    (div_pos (hg_pos x) hfx_pos).le
  change |Real.log (f x / g x)| ≤ B x + g x / f x
  by_cases hr_one : f x / g x ≤ 1
  · have habs_mul := Real.abs_log_mul_self_lt (f x / g x) hr hr_one
    have habs_le_inv : |Real.log (f x / g x)| ≤ (f x / g x)⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hr).2
      calc
        |Real.log (f x / g x)| * (f x / g x) =
            |Real.log (f x / g x) * (f x / g x)| := by
              rw [abs_mul, abs_of_pos hr]
        _ ≤ 1 := habs_mul.le
    have hinv : (f x / g x)⁻¹ = g x / f x := by
      field_simp
    rw [hinv] at habs_le_inv
    linarith [hB_nonneg x]
  · have hr_ge : 1 ≤ f x / g x := le_of_not_ge hr_one
    rw [abs_of_nonneg (Real.log_nonneg hr_ge)]
    linarith [hupper x hfx, hquot_nonneg]

/-! ## Jiang's raw density against the explicit Gaussian density -/

/-- Strict-size, internally proved absolute continuity. -/
theorem
    jiangSqrtScaledTallHaarCornerLaw_absolutelyContinuous_gaussian_proved_strict
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N <= K)
    (hs : K + N < M) :
    jiangSqrtScaledTallHaarCornerLaw M K N ≪
      standardGaussianBlockLaw K N := by
  rw [jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs,
    standardGaussianBlockLaw_eq_withDensity_ofReal_H19 K N]
  exact withDensity_ofReal_absolutelyContinuous
    (complexRectangularLebesgueVolume K N)
    (jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (standardComplexGaussianTallRealPDF K N)
    (measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (measurable_standardComplexGaussianTallRealPDF K N)
    (jiangSqrtScaledTallHaarCornerRealPDF_nonneg M K N)
    (fun Z => by
      unfold standardComplexGaussianTallRealPDF
      exact mul_pos (inv_pos.mpr (pow_pos Real.pi_pos _))
        (Real.exp_pos _))

theorem integrable_standardComplexGaussianTallRealPDF (K N : Nat) :
    Integrable (standardComplexGaussianTallRealPDF K N)
      (complexRectangularLebesgueVolume K N) := by
  let nu : Measure (Matrix (Fin K) (Fin N) Complex) :=
    standardGaussianBlockLaw K N
  letI : IsProbabilityMeasure nu :=
    standardComplexGaussianRectangularMeasure_isProbability K N
  have hone : Integrable
      (fun _Z : Matrix (Fin K) (Fin N) Complex ↦ (1 : Real)) nu :=
    integrable_const _
  dsimp only [nu] at hone
  rw [standardGaussianBlockLaw_eq_withDensity_ofReal_H19 K N] at hone
  have h := (integrable_withDensity_iff
    (measurable_standardComplexGaussianTallRealPDF K N).ennreal_ofReal
    (ae_of_all (complexRectangularLebesgueVolume K N)
      fun _ ↦ ENNReal.ofReal_lt_top)).mp hone
  simpa only [one_mul, ENNReal.toReal_ofReal
    (standardComplexGaussianTallRealPDF_nonneg K N _)] using h

theorem measurable_jiangScaledTallEnergy (K N : Nat) :
    Measurable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re) := by
  have heq :
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re) =
      (fun Z ↦ ∑ i : Fin K, ∑ j : Fin N, ‖Z i j‖ ^ 2) := by
    funext Z
    exact trace_conjTranspose_mul_self_re_eq_sum_norm_sq Z
  rw [heq]
  fun_prop

theorem jiangScaledTallEnergy_nonneg {K N : Nat}
    (Z : Matrix (Fin K) (Fin N) Complex) :
    0 ≤ (Matrix.trace (Z.conjTranspose * Z)).re := by
  rw [trace_conjTranspose_mul_self_re_eq_sum_norm_sq]
  positivity

/-- Strict-size, internally proved log-density-ratio identity. -/
theorem
    llr_jiangSqrtScaledTallHaarCornerLaw_eq_log_densityRatio_proved_strict
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N <= K)
    (hs : K + N < M) :
    llr (jiangSqrtScaledTallHaarCornerLaw M K N)
        (standardGaussianBlockLaw K N) =ᵐ[
      jiangSqrtScaledTallHaarCornerLaw M K N]
      (fun Z => Real.log
        (jiangSqrtScaledTallHaarCornerRealPDF M K N Z /
          standardComplexGaussianTallRealPDF K N Z)) := by
  rw [jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs,
    standardGaussianBlockLaw_eq_withDensity_ofReal_H19 K N]
  exact llr_withDensity_ofReal_common
    (complexRectangularLebesgueVolume K N)
    (jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (standardComplexGaussianTallRealPDF K N)
    (measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (measurable_standardComplexGaussianTallRealPDF K N)
    (jiangSqrtScaledTallHaarCornerRealPDF_nonneg M K N)
    (fun Z => by
      unfold standardComplexGaussianTallRealPDF
      exact mul_pos (inv_pos.mpr (pow_pos Real.pi_pos _))
        (Real.exp_pos _))

/-! ## Elementary normalization algebra -/

/-- The constant part of the scaled Jiang density divided by the Gaussian
normalizer. -/
def jiangScaledTallNormalizerRatio (M K N : Nat) : Real :=
  ((M : Real)⁻¹) ^ (K * N) *
    jiangUnscaledTallHaarCornerNormalizer M K N *
      Real.pi ^ (K * N)

private theorem h19_factorial_ratio_eq_descFactorial
    {m K : Nat} (hK : K <= m) :
    ((Nat.factorial m : Nat) : Real) /
        ((Nat.factorial (m - K) : Nat) : Real) =
      ((Nat.descFactorial m K : Nat) : Real) := by
  have hden : ((Nat.factorial (m - K) : Nat) : Real) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m - K)
  rw [div_eq_iff hden]
  norm_cast
  simpa [Nat.mul_comm] using (Nat.factorial_mul_descFactorial hK).symm

theorem jiangScaledTallNormalizerRatio_eq_rectangularProduct
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hs : K + N <= M) :
    jiangScaledTallNormalizerRatio M K N =
      ∏ i : Fin N × Fin K,
        (1 - rectangularNormalizedIndex K N M i) := by
  have hM : (0 : Real) < M := by exact_mod_cast (by omega : 0 < M)
  have hpi : Real.pi ^ (K * N) ≠ 0 :=
    pow_ne_zero _ Real.pi_ne_zero
  unfold jiangScaledTallNormalizerRatio
  rw [jiangUnscaledTallHaarCornerNormalizer]
  have hcancel :
      ((M : Real)⁻¹) ^ (K * N) *
          ((Real.pi ^ (K * N))⁻¹ *
            ∏ j : Fin N,
              ((Nat.factorial (M - (j.1 + 1)) : Nat) : Real) /
                ((Nat.factorial (M - (j.1 + 1) - K) : Nat) : Real)) *
            Real.pi ^ (K * N) =
        ((M : Real)⁻¹) ^ (K * N) *
          ∏ j : Fin N,
            ((Nat.factorial (M - (j.1 + 1)) : Nat) : Real) /
              ((Nat.factorial (M - (j.1 + 1) - K) : Nat) : Real) := by
    field_simp [hpi]
  rw [hcancel]
  rw [show ((M : Real)⁻¹) ^ (K * N) =
      ∏ _j : Fin N, ((M : Real)⁻¹) ^ K by
    simp [pow_mul]]
  rw [← Finset.prod_mul_distrib]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _hj
  have hjM : j.1 + 1 + K <= M := by omega
  have hKle : K <= M - (j.1 + 1) := by omega
  rw [h19_factorial_ratio_eq_descFactorial hKle,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [← Fin.prod_univ_eq_prod_range]
  rw [show ((M : Real)⁻¹) ^ K =
      ∏ _ell : Fin K, (M : Real)⁻¹ by simp]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ell _hell
  change (M : Real)⁻¹ * (M - (j.1 + 1) - ell.1 : Nat) =
    1 - (((j.1 : Real) + 1 + (ell.1 : Real)) / M)
  rw [Nat.cast_sub (by omega : ell.1 <= M - (j.1 + 1)),
    Nat.cast_sub (by omega : j.1 + 1 <= M)]
  field_simp
  push_cast
  ring

theorem log_jiangScaledTallNormalizerRatio_eq_logNormalizer
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hs : K + N <= M) :
    Real.log (jiangScaledTallNormalizerRatio M K N) =
      jiangScaledBlockLogNormalizer M N K := by
  rw [jiangScaledTallNormalizerRatio_eq_rectangularProduct hN hK hs]
  unfold jiangScaledBlockLogNormalizer
  rw [Real.log_prod]
  intro i _hi
  exact (sub_pos.mpr (rectangular_index_lt_one hK hN hs i)).ne'

theorem jiangScaledBlockLogNormalizer_nonpos_raw
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hs : K + N ≤ M) :
    jiangScaledBlockLogNormalizer M N K ≤ 0 := by
  unfold jiangScaledBlockLogNormalizer
  apply Finset.sum_nonpos
  intro i _hi
  have hx0 : 0 ≤ rectangularNormalizedIndex K N M i :=
    rectangular_index_nonneg K N M i
  have hx1 : rectangularNormalizedIndex K N M i < 1 :=
    rectangular_index_lt_one hK hN hs i
  exact Real.log_nonpos (sub_nonneg.mpr hx1.le)
    (by linarith)

/-! ## Identification with Jiang's explicit scaled likelihood -/

def jiangScaledTallLogLikelihood {K N : Nat} (M : Nat)
    (Z : Matrix (Fin K) (Fin N) Complex) : Real :=
  jiangScaledBlockLogNormalizer M N K +
    ((M : Real) - K - N) *
      Real.log
        (Matrix.det
          (1 - ((((M : Real)⁻¹ : Real) : Complex)) •
            (Z.conjTranspose * Z))).re +
    (Matrix.trace (Z.conjTranspose * Z)).re

theorem jiangScaledTallLogLikelihood_eq_wide
    {K N : Nat} (M : Nat) (Z : Matrix (Fin K) (Fin N) Complex) :
    jiangScaledTallLogLikelihood M Z =
      jiangScaledBlockLogLikelihood M Z.conjTranspose := by
  unfold jiangScaledTallLogLikelihood jiangScaledBlockLogLikelihood
    scaledBlockLogDetComplement scaledBlockEnergy
  simp

theorem jiangScaledTallNormalizerRatio_pos
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hs : K + N <= M) :
    0 < jiangScaledTallNormalizerRatio M K N := by
  rw [jiangScaledTallNormalizerRatio_eq_rectangularProduct hN hK hs]
  exact Finset.prod_pos fun i _ =>
    sub_pos.mpr (rectangular_index_lt_one hK hN hs i)

/-- On the nonzero-density set, the literal density ratio is exactly the
exponential of Jiang's scaled likelihood.  The hypothesis is automatic
almost everywhere under the Jiang law. -/
theorem log_jiangTallDensityRatio_eq_jiangScaledTallLogLikelihood_of_ne_zero
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N <= K)
    (hs : K + N <= M)
    (Z : Matrix (Fin K) (Fin N) Complex)
    (hf : jiangSqrtScaledTallHaarCornerRealPDF M K N Z ≠ 0) :
    Real.log
        (jiangSqrtScaledTallHaarCornerRealPDF M K N Z /
          standardComplexGaussianTallRealPDF K N Z) =
      jiangScaledTallLogLikelihood M Z := by
  have hMnat : 0 < M := by omega
  have hM : (0 : Real) < M := by exact_mod_cast hMnat
  have hsupport : jiangUnscaledTallHaarCornerSupport
      ((Real.sqrt (M : Real))⁻¹ • Z) := by
    by_contra hn
    apply hf
    simp [jiangSqrtScaledTallHaarCornerRealPDF, hn]
  let D : Real :=
    (Matrix.det
      (1 - ((((M : Real)⁻¹ : Real) : Complex)) •
        (Z.conjTranspose * Z))).re
  let T : Real := (Matrix.trace (Z.conjTranspose * Z)).re
  let c : Nat := M - K - N
  have hgram := conjTranspose_invSqrt_smul_mul_self hMnat Z
  have hpdf :
      jiangSqrtScaledTallHaarCornerRealPDF M K N Z =
        ((M : Real)⁻¹) ^ (K * N) *
          jiangUnscaledTallHaarCornerNormalizer M K N * D ^ c := by
    unfold jiangSqrtScaledTallHaarCornerRealPDF
    rw [if_pos hsupport, hgram]
    simp only [D, c]
    ring
  have hconst :
      ((M : Real)⁻¹) ^ (K * N) *
          jiangUnscaledTallHaarCornerNormalizer M K N ≠ 0 := by
    intro hz
    apply hf
    rw [hpdf, hz, zero_mul]
  have hDpow : D ^ c ≠ 0 := by
    intro hz
    apply hf
    rw [hpdf, hz, mul_zero]
  have hR : jiangScaledTallNormalizerRatio M K N ≠ 0 :=
    (jiangScaledTallNormalizerRatio_pos hN hK hs).ne'
  have hpi : Real.pi ^ (K * N) ≠ 0 :=
    pow_ne_zero _ Real.pi_ne_zero
  have hgauss :
      standardComplexGaussianTallRealPDF K N Z =
        (Real.pi ^ (K * N))⁻¹ * Real.exp (-T) := by rfl
  have hgauss0 : standardComplexGaussianTallRealPDF K N Z ≠ 0 := by
    rw [hgauss]
    exact mul_ne_zero (inv_ne_zero hpi) (Real.exp_ne_zero _)
  have hratio :
      jiangSqrtScaledTallHaarCornerRealPDF M K N Z /
          standardComplexGaussianTallRealPDF K N Z =
        jiangScaledTallNormalizerRatio M K N * D ^ c * Real.exp T := by
    rw [hpdf, hgauss]
    unfold jiangScaledTallNormalizerRatio
    field_simp [hpi, Real.exp_ne_zero]
    rw [mul_assoc]
    rw [← Real.exp_add]
    simp
  rw [hratio, Real.log_mul (mul_ne_zero hR hDpow) (Real.exp_ne_zero _),
    Real.log_mul hR hDpow, Real.log_pow, Real.log_exp,
    log_jiangScaledTallNormalizerRatio_eq_logNormalizer hN hK hs]
  unfold jiangScaledTallLogLikelihood D T c
  rw [Nat.cast_sub (by omega : N ≤ M - K),
    Nat.cast_sub (by omega : K ≤ M)]

/-- The positive part of Jiang's likelihood is dominated by the Gaussian
quadratic energy.  Strict slack in the ambient dimension ensures that a
nonzero Jiang density excludes a singular matrix-ball boundary. -/
theorem jiangScaledTallLogLikelihood_le_energy_of_ne_zero
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hs : K + N < M)
    (Z : Matrix (Fin K) (Fin N) Complex)
    (hf : jiangSqrtScaledTallHaarCornerRealPDF M K N Z ≠ 0) :
    jiangScaledTallLogLikelihood M Z ≤
      (Matrix.trace (Z.conjTranspose * Z)).re := by
  have hsle : K + N ≤ M := hs.le
  have hMnat : 0 < M := by omega
  have hsupport : jiangUnscaledTallHaarCornerSupport
      ((Real.sqrt (M : Real))⁻¹ • Z) := by
    by_contra hn
    apply hf
    simp [jiangSqrtScaledTallHaarCornerRealPDF, hn]
  let A : Matrix (Fin N) (Fin N) Complex :=
    ((((M : Real)⁻¹ : Real) : Complex)) • (Z.conjTranspose * Z)
  let D : Real := (Matrix.det (1 - A)).re
  let c : Nat := M - K - N
  have hgram := conjTranspose_invSqrt_smul_mul_self hMnat Z
  have hpdf :
      jiangSqrtScaledTallHaarCornerRealPDF M K N Z =
        ((M : Real)⁻¹) ^ (K * N) *
          jiangUnscaledTallHaarCornerNormalizer M K N * D ^ c := by
    unfold jiangSqrtScaledTallHaarCornerRealPDF
    rw [if_pos hsupport, hgram]
    simp only [A, D, c]
    ring
  have hDpow : D ^ c ≠ 0 := by
    intro hz
    apply hf
    rw [hpdf, hz, mul_zero]
  have hc : c ≠ 0 := by
    dsimp only [c]
    omega
  have hDne : D ≠ 0 := (pow_ne_zero_iff hc).mp hDpow
  have hA : A.PosSemidef := by
    dsimp only [A]
    exact (Matrix.posSemidef_conjTranspose_mul_self Z).smul
      (a := ((((M : Real)⁻¹ : Real) : Complex)))
      (Complex.nonneg_iff.mpr ⟨by
        simp only [Complex.ofReal_re]
        exact inv_nonneg.mpr (Nat.cast_nonneg M), by simp⟩)
  have hcomp : (1 - A).PosSemidef := by
    have hcomp' :=
      (jiangUnscaledTallHaarCornerSupport_iff_posSemidef _).mp hsupport
    rw [hgram] at hcomp'
    simpa only [A] using hcomp'
  have hDnonneg : 0 ≤ D := by
    dsimp only [D]
    exact (Complex.nonneg_iff.mp hcomp.det_nonneg).1
  have hDpos : 0 < D := lt_of_le_of_ne hDnonneg (Ne.symm hDne)
  have hsecond :=
    log_det_one_sub_le_neg_trace_sub_half_trace_sq_h19 A hA hcomp hDpos
  have htraceA : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htraceA2 : 0 ≤ (Matrix.trace (A * A)).re := by
    rw [show A * A = A ^ 2 by noncomm_ring]
    exact (Complex.nonneg_iff.mp (hA.pow 2).trace_nonneg).1
  have hlogD : Real.log D ≤ 0 := by
    dsimp only [D] at hsecond ⊢
    linarith
  have hnorm := jiangScaledBlockLogNormalizer_nonpos_raw hN hK hsle
  have hcoeff : 0 ≤ (M : Real) - K - N := by
    have hcast : (K : Real) + N ≤ M := by exact_mod_cast hsle
    linarith
  unfold jiangScaledTallLogLikelihood
  change jiangScaledBlockLogNormalizer M N K +
      ((M : Real) - K - N) * Real.log D +
        (Matrix.trace (Z.conjTranspose * Z)).re ≤ _
  exact add_le_of_nonpos_of_le
    (add_nonpos hnorm (mul_nonpos_of_nonneg_of_nonpos hcoeff hlogD))
    (le_refl _)

/-- Strict-size, internally proved explicit Jiang log-likelihood identity. -/
theorem llr_jiangSqrtScaledTallHaarCornerLaw_eq_explicit_proved_strict
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N <= K)
    (hs : K + N < M) :
    llr (jiangSqrtScaledTallHaarCornerLaw M K N)
        (standardGaussianBlockLaw K N) =ᵐ[
      jiangSqrtScaledTallHaarCornerLaw M K N]
      jiangScaledTallLogLikelihood M := by
  have hratio :=
    llr_jiangSqrtScaledTallHaarCornerLaw_eq_log_densityRatio_proved_strict
      hN hK hNK hs
  rw [jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs] at hratio ⊢
  refine hratio.trans ?_
  refine (ae_withDensity_iff
    ((measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N).ennreal_ofReal)).2 ?_
  filter_upwards with Z
  intro hf
  exact log_jiangTallDensityRatio_eq_jiangScaledTallLogLikelihood_of_ne_zero
    hN hK hNK hs.le Z (ENNReal.ofReal_ne_zero_iff.mp hf).ne'

/-- Once the elementary quadratic energy is known integrable under the Haar
corner law, likelihood integrability follows directly from the raw density.
The negative log-likelihood tail is handled by `r * |log r| < 1`, not by a
matrix-beta factorization or a postulated KL identity. -/
theorem integrable_llr_jiangSqrtScaledTallHaarCornerLaw_of_energy_integrable
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M)
    (henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N)) :
    Integrable
      (llr (jiangSqrtScaledTallHaarCornerLaw M K N)
        (standardGaussianBlockLaw K N))
      (jiangSqrtScaledTallHaarCornerLaw M K N) := by
  have hlaw :=
    jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs
  have henergyDensity := henergy
  rw [hlaw] at henergyDensity
  have hratioDensity : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        Real.log
          (jiangSqrtScaledTallHaarCornerRealPDF M K N Z /
            standardComplexGaussianTallRealPDF K N Z))
      ((complexRectangularLebesgueVolume K N).withDensity
        (fun Z ↦ ENNReal.ofReal
          (jiangSqrtScaledTallHaarCornerRealPDF M K N Z))) := by
    apply integrable_log_densityRatio_of_integrable_upper
      (complexRectangularLebesgueVolume K N)
      (jiangSqrtScaledTallHaarCornerRealPDF M K N)
      (standardComplexGaussianTallRealPDF K N)
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N)
      (measurable_standardComplexGaussianTallRealPDF K N)
      (measurable_jiangScaledTallEnergy K N)
      (jiangSqrtScaledTallHaarCornerRealPDF_nonneg M K N)
      (fun Z ↦ by
        unfold standardComplexGaussianTallRealPDF
        exact mul_pos (inv_pos.mpr (pow_pos Real.pi_pos _))
          (Real.exp_pos _))
      jiangScaledTallEnergy_nonneg
      (integrable_standardComplexGaussianTallRealPDF K N)
      henergyDensity
    intro Z hf
    rw [log_jiangTallDensityRatio_eq_jiangScaledTallLogLikelihood_of_ne_zero
      hN hK hNK hs.le Z hf]
    exact jiangScaledTallLogLikelihood_le_energy_of_ne_zero
      hN hK hs Z hf
  have hratio : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        Real.log
          (jiangSqrtScaledTallHaarCornerRealPDF M K N Z /
            standardComplexGaussianTallRealPDF K N Z))
      (jiangSqrtScaledTallHaarCornerLaw M K N) := by
    rw [hlaw]
    exact hratioDensity
  exact hratio.congr
    (llr_jiangSqrtScaledTallHaarCornerLaw_eq_log_densityRatio_proved_strict
      hN hK hNK hs).symm

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
