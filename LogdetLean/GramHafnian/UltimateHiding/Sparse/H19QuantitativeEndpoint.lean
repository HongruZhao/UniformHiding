import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19QuantitativeRawDensity
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangDensityProved
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19QuantitativeAlgebra
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarGramSecondMoment
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19DirectTV
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19RawBranchBridge
import Mathlib.Tactic

/-!
# Quantitative H19 from the raw Jiang density

This module combines the raw-density likelihood adapter, a deterministic
second-order log-determinant inequality, and internally proved Haar moments.
It introduces no scientific axiom beyond Jiang's literal Proposition 2.1
density declaration.
-/

open MeasureTheory
open scoped BigOperators ENNReal ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LocalAnticoncentration

/-- The squared Gram energy in Jiang's native tall orientation. -/
def jiangScaledTallGramSecondEnergy {K N : Nat}
    (Z : Matrix (Fin K) (Fin N) Complex) : Real :=
  (Matrix.trace
    ((Z.conjTranspose * Z) * (Z.conjTranspose * Z))).re

theorem measurable_jiangScaledTallGramSecondEnergy (K N : Nat) :
    Measurable (@jiangScaledTallGramSecondEnergy K N) := by
  unfold jiangScaledTallGramSecondEnergy Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  fun_prop

theorem jiangScaledTallGramSecondEnergy_nonneg {K N : Nat}
    (Z : Matrix (Fin K) (Fin N) Complex) :
    0 ≤ jiangScaledTallGramSecondEnergy Z := by
  let W : Matrix (Fin N) (Fin N) Complex := Z.conjTranspose * Z
  have hW : W.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Z
  unfold jiangScaledTallGramSecondEnergy
  change 0 ≤ (Matrix.trace (W * W)).re
  rw [show W * W = W ^ 2 by noncomm_ring]
  exact (Complex.nonneg_iff.mp (hW.pow 2).trace_nonneg).1

/-- First-order control of the finite Jiang normalizer. -/
theorem jiangScaledBlockLogNormalizer_le_firstOrder_raw
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hs : K + N ≤ M) :
    jiangScaledBlockLogNormalizer M N K ≤
      -((K : Real) * N * ((K : Real) + N)) / (2 * M) := by
  unfold jiangScaledBlockLogNormalizer
  calc
    ∑ i : Fin N × Fin K,
        Real.log (1 - rectangularNormalizedIndex K N M i) ≤
        ∑ i : Fin N × Fin K,
          -rectangularNormalizedIndex K N M i := by
      apply Finset.sum_le_sum
      intro i _hi
      have hden : 0 < 1 - rectangularNormalizedIndex K N M i :=
        sub_pos.mpr (rectangular_index_lt_one hK hN hs i)
      have hlog := Real.log_le_sub_one_of_pos hden
      linarith
    _ = -((K : Real) * N * ((K : Real) + N)) / (2 * M) := by
      rw [Finset.sum_neg_distrib, sum_rectangular_normalized_index K N M]
      ring

/-- Pointwise second-order upper bound for the raw Jiang likelihood. -/
theorem jiangScaledTallLogLikelihood_le_secondOrder_of_ne_zero
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K)
    (hs : K + N < M)
    (Z : Matrix (Fin K) (Fin N) Complex)
    (hf : jiangSqrtScaledTallHaarCornerRealPDF M K N Z ≠ 0) :
    jiangScaledTallLogLikelihood M Z ≤
      jiangScaledBlockLogNormalizer M N K +
        (((K : Real) + N) / M) *
          (Matrix.trace (Z.conjTranspose * Z)).re -
        (((M : Real) - K - N) / (2 * (M : Real) ^ 2)) *
          jiangScaledTallGramSecondEnergy Z := by
  have hMnat : 0 < M := by omega
  have hsupport : jiangUnscaledTallHaarCornerSupport
      ((Real.sqrt (M : Real))⁻¹ • Z) := by
    by_contra hn
    apply hf
    simp [jiangSqrtScaledTallHaarCornerRealPDF, hn]
  let W : Matrix (Fin N) (Fin N) Complex := Z.conjTranspose * Z
  let A : Matrix (Fin N) (Fin N) Complex :=
    ((((M : Real)⁻¹ : Real) : Complex)) • W
  let D : Real := (Matrix.det (1 - A)).re
  let c : Nat := M - K - N
  have hgram := conjTranspose_invSqrt_smul_mul_self hMnat Z
  have hpdf :
      jiangSqrtScaledTallHaarCornerRealPDF M K N Z =
        ((M : Real)⁻¹) ^ (K * N) *
          jiangUnscaledTallHaarCornerNormalizer M K N * D ^ c := by
    unfold jiangSqrtScaledTallHaarCornerRealPDF
    rw [if_pos hsupport, hgram]
    simp only [W, A, D, c]
    ring
  have hDpow : D ^ c ≠ 0 := by
    intro hz
    apply hf
    rw [hpdf, hz, mul_zero]
  have hc : c ≠ 0 := by
    dsimp only [c]
    omega
  have hDne : D ≠ 0 := (pow_ne_zero_iff hc).mp hDpow
  have hW : W.PosSemidef := by
    dsimp only [W]
    exact Matrix.posSemidef_conjTranspose_mul_self Z
  have hA : A.PosSemidef := by
    dsimp only [A]
    exact hW.smul
      (a := ((((M : Real)⁻¹ : Real) : Complex)))
      (Complex.nonneg_iff.mpr ⟨by
        simp only [Complex.ofReal_re]
        exact inv_nonneg.mpr (Nat.cast_nonneg M), by simp⟩)
  have hcomp : (1 - A).PosSemidef := by
    have hcomp' :=
      (jiangUnscaledTallHaarCornerSupport_iff_posSemidef _).mp hsupport
    rw [hgram] at hcomp'
    simpa only [W, A] using hcomp'
  have hDnonneg : 0 ≤ D := by
    dsimp only [D]
    exact (Complex.nonneg_iff.mp hcomp.det_nonneg).1
  have hDpos : 0 < D := lt_of_le_of_ne hDnonneg (Ne.symm hDne)
  have hsecond :=
    log_det_one_sub_le_neg_trace_sub_half_trace_sq_h19 A hA hcomp hDpos
  have htraceA :
      (Matrix.trace A).re = (M : Real)⁻¹ *
        (Matrix.trace W).re := by
    rw [show A = ((((M : Real)⁻¹ : Real) : Complex)) • W by rfl,
      Matrix.trace_smul]
    change (((((M : Real)⁻¹ : Real) : Complex) * Matrix.trace W)).re = _
    exact Complex.re_ofReal_mul _ _
  have htraceA2 :
      (Matrix.trace (A * A)).re = ((M : Real)⁻¹) ^ 2 *
        (Matrix.trace (W * W)).re := by
    have hscalar :
        ((((M : Real)⁻¹ : Real) : Complex)) *
            ((((M : Real)⁻¹ : Real) : Complex)) =
          (((((M : Real)⁻¹) ^ 2 : Real) : Complex)) := by
      norm_cast
      ring
    have hAA : A * A =
        (((((M : Real)⁻¹) ^ 2 : Real) : Complex)) • (W * W) := by
      dsimp only [A]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hscalar]
    rw [hAA, Matrix.trace_smul]
    change ((((((M : Real)⁻¹) ^ 2 : Real) : Complex) *
      Matrix.trace (W * W))).re = _
    exact Complex.re_ofReal_mul _ _
  have hlogD : Real.log D ≤
      -((M : Real)⁻¹ * (Matrix.trace W).re) -
        ((M : Real)⁻¹) ^ 2 * (Matrix.trace (W * W)).re / 2 := by
    dsimp only [D] at hsecond ⊢
    rw [htraceA, htraceA2] at hsecond
    exact hsecond
  have hcoeff : 0 ≤ (M : Real) - K - N := by
    have hcast : (K : Real) + N ≤ M := by exact_mod_cast hs.le
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlogD hcoeff
  have hlogD' : Real.log D ≤
      -(M : Real)⁻¹ * (Matrix.trace W).re -
        ((M : Real)⁻¹) ^ 2 * (Matrix.trace (W * W)).re / 2 := by
    nlinarith [hlogD]
  unfold jiangScaledTallLogLikelihood
  change jiangScaledBlockLogNormalizer M N K +
      ((M : Real) - K - N) * Real.log D +
        (Matrix.trace W).re ≤ _
  unfold jiangScaledTallGramSecondEnergy
  change _ ≤ jiangScaledBlockLogNormalizer M N K +
      (((K : Real) + N) / M) * (Matrix.trace W).re -
        (((M : Real) - K - N) / (2 * (M : Real) ^ 2)) *
          (Matrix.trace (W * W)).re
  have hM : (0 : Real) < M := by exact_mod_cast hMnat
  have hMne : (M : Real) ≠ 0 := hM.ne'
  calc
    jiangScaledBlockLogNormalizer M N K +
          ((M : Real) - K - N) * Real.log D +
          (Matrix.trace W).re ≤
        jiangScaledBlockLogNormalizer M N K +
          ((M : Real) - K - N) *
            (-(M : Real)⁻¹ * (Matrix.trace W).re -
              ((M : Real)⁻¹) ^ 2 *
                (Matrix.trace (W * W)).re / 2) +
          (Matrix.trace W).re := by gcongr
    _ = jiangScaledBlockLogNormalizer M N K +
          (((K : Real) + N) / M) * (Matrix.trace W).re -
          (((M : Real) - K - N) / (2 * (M : Real) ^ 2)) *
            (Matrix.trace (W * W)).re := by
      field_simp [hMne]
      ring

/-- Expectation-level quantitative bound, parameterized only by the two
elementary Haar Gram moments supplied by the internal moment module. -/
theorem integral_llr_jiangTall_le_three_quarters_of_moments
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) (E : Real)
    (henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (henergyMean :
      (∫ Z : Matrix (Fin K) (Fin N) Complex,
        (Matrix.trace (Z.conjTranspose * Z)).re
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        (K : Real) * N)
    (hsecond : Integrable jiangScaledTallGramSecondEnergy
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (hsecondMean :
      (∫ Z, jiangScaledTallGramSecondEnergy Z
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) = E)
    (hsecondLower :
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤ E) :
    (∫ Z, llr (jiangSqrtScaledTallHaarCornerLaw M K N)
        (standardGaussianBlockLaw K N) Z
        ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) ≤
      3 * ((K : Real) * N) * ((K : Real) + N) ^ 2 /
        (4 * (M : Real) ^ 2) := by
  let mu := jiangSqrtScaledTallHaarCornerLaw M K N
  let nu := standardGaussianBlockLaw K N
  have hMnat : 0 < M := by omega
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  letI : IsProbabilityMeasure mu :=
    jiangSqrtScaledTallHaarCornerLaw_isProbability hMnat hKM hNM
  letI : IsProbabilityMeasure nu :=
    standardComplexGaussianRectangularMeasure_isProbability K N
  have hllrInt : Integrable (llr mu nu) mu := by
    exact integrable_llr_jiangSqrtScaledTallHaarCornerLaw_of_energy_integrable
      hN hK hNK hs henergy
  let F : Matrix (Fin K) (Fin N) Complex → Real := fun Z ↦
    jiangScaledBlockLogNormalizer M N K +
      (((K : Real) + N) / M) *
        (Matrix.trace (Z.conjTranspose * Z)).re -
      (((M : Real) - K - N) / (2 * (M : Real) ^ 2)) *
        jiangScaledTallGramSecondEnergy Z
  have hconst : Integrable
      (fun _Z : Matrix (Fin K) (Fin N) Complex ↦
        jiangScaledBlockLogNormalizer M N K) mu :=
    integrable_const _
  have henergyScaled := henergy.const_mul (((K : Real) + N) / M)
  have hsecondScaled := hsecond.const_mul
    (((M : Real) - K - N) / (2 * (M : Real) ^ 2))
  have hFint : Integrable F mu := by
    exact (hconst.add henergyScaled).sub hsecondScaled
  have hrawPoint : ∀ᵐ Z ∂mu,
      jiangScaledTallLogLikelihood M Z ≤ F Z := by
    dsimp only [mu]
    rw [jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs]
    refine (ae_withDensity_iff
      ((measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N).ennreal_ofReal)).2 ?_
    filter_upwards with Z
    intro hf
    exact jiangScaledTallLogLikelihood_le_secondOrder_of_ne_zero
      hN hK hs Z (ENNReal.ofReal_ne_zero_iff.mp hf).ne'
  have hllrEq : llr mu nu =ᵐ[mu] jiangScaledTallLogLikelihood M := by
    exact llr_jiangSqrtScaledTallHaarCornerLaw_eq_explicit_proved_strict
      hN hK hNK hs
  have hpoint : llr mu nu ≤ᵐ[mu] F := by
    filter_upwards [hllrEq, hrawPoint] with Z hZ hle
    rw [hZ]
    exact hle
  have hintegral := integral_mono_ae hllrInt hFint hpoint
  have hFintegral : (∫ Z, F Z ∂mu) =
      jiangScaledBlockLogNormalizer M N K +
        (((K : Real) + N) / M) * ((K : Real) * N) -
        (((M : Real) - K - N) / (2 * (M : Real) ^ 2)) * E := by
    dsimp only [F]
    rw [integral_sub
        (f := fun Z : Matrix (Fin K) (Fin N) Complex ↦
          jiangScaledBlockLogNormalizer M N K +
            (((K : Real) + N) / M) *
              (Matrix.trace (Z.conjTranspose * Z)).re)
        (g := fun Z : Matrix (Fin K) (Fin N) Complex ↦
          (((M : Real) - K - N) / (2 * (M : Real) ^ 2)) *
            jiangScaledTallGramSecondEnergy Z)
        (hconst.add henergyScaled) hsecondScaled,
      integral_add
        (f := fun _Z : Matrix (Fin K) (Fin N) Complex ↦
          jiangScaledBlockLogNormalizer M N K)
        (g := fun Z : Matrix (Fin K) (Fin N) Complex ↦
          (((K : Real) + N) / M) *
            (Matrix.trace (Z.conjTranspose * Z)).re)
        hconst henergyScaled,
      integral_const,
      integral_const_mul, integral_const_mul, henergyMean, hsecondMean]
    simp only [measureReal_def, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one, one_smul]
  rw [hFintegral] at hintegral
  have hM : (0 : Real) < M := by exact_mod_cast hMnat
  have hMne : (M : Real) ≠ 0 := hM.ne'
  have hsCast : (K : Real) + N ≤ M := by exact_mod_cast hs.le
  have hlogR := jiangScaledBlockLogNormalizer_le_firstOrder_raw
    hN hK hs.le
  have hcancel := expected_logLikelihood_cancellation_h19
    (M := (M : Real)) (d := (K : Real) * N)
    (s := (K : Real) + N)
    (E := E) (logR := jiangScaledBlockLogNormalizer M N K)
    hM (by positivity) (by positivity) hsCast hlogR hsecondLower
  have heq :
      jiangScaledBlockLogNormalizer M N K +
          (((K : Real) + N) / M) * ((K : Real) * N) -
          (((M : Real) - K - N) / (2 * (M : Real) ^ 2)) * E =
        jiangScaledBlockLogNormalizer M N K +
          ((M : Real) - ((K : Real) + N)) *
            (-((K : Real) * N) / M - E / (2 * (M : Real) ^ 2)) +
          ((K : Real) * N) := by
    field_simp [hMne]
    ring
  rw [heq] at hintegral
  exact hintegral.trans hcancel

theorem toReal_klDiv_jiangTall_le_three_quarters_of_moments
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) (E : Real)
    (henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (henergyMean :
      (∫ Z : Matrix (Fin K) (Fin N) Complex,
        (Matrix.trace (Z.conjTranspose * Z)).re
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        (K : Real) * N)
    (hsecond : Integrable jiangScaledTallGramSecondEnergy
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (hsecondMean :
      (∫ Z, jiangScaledTallGramSecondEnergy Z
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) = E)
    (hsecondLower :
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤ E) :
    (InformationTheory.klDiv
      (jiangSqrtScaledTallHaarCornerLaw M K N)
      (standardGaussianBlockLaw K N)).toReal ≤
      3 * ((K : Real) * N) * ((K : Real) + N) ^ 2 /
        (4 * (M : Real) ^ 2) := by
  let mu := jiangSqrtScaledTallHaarCornerLaw M K N
  let nu := standardGaussianBlockLaw K N
  have hMnat : 0 < M := by omega
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  letI : IsProbabilityMeasure mu :=
    jiangSqrtScaledTallHaarCornerLaw_isProbability hMnat hKM hNM
  letI : IsProbabilityMeasure nu :=
    standardComplexGaussianRectangularMeasure_isProbability K N
  have hac : mu ≪ nu :=
    jiangSqrtScaledTallHaarCornerLaw_absolutelyContinuous_gaussian_proved_strict
      hN hK hNK hs
  have hllrInt : Integrable (llr mu nu) mu :=
    integrable_llr_jiangSqrtScaledTallHaarCornerLaw_of_energy_integrable
      hN hK hNK hs henergy
  have hrepr := InformationTheory.toReal_klDiv hac hllrInt
  simp only [measureReal_def, IsProbabilityMeasure.measure_univ,
    ENNReal.toReal_one, add_sub_cancel_right] at hrepr
  rw [hrepr]
  exact integral_llr_jiangTall_le_three_quarters_of_moments
    hN hK hNK hs E henergy henergyMean hsecond hsecondMean hsecondLower

theorem jiangTall_probabilityTotalVariationLE_raw_of_moments
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) (E : Real)
    (henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (henergyMean :
      (∫ Z : Matrix (Fin K) (Fin N) Complex,
        (Matrix.trace (Z.conjTranspose * Z)).re
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        (K : Real) * N)
    (hsecond : Integrable jiangScaledTallGramSecondEnergy
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (hsecondMean :
      (∫ Z, jiangScaledTallGramSecondEnergy Z
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) = E)
    (hsecondLower :
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤ E) :
    probabilityTotalVariationLE
      (jiangSqrtScaledTallHaarCornerLaw M K N)
      (standardGaussianBlockLaw K N)
      (((K : Real) + N) * Real.sqrt ((K : Real) * N) / M) := by
  let mu := jiangSqrtScaledTallHaarCornerLaw M K N
  let nu := standardGaussianBlockLaw K N
  have hMnat : 0 < M := by omega
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  letI : IsProbabilityMeasure mu :=
    jiangSqrtScaledTallHaarCornerLaw_isProbability hMnat hKM hNM
  letI : IsProbabilityMeasure nu :=
    standardComplexGaussianRectangularMeasure_isProbability K N
  have hac : mu ≪ nu :=
    jiangSqrtScaledTallHaarCornerLaw_absolutelyContinuous_gaussian_proved_strict
      hN hK hNK hs
  have hllrInt : Integrable (llr mu nu) mu :=
    integrable_llr_jiangSqrtScaledTallHaarCornerLaw_of_energy_integrable
      hN hK hNK hs henergy
  have hpinsker := eventwisePinskerKLLowerBound_of_integrable
    mu nu hac hllrInt
  have hKL := toReal_klDiv_jiangTall_le_three_quarters_of_moments
    hN hK hNK hs E henergy henergyMean hsecond hsecondMean hsecondLower
  have hM : (0 : Real) < M := by exact_mod_cast hMnat
  have hKLcoarse :
      (InformationTheory.klDiv mu nu).toReal ≤
        (K : Real) * N * (2 * ((K : Real) + N)) ^ 2 /
          (2 * (M : Real) ^ 2) := by
    have hd : 0 ≤ (K : Real) * N := by positivity
    have hs0 : 0 ≤ (K : Real) + N := by positivity
    calc
      (InformationTheory.klDiv mu nu).toReal ≤
          3 * ((K : Real) * N) * ((K : Real) + N) ^ 2 /
            (4 * (M : Real) ^ 2) := hKL
      _ ≤ (K : Real) * N * (2 * ((K : Real) + N)) ^ 2 /
            (2 * (M : Real) ^ 2) := by
        have hden : 0 < (M : Real) ^ 2 := sq_pos_of_pos hM
        field_simp [hM.ne']
        nlinarith [mul_nonneg hd (sq_nonneg ((K : Real) + N))]
  intro event hevent
  have hrate := pinsker_finite_sparse_rate
    (tv := |mu.real event - nu.real event|)
    (divergence := (InformationTheory.klDiv mu nu).toReal)
    (p := (K : Real)) (q := (N : Real))
    (s := 2 * ((K : Real) + N)) (M := (M : Real))
    (abs_nonneg _) (Nat.cast_nonneg K) (Nat.cast_nonneg N)
    (by positivity) hM (hpinsker event hevent) hKLcoarse
  dsimp only [mu, nu] at hrate ⊢
  convert hrate using 1 <;> ring

/-- Canonical wide block bound obtained by conjugate-transpose transport. -/
theorem canonicalHaarBlock_probabilityTotalVariationLE_raw_of_moments
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) (E : Real)
    (henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (henergyMean :
      (∫ Z : Matrix (Fin K) (Fin N) Complex,
        (Matrix.trace (Z.conjTranspose * Z)).re
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        (K : Real) * N)
    (hsecond : Integrable jiangScaledTallGramSecondEnergy
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (hsecondMean :
      (∫ Z, jiangScaledTallGramSecondEnergy Z
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) = E)
    (hsecondLower :
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤ E) :
    probabilityTotalVariationLE
      (sqrtScaledHaarBlockLaw
        canonicalUnitaryHaarProbabilityFamily M N K)
      (standardGaussianBlockLaw N K)
      (((K : Real) + N) * Real.sqrt ((K : Real) * N) / M) := by
  have htall := jiangTall_probabilityTotalVariationLE_raw_of_moments
    hN hK hNK hs E henergy henergyMean hsecond hsecondMean hsecondLower
  have hmap := probabilityTotalVariationLE_map
    (rectangularConjTransposeMeasurableEquiv K N)
    (rectangularConjTransposeMeasurableEquiv K N).measurable htall
  rw [map_rectangularConjTranspose_jiangSqrtScaledTallHaarCornerLaw
      hNK hs.le,
    map_rectangularConjTranspose_standardGaussianBlockLaw_H19 K N] at hmap
  exact hmap

/-- Transpose-Gram data processing, still parameterized only by the two
internally checkable Haar moments. -/
theorem transposeGram_probabilityTotalVariationLE_raw_of_moments
    (H : UnitaryHaarProbabilityFamily)
    {M K N : Nat} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (hs : K + N < M) (E : Real)
    (henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (henergyMean :
      (∫ Z : Matrix (Fin K) (Fin N) Complex,
        (Matrix.trace (Z.conjTranspose * Z)).re
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        (K : Real) * N)
    (hsecond : Integrable jiangScaledTallGramSecondEnergy
      (jiangSqrtScaledTallHaarCornerLaw M K N))
    (hsecondMean :
      (∫ Z, jiangScaledTallGramSecondEnergy Z
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) = E)
    (hsecondLower :
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤ E) :
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (((K : Real) + N) * Real.sqrt ((K : Real) * N) / M) := by
  have hblock := canonicalHaarBlock_probabilityTotalVariationLE_raw_of_moments
    hN hK hNK hs E henergy henergyMean hsecond hsecondMean hsecondLower
  rw [← sqrtScaledHaarBlockLaw_eq_canonical H M N K] at hblock
  have hmap := probabilityTotalVariationLE_map
    (rectangularTransposeGram :
      Matrix (Fin N) (Fin K) Complex → Matrix (Fin N) (Fin N) Complex)
    (measurable_rectangularTransposeGram N K) hblock
  have hNM : N ≤ M := by omega
  have hKM : K ≤ M := by omega
  rw [map_rectangularTransposeGram_sqrtScaledHaarBlockLaw H hNM hKM,
    map_rectangularTransposeGram_standardGaussianBlockLaw N K] at hmap
  exact hmap

/-- The quantitative H19 input needed by the sparse branch, proved from the
literal Jiang density and internal Haar-coordinate moments. -/
theorem rawDensityTransposeGramQuantitative_proved :
    RawDensityTransposeGramQuantitative := by
  intro H M N K hN hK hNK hs
  let E : Real :=
    (N : Real) * K * M *
        ((M : Real) * ((N : Real) + K) - (N : Real) * K - 1) /
      ((M : Real) ^ 2 - 1)
  have hM2 : 2 ≤ M := by omega
  have henergy : Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace (Z.conjTranspose * Z)).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N) :=
    integrable_jiangSqrtScaledTallHaarCorner_energy hNK hs.le
  have henergyMean :
      (∫ Z : Matrix (Fin K) (Fin N) Complex,
        (Matrix.trace (Z.conjTranspose * Z)).re
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) =
        (K : Real) * N := by
    rw [integral_jiangSqrtScaledTallHaarCorner_energy hN hNK hs.le]
    ring
  have hsecond : Integrable jiangScaledTallGramSecondEnergy
      (jiangSqrtScaledTallHaarCornerLaw M K N) := by
    change Integrable
      (fun Z : Matrix (Fin K) (Fin N) Complex ↦
        (Matrix.trace ((Z.conjTranspose * Z) *
          (Z.conjTranspose * Z))).re)
      (jiangSqrtScaledTallHaarCornerLaw M K N)
    exact integrable_jiangSqrtScaledTallHaarCorner_gramSecondEnergy
      hNK hs.le
  have hsecondMean :
      (∫ Z, jiangScaledTallGramSecondEnergy Z
          ∂(jiangSqrtScaledTallHaarCornerLaw M K N)) = E := by
    simpa only [jiangScaledTallGramSecondEnergy, E] using
      (integral_jiangSqrtScaledTallHaarCorner_gramSecondEnergy
        hM2 hN hNK hs.le)
  have hMpos : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  have hMone : (1 : Real) < M := by exact_mod_cast (show 1 < M by omega)
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hKreal : (1 : Real) ≤ K := by exact_mod_cast hK
  have hsRealKN : (K : Real) + N ≤ M := by exact_mod_cast hs.le
  have hsReal : (N : Real) + K ≤ M := by linarith
  have hsecondLower :
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤ E := by
    have h := haar_gram_second_moment_coarse_lower_h19
      (M := (M : Real)) (N := (N : Real)) (K := (K : Real))
      hMpos hMone hNreal hKreal hsReal
    simpa only [E] using (show
      (K : Real) * N *
          (((K : Real) + N) - ((K : Real) + N) ^ 2 / (2 * M)) ≤
        (N : Real) * K * M *
            ((M : Real) * ((N : Real) + K) - (N : Real) * K - 1) /
          ((M : Real) ^ 2 - 1) by
      convert h using 1 <;> ring)
  have htv := transposeGram_probabilityTotalVariationLE_raw_of_moments
    H hN hK hNK hs E henergy henergyMean hsecond hsecondMean hsecondLower
  exact ⟨by positivity, htv⟩

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
