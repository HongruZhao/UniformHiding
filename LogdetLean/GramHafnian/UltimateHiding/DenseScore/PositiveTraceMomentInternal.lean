import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLikelihoodLowBellCalculus
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreOneDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9MomentRewire
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10MomentRewire
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentEndpointA4
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open Matrix Unitary
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration
open MeasureTheory

private theorem sum_sq_le_sum_sq_of_nonneg
    {n : Type*} [Fintype n] (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ (∑ i, x i) ^ 2 := by
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ hx i

private theorem sum_cube_le_sum_cube_of_nonneg
    {n : Type*} [Fintype n] (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 3 ≤ (∑ i, x i) ^ 3 := by
  have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ ↦ hx i
  calc
    ∑ i, x i ^ 3 ≤ ∑ i, x i ^ 2 * (∑ j, x j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hxi : x i ≤ ∑ j, x j := Finset.single_le_sum
        (fun j _ ↦ hx j) (Finset.mem_univ i)
      exact mul_le_mul_of_nonneg_left hxi (sq_nonneg (x i))
    _ = (∑ i, x i ^ 2) * (∑ j, x j) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, x i) ^ 2 * (∑ j, x j) :=
      mul_le_mul_of_nonneg_right (sum_sq_le_sum_sq_of_nonneg x hx) hsum
    _ = (∑ i, x i) ^ 3 := by ring

theorem posSemidef_trace_square_re_le_trace_re_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (Matrix.trace (A ^ 2)).re ≤ (Matrix.trace A).re ^ 2 := by
  let hH : A.IsHermitian := hA.isHermitian
  have hspectral := hH.spectral_theorem
  have htrace : Matrix.trace A = ∑ i, (hH.eigenvalues i : ℂ) :=
    hH.trace_eq_sum_eigenvalues
  have htrace2 : Matrix.trace (A ^ 2) =
      ∑ i, ((hH.eigenvalues i : ℂ) ^ 2) := by
    conv_lhs => rw [hspectral]
    rw [← map_pow]
    rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, htrace2]
  rw [Complex.re_sum, Complex.re_sum]
  norm_cast
  exact sum_sq_le_sum_sq_of_nonneg _ hA.eigenvalues_nonneg

theorem posSemidef_trace_cube_re_le_trace_re_cube
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (Matrix.trace (A ^ 3)).re ≤ (Matrix.trace A).re ^ 3 := by
  let hH : A.IsHermitian := hA.isHermitian
  have hspectral := hH.spectral_theorem
  have htrace : Matrix.trace A = ∑ i, (hH.eigenvalues i : ℂ) :=
    hH.trace_eq_sum_eigenvalues
  have htrace3 : Matrix.trace (A ^ 3) =
      ∑ i, ((hH.eigenvalues i : ℂ) ^ 3) := by
    conv_lhs => rw [hspectral]
    rw [← map_pow]
    rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, htrace3]
  rw [Complex.re_sum, Complex.re_sum]
  norm_cast
  exact sum_cube_le_sum_cube_of_nonneg _ hA.eigenvalues_nonneg

theorem concreteCOEY_posSemidef_of_support
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (concreteCOEY N K A).PosSemidef := by
  let C := unscaleCOECorner K A
  have hH : (1 - C.conjTranspose * C).PosDef := by
    simpa only [coeCornerSupport, C] using hsupport
  have hZ : (C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose).PosSemidef :=
    hH.inv.posSemidef.mul_mul_conjTranspose_same C
  have hc : 0 ≤ concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have hgapR : (2 : ℝ) * (N : ℝ) + 8 ≤ (K : ℝ) := by
      exact_mod_cast hgap
    linarith
  unfold concreteCOEY concreteCOEZ
  dsimp only
  have hscaled := hZ.smul hc
  have hsmul : (concreteCOEExponent N K : ℝ) •
      (C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose) =
      ((concreteCOEExponent N K : ℝ) : ℂ) •
        (C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose) :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [hsmul] at hscaled
  simpa only [C] using hscaled

theorem concreteCOETraceTwo_nonneg_of_support
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    0 ≤ concreteCOETraceTwo N K A := by
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have htr := (hY.pow 2).trace_nonneg
  change 0 ≤ (Matrix.trace
    (concreteCOEY N K A * concreteCOEY N K A)).re
  simpa only [pow_two] using (Complex.nonneg_iff.mp htr).1

theorem concreteCOETraceTwo_le_traceOne_sq_of_support
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOETraceTwo N K A ≤ concreteCOETraceOne N K A ^ 2 := by
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  change (Matrix.trace
      (concreteCOEY N K A * concreteCOEY N K A)).re ≤
    (Matrix.trace (concreteCOEY N K A)).re ^ 2
  simpa only [pow_two] using posSemidef_trace_square_re_le_trace_re_sq
      (concreteCOEY N K A) hY

theorem concreteCOETraceThree_nonneg_of_support
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    0 ≤ concreteCOETraceThree N K A := by
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have htr := (hY.pow 3).trace_nonneg
  change 0 ≤ (Matrix.trace
    (concreteCOEY N K A * concreteCOEY N K A * concreteCOEY N K A)).re
  simpa only [pow_succ, pow_two, pow_zero, one_mul] using
    (Complex.nonneg_iff.mp htr).1

theorem concreteCOETraceThree_le_traceOne_cube_of_support
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOETraceThree N K A ≤ concreteCOETraceOne N K A ^ 3 := by
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  change (Matrix.trace
      (concreteCOEY N K A * concreteCOEY N K A * concreteCOEY N K A)).re ≤
    (Matrix.trace (concreteCOEY N K A)).re ^ 3
  simpa only [pow_succ, pow_two, pow_zero, one_mul] using
    posSemidef_trace_cube_re_le_trace_re_cube
      (concreteCOEY N K A) hY

private theorem map_concrete_trace_four_eq_beta_prime
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (concreteCOETracePowerVector 4 N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      betaPrimeTraceFourLaw N K := by
  simpa only [betaPrimeTraceFourLaw] using
    (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
      (r := 4) hN h2NK)

private theorem betaPrimeYTraceOne_comp_concrete_trace_four
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceOne N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceOne N K A := by
  unfold betaPrimeYTraceOne concreteCOETracePowerVector concreteCOETraceOne
    concreteCOEY concreteRealTrace
  simp [pow_succ, Complex.mul_re]

private theorem betaPrimeYTraceTwo_comp_concrete_trace_four
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceTwo N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceTwo N K A := by
  unfold betaPrimeYTraceTwo concreteCOETracePowerVector concreteCOETraceTwo
    concreteCOEY concreteRealTrace
  simp [pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, Complex.mul_re]

private theorem betaPrimeYTraceThree_comp_concrete_trace_four
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceThree N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceThree N K A := by
  unfold betaPrimeYTraceThree concreteCOETracePowerVector concreteCOETraceThree
    concreteCOEY concreteRealTrace
  simp [pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, Complex.mul_re]
  left
  ring

theorem betaPrimeYTraceTwo_nonneg_le_traceOne_sq_ae_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    ∀ᵐ u ∂(betaPrimeTraceFourLaw N K),
      0 ≤ betaPrimeYTraceTwo N K u ∧
        betaPrimeYTraceTwo N K u ≤ betaPrimeYTraceOne N K u ^ 2 := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  have hf : AEMeasurable f mu :=
    (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable
  have hOne : Measurable (betaPrimeYTraceOne N K) := by
    unfold betaPrimeYTraceOne
    fun_prop
  have hTwo : Measurable (betaPrimeYTraceTwo N K) := by
    unfold betaPrimeYTraceTwo
    fun_prop
  have hp : MeasurableSet {u : Fin 4 → ℝ |
      0 ≤ betaPrimeYTraceTwo N K u ∧
        betaPrimeYTraceTwo N K u ≤ betaPrimeYTraceOne N K u ^ 2} := by
    exact (measurableSet_le measurable_const hTwo).inter
      (measurableSet_le hTwo (hOne.pow_const 2))
  rw [← map_concrete_trace_four_eq_beta_prime hN (by omega)]
  apply (ae_map_iff hf hp).2
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hsupport
  rcases hsupport with ⟨_, hball⟩
  rw [betaPrimeYTraceOne_comp_concrete_trace_four,
    betaPrimeYTraceTwo_comp_concrete_trace_four]
  exact ⟨concreteCOETraceTwo_nonneg_of_support hgap A hball,
    concreteCOETraceTwo_le_traceOne_sq_of_support hgap A hball⟩

theorem betaPrimeYTraceThree_nonneg_le_traceOne_cube_ae_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    ∀ᵐ u ∂(betaPrimeTraceFourLaw N K),
      0 ≤ betaPrimeYTraceThree N K u ∧
        betaPrimeYTraceThree N K u ≤ betaPrimeYTraceOne N K u ^ 3 := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  have hf : AEMeasurable f mu :=
    (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable
  have hOne : Measurable (betaPrimeYTraceOne N K) := by
    unfold betaPrimeYTraceOne
    fun_prop
  have hThree : Measurable (betaPrimeYTraceThree N K) := by
    unfold betaPrimeYTraceThree
    fun_prop
  have hp : MeasurableSet {u : Fin 4 → ℝ |
      0 ≤ betaPrimeYTraceThree N K u ∧
        betaPrimeYTraceThree N K u ≤ betaPrimeYTraceOne N K u ^ 3} := by
    exact (measurableSet_le measurable_const hThree).inter
      (measurableSet_le hThree (hOne.pow_const 3))
  rw [← map_concrete_trace_four_eq_beta_prime hN (by omega)]
  apply (ae_map_iff hf hp).2
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hsupport
  rcases hsupport with ⟨_, hball⟩
  rw [betaPrimeYTraceOne_comp_concrete_trace_four,
    betaPrimeYTraceThree_comp_concrete_trace_four]
  exact ⟨concreteCOETraceThree_nonneg_of_support hgap A hball,
    concreteCOETraceThree_le_traceOne_cube_of_support hgap A hball⟩

/-- The raw first trace is in `L³`, by adding its finite mean back to the
retained centered `L³` input. -/
theorem betaPrimeYTraceOne_memLp_three_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceOne N K) 3 (betaPrimeTraceFourLaw N K) := by
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceOne N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceOne N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 3 mu := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceOne_centered_memLp_three_proved_allDimensions hN hgap
  rw [show betaPrimeYTraceOne N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  exact hcentered.add (memLp_const mean)

/-- Finiteness of the raw second trace is not a separate random-matrix
input: positivity gives `Tr Y² ≤ (Tr Y)²` almost surely. -/
theorem betaPrimeYTraceTwo_memLp_one_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceTwo N K) 1 (betaPrimeTraceFourLaw N K) := by
  have hsq := betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions hN hgap
  have hmeas : AEStronglyMeasurable (betaPrimeYTraceTwo N K)
      (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    unfold betaPrimeYTraceTwo
    fun_prop
  apply hsq.mono hmeas
  filter_upwards [betaPrimeYTraceTwo_nonneg_le_traceOne_sq_ae_internal hN hgap]
    with u hu
  calc
    ‖betaPrimeYTraceTwo N K u‖ = betaPrimeYTraceTwo N K u := by
      rw [Real.norm_eq_abs, abs_of_nonneg hu.1]
    _ ≤ betaPrimeYTraceOne N K u ^ 2 := hu.2
    _ = ‖betaPrimeYTraceOne N K u ^ 2‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- Finiteness of the raw third trace likewise follows from
`Tr Y³ ≤ (Tr Y)³` and the retained centered first-trace `L³` package. -/
theorem betaPrimeYTraceThree_memLp_one_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceThree N K) 1 (betaPrimeTraceFourLaw N K) := by
  have hone := betaPrimeYTraceOne_memLp_three_internal hN hgap
  have hcube := hone.norm_rpow_div (3 : ENNReal)
  have hdiv : (3 : ENNReal) / 3 = 1 :=
    ENNReal.div_self (by norm_num) (by norm_num)
  rw [hdiv] at hcube
  have hmeas : AEStronglyMeasurable (betaPrimeYTraceThree N K)
      (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    unfold betaPrimeYTraceThree
    fun_prop
  apply hcube.mono hmeas
  filter_upwards [betaPrimeYTraceThree_nonneg_le_traceOne_cube_ae_internal hN hgap]
    with u hu
  rw [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  calc
    ‖betaPrimeYTraceThree N K u‖ = betaPrimeYTraceThree N K u := by
      rw [Real.norm_eq_abs, abs_of_nonneg hu.1]
    _ ≤ betaPrimeYTraceOne N K u ^ 3 := hu.2
    _ ≤ |betaPrimeYTraceOne N K u ^ 3| := le_abs_self _
    _ = ‖‖betaPrimeYTraceOne N K u‖ ^ 3‖ := by
      rw [abs_pow]
      simp only [Real.norm_eq_abs]
      exact (abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)).symm

private theorem concreteCenteredEll_one_eq_centeredTracePair_re
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 1 N K (A, v) =
      2 * (complexCenteredProjectiveTracePair v
        (concreteCOEY N K A)).re := by
  unfold concreteCenteredEll
  rw [← coeCorner_centeredDensityScore_one_eq_logScore hN v A hsupport]
  rw [coeCorner_centeredDensityScore_one_eq_explicit_external_derived
    hN hgap v A hsymm hsupport]
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
  simp [Complex.mul_re]

private theorem complexCenteredProjectiveTracePair_im_zero_on_support
    {N K : ℕ} (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (complexCenteredProjectiveTracePair v (concreteCOEY N K A)).im = 0 := by
  have hY := concreteCOEY_isHermitian_of_support A hsupport
  have hP : (complexRankOneProjection v).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [Matrix.conjTranspose_apply, complexRankOneProjection]
    ring
  have hpair :
      (complexProjectiveTracePair v (concreteCOEY N K A)).im = 0 := by
    rw [complexProjectiveTracePair_eq_trace]
    apply Complex.conj_eq_iff_im.mp
    calc
      star (Matrix.trace
          (complexRankOneProjection v * concreteCOEY N K A)) =
          Matrix.trace
            ((complexRankOneProjection v * concreteCOEY N K A).conjTranspose) := by
        rw [Matrix.trace_conjTranspose]
      _ = Matrix.trace (concreteCOEY N K A * complexRankOneProjection v) := by
        rw [Matrix.conjTranspose_mul, hY, hP]
      _ = Matrix.trace (complexRankOneProjection v * concreteCOEY N K A) :=
        Matrix.trace_mul_comm _ _
  have htrace := concreteCOEY_trace_im_eq_zero_of_support A hsupport
  unfold complexCenteredProjectiveTracePair
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, hpair, htrace, sub_zero]
  ring

theorem integral_concreteCenteredEll_one_sq_eq_trace_variance
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N, concreteCenteredEll 1 N K (A, v) ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) =
      4 * ((N : ℝ) * ((N : ℝ) + 1))⁻¹ *
        (concreteCOETraceTwo N K A -
          (N : ℝ)⁻¹ * concreteCOETraceOne N K A ^ 2) := by
  let Y := concreteCOEY N K A
  let s : ComplexUnitSphere N → ℂ :=
    fun v ↦ complexCenteredProjectiveTracePair v Y
  have hsint : Integrable (fun v ↦ s v * s v)
      (complexUnitSphereProbabilityMeasure N) := by
    simpa only [s, Y] using
      integrable_complexCenteredProjectiveTracePair_mul hN Y Y
  have hfourInt : Integrable (fun v ↦ (4 : ℂ) * (s v * s v))
      (complexUnitSphereProbabilityMeasure N) := hsint.const_mul 4
  have hYone := concreteCOEY_trace_im_eq_zero_of_support A hsupport
  have hYtwo := concreteCOEY_sq_trace_im_eq_zero_of_support A hsupport
  calc
    (∫ v : ComplexUnitSphere N, concreteCenteredEll 1 N K (A, v) ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∫ v : ComplexUnitSphere N, ((4 : ℂ) * (s v * s v)).re
          ∂(complexUnitSphereProbabilityMeasure N) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [concreteCenteredEll_one_eq_centeredTracePair_re
        hN hgap A v hsymm hsupport]
      have hsim : (s v).im = 0 := by
        simpa only [s, Y] using
          complexCenteredProjectiveTracePair_im_zero_on_support A v hsupport
      change (2 * (s v).re) ^ 2 = ((4 : ℂ) * (s v * s v)).re
      norm_num [Complex.mul_re, hsim]
      ring
    _ = (∫ v : ComplexUnitSphere N, (4 : ℂ) * (s v * s v)
          ∂(complexUnitSphereProbabilityMeasure N)).re := by
      change (∫ v : ComplexUnitSphere N,
          RCLike.re ((4 : ℂ) * (s v * s v))
            ∂(complexUnitSphereProbabilityMeasure N)) =
        RCLike.re (∫ v : ComplexUnitSphere N, (4 : ℂ) * (s v * s v)
          ∂(complexUnitSphereProbabilityMeasure N))
      exact integral_re hfourInt
    _ = _ := by
      rw [integral_const_mul]
      rw [show (∫ v : ComplexUnitSphere N, s v * s v
          ∂(complexUnitSphereProbabilityMeasure N)) =
          ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
            (Matrix.trace (Y * Y) -
              (((N : ℝ)⁻¹ : ℝ) : ℂ) *
                Matrix.trace Y * Matrix.trace Y) by
        simpa only [s] using
          integral_complexCenteredProjectiveTracePair_mul hN Y Y]
      dsimp only [Y]
      have hYone' : (Matrix.trace Y).im = 0 := by simpa only [Y] using hYone
      have hYtwo' : (Matrix.trace (Y * Y)).im = 0 := by
        simpa only [Y] using hYtwo
      have h4re : (4 : ℂ).re = 4 := by norm_num
      have h4im : (4 : ℂ).im = 0 := by norm_num
      have hEq :
          (4 : ℂ) *
              (((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
                (Matrix.trace (Y * Y) -
                  (((N : ℝ)⁻¹ : ℝ) : ℂ) *
                    Matrix.trace Y * Matrix.trace Y)) =
            ((4 * ((N : ℝ) * ((N : ℝ) + 1))⁻¹ *
              (concreteCOETraceTwo N K A -
                (N : ℝ)⁻¹ * concreteCOETraceOne N K A ^ 2) : ℝ) : ℂ) := by
        apply Complex.ext
        · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
            Complex.ofReal_im, hYone', hYtwo', h4re, h4im, zero_mul,
            mul_zero, sub_zero]
          dsimp only [Y]
          rw [show (Matrix.trace
              (concreteCOEY N K A * concreteCOEY N K A)).re =
                concreteCOETraceTwo N K A by rfl]
          rw [show (Matrix.trace (concreteCOEY N K A)).re =
                concreteCOETraceOne N K A by rfl]
          ring
        · simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
            Complex.ofReal_im, hYone', hYtwo', h4re, h4im, zero_mul,
            mul_zero, add_zero, sub_zero]
      rw [hEq]
      exact Complex.ofReal_re _

private theorem concreteCenteredScoreProductLaw_isProbability_internal
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    IsProbabilityMeasure (concreteCenteredScoreProductLaw N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure mu := by
    letI : IsProbabilityMeasure
        (scaledHaarTransposeGramLaw
          canonicalUnitaryHaarProbabilityFamily K N K) :=
      scaledHaarTransposeGramLaw_isProbability _ hNK le_rfl
    unfold mu concreteScaledCOECornerLaw concreteHaarAmbientLaw
      normalizedHaarTransposeGramLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold concreteCenteredScoreProductLaw
  infer_instance

private theorem lpNorm_one_le_two_probability_internal
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {f : Omega → ℝ} (hf : MemLp f 2 mu) :
    lpNorm f 1 mu ≤ lpNorm f 2 mu := by
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le
    (μ := mu) (f := f) (p := (1 : ENNReal)) (q := (2 : ENNReal))
    (by norm_num) hf.aestronglyMeasurable
  have hfOne : MemLp f 1 mu := hf.mono_exponent (by norm_num)
  rw [← toReal_eLpNorm hfOne.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top hmono

private theorem lpNorm_two_sq_eq_lpNorm_sq_one_internal'
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ}
    (hf : MemLp f 2 mu) :
    lpNorm f 2 mu ^ 2 = lpNorm (fun x ↦ f x ^ 2) 1 mu := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num)
      (by norm_num) hf.aestronglyMeasurable]
  rw [lpNorm_one_eq_integral_norm]
  · norm_num
    have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂mu :=
      integral_nonneg fun _ ↦ sq_nonneg _
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  · exact AEStronglyMeasurable.pow hf.aestronglyMeasurable 2

/-- The retained fourth moment of the first centered log score implies the
sharp product-law `L¹` bound for its square. -/
theorem centeredLogScore_oneSquare_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 2) 1
            (concreteCenteredScoreProductLaw N K) ≤
          denseClassicalMomentConstant ^ 2 * (N : ℝ)) := by
  let law := concreteCenteredScoreProductLaw N K
  let ell := concreteCenteredEll 1 N K
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ ell p ^ 2
  have hfour : MemLp (fun p ↦ ell p ^ 4) 1 law := by
    simpa only [ell, law] using
      centeredLogScore_oneFourth_memLp_one_proved_A1A2A3A4 hN hgap
  have hfMeas : AEStronglyMeasurable f law := by
    have hsqrt :=
      hfour.aestronglyMeasurable.aemeasurable.sqrt.aestronglyMeasurable
    have heq : (fun p ↦ Real.sqrt (ell p ^ 4)) = f := by
      funext p
      rw [show ell p ^ 4 = (ell p ^ 2) ^ 2 by ring,
        Real.sqrt_sq (sq_nonneg _)]
    exact hsqrt.congr (Filter.Eventually.of_forall fun p ↦ congrFun heq p)
  have hfTwo : MemLp f 2 law := by
    apply (memLp_two_iff_integrable_sq hfMeas).2
    have hfun : (fun p ↦ f p ^ 2) = fun p ↦ ell p ^ 4 := by
      funext p
      simp only [f]
      ring
    rw [hfun]
    exact memLp_one_iff_integrable.mp hfour
  letI : IsProbabilityMeasure law :=
    concreteCenteredScoreProductLaw_isProbability_internal hN (by omega)
  constructor
  · simpa only [f, ell, law] using hfTwo.mono_exponent (by norm_num)
  · intro hdense
    have hfourNorm : lpNorm (fun p ↦ ell p ^ 4) 1 law ≤
        centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      simpa only [ell, law] using
        centeredLogScore_oneFourth_lpNorm_one_le_proved_A1A2A3A4 hN hdense
    have hsq := lpNorm_two_sq_eq_lpNorm_sq_one_internal' hfTwo
    have hfun : (fun p ↦ f p ^ 2) = fun p ↦ ell p ^ 4 := by
      funext p
      simp only [f]
      ring
    rw [hfun] at hsq
    have hsquare : lpNorm f 2 law ^ 2 ≤
        (denseClassicalMomentConstant ^ 2 * (N : ℝ)) ^ 2 := by
      rw [hsq]
      calc
        lpNorm (fun p ↦ ell p ^ 4) 1 law ≤
            centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := hfourNorm
        _ = (denseClassicalMomentConstant ^ 2 * (N : ℝ)) ^ 2 := by
          unfold centeredLogScoreFourthMomentConstant
          ring
    have htwo : lpNorm f 2 law ≤
        denseClassicalMomentConstant ^ 2 * (N : ℝ) :=
      (sq_le_sq₀ lpNorm_nonneg (by positivity)).mp hsquare
    exact (lpNorm_one_le_two_probability_internal hfTwo).trans htwo

private theorem memLp_comp_concrete_trace_four_internal
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : MemLp g p (betaPrimeTraceFourLaw N K)) :
    MemLp (g ∘ concreteCOETracePowerVector 4 N K) p
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  apply MemLp.comp_of_map
  · simpa only [map_concrete_trace_four_eq_beta_prime hN h2NK] using hg
  · exact (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable

private theorem lpNorm_comp_concrete_trace_four_internal
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K)) :
    lpNorm (g ∘ concreteCOETracePowerVector 4 N K) p
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      lpNorm g p (betaPrimeTraceFourLaw N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  have hmap : Measure.map f mu = betaPrimeTraceFourLaw N K := by
    simpa only [mu, f] using map_concrete_trace_four_eq_beta_prime hN h2NK
  have hgf : AEStronglyMeasurable g (Measure.map f mu) := by
    simpa only [hmap] using hg
  have hf : AEMeasurable f mu :=
    (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable
  rw [← hmap, ← toReal_eLpNorm (hgf.comp_aemeasurable hf),
    ← toReal_eLpNorm hgf]
  exact congrArg ENNReal.toReal (eLpNorm_map_measure hgf hf).symm

def concreteCenteredEllOneSquareAverage (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  ∫ v : ComplexUnitSphere N, concreteCenteredEll 1 N K (A, v) ^ 2
    ∂(complexUnitSphereProbabilityMeasure N)

/-- On the COE support, the second trace is the scalar trace-square part plus
the projective variance measured by the averaged first centered score. -/
theorem concreteCOETraceTwo_eq_traceOne_sq_add_scoreAverage
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOETraceTwo N K A =
      (N : ℝ)⁻¹ * concreteCOETraceOne N K A ^ 2 +
        ((N : ℝ) * ((N : ℝ) + 1) / 4) *
          concreteCenteredEllOneSquareAverage N K A := by
  have h := integral_concreteCenteredEll_one_sq_eq_trace_variance
    hN hgap A hsymm hsupport
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  unfold concreteCenteredEllOneSquareAverage
  rw [h]
  field_simp
  ring

/-- Averaging the squared first centered score over the projective direction
does not increase its product-law `L¹` norm. -/
theorem concreteCenteredEllOneSquareAverage_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEllOneSquareAverage N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEllOneSquareAverage N K) 1
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          denseClassicalMomentConstant ^ 2 * (N : ℝ)) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure mu := by
    letI : IsProbabilityMeasure
        (scaledHaarTransposeGramLaw
          canonicalUnitaryHaarProbabilityFamily K N K) :=
      scaledHaarTransposeGramLaw_isProbability _ (by omega) le_rfl
    unfold mu concreteScaledCOECornerLaw concreteHaarAmbientLaw
      normalizedHaarTransposeGramLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  let ellSq : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p ^ 2
  let avg : ConcreteMatrixState N → ℝ :=
    fun A ↦ ∫ v, ellSq (A, v) ∂sphere
  have hellPkg := centeredLogScore_oneSquare_momentPackage_internal hN hgap
  have hellMem : MemLp ellSq 1 (mu.prod sphere) := by
    simpa only [ellSq, mu, sphere, concreteCenteredScoreProductLaw] using
      hellPkg.1
  have hellInt : Integrable ellSq (mu.prod sphere) :=
    memLp_one_iff_integrable.mp hellMem
  have havgInt : Integrable avg mu := by
    simpa only [avg] using hellInt.integral_prod_left
  have havgEq : avg = concreteCenteredEllOneSquareAverage N K := by
    funext A
    rfl
  constructor
  · rw [← havgEq]
    exact memLp_one_iff_integrable.mpr havgInt
  · intro hdense
    have hellNorm : lpNorm ellSq 1 (mu.prod sphere) ≤
        denseClassicalMomentConstant ^ 2 * (N : ℝ) := by
      simpa only [ellSq, mu, sphere, concreteCenteredScoreProductLaw] using
        hellPkg.2 hdense
    rw [← havgEq]
    calc
      lpNorm avg 1 mu = ∫ A, avg A ∂mu := by
        rw [lpNorm_one_eq_integral_norm havgInt.aestronglyMeasurable]
        apply integral_congr_ae
        filter_upwards [] with A
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact integral_nonneg fun v ↦ sq_nonneg _
      _ = ∫ p, ellSq p ∂(mu.prod sphere) := by
        exact (integral_prod ellSq hellInt).symm
      _ = lpNorm ellSq 1 (mu.prod sphere) := by
        rw [lpNorm_one_eq_integral_norm hellMem.aestronglyMeasurable]
        apply integral_congr_ae
        filter_upwards [] with p
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact sq_nonneg _
      _ ≤ denseClassicalMomentConstant ^ 2 * (N : ℝ) := hellNorm

/-- A generous coefficient for the raw second trace recovered from its
scalar trace-square component and the projective score variance. -/
def derivedPositiveRawTraceTwoConstant : ℝ :=
  derivedRawTraceProductConstant + denseClassicalMomentConstant ^ 2

/-- Sharp `O(N³)` raw second-trace package on the concrete COE law, obtained
without the external beta-prime raw second-trace package. -/
theorem concreteCOETraceTwo_momentPackage_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCOETraceTwo N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCOETraceTwo N K) 1
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let q : ConcreteMatrixState N → ℝ :=
    fun A ↦ concreteCOETraceOne N K A ^ 2
  let avg : ConcreteMatrixState N → ℝ :=
    concreteCenteredEllOneSquareAverage N K
  let a : ℝ := (N : ℝ)⁻¹
  let c : ℝ := (N : ℝ) * ((N : ℝ) + 1) / 4
  let rhs : ConcreteMatrixState N → ℝ := a • q + c • avg
  have hqMem : MemLp q 1 mu := by
    have hpull := memLp_comp_concrete_trace_four_internal hN (by omega)
      (betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions hN hgap)
    have hfun :
        ((fun u ↦ betaPrimeYTraceOne N K u ^ 2) ∘ f) = q := by
      funext A
      simp only [f, q, Function.comp_apply]
      rw [betaPrimeYTraceOne_comp_concrete_trace_four]
    rw [← hfun]
    simpa only [mu, f] using hpull
  have havgPkg :=
    concreteCenteredEllOneSquareAverage_momentPackage_internal hN hgap
  have havgMem : MemLp avg 1 mu := by
    simpa only [avg, mu] using havgPkg.1
  have hrhsMem : MemLp rhs 1 mu := by
    exact (hqMem.const_smul a).add (havgMem.const_smul c)
  have heq : concreteCOETraceTwo N K =ᵐ[mu] rhs := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hsupport
    rcases hsupport with ⟨hsymm, hball⟩
    simpa only [rhs, q, avg, a, c, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using
      concreteCOETraceTwo_eq_traceOne_sq_add_scoreAverage
        hN hgap A hsymm hball
  have htMem : MemLp (concreteCOETraceTwo N K) 1 mu :=
    (memLp_congr_ae heq).2 hrhsMem
  constructor
  · simpa only [mu] using htMem
  · intro hdense
    have hqNorm : lpNorm q 1 mu ≤
        derivedRawTraceProductConstant * (N : ℝ) ^ 4 := by
      have htransport := lpNorm_comp_concrete_trace_four_internal
        hN (by omega) (p := (1 : ENNReal))
        (betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions hN hgap).aestronglyMeasurable
      have hfun :
          ((fun u ↦ betaPrimeYTraceOne N K u ^ 2) ∘ f) = q := by
        funext A
        simp only [f, q, Function.comp_apply]
        rw [betaPrimeYTraceOne_comp_concrete_trace_four]
      have hpull : lpNorm q 1 mu =
          lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
            (betaPrimeTraceFourLaw N K) := by
        rw [hfun] at htransport
        simpa only [mu] using htransport
      rw [hpull]
      exact betaPrimeYTraceOneSquare_lpNorm_one_le_proved_allDimensions hN hdense
    have havgNorm : lpNorm avg 1 mu ≤
        denseClassicalMomentConstant ^ 2 * (N : ℝ) := by
      simpa only [avg, mu] using havgPkg.2 hdense
    have hnormEq : lpNorm (concreteCOETraceTwo N K) 1 mu =
        lpNorm rhs 1 mu := by
      rw [← toReal_eLpNorm htMem.aestronglyMeasurable,
        ← toReal_eLpNorm hrhsMem.aestronglyMeasurable,
        eLpNorm_congr_ae heq]
    have htri : lpNorm rhs 1 mu ≤
        lpNorm (a • q) 1 mu + lpNorm (c • avg) 1 mu := by
      exact lpNorm_add_le (hqMem.const_smul a) (p := (1 : ENNReal))
        (by norm_num)
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have ha : 0 ≤ a := by simp [a]
    have hc : 0 ≤ c := by positivity
    have hqScaled : lpNorm (a • q) 1 mu ≤
        derivedRawTraceProductConstant * (N : ℝ) ^ 3 := by
      rw [lpNorm_const_smul]
      simp only [NNReal.smul_def, ha, Real.nnnorm_of_nonneg]
      calc
        a * lpNorm q 1 mu ≤
            a * (derivedRawTraceProductConstant * (N : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left hqNorm ha
        _ = derivedRawTraceProductConstant * (N : ℝ) ^ 3 := by
          simp only [a]
          have hN0 : (N : ℝ) ≠ 0 := by positivity
          field_simp
    have havgScaled : lpNorm (c • avg) 1 mu ≤
        denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 3 := by
      rw [lpNorm_const_smul]
      simp only [NNReal.smul_def, hc, Real.nnnorm_of_nonneg]
      calc
        c * lpNorm avg 1 mu ≤
            c * (denseClassicalMomentConstant ^ 2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left havgNorm hc
        _ ≤ denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 3 := by
          have hD : 0 ≤ denseClassicalMomentConstant ^ 2 := sq_nonneg _
          have hcN : c ≤ (N : ℝ) ^ 2 := by
            dsimp only [c]
            nlinarith
          calc
            c * (denseClassicalMomentConstant ^ 2 * (N : ℝ)) ≤
                (N : ℝ) ^ 2 *
                  (denseClassicalMomentConstant ^ 2 * (N : ℝ)) :=
              mul_le_mul_of_nonneg_right hcN (mul_nonneg hD (by positivity))
            _ = denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 3 := by
              ring
    simpa only [mu] using
      (calc
        lpNorm (concreteCOETraceTwo N K) 1 mu = lpNorm rhs 1 mu := hnormEq
        _ ≤ lpNorm (a • q) 1 mu + lpNorm (c • avg) 1 mu := htri
        _ ≤ derivedRawTraceProductConstant * (N : ℝ) ^ 3 +
            denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 3 :=
          add_le_add hqScaled havgScaled
        _ = derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 := by
          unfold derivedPositiveRawTraceTwoConstant
          ring)

/-- Sharp `O(N³)` raw second-trace package on the literal beta-prime law.
This theorem eliminates the need for
`betaPrimeYTraceTwo_momentPackage_external`, at the price of replacing its
coefficient by the explicit derived coefficient above. -/
theorem betaPrimeYTraceTwo_momentPackage_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceTwo N K) 1 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (betaPrimeYTraceTwo N K) 1 (betaPrimeTraceFourLaw N K) ≤
          derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3) := by
  constructor
  · exact betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  · intro hdense
    have hconcrete :=
      (concreteCOETraceTwo_momentPackage_positive_internal hN hgap).2 hdense
    have htransport := lpNorm_comp_concrete_trace_four_internal
      hN (by omega) (p := (1 : ENNReal))
      (betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap).aestronglyMeasurable
    have hfun :
        betaPrimeYTraceTwo N K ∘ concreteCOETracePowerVector 4 N K =
          concreteCOETraceTwo N K := by
      funext A
      exact betaPrimeYTraceTwo_comp_concrete_trace_four N K A
    rw [hfun] at htransport
    rw [← htransport]
    exact hconcrete

/-- Convenient norm projection of the internally proved raw second-trace
package. -/
theorem betaPrimeYTraceTwo_lpNorm_one_le_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceTwo N K) 1 (betaPrimeTraceFourLaw N K) ≤
      derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 := by
  exact (betaPrimeYTraceTwo_momentPackage_positive_internal hN (by omega)).2 hdense

/-- Coefficient for the raw second trace in `L²`, recovered by adding its
retained centered `L²` part to the internally bounded mean. -/
def derivedPositiveRawTraceTwoL2Constant : ℝ :=
  denseClassicalMomentConstant + derivedPositiveRawTraceTwoConstant

theorem betaPrimeYTraceTwo_memLp_two_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) := by
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceTwo N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceTwo N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceTwo_centered_memLp_two_proved_allDimensions hN hgap
  rw [show betaPrimeYTraceTwo N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  exact hcentered.add (memLp_const mean)

theorem betaPrimeYTraceTwo_lpNorm_two_le_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) ≤
      derivedPositiveRawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceTwo N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceTwo N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceTwo_centered_memLp_two_proved_allDimensions hN hgap
  have hcenteredNorm : lpNorm centered 2 mu ≤
      denseClassicalMomentConstant * (N : ℝ) ^ 2 := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceTwo_centered_lpNorm_two_le_proved_allDimensions hN hdense
  have hrawOne := betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  have hrawOneNorm :=
    (betaPrimeYTraceTwo_momentPackage_positive_internal hN hgap).2 hdense
  have hmeanAbs : |mean| ≤
      derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 := by
    calc
      |mean| ≤ ∫ u, |betaPrimeYTraceTwo N K u| ∂mu := by
        simpa only [mean] using abs_integral_le_integral_abs
      _ = lpNorm (betaPrimeYTraceTwo N K) 1 mu := by
        rw [lpNorm_one_eq_integral_norm hrawOne.aestronglyMeasurable]
        rfl
      _ ≤ derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 := by
        simpa only [mu] using hrawOneNorm
  have htri := lpNorm_add_le hcentered (p := (2 : ENNReal)) (by norm_num)
    (g := fun _ : Fin 4 → ℝ ↦ mean)
  have hconstNorm : lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 2 mu = |mean| := by
    rw [lpNorm_const (p := (2 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero mu) mean]
    simp [Real.norm_eq_abs]
  rw [show betaPrimeYTraceTwo N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  calc
    lpNorm (centered + (fun _ : Fin 4 → ℝ ↦ mean)) 2 mu ≤
        lpNorm centered 2 mu +
          lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 2 mu := htri
    _ = lpNorm centered 2 mu + |mean| := by rw [hconstNorm]
    _ ≤ denseClassicalMomentConstant * (N : ℝ) ^ 2 +
        derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 :=
      add_le_add hcenteredNorm hmeanAbs
    _ ≤ derivedPositiveRawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hD : 0 ≤ denseClassicalMomentConstant := by
        norm_num [denseClassicalMomentConstant]
      have hpow : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
        nlinarith
      calc
        denseClassicalMomentConstant * (N : ℝ) ^ 2 +
            derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 3 +
            derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 :=
          add_le_add (mul_le_mul_of_nonneg_left hpow hD) le_rfl
        _ = derivedPositiveRawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
          unfold derivedPositiveRawTraceTwoL2Constant
          ring

private theorem lpNorm_mul_le_lpNorm_two_mul_positive_internal
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g : Omega → ℝ} (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    lpNorm (fun ω ↦ f ω * g ω) 1 mu ≤
      lpNorm f 2 mu * lpNorm g 2 mu := by
  have hprod : MemLp (fun ω ↦ f ω * g ω) 1 mu := hg.mul' hf
  have he : eLpNorm (fun ω ↦ f ω * g ω) 1 mu ≤
      eLpNorm f 2 mu * eLpNorm g 2 mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      hf.aestronglyMeasurable hg.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with ω
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) he

def derivedPositiveRawTraceOneTwoConstant : ℝ :=
  derivedRawTraceOneConstant * derivedPositiveRawTraceTwoL2Constant

theorem betaPrimeYTraceOneTwo_momentPackage_positive_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u *
          betaPrimeYTraceTwo N K u) 1 (betaPrimeTraceFourLaw N K) ≤
          derivedPositiveRawTraceOneTwoConstant * (N : ℝ) ^ 5) := by
  have hone := betaPrimeYTraceOne_memLp_two_proved_allDimensions hN hgap
  have htwo := betaPrimeYTraceTwo_memLp_two_positive_internal hN hgap
  constructor
  · exact htwo.mul' hone
  · intro hdense
    have honeNorm :=
      betaPrimeYTraceOne_lpNorm_two_le_proved_allDimensions hN hdense
    have htwoNorm :=
      betaPrimeYTraceTwo_lpNorm_two_le_positive_internal hN hdense
    have hOneNonneg :
        0 ≤ derivedRawTraceOneConstant * (N : ℝ) ^ 2 := by
      have : 0 ≤ derivedRawTraceOneConstant := by
        norm_num [derivedRawTraceOneConstant, denseClassicalMomentConstant]
      positivity
    calc
      lpNorm (fun u ↦ betaPrimeYTraceOne N K u *
          betaPrimeYTraceTwo N K u) 1 (betaPrimeTraceFourLaw N K) ≤
        lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) *
          lpNorm (betaPrimeYTraceTwo N K) 2
            (betaPrimeTraceFourLaw N K) :=
        lpNorm_mul_le_lpNorm_two_mul_positive_internal hone htwo
      _ ≤ (derivedRawTraceOneConstant * (N : ℝ) ^ 2) *
          (derivedPositiveRawTraceTwoL2Constant * (N : ℝ) ^ 3) :=
        mul_le_mul honeNorm htwoNorm lpNorm_nonneg hOneNonneg
      _ = derivedPositiveRawTraceOneTwoConstant * (N : ℝ) ^ 5 := by
        unfold derivedPositiveRawTraceOneTwoConstant
        ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
