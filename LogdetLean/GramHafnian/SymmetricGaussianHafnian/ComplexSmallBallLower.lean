import LogdetLean.GramHafnian.SymmetricGaussianHafnian.Constants
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.SecondMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# A genuine lower small-ball bound for the complex symmetric hafnian

The proof uses only the literal independent-edge ensemble. Exposing the last
vertex gives the exact circular-Gaussian linear-form mixture already proved in
`LastVertex`. Markov's inequality and the exact cofactor-energy first moment
put at least half of the background mass below twice its mean. On this event,
the conditional disk contains a fixed disk for one standard circular Gaussian.

No inverse moment, density approximation, or abstract cofactor-law hypothesis
is used. This file is isolated from the public assembly until explicitly
imported there.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- At least half of the odd-background ensemble has cofactor energy below
twice its exact mean. The strict good event makes its complement exactly the
closed Markov tail. -/
theorem half_le_measure_edgeCofactorEnergy_lt_two_mean (n : ℕ) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤
      (edgeGaussian (Fin (2 * n + 1)))
        {x | edgeCofactorEnergy x < 2 * (oddPairingNat (n + 1) : ℝ)} := by
  let μ := edgeGaussian (Fin (2 * n + 1))
  let M : ℝ := oddPairingNat (n + 1)
  let good : Set (Edge (Fin (2 * n + 1)) → ℂ) :=
    {x | edgeCofactorEnergy x < 2 * M}
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast oddPairingNat_pos (n + 1)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall edgeCofactorEnergy_nonneg)
    (integrable_edgeCofactorEnergy_odd n) (2 * M)
  have hmean : (∫ x, edgeCofactorEnergy x ∂μ) = M := by
    simpa [μ, M] using integral_edgeCofactorEnergy_odd n
  rw [hmean] at hmarkov
  have hbad : μ.real {x | 2 * M ≤ edgeCofactorEnergy x} ≤ 1 / 2 := by
    nlinarith
  have hgoodMeas : MeasurableSet good := by
    dsimp [good]
    exact measurableSet_lt measurable_edgeCofactorEnergy measurable_const
  have hcompl : goodᶜ = {x | 2 * M ≤ edgeCofactorEnergy x} := by
    ext x
    simp [good]
  have hgoodReal : 1 / 2 ≤ μ.real good := by
    have hc := probReal_compl_eq_one_sub (μ := μ) hgoodMeas
    rw [hcompl] at hc
    nlinarith
  rw [Measure.real_def] at hgoodReal
  change ENNReal.ofReal (1 / 2 : ℝ) ≤ μ good
  exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top μ good)).mp
    (by simpa using hgoodReal)

/-- A fixed standard circular disk is contained in every conditional
linear-form disk whose coefficient energy is below twice `M`. This includes
zero coefficient energy. -/
theorem circularGaussian_smallBall_le_iidCircularLinearForm_of_energy_lt
    {k : ℕ} (y : Fin k → ℂ) (M ε : ℝ) (_hM : 0 ≤ M) (_hε : 0 ≤ ε)
    (hy : circularCoefficientEnergy y < 2 * M) :
    circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2} ≤
      (standardGaussianProduct (Fin k))
        {g | ‖iidCircularTransposeLinearForm y g‖ ≤ ε * Real.sqrt M} := by
  let B : Set ℂ := {z | ‖z‖ ≤ ε / Real.sqrt 2}
  let T : Set ℂ := {z | ‖z‖ ≤ ε * Real.sqrt M}
  have hT : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_le continuous_norm.measurable measurable_const
  have hsubset : B ⊆
      (fun z : ℂ ↦ Real.sqrt (circularCoefficientEnergy y) • z) ⁻¹' T := by
    intro z hz
    change ‖Real.sqrt (circularCoefficientEnergy y) • z‖ ≤ ε * Real.sqrt M
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (circularCoefficientEnergy y))]
    have hsqrtEnergy :
        Real.sqrt (circularCoefficientEnergy y) ≤ Real.sqrt (2 * M) :=
      Real.sqrt_le_sqrt hy.le
    have hsqrtTwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hz' : ‖z‖ ≤ ε / Real.sqrt 2 := hz
    calc
      Real.sqrt (circularCoefficientEnergy y) * ‖z‖ ≤
          Real.sqrt (2 * M) * (ε / Real.sqrt 2) :=
        mul_le_mul hsqrtEnergy hz' (norm_nonneg z) (Real.sqrt_nonneg _)
      _ = ε * Real.sqrt M := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp [hsqrtTwo.ne']
  calc
    circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2} = circularGaussian B := rfl
    _ ≤ circularGaussian
        ((fun z : ℂ ↦ Real.sqrt (circularCoefficientEnergy y) • z) ⁻¹' T) :=
      measure_mono hsubset
    _ = (circularGaussian.map
        (fun z : ℂ ↦ Real.sqrt (circularCoefficientEnergy y) • z)) T :=
      (Measure.map_apply (by fun_prop) hT).symm
    _ = ((standardGaussianProduct (Fin k)).map
        (iidCircularTransposeLinearForm y)) T := by
      change (circularGaussian.map
        (fun z : ℂ ↦ Real.sqrt (circularCoefficientEnergy y) • z)) T =
        ((Measure.pi fun _ : Fin k ↦ circularGaussian).map
          (iidCircularTransposeLinearForm y)) T
      rw [map_iidCircularTransposeLinearForm_eq_scaled_circular]
    _ = (standardGaussianProduct (Fin k))
        ((iidCircularTransposeLinearForm y) ⁻¹' T) :=
      Measure.map_apply (measurable_iidCircularTransposeLinearForm y) hT
    _ = (standardGaussianProduct (Fin k))
        {g | ‖iidCircularTransposeLinearForm y g‖ ≤ ε * Real.sqrt M} := rfl

/-- Literal complex lower-small-ball endpoint. Here `sigma n² = (2n-1)!!`.
For every `n ≥ 1`, the normalized hafnian disk has at least half the mass of
the standard circular-Gaussian disk at radius `ε / sqrt 2`. -/
theorem complex_edgeHafnian_smallBall_lower
    (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 ≤ ε) :
    ENNReal.ofReal (1 / 2 : ℝ) *
        circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2} ≤
      (edgeGaussian (Fin (2 * n)))
        {x | ‖edgeHafnian x‖ ≤ ε * sigma n} := by
  let m : ℕ := 2 * n - 1
  let μ := edgeGaussian (Fin m)
  let ν := standardGaussianProduct (Fin m)
  let M : ℝ := oddPairingNat n
  let good : Set (Edge (Fin m) → ℂ) :=
    {x | edgeCofactorEnergy x < 2 * M}
  let S : Set ((Edge (Fin m) → ℂ) × (Fin m → ℂ)) :=
    {p | ‖conditionalCircularLinearForm edgeCofactor p‖ ≤ ε * sigma n}
  have hm : m = 2 * (n - 1) + 1 := by
    dsimp [m]
    omega
  have hdim : m + 1 = 2 * n := by
    dsimp [m]
    omega
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Nat.cast_nonneg _
  have hgoodMeas : MeasurableSet good := by
    dsimp [good]
    exact measurableSet_lt measurable_edgeCofactorEnergy measurable_const
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le
      (measurable_conditionalCircularLinearForm measurable_edgeCofactor).norm
      measurable_const
  have hgood : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ good := by
    have h := half_le_measure_edgeCofactorEnergy_lt_two_mean (n - 1)
    rw [← hm] at h
    simpa only [μ, good, M, show n - 1 + 1 = n by omega] using h
  have hsection (x : Edge (Fin m) → ℂ) (hx : x ∈ good) :
      circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2} ≤
        ν (Prod.mk x ⁻¹' S) := by
    have hxEnergy : edgeCofactorEnergy x < 2 * M := hx
    have hfixed := circularGaussian_smallBall_le_iidCircularLinearForm_of_energy_lt
      (edgeCofactor x) M ε hM hε hxEnergy
    have hsigma : Real.sqrt M = sigma n := rfl
    simpa [ν, S, conditionalCircularLinearForm, edgeCofactorEnergy,
      circularCoefficientEnergy, hsigma] using hfixed
  have hprod :
      ENNReal.ofReal (1 / 2 : ℝ) *
          circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2} ≤
        (μ.prod ν) S := by
    rw [Measure.prod_apply hS]
    let p : ℝ≥0∞ := circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2}
    have hpoint (x : Edge (Fin m) → ℂ) :
        good.indicator (fun _ ↦ p) x ≤ ν (Prod.mk x ⁻¹' S) := by
      by_cases hx : x ∈ good
      · rw [indicator_of_mem hx]
        exact hsection x hx
      · rw [Set.indicator_of_notMem hx]
        exact bot_le
    calc
      ENNReal.ofReal (1 / 2 : ℝ) *
          circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2} =
          p * ENNReal.ofReal (1 / 2 : ℝ) := by rw [mul_comm]
      _ ≤ p * μ good := mul_le_mul le_rfl hgood bot_le bot_le
      _ = ∫⁻ x, good.indicator (fun _ ↦ p) x ∂μ :=
        (lintegral_indicator_const hgoodMeas p).symm
      _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ := lintegral_mono hpoint
  rw [← hdim]
  let T : Set (Edge (Fin (m + 1)) → ℂ) :=
    {x | ‖edgeHafnian x‖ ≤ ε * sigma n}
  have hT : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_le measurable_edgeHafnian.norm measurable_const
  have hpreimage : T = lastVertexSplit m ⁻¹' S := by
    ext x
    change (‖edgeHafnian x‖ ≤ ε * sigma n) ↔
      (‖conditionalCircularLinearForm edgeCofactor (lastVertexSplit m x)‖ ≤
        ε * sigma n)
    rw [edgeHafnian_eq_lastVertexLinearForm]
  change ENNReal.ofReal (1 / 2 : ℝ) *
      circularGaussian {z : ℂ | ‖z‖ ≤ ε / Real.sqrt 2} ≤
    (edgeGaussian (Fin (m + 1))) T
  rw [hpreimage,
    (measurePreserving_lastVertexSplit m).measure_preimage hS.nullMeasurableSet]
  exact hprod

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
