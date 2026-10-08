import A3.Target
import A3.Shared.PolynomialNullity
import Mathlib.Probability.Distributions.Beta

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace A3Research

theorem measurableSet_betaJacobiOpenCube (n : ℕ) :
    MeasurableSet (betaJacobiOpenCube n) := by
  change MeasurableSet {lambda : Fin n → ℝ | ∀ i, lambda i ∈ Ioo 0 1}
  convert! (MeasurableSet.iInter fun i : Fin n ↦
    (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1)).preimage
      (measurable_pi_apply i : Measurable (fun x : Fin n → ℝ ↦ x i))) using 1
  ext lambda
  simp

theorem volume_betaJacobiOpenCube (n : ℕ) :
    volume (betaJacobiOpenCube n) = 1 := by
  have hs : betaJacobiOpenCube n = Set.pi Set.univ (fun _ : Fin n ↦ Ioo (0 : ℝ) 1) := by
    ext lambda
    simp [H6CoordinateAlgebra.openUnitCube, Set.mem_pi]
  rw [hs, Real.volume_pi_Ioo]
  simp

theorem measurable_betaJacobiKernel (n : ℕ) (a b β : ℝ) :
    Measurable (betaJacobiKernel n a b β) := by
  unfold betaJacobiKernel
  simp only [ENNReal.rpow_eq_pow]
  fun_prop

theorem betaPDFReal_nonneg (α δ x : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    0 ≤ betaPDFReal α δ x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 hα hδ).le
  · simp [betaPDFReal, hx]

theorem integrable_betaPDFReal (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    Integrable (betaPDFReal α δ) (volume : Measure ℝ) := by
  refine ⟨(measurable_betaPDFReal α δ).aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖betaPDFReal α δ x‖ₑ) < ∞
  simp_rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (betaPDFReal_nonneg α δ _ hα hδ)]
  change (∫⁻ x, betaPDF α δ x) < ∞
  rw [lintegral_betaPDF_eq_one hα hδ]
  simp

theorem betaJacobi_endpoint_weight_eq_betaPDF (α δ x : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (ENNReal.ofReal x).rpow (α - 1) * (ENNReal.ofReal (1 - x)).rpow (δ - 1) =
      ENNReal.ofReal (beta α δ) * betaPDF α δ x := by
  have hb := beta_pos hα hδ
  have h1x : 0 < 1 - x := sub_pos.mpr hx.2
  simp only [ENNReal.rpow_eq_pow]
  rw [ENNReal.ofReal_rpow_of_pos hx.1, ENNReal.ofReal_rpow_of_pos h1x,
    ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hx.1 _).le,
    betaPDF_of_pos_lt_one hx.1 hx.2, ← ENNReal.ofReal_mul hb.le]
  congr 1
  field_simp

theorem betaJacobiKernel_le_endpoint_density {n : ℕ} (a b β : ℝ)
    (hα : 0 < β * (a + 1) / 2) (hδ : 0 < β * (b + 1) / 2) (hβ : 0 ≤ β)
    {lambda : Fin n → ℝ} (hlambda : lambda ∈ betaJacobiOpenCube n) :
    betaJacobiKernel n a b β lambda ≤
      (ENNReal.ofReal (beta (β * (a + 1) / 2) (β * (b + 1) / 2))) ^ n *
        ∏ i, betaPDF (β * (a + 1) / 2) (β * (b + 1) / 2) (lambda i) := by
  have hv : (∏ p ∈ a2StrictPairs n,
      (ENNReal.ofReal |lambda p.2 - lambda p.1|).rpow β) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      exact bot_le
    · intro p hp
      apply ENNReal.rpow_le_one _ hβ
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_le]
      exact ⟨by linarith [(hlambda p.2).1, (hlambda p.1).2],
        by linarith [(hlambda p.2).2, (hlambda p.1).1]⟩
  calc
    betaJacobiKernel n a b β lambda ≤ ∏ i,
        (ENNReal.ofReal (lambda i)).rpow (β * (a + 1) / 2 - 1) *
          (ENNReal.ofReal (1 - lambda i)).rpow (β * (b + 1) / 2 - 1) := by
      exact (mul_le_mul_right hv _).trans_eq (mul_one _)
    _ = _ := by
      simp_rw [betaJacobi_endpoint_weight_eq_betaPDF _ _ _ hα hδ (hlambda _)]
      rw [Finset.prod_mul_distrib]
      simp

/-- The full beta-Jacobi normalization is finite even at the square real endpoint. -/
theorem betaJacobiNormalization_ne_top (n : ℕ) (a b β : ℝ)
    (hα : 0 < β * (a + 1) / 2) (hδ : 0 < β * (b + 1) / 2) (hβ : 0 ≤ β) :
    betaJacobiNormalization n a b β ≠ ∞ := by
  let α := β * (a + 1) / 2
  let δ := β * (b + 1) / 2
  let B := beta α δ
  let f : (Fin n → ℝ) → ℝ := fun lambda ↦ B ^ n * ∏ i, betaPDFReal α δ (lambda i)
  have hf : Integrable f (volume : Measure (Fin n → ℝ)) := by
    exact (Integrable.fintype_prod (fun _ : Fin n ↦ integrable_betaPDFReal α δ hα hδ)).const_mul _
  have hf0 (lambda : Fin n → ℝ) : 0 ≤ f lambda :=
    mul_nonneg (pow_nonneg (beta_pos hα hδ).le _) (Finset.prod_nonneg fun _ _ ↦
      betaPDFReal_nonneg α δ _ hα hδ)
  have he (lambda : Fin n → ℝ) : ENNReal.ofReal (f lambda) =
      ENNReal.ofReal B ^ n * ∏ i, betaPDF α δ (lambda i) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (beta_pos hα hδ).le _),
      ENNReal.ofReal_pow (beta_pos hα hδ).le]
    congr 1
    rw [ENNReal.ofReal_prod_of_nonneg]
    · rfl
    · exact fun i _ ↦ betaPDFReal_nonneg α δ _ hα hδ
  have hbound : (∫⁻ lambda in betaJacobiOpenCube n, betaJacobiKernel n a b β lambda) ≤
      ∫⁻ lambda, ENNReal.ofReal (f lambda) := by
    calc
      _ ≤ ∫⁻ lambda in betaJacobiOpenCube n, ENNReal.ofReal (f lambda) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_betaJacobiOpenCube n)] with lambda hlambda
        rw [he]
        exact betaJacobiKernel_le_endpoint_density a b β hα hδ hβ hlambda
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hfinite : (∫⁻ lambda, ENNReal.ofReal (f lambda)) < ∞ := by
    have h := hf.hasFiniteIntegral
    change (∫⁻ lambda, ‖f lambda‖ₑ) < ∞ at h
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 _)] using h
  unfold betaJacobiNormalization betaJacobiRawMeasure
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact ne_of_lt (lt_of_le_of_lt hbound hfinite)

theorem ae_injective_real_coordinates (n : ℕ) :
    ∀ᵐ lambda ∂(volume : Measure (Fin n → ℝ)), Function.Injective lambda := by
  classical
  have hp : ∀ᵐ lambda ∂(volume : Measure (Fin n → ℝ)),
      ∀ i j, i ≠ j → lambda i ≠ lambda j := by
    simp_rw [Filter.eventually_all]
    intro i j
    intro hij
    have hpoly : (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ≠ 0 := by
        intro hz
        have he := congrArg (MvPolynomial.eval (fun k : Fin n ↦ if k = j then (1 : ℝ) else 0)) hz
        simpa [hij] using he
    have h := ae_mvPolynomial_eval_ne_zero (volume : Measure ℝ) _ hpoly
    filter_upwards [h] with lambda hlambda
    simpa only [MvPolynomial.eval_sub, MvPolynomial.eval_X, ne_eq, sub_eq_zero,
      eq_comm] using hlambda
  filter_upwards [hp] with lambda hlambda
  intro i j he
  by_contra hij
  exact hlambda i j hij he

theorem betaJacobiKernel_pos_of_injective {n : ℕ} (a b β : ℝ)
    {lambda : Fin n → ℝ} (hlambda : lambda ∈ betaJacobiOpenCube n) (hi : Function.Injective lambda) :
    0 < betaJacobiKernel n a b β lambda := by
  classical
  unfold betaJacobiKernel
  simp only [ENNReal.rpow_eq_pow]
  apply ENNReal.mul_pos
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact mul_ne_zero
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (hlambda i).1) ENNReal.ofReal_ne_top).ne'
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hlambda i).2))
        ENNReal.ofReal_ne_top).ne'
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hij : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr
      (abs_pos.mpr (sub_ne_zero.mpr (fun h ↦ hij (hi h).symm))))
        ENNReal.ofReal_ne_top).ne'

/-- Positivity comes from the actual collision hyperplanes being Lebesgue-null. -/
theorem betaJacobiNormalization_ne_zero (n : ℕ) (a b β : ℝ) :
    betaJacobiNormalization n a b β ≠ 0 := by
  intro hz
  have hm : betaJacobiRawMeasure n a b β = 0 :=
    Measure.measure_univ_eq_zero.mp hz
  have hae := (withDensity_eq_zero_iff (measurable_betaJacobiKernel n a b β).aemeasurable).mp
    (show (volume.restrict (betaJacobiOpenCube n)).withDensity
      (betaJacobiKernel n a b β) = 0 from hm)
  have hfalse : ∀ᵐ _lambda ∂(volume.restrict (betaJacobiOpenCube n)), False := by
    filter_upwards [hae, ae_restrict_mem (measurableSet_betaJacobiOpenCube n),
      ae_restrict_of_ae (ae_injective_real_coordinates n)] with lambda hzero hcube hinj
    exact (betaJacobiKernel_pos_of_injective a b β hcube hinj).ne' hzero
  have hbase : volume.restrict (betaJacobiOpenCube n) = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    simpa using ae_iff.mp hfalse
  have he := congrArg (fun μ : Measure (Fin n → ℝ) ↦ μ Set.univ) hbase
  simpa [volume_betaJacobiOpenCube n] using he

theorem isProbabilityMeasure_betaJacobiProbabilityMeasure (n : ℕ) (a b β : ℝ)
    (hα : 0 < β * (a + 1) / 2) (hδ : 0 < β * (b + 1) / 2) (hβ : 0 ≤ β) :
    IsProbabilityMeasure (betaJacobiProbabilityMeasure n a b β) where
  measure_univ := by
    rw [betaJacobiProbabilityMeasure, H6RadialMeasureAdapters.normalizeMeasure,
      Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (betaJacobiNormalization_ne_zero n a b β)
      (betaJacobiNormalization_ne_top n a b β hα hδ hβ)

theorem isProbabilityMeasure_betaJacobiProbabilityMeasure_nat (n a b : ℕ) (β : ℝ)
    (hβ : β = 1 ∨ β = 2) :
    IsProbabilityMeasure (betaJacobiProbabilityMeasure n (a : ℝ) (b : ℝ) β) := by
  apply isProbabilityMeasure_betaJacobiProbabilityMeasure
  all_goals rcases hβ with hβ | hβ <;> subst β <;> positivity

end A3Research
