import LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentrationEndpoints
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped ENNReal
open Filter MeasureTheory Set
open LogdetLean.GramHafnian

namespace LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration

noncomputable section

lemma lintegral_Ioc_rpow_eq {r c : ℝ} (hr : -1 < r) (hc : 0 < c) :
    ∫⁻ t in Ioc (0 : ℝ) c, ENNReal.ofReal (t ^ r) ∂volume =
      ENNReal.ofReal (c ^ (r + 1) / (r + 1)) := by
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ r) (Ioc 0 c) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hr).1
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) c), 0 ≤ t ^ r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le r
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ← intervalIntegral.integral_of_le hc.le, integral_rpow (Or.inl hr)]
  simp [Real.zero_rpow (by linarith : r + 1 ≠ 0)]

lemma lintegral_Ioi_rpow_eq {r c : ℝ} (hr : r < -1) (hc : 0 < c) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (t ^ r) ∂volume =
      ENNReal.ofReal (-c ^ (r + 1) / (r + 1)) := by
  have hint := integrableOn_Ioi_rpow_of_lt hr hc
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioi c), 0 ≤ t ^ r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hc.le.trans ht.le) r
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_Ioi_rpow_of_lt hr hc]

def normalizedShiftedIntensityObservable
    (k n : ℕ) (z : ℂ) (X : ComplexColumnMatrix n k) : ℝ :=
  (‖gramHafnianObservable n k X - z‖ / gramHafnianSigma k n) ^ 2

@[fun_prop]
theorem measurable_normalizedShiftedIntensityObservable
    (k n : ℕ) (z : ℂ) :
    Measurable (normalizedShiftedIntensityObservable k n z) := by
  unfold normalizedShiftedIntensityObservable
  fun_prop

theorem normalizedShiftedIntensity_event_eq
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    {X | normalizedShiftedIntensityObservable k n z X ≤ t} =
      gramHafnianShiftedSmallBallEvent k n z (Real.sqrt t) := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k n := gramHafnianSigma_pos k n hkpos
  ext X
  unfold normalizedShiftedIntensityObservable gramHafnianShiftedSmallBallEvent
  change (‖gramHafnianObservable n k X - z‖ / gramHafnianSigma k n) ^ 2 ≤ t ↔
    ‖gramHafnianObservable n k X - z‖ ≤ Real.sqrt t * gramHafnianSigma k n
  conv_lhs => rw [← Real.sq_sqrt ht]
  rw [sq_le_sq₀ (div_nonneg (norm_nonneg _) hsigma.le) (Real.sqrt_nonneg t),
    div_le_iff₀ hsigma]

theorem negativeRpowMoment_le_of_lowerTail
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (q : Ω → ℝ) (hqmeas : Measurable q)
    (hqpos : ∀ᵐ ω ∂mu, 0 < q ω)
    {B alpha s : ℝ} (hB : 0 < B) (halpha : 0 < alpha)
    (hs : 0 < s) (hsa : s < alpha)
    (htail : ∀ t : ℝ, 0 ≤ t →
      mu.real {ω | q ω ≤ t} ≤ min 1 (B * t ^ alpha)) :
    (∫⁻ ω, ENNReal.ofReal ((q ω)⁻¹ ^ s) ∂mu) ≤
      ENNReal.ofReal (alpha / (alpha - s) * B ^ (s / alpha)) := by
  let f : Ω → ℝ := fun ω ↦ (q ω)⁻¹
  let c : ℝ := B ^ (1 / alpha)
  have hc : 0 < c := Real.rpow_pos_of_pos hB _
  have hf_nonneg : ∀ᵐ ω ∂mu, 0 ≤ f ω :=
    hqpos.mono fun _ hq ↦ (inv_pos.mpr hq).le
  have hf_meas : Measurable f := hqmeas.inv
  rw [show (fun ω ↦ ENNReal.ofReal ((q ω)⁻¹ ^ s)) =
      (fun ω ↦ ENNReal.ofReal (f ω ^ s)) by rfl,
    lintegral_rpow_eq_lintegral_meas_le_mul mu hf_nonneg hf_meas.aemeasurable hs]
  have hevent (t : ℝ) (ht : 0 < t) :
      mu {ω | t ≤ f ω} = mu {ω | q ω ≤ t⁻¹} := by
    apply measure_congr
    filter_upwards [hqpos] with ω hq
    change (t ≤ (q ω)⁻¹) = (q ω ≤ t⁻¹)
    exact propext (le_inv_comm₀ ht hq)
  have hmeasure_one (t : ℝ) : mu {ω | t ≤ f ω} ≤ 1 := by
    have h := measure_mono (μ := mu) (Set.subset_univ {ω | t ≤ f ω})
    simpa only [measure_univ] using h
  have hmeasure_tail (t : ℝ) (ht : 0 < t) :
      mu {ω | t ≤ f ω} ≤ ENNReal.ofReal (B * (t⁻¹) ^ alpha) := by
    rw [hevent t ht]
    have hr := (htail t⁻¹ (inv_nonneg.mpr ht.le)).trans (min_le_right _ _)
    calc
      mu {ω | q ω ≤ t⁻¹} = ENNReal.ofReal (mu.real {ω | q ω ≤ t⁻¹}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top mu _)]
      _ ≤ ENNReal.ofReal (B * (t⁻¹) ^ alpha) := ENNReal.ofReal_le_ofReal hr
  have hsplit : Ioi (0 : ℝ) = Ioc 0 c ∪ Ioi c := by
    ext t
    constructor
    · intro ht
      by_cases htc : t ≤ c
      · exact Or.inl ⟨ht, htc⟩
      · exact Or.inr (lt_of_not_ge htc)
    · intro ht
      rcases ht with ht | ht
      · exact ht.1
      · exact hc.trans ht
  rw [hsplit, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hnear :
      (∫⁻ t in Ioc (0 : ℝ) c,
        mu {a | t ≤ f a} * ENNReal.ofReal (t ^ (s - 1)) ∂volume) ≤
      ENNReal.ofReal (c ^ s / s) := by
    calc
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) c,
          ENNReal.ofReal (t ^ (s - 1)) ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro t ht
        simpa using mul_le_of_le_one_left' (hmeasure_one t)
      _ = ENNReal.ofReal (c ^ ((s - 1) + 1) / ((s - 1) + 1)) :=
        lintegral_Ioc_rpow_eq (by linarith) hc
      _ = ENNReal.ofReal (c ^ s / s) := by ring_nf
  have hfar :
      (∫⁻ t in Ioi c,
        mu {a | t ≤ f a} * ENNReal.ofReal (t ^ (s - 1)) ∂volume) ≤
      ENNReal.ofReal (B * (-c ^ (s - alpha) / (s - alpha))) := by
    calc
      _ ≤ ∫⁻ t in Ioi c,
          ENNReal.ofReal (B * t ^ (s - alpha - 1)) ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := hc.trans ht
        calc
          mu {a | t ≤ f a} * ENNReal.ofReal (t ^ (s - 1)) ≤
              ENNReal.ofReal (B * (t⁻¹) ^ alpha) *
                ENNReal.ofReal (t ^ (s - 1)) :=
            mul_le_mul_left (hmeasure_tail t ht0) _
          _ = ENNReal.ofReal (B * t ^ (s - alpha - 1)) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hB.le
              (Real.rpow_nonneg (inv_nonneg.mpr ht0.le) alpha))]
            apply congrArg ENNReal.ofReal
            rw [mul_assoc, Real.inv_rpow ht0.le,
              ← Real.rpow_neg ht0.le alpha,
              ← Real.rpow_add ht0]
            rw [show -alpha + (s - 1) = s - alpha - 1 by ring]
      _ = ENNReal.ofReal B *
          (∫⁻ t in Ioi c, ENNReal.ofReal (t ^ (s - alpha - 1)) ∂volume) := by
        rw [← lintegral_const_mul'' (ENNReal.ofReal B)]
        · apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht
          change ENNReal.ofReal (B * t ^ (s - alpha - 1)) =
            ENNReal.ofReal B * ENNReal.ofReal (t ^ (s - alpha - 1))
          exact ENNReal.ofReal_mul hB.le
        · fun_prop
      _ = ENNReal.ofReal B *
          ENNReal.ofReal (-c ^ ((s - alpha - 1) + 1) /
            ((s - alpha - 1) + 1)) := by
        rw [lintegral_Ioi_rpow_eq (by linarith) hc]
      _ = ENNReal.ofReal (B * (-c ^ (s - alpha) / (s - alpha))) := by
        rw [← ENNReal.ofReal_mul hB.le]
        ring_nf
  calc
    ENNReal.ofReal s *
        ((∫⁻ t in Ioc (0 : ℝ) c,
          mu {a | t ≤ f a} * ENNReal.ofReal (t ^ (s - 1)) ∂volume) +
        ∫⁻ t in Ioi c,
          mu {a | t ≤ f a} * ENNReal.ofReal (t ^ (s - 1)) ∂volume) ≤
      ENNReal.ofReal s *
        (ENNReal.ofReal (c ^ s / s) +
          ENNReal.ofReal (B * (-c ^ (s - alpha) / (s - alpha)))) := by
      gcongr
    _ = ENNReal.ofReal
        (s * (c ^ s / s + B * (-c ^ (s - alpha) / (s - alpha)))) := by
      have hfar_factor :
          -c ^ (s - alpha) / (s - alpha) = c ^ (s - alpha) / (alpha - s) := by
        field_simp [sub_ne_zero.mpr hsa.ne, sub_ne_zero.mpr hsa.ne']
        ring
      have hfar_nonneg : 0 ≤ B * (-c ^ (s - alpha) / (s - alpha)) := by
        rw [hfar_factor]
        exact mul_nonneg hB.le (div_nonneg (Real.rpow_nonneg hc.le _) (by linarith))
      rw [← ENNReal.ofReal_add (div_nonneg (Real.rpow_nonneg hc.le s) hs.le)
        hfar_nonneg,
        ← ENNReal.ofReal_mul hs.le]
    _ = ENNReal.ofReal (alpha / (alpha - s) * B ^ (s / alpha)) := by
      congr 1
      dsimp [c]
      have hrewrite1 : (B ^ (1 / alpha)) ^ s = B ^ (s / alpha) := by
        calc
          (B ^ (1 / alpha)) ^ s = B ^ ((1 / alpha) * s) :=
            (Real.rpow_mul hB.le _ _).symm
          _ = B ^ (s / alpha) := by
            congr 1
            field_simp [halpha.ne']
      have hrewrite2 :
          B * (B ^ (1 / alpha)) ^ (s - alpha) = B ^ (s / alpha) := by
        calc
          B * (B ^ (1 / alpha)) ^ (s - alpha) =
              B ^ 1 * B ^ ((1 / alpha) * (s - alpha)) := by
            rw [Real.rpow_one]
            congr 1
            exact (Real.rpow_mul hB.le _ _).symm
          _ = B ^ (1 + (1 / alpha) * (s - alpha)) :=
            (Real.rpow_add hB _ _).symm
          _ = B ^ (s / alpha) := by
            congr 1
            field_simp [halpha.ne']
            ring
      rw [hrewrite1]
      have hterm :
          B * (-(B ^ (1 / alpha)) ^ (s - alpha) / (s - alpha)) =
            -(B ^ (s / alpha)) / (s - alpha) := by
        calc
          B * (-(B ^ (1 / alpha)) ^ (s - alpha) / (s - alpha)) =
              -(B * (B ^ (1 / alpha)) ^ (s - alpha)) / (s - alpha) := by ring
          _ = -(B ^ (s / alpha)) / (s - alpha) := by rw [hrewrite2]
      rw [hterm]
      field_simp [hs.ne', sub_ne_zero.mpr hsa.ne, sub_ne_zero.mpr hsa.ne']
      ring

/-- The lower-tail estimate itself excludes an atom at zero, so positivity
need not be supplied separately. -/
theorem negativeRpowMoment_le_of_powerLowerTail
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (q : Ω → ℝ) (hqmeas : Measurable q)
    {B alpha s : ℝ} (hB : 0 < B) (halpha : 0 < alpha)
    (hs : 0 < s) (hsa : s < alpha)
    (htail : ∀ t : ℝ, 0 ≤ t →
      mu.real {ω | q ω ≤ t} ≤ min 1 (B * t ^ alpha)) :
    (∫⁻ ω, ENNReal.ofReal ((q ω)⁻¹ ^ s) ∂mu) ≤
      ENNReal.ofReal (alpha / (alpha - s) * B ^ (s / alpha)) := by
  have hzero_real : mu.real {ω | q ω ≤ 0} = 0 := by
    apply le_antisymm
    · have h := htail 0 le_rfl
      simpa [Real.zero_rpow halpha.ne'] using h
    · exact measureReal_nonneg
  have hzero : mu {ω | q ω ≤ 0} = 0 :=
    (measureReal_eq_zero_iff).mp hzero_real
  have hqpos : ∀ᵐ ω ∂mu, 0 < q ω := by
    rw [ae_iff]
    simpa only [not_lt] using hzero
  exact negativeRpowMoment_le_of_lowerTail mu q hqmeas hqpos
    hB halpha hs hsa htail

theorem normalizedShiftedIntensity_lowerTail
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (circularGaussianColumnMatrixMeasure n k).real
        {X | normalizedShiftedIntensityObservable k n z X ≤ t} ≤
      min 1 (shiftedAnticoncentrationConstant k n * t) := by
  rw [normalizedShiftedIntensity_event_eq n k hn hk z t ht]
  change gramHafnianShiftedSmallBallProbability k n z (Real.sqrt t) ≤ _
  simpa [Real.sq_sqrt ht] using
    gaussianGramHafnianShiftedAnticoncentration_min
      n k hn hk z (Real.sqrt t) (Real.sqrt_nonneg t)

theorem shiftedAnticoncentrationConstant_pos
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    0 < shiftedAnticoncentrationConstant k n := by
  unfold shiftedAnticoncentrationConstant
  have hkpos : 0 < k := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkR : (4 : ℝ) * n ≤ k := by exact_mod_cast hk
  have hkRpos : (0 : ℝ) < k := by positivity
  have hkm1 : 0 < (k : ℝ) - 1 := by linarith
  have hchoose : 0 < ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)
  have hprod : 0 < ∏ r ∈ Finset.Icc 2 n,
      (((k : ℝ) + 2 * (r : ℝ) - 2) /
        ((k : ℝ) - 4 * (r : ℝ) + 1)) := by
    apply Finset.prod_pos
    intro r hr
    have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
    have hrnR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hnum : 0 < (k : ℝ) + 2 * (r : ℝ) - 2 := by
      linarith
    have hden : 0 < (k : ℝ) - 4 * (r : ℝ) + 1 := by
      linarith
    exact div_pos hnum hden
  exact mul_pos
    (mul_pos
      (div_pos
        (mul_pos (mul_pos (by norm_num) (by exact_mod_cast (show 0 < n by omega))) hchoose)
        (by positivity))
      (div_pos hkRpos hkm1))
    hprod

theorem normalizedShiftedIntensity_negativeMoment
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (∫⁻ X, ENNReal.ofReal
        ((normalizedShiftedIntensityObservable k n z X)⁻¹ ^ s)
        ∂(circularGaussianColumnMatrixMeasure n k)) ≤
      ENNReal.ofReal
        (shiftedAnticoncentrationConstant k n ^ s / (1 - s)) := by
  have hB := shiftedAnticoncentrationConstant_pos n k hn hk
  have h := negativeRpowMoment_le_of_powerLowerTail
    (circularGaussianColumnMatrixMeasure n k)
    (normalizedShiftedIntensityObservable k n z)
    (measurable_normalizedShiftedIntensityObservable k n z)
    hB (by norm_num : (0 : ℝ) < 1) hs hs1
    (by
      intro t ht
      simpa using normalizedShiftedIntensity_lowerTail n k hn hk z t ht)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem ae_normalizedShiftedIntensity_pos
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) (z : ℂ) :
    ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure n k),
      0 < normalizedShiftedIntensityObservable k n z X := by
  have hzero_real :
      (circularGaussianColumnMatrixMeasure n k).real
          {X | normalizedShiftedIntensityObservable k n z X ≤ 0} = 0 := by
    apply le_antisymm
    · simpa using normalizedShiftedIntensity_lowerTail n k hn hk z 0 le_rfl
    · exact measureReal_nonneg
  have hzero :
      (circularGaussianColumnMatrixMeasure n k)
          {X | normalizedShiftedIntensityObservable k n z X ≤ 0} = 0 :=
    (measureReal_eq_zero_iff).mp hzero_real
  rw [ae_iff]
  simpa only [not_lt] using hzero

/-- AC2's application to an additive estimate at the reference scale. -/
theorem normalizedShiftedIntensity_relativeErrorMoment
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (pTilde : ComplexColumnMatrix n k → ℝ)
    {pRef eta s : ℝ} (hpRef : 0 < pRef) (heta : 0 ≤ eta)
    (hs : 0 < s) (hs1 : s < 1)
    (hadd : ∀ᵐ X ∂(circularGaussianColumnMatrixMeasure n k),
      |pTilde X - pRef * normalizedShiftedIntensityObservable k n z X| ≤
        eta * pRef) :
    (∫⁻ X, ENNReal.ofReal
        ((|pTilde X - pRef * normalizedShiftedIntensityObservable k n z X| /
          (pRef * normalizedShiftedIntensityObservable k n z X)) ^ s)
        ∂(circularGaussianColumnMatrixMeasure n k)) ≤
      ENNReal.ofReal
        ((eta * shiftedAnticoncentrationConstant k n) ^ s / (1 - s)) := by
  let mu := circularGaussianColumnMatrixMeasure n k
  let q := normalizedShiftedIntensityObservable k n z
  have hqpos : ∀ᵐ X ∂mu, 0 < q X :=
    ae_normalizedShiftedIntensity_pos n k hn hk z
  have hpoint : ∀ᵐ X ∂mu,
      ENNReal.ofReal
          ((|pTilde X - pRef * q X| / (pRef * q X)) ^ s) ≤
        ENNReal.ofReal (eta ^ s) *
          ENNReal.ofReal (((q X)⁻¹) ^ s) := by
    filter_upwards [hadd, hqpos] with X hXadd hXq
    have hden : 0 < pRef * q X := mul_pos hpRef hXq
    have hratio0 : 0 ≤
        |pTilde X - pRef * q X| / (pRef * q X) :=
      div_nonneg (abs_nonneg _) hden.le
    have hratio :
        |pTilde X - pRef * q X| / (pRef * q X) ≤ eta * (q X)⁻¹ := by
      calc
        |pTilde X - pRef * q X| / (pRef * q X) ≤
            (eta * pRef) / (pRef * q X) :=
          (div_le_div_iff_of_pos_right hden).mpr hXadd
        _ = eta * (q X)⁻¹ := by
          field_simp [hpRef.ne', hXq.ne']
    calc
      ENNReal.ofReal
          ((|pTilde X - pRef * q X| / (pRef * q X)) ^ s) ≤
          ENNReal.ofReal ((eta * (q X)⁻¹) ^ s) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hratio0 hratio hs.le)
      _ = ENNReal.ofReal (eta ^ s * ((q X)⁻¹) ^ s) := by
        rw [Real.mul_rpow heta (inv_nonneg.mpr hXq.le)]
      _ = ENNReal.ofReal (eta ^ s) *
          ENNReal.ofReal (((q X)⁻¹) ^ s) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg heta s)
  have hmeas : AEMeasurable
      (fun X ↦ ENNReal.ofReal (((q X)⁻¹) ^ s)) mu := by
    dsimp [q, mu]
    fun_prop
  have hmoment := normalizedShiftedIntensity_negativeMoment n k hn hk z hs hs1
  calc
    (∫⁻ X, ENNReal.ofReal
        ((|pTilde X - pRef * normalizedShiftedIntensityObservable k n z X| /
          (pRef * normalizedShiftedIntensityObservable k n z X)) ^ s)
        ∂(circularGaussianColumnMatrixMeasure n k)) ≤
      ∫⁻ X, ENNReal.ofReal (eta ^ s) *
        ENNReal.ofReal (((q X)⁻¹) ^ s) ∂mu :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (eta ^ s) *
        (∫⁻ X, ENNReal.ofReal (((q X)⁻¹) ^ s) ∂mu) :=
      lintegral_const_mul'' _ hmeas
    _ ≤ ENNReal.ofReal (eta ^ s) *
        ENNReal.ofReal
          (shiftedAnticoncentrationConstant k n ^ s / (1 - s)) :=
      mul_le_mul_right hmoment _
    _ = ENNReal.ofReal
        ((eta * shiftedAnticoncentrationConstant k n) ^ s / (1 - s)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg heta s)]
      congr 1
      rw [Real.mul_rpow heta (shiftedAnticoncentrationConstant_pos n k hn hk).le]
      ring

theorem normalizedShiftedIntensity_lowerTail_div_t_tendsto
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) (z : ℂ) :
    Tendsto
      (fun t : ℝ ↦
        (circularGaussianColumnMatrixMeasure n k).real
            {X | normalizedShiftedIntensityObservable k n z X ≤ t} / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (gramHafnianSigma k n ^ 2 *
        (Real.pi * localAnticoncentrationGramHafnianDensity (k := k) hn z))) := by
  have hsqrt : Tendsto (fun t : ℝ ↦ Real.sqrt t)
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.2 ht
  have hlocal :=
    (gramHafnian_normalized_shrinkingDisk_limit_density hn hk z).comp hsqrt
  apply hlocal.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  simp only [Function.comp_apply]
  rw [normalizedShiftedIntensity_event_eq n k hn hk z t ht0.le]
  unfold gramHafnianShiftedSmallBallEvent
  rw [Real.sq_sqrt ht0.le]

/-- A linear lower tail at zero forces every inverse moment of order at least
one to diverge. -/
theorem negativeRpowMoment_eq_top_of_linearLowerTail
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (q : Ω → ℝ) (hqmeas : Measurable q)
    (hqpos : ∀ᵐ ω ∂mu, 0 < q ω)
    {s c t0 : ℝ} (hs : 0 < s) (hs1 : 1 ≤ s)
    (hc : 0 < c) (ht0 : 0 < t0)
    (hlower : ∀ t : ℝ, 0 < t → t < t0 →
      c * t ≤ mu.real {ω | q ω ≤ t}) :
    (∫⁻ ω, ENNReal.ofReal ((q ω)⁻¹ ^ s) ∂mu) = ⊤ := by
  let f : Ω → ℝ := fun ω ↦ (q ω)⁻¹
  let a : ℝ := t0⁻¹
  have ha : 0 < a := inv_pos.mpr ht0
  have hf_nonneg : ∀ᵐ ω ∂mu, 0 ≤ f ω :=
    hqpos.mono fun _ hq ↦ (inv_pos.mpr hq).le
  have hf_meas : Measurable f := hqmeas.inv
  rw [show (fun ω ↦ ENNReal.ofReal ((q ω)⁻¹ ^ s)) =
      (fun ω ↦ ENNReal.ofReal (f ω ^ s)) by rfl,
    lintegral_rpow_eq_lintegral_meas_le_mul mu hf_nonneg hf_meas.aemeasurable hs]
  have hevent (u : ℝ) (hu : 0 < u) :
      mu {ω | u ≤ f ω} = mu {ω | q ω ≤ u⁻¹} := by
    apply measure_congr
    filter_upwards [hqpos] with ω hq
    change (u ≤ (q ω)⁻¹) = (q ω ≤ u⁻¹)
    exact propext (le_inv_comm₀ hu hq)
  have hmeasure_lower (u : ℝ) (hu : a < u) :
      ENNReal.ofReal (c * u⁻¹) ≤ mu {ω | u ≤ f ω} := by
    have hu0 : 0 < u := ha.trans hu
    have huit0 : u⁻¹ < t0 := (inv_lt_comm₀ ht0 hu0).mp hu
    have hreal := hlower u⁻¹ (inv_pos.mpr hu0) huit0
    rw [hevent u hu0]
    calc
      ENNReal.ofReal (c * u⁻¹) ≤
          ENNReal.ofReal (mu.real {ω | q ω ≤ u⁻¹}) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = mu {ω | q ω ≤ u⁻¹} := by
        rw [measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top mu _)]
  have hpow_top :
      (∫⁻ u in Ioi a, ENNReal.ofReal (u ^ (s - 2)) ∂volume) = ⊤ := by
    by_contra hne
    have hmeas : AEStronglyMeasurable (fun u : ℝ ↦ u ^ (s - 2))
        (volume.restrict (Ioi a)) := by fun_prop
    have hnonneg : ∀ᵐ u ∂volume.restrict (Ioi a), 0 ≤ u ^ (s - 2) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      exact Real.rpow_nonneg (ha.le.trans hu.le) _
    have hint : IntegrableOn (fun u : ℝ ↦ u ^ (s - 2)) (Ioi a) volume :=
      (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp hne
    have hexp : s - 2 < -1 := (integrableOn_Ioi_rpow_iff ha).mp hint
    linarith
  have hcpow_top :
      (∫⁻ u in Ioi a, ENNReal.ofReal (c * u ^ (s - 2)) ∂volume) = ⊤ := by
    calc
      (∫⁻ u in Ioi a, ENNReal.ofReal (c * u ^ (s - 2)) ∂volume) =
          ∫⁻ u in Ioi a, ENNReal.ofReal c *
            ENNReal.ofReal (u ^ (s - 2)) ∂volume := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro u hu
        exact ENNReal.ofReal_mul hc.le
      _ = ENNReal.ofReal c *
          (∫⁻ u in Ioi a, ENNReal.ofReal (u ^ (s - 2)) ∂volume) := by
        rw [lintegral_const_mul'']
        fun_prop
      _ = ⊤ := by
        rw [hpow_top, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']
  have hinner_top :
      (∫⁻ u in Ioi (0 : ℝ),
        mu {ω | u ≤ f ω} * ENNReal.ofReal (u ^ (s - 1)) ∂volume) = ⊤ := by
    apply top_unique
    calc
      ⊤ = ∫⁻ u in Ioi a,
          ENNReal.ofReal (c * u ^ (s - 2)) ∂volume := hcpow_top.symm
      _ ≤ ∫⁻ u in Ioi a,
          mu {ω | u ≤ f ω} * ENNReal.ofReal (u ^ (s - 1)) ∂volume := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro u hu
        have hu0 : 0 < u := ha.trans hu
        calc
          ENNReal.ofReal (c * u ^ (s - 2)) =
              ENNReal.ofReal (c * u⁻¹) *
                ENNReal.ofReal (u ^ (s - 1)) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hc.le (inv_nonneg.mpr hu0.le))]
            apply congrArg ENNReal.ofReal
            rw [show u⁻¹ = u ^ (-1 : ℝ) by
              rw [Real.rpow_neg hu0.le]
              norm_num]
            rw [mul_assoc, ← Real.rpow_add hu0]
            congr 1
            ring
          _ ≤ mu {ω | u ≤ f ω} * ENNReal.ofReal (u ^ (s - 1)) :=
            mul_le_mul_left (hmeasure_lower u hu) _
      _ ≤ ∫⁻ u in Ioi (0 : ℝ),
          mu {ω | u ≤ f ω} * ENNReal.ofReal (u ^ (s - 1)) ∂volume :=
        lintegral_mono_set fun u hu ↦ ha.trans hu
  rw [hinner_top, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hs).ne']

theorem normalizedShiftedIntensity_exists_linearLowerTail
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) (z : ℂ) :
    ∃ c : ℝ, 0 < c ∧ ∃ t0 : ℝ, 0 < t0 ∧
      ∀ t : ℝ, 0 < t → t < t0 →
        c * t ≤ (circularGaussianColumnMatrixMeasure n k).real
          {X | normalizedShiftedIntensityObservable k n z X ≤ t} := by
  let L : ℝ := gramHafnianSigma k n ^ 2 *
    (Real.pi * localAnticoncentrationGramHafnianDensity (k := k) hn z)
  have hL : 0 < L := by
    dsimp [L]
    rw [pi_mul_localAnticoncentrationGramHafnianDensity_eq_localSharpnessCoefficient]
    exact gramHafnian_normalized_shrinkingDisk_limit_coefficient_pos hn hk z
  have hlim := normalizedShiftedIntensity_lowerTail_div_t_tendsto n k hn hk z
  have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      L / 2 <
        (circularGaussianColumnMatrixMeasure n k).real
          {X | normalizedShiftedIntensityObservable k n z X ≤ t} / t :=
    hlim.eventually (Ioi_mem_nhds (by linarith : L / 2 < L))
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hevent with
    ⟨u, hu, husub⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨eps, heps, hball⟩
  refine ⟨L / 2, by linarith, eps, heps, ?_⟩
  intro t ht hteps
  have htball : t ∈ Metric.ball (0 : ℝ) eps := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hteps
  have hratio := husub ⟨hball htball, ht⟩
  calc
    (L / 2) * t ≤
        ((circularGaussianColumnMatrixMeasure n k).real
          {X | normalizedShiftedIntensityObservable k n z X ≤ t} / t) * t :=
      mul_le_mul_of_nonneg_right hratio.le ht.le
    _ = (circularGaussianColumnMatrixMeasure n k).real
          {X | normalizedShiftedIntensityObservable k n z X ≤ t} := by
      field_simp [ht.ne']

theorem normalizedShiftedIntensity_negativeMoment_eq_top
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) (z : ℂ)
    {s : ℝ} (hs1 : 1 ≤ s) :
    (∫⁻ X, ENNReal.ofReal
        ((normalizedShiftedIntensityObservable k n z X)⁻¹ ^ s)
        ∂(circularGaussianColumnMatrixMeasure n k)) = ⊤ := by
  rcases normalizedShiftedIntensity_exists_linearLowerTail n k hn hk z with
    ⟨c, hc, t0, ht0, hlower⟩
  exact negativeRpowMoment_eq_top_of_linearLowerTail
    (circularGaussianColumnMatrixMeasure n k)
    (normalizedShiftedIntensityObservable k n z)
    (measurable_normalizedShiftedIntensityObservable k n z)
    (ae_normalizedShiftedIntensity_pos n k hn hk z)
    (lt_of_lt_of_le zero_lt_one hs1) hs1 hc ht0 hlower

/-! ## Gaussian-surrogate GBS normalization and probability transfers -/

/-- The collision-free Gaussian-surrogate prefactor used in the paper. -/
def gaussianGBSWeightPrefactor (M K N : ℕ) (r : ℝ) : ℝ :=
  Real.tanh r ^ N / ((M : ℝ) ^ N * Real.cosh r ^ K)

/-- The Gaussian-surrogate collision-free pattern weight. -/
def gaussianGBSPatternWeight
    (M K N n : ℕ) (r : ℝ) (X : ComplexColumnMatrix n K) : ℝ :=
  gaussianGBSWeightPrefactor M K N r * ‖gramHafnianObservable n K X‖ ^ 2

/-- The reference scale multiplying the normalized intensity. -/
def gaussianGBSReferenceWeight
    (M K N n : ℕ) (r : ℝ) : ℝ :=
  gaussianGBSWeightPrefactor M K N r * gramHafnianSigma K n ^ 2

/-- Exact algebraic content of the paper's Gaussian GBS weight
normalization: `p_G = p_ref Q_0`. -/
theorem gaussianGBSPatternWeight_eq_reference_mul_normalizedIntensity
    (M K N n : ℕ) (r : ℝ) (X : ComplexColumnMatrix n K)
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) :
    gaussianGBSPatternWeight M K N n r X =
      gaussianGBSReferenceWeight M K N n r *
        normalizedShiftedIntensityObservable K n 0 X := by
  have hKpos : 0 < K := by omega
  have hsigma : 0 < gramHafnianSigma K n :=
    gramHafnianSigma_pos K n hKpos
  unfold gaussianGBSPatternWeight gaussianGBSReferenceWeight
    normalizedShiftedIntensityObservable
  simp only [sub_zero]
  field_simp [hsigma.ne']

/-- Elementary union-bound conversion from an additive error at reference
scale to a relative error.  The probability space may include arbitrary
estimator randomness; only the displayed lower-tail input is used. -/
theorem additiveToRelative_of_lowerTail
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (q pTilde : Ω → ℝ)
    {pRef eta rho gamma B : ℝ}
    (hpRef : 0 < pRef) (_heta : 0 ≤ eta) (hrho : 0 < rho)
    (hadd : mu.real {ω |
      |pTilde ω - pRef * q ω| > eta * pRef} ≤ gamma)
    (htail : mu.real {ω | q ω ≤ eta / rho} ≤ B * (eta / rho)) :
    mu.real {ω |
        |pTilde ω - pRef * q ω| > rho * (pRef * q ω)} ≤
      min 1 (gamma + B * eta / rho) := by
  let Eadd : Set Ω := {ω |
    |pTilde ω - pRef * q ω| > eta * pRef}
  let Edark : Set Ω := {ω | q ω ≤ eta / rho}
  have hsubset :
      {ω | |pTilde ω - pRef * q ω| > rho * (pRef * q ω)} ⊆
        Eadd ∪ Edark := by
    intro ω hrel
    by_cases ha : |pTilde ω - pRef * q ω| > eta * pRef
    · exact Or.inl ha
    · right
      change q ω ≤ eta / rho
      by_contra hq
      have hqrho : eta < rho * q ω := by
        simpa [mul_comm] using (div_lt_iff₀ hrho).mp (lt_of_not_ge hq)
      have hthreshold : eta * pRef < rho * (pRef * q ω) := by
        have := mul_lt_mul_of_pos_right hqrho hpRef
        nlinarith
      exact (not_lt_of_ge ((not_lt.mp ha).trans hthreshold.le)) hrel
  apply le_min
  · exact measureReal_le_one
  · calc
      mu.real {ω |
          |pTilde ω - pRef * q ω| > rho * (pRef * q ω)} ≤
          mu.real (Eadd ∪ Edark) := measureReal_mono hsubset
      _ ≤ mu.real Eadd + mu.real Edark := measureReal_union_le _ _
      _ ≤ gamma + B * (eta / rho) := add_le_add hadd htail
      _ = gamma + B * eta / rho := by ring

/-- Paper specific additive to relative transfer.  The random experiment may
contain arbitrary estimator randomness.  The measurable instance coordinate
is required to have the exact Gaussian matrix marginal; consequently the
lower tail premise of `additiveToRelative_of_lowerTail` is discharged by the
Article's normalized shifted intensity theorem rather than left as an
additional assumption. -/
theorem gaussianGBSAdditiveToRelative
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (instanceMatrix : Ω → ComplexColumnMatrix n k)
    (hinstance : Measurable instanceMatrix)
    (hinstanceLaw : Measure.map instanceMatrix mu =
      circularGaussianColumnMatrixMeasure n k)
    (pTilde : Ω → ℝ)
    {pRef eta rho deltaAdd : ℝ}
    (hpRef : 0 < pRef) (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hadd : mu.real {ω |
      |pTilde ω - pRef * normalizedShiftedIntensityObservable k n 0
        (instanceMatrix ω)| > eta * pRef} ≤ deltaAdd) :
    mu.real {ω |
        |pTilde ω - pRef * normalizedShiftedIntensityObservable k n 0
          (instanceMatrix ω)| >
          rho * (pRef * normalizedShiftedIntensityObservable k n 0
            (instanceMatrix ω))} ≤
      min 1 (deltaAdd + shiftedAnticoncentrationConstant k n * eta / rho) := by
  let q : Ω → ℝ := fun ω ↦
    normalizedShiftedIntensityObservable k n 0 (instanceMatrix ω)
  have ht : 0 ≤ eta / rho := div_nonneg heta hrho.le
  have hset : MeasurableSet
      {X | normalizedShiftedIntensityObservable k n 0 X ≤ eta / rho} :=
    measurableSet_le
      (measurable_normalizedShiftedIntensityObservable k n 0) measurable_const
  have htail :
      mu.real {ω | q ω ≤ eta / rho} ≤
        shiftedAnticoncentrationConstant k n * (eta / rho) := by
    have hgaussian :=
      (normalizedShiftedIntensity_lowerTail n k hn hk 0 (eta / rho) ht).trans
        (min_le_right _ _)
    rw [← hinstanceLaw, map_measureReal_apply hinstance hset] at hgaussian
    simpa [q] using hgaussian
  simpa [q] using
    additiveToRelative_of_lowerTail mu q pTilde hpRef heta hrho hadd htail

/-! ## Real-valued denominator resolution -/

/-- AC3 with the manuscript's real nonnegative bit parameter. -/
theorem normalizedDenominatorResolutionReal
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (b : ℝ) :
    (circularGaussianColumnMatrixMeasure n k).real
        {X | normalizedShiftedIntensityObservable k n z X ≤
          (2 : ℝ) ^ (-b)} ≤
      min 1 (shiftedAnticoncentrationConstant k n * (2 : ℝ) ^ (-b)) := by
  apply normalizedShiftedIntensity_lowerTail n k hn hk z
  positivity

/-- The literal base-two logarithmic budget printed in AC3. -/
theorem normalizedDenominatorResolutionReal_of_logBudget
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (b : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hbudget : Real.logb 2
      (shiftedAnticoncentrationConstant k n / delta) ≤ b) :
    (circularGaussianColumnMatrixMeasure n k).real
        {X | normalizedShiftedIntensityObservable k n z X ≤
          (2 : ℝ) ^ (-b)} ≤ delta := by
  have hB := shiftedAnticoncentrationConstant_pos n k hn hk
  have hpow : (2 : ℝ) ^ (-b) ≤
      (2 : ℝ) ^ (-Real.logb 2
        (shiftedAnticoncentrationConstant k n / delta)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hbudget)
  have hlogpow :
      (2 : ℝ) ^ (-Real.logb 2
        (shiftedAnticoncentrationConstant k n / delta)) =
        delta / shiftedAnticoncentrationConstant k n := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1) (div_pos hB hdelta)]
    field_simp [hB.ne', hdelta.ne']
  have hscalar :
      shiftedAnticoncentrationConstant k n * (2 : ℝ) ^ (-b) ≤ delta := by
    calc
      shiftedAnticoncentrationConstant k n * (2 : ℝ) ^ (-b) ≤
          shiftedAnticoncentrationConstant k n *
            (2 : ℝ) ^ (-Real.logb 2
              (shiftedAnticoncentrationConstant k n / delta)) :=
        mul_le_mul_of_nonneg_left hpow hB.le
      _ = delta := by rw [hlogpow]; field_simp [hB.ne']
  exact (normalizedDenominatorResolutionReal n k hn hk z b).trans
    ((min_le_right _ _).trans hscalar)

end
end LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration
