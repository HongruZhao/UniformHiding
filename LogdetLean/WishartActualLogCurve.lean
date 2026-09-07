import LogdetLean.WishartIdentityTransformODE
import LogdetLean.WishartPopulationLogDerivative
import LogdetLean.WishartComplexMGF
import LogdetLean.WishartLogDetMoments
import LogdetLean.GeneralRLeadingVarianceAlgebra
import Mathlib.Tactic

/-!
# A global branch-free log-derivative curve for the actual leading statistic

This module combines the exact Gamma-product transform with the identity and
population derivative packages.  It proves the ODE for the actual transform,
then restricts it to the characteristic-function axis.  The resulting real
frequency logarithmic derivative has exact first and second derivatives and
the global third-cumulant envelope from Zhao, arXiv:2608.00565v1, Lemma 5.4.
-/

namespace LogdetLean

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

/-- The complex logarithmic derivative of the centered actual transform. -/
def actualWishartComplexLogDerivative {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (z : ℂ) : ℂ :=
  ((-GeneralRDecomposition.W0LogDetMean m p + (p : ℝ) : ℝ) : ℂ) +
    wishartIdentityLogDerivative m p z +
    wishartPopulationCorrectionOne R (m : ℝ) z

/-- First complex derivative of the preceding logarithmic derivative. -/
def actualWishartComplexLogDerivativeOne {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (z : ℂ) : ℂ :=
  wishartIdentityLogDerivativeOne m p z +
    wishartPopulationCorrectionTwo R (m : ℝ) z

/-- Second complex derivative; this is the raw third cumulant function. -/
def actualWishartComplexLogDerivativeTwo {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (z : ℂ) : ℂ :=
  wishartIdentityLogDerivativeTwo m p z +
    wishartPopulationCorrectionThree R (m : ℝ) z

/-- Exact complex ODE for the actual branch-safe transform on the imaginary
axis. -/
theorem hasDerivAt_actualWishartComplexTransform_axis
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m)
    (R : CorrelationMatrix p) (u : ℝ) :
    HasDerivAt (actualWishartComplexTransform m R)
      (actualWishartComplexLogDerivative m R ((u : ℂ) * Complex.I) *
        actualWishartComplexTransform m R ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  let z : ℂ := (u : ℂ) * Complex.I
  let c : ℂ :=
    ((-GeneralRDecomposition.W0LogDetMean m p + (p : ℝ) : ℝ) : ℂ)
  have hlinear : HasDerivAt (fun w : ℂ ↦ w * c) c z := by
    have hraw := (hasDerivAt_id z).mul_const c
    exact hraw.congr_deriv (by ring)
  have hcenter := hlinear.cexp
  have hI := hasDerivAt_complexWishartIdentityTransform_axis hm hpm u
  have hD := hasDerivAt_wishartPopulationCorrection_axis R
    (show (0 : ℝ) < m by exact_mod_cast hm) u
  have hDexp := hD.cexp
  have hraw := (hcenter.mul hI).mul hDexp
  have hraw' := hraw.congr_deriv (show
      (Complex.exp (z * c) * c *
            complexWishartIdentityTransform m p z +
          Complex.exp (z * c) *
            (wishartIdentityLogDerivative m p z *
              complexWishartIdentityTransform m p z)) *
            Complex.exp (wishartPopulationCorrection R (m : ℝ) z) +
        (Complex.exp (z * c) * complexWishartIdentityTransform m p z) *
          (Complex.exp (wishartPopulationCorrection R (m : ℝ) z) *
            wishartPopulationCorrectionOne R (m : ℝ) z) =
      (c + wishartIdentityLogDerivative m p z +
          wishartPopulationCorrectionOne R (m : ℝ) z) *
        (Complex.exp (z * c) *
          (complexWishartIdentityTransform m p z *
            Complex.exp (wishartPopulationCorrection R (m : ℝ) z))) by
    ring)
  have heq : actualWishartComplexTransform m R =
      ((fun w : ℂ ↦ Complex.exp (w * c)) *
        complexWishartIdentityTransform m p) *
        (fun w : ℂ ↦
          Complex.exp (wishartPopulationCorrection R (m : ℝ) w)) := by
    funext w
    unfold actualWishartComplexTransform
    rw [complexWishartCorrelationTransform_eq_identity_mul_exp_correction]
    dsimp [c]
    ring
  rw [heq]
  unfold actualWishartComplexLogDerivative
  dsimp [z, c]
  apply hraw'.congr_deriv
  ring

/-- First differentiation of the actual complex logarithmic derivative. -/
theorem hasDerivAt_actualWishartComplexLogDerivative_axis
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) (u : ℝ) :
    HasDerivAt (actualWishartComplexLogDerivative m R)
      (actualWishartComplexLogDerivativeOne m R ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  have hmNat : 0 < m := by
    have hpNat := h.1
    have hpm := h.2
    omega
  unfold actualWishartComplexLogDerivative
    actualWishartComplexLogDerivativeOne
  have hbase := (hasDerivAt_wishartIdentityLogDerivative_axis h u).const_add
    (((-GeneralRDecomposition.W0LogDetMean m p + (p : ℝ) : ℝ) : ℂ))
  have hsum := hbase.add
    (hasDerivAt_wishartPopulationCorrectionOne_axis R
      (show (0 : ℝ) < m by exact_mod_cast hmNat) u)
  convert hsum using 1 <;> rfl

/-- Second differentiation of the actual complex logarithmic derivative. -/
theorem hasDerivAt_actualWishartComplexLogDerivativeOne_axis
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) (u : ℝ) :
    HasDerivAt (actualWishartComplexLogDerivativeOne m R)
      (actualWishartComplexLogDerivativeTwo m R ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  have hmNat : 0 < m := by
    have hpNat := h.1
    have hpm := h.2
    omega
  unfold actualWishartComplexLogDerivativeOne
    actualWishartComplexLogDerivativeTwo
  exact (hasDerivAt_wishartIdentityLogDerivativeOne_axis h u).add
    (hasDerivAt_wishartPopulationCorrectionTwo_axis R
      (show (0 : ℝ) < m by exact_mod_cast hmNat) u)

/-- Actual transform on the characteristic-function frequency axis. -/
def actualWishartFrequencyCurve {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (t : ℝ) : ℂ :=
  actualWishartComplexTransform m R ((t : ℂ) * Complex.I)

/-- Real-frequency logarithmic derivative `h'(t)`. -/
def actualWishartFrequencyLogDerivative {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (t : ℝ) : ℂ :=
  Complex.I *
    actualWishartComplexLogDerivative m R ((t : ℂ) * Complex.I)

/-- Its first derivative `h''(t)`. -/
def actualWishartFrequencyLogDerivativeOne {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (t : ℝ) : ℂ :=
  -actualWishartComplexLogDerivativeOne m R ((t : ℂ) * Complex.I)

/-- Its second derivative `h'''(t)`. -/
def actualWishartFrequencyLogDerivativeTwo {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (t : ℝ) : ℂ :=
  -Complex.I *
    actualWishartComplexLogDerivativeTwo m R ((t : ℂ) * Complex.I)

private theorem hasDerivAt_mul_I_complex (u : ℝ) :
    HasDerivAt (fun z : ℂ ↦ z * Complex.I) Complex.I (u : ℂ) := by
  have hraw := (hasDerivAt_id (u : ℂ)).mul_const Complex.I
  exact hraw.congr_deriv (by ring)

/-- Frequency-curve ODE `F'=gF`. -/
theorem hasDerivAt_actualWishartFrequencyCurve
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m)
    (R : CorrelationMatrix p) (u : ℝ) :
    HasDerivAt (actualWishartFrequencyCurve m R)
      (actualWishartFrequencyLogDerivative m R u *
        actualWishartFrequencyCurve m R u) u := by
  have hc := (hasDerivAt_actualWishartComplexTransform_axis hm hpm R u).comp
    (u : ℂ) (hasDerivAt_mul_I_complex u)
  have hr := hc.comp_ofReal
  unfold actualWishartFrequencyCurve actualWishartFrequencyLogDerivative
  apply hr.congr_deriv
  ring

/-- First derivative of the frequency logarithmic derivative. -/
theorem hasDerivAt_actualWishartFrequencyLogDerivative
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) (u : ℝ) :
    HasDerivAt (actualWishartFrequencyLogDerivative m R)
      (actualWishartFrequencyLogDerivativeOne m R u) u := by
  have hc := (hasDerivAt_actualWishartComplexLogDerivative_axis h R u).comp
    (u : ℂ) (hasDerivAt_mul_I_complex u)
  have hcI := hc.const_mul Complex.I
  have hr := hcI.comp_ofReal
  unfold actualWishartFrequencyLogDerivative
    actualWishartFrequencyLogDerivativeOne
  apply hr.congr_deriv
  calc
    Complex.I * (actualWishartComplexLogDerivativeOne m R
        ((u : ℂ) * Complex.I) * Complex.I) =
        (Complex.I * Complex.I) *
          actualWishartComplexLogDerivativeOne m R
            ((u : ℂ) * Complex.I) := by ring
    _ = -actualWishartComplexLogDerivativeOne m R
          ((u : ℂ) * Complex.I) := by
      rw [Complex.I_mul_I]
      ring

/-- Second derivative of the frequency logarithmic derivative. -/
theorem hasDerivAt_actualWishartFrequencyLogDerivativeOne
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) (u : ℝ) :
    HasDerivAt (actualWishartFrequencyLogDerivativeOne m R)
      (actualWishartFrequencyLogDerivativeTwo m R u) u := by
  have hc := (hasDerivAt_actualWishartComplexLogDerivativeOne_axis h R u).comp
    (u : ℂ) (hasDerivAt_mul_I_complex u)
  have hcneg := hc.neg
  have hr := hcneg.comp_ofReal
  unfold actualWishartFrequencyLogDerivativeOne
    actualWishartFrequencyLogDerivativeTwo
  apply hr.congr_deriv
  ring

/-- Zero lies in the interior of the real exponential-integrability domain
of the actual leading statistic. -/
theorem zero_mem_interior_integrableExpSet_M_R
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m)
    (R : CorrelationMatrix p) :
    (0 : ℝ) ∈ interior
      (integrableExpSet (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p)) := by
  have hr := wishartComplexMGFRadius_pos hm R
  apply interior_maximal
  · intro t ht
    change -wishartComplexMGFRadius m R < t ∧
      t < wishartComplexMGFRadius m R at ht
    exact integrable_exp_mul_M_R_of_abs_lt_radius hm hpm R
      (by simpa [abs_lt] using ht)
  · exact isOpen_Ioo
  · exact ⟨by linarith, by linarith⟩

/-- Exponential integrability gives ordinary integrability of the actual
leading statistic. -/
theorem integrable_M_R_from_exact_transform
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m)
    (R : CorrelationMatrix p) :
    Integrable (GeneralRDecomposition.M_R m R)
      (standardGaussianDataMeasure m p) :=
  integrable_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_M_R hm hpm R)

/-- The exact transform also gives square integrability of `M_R`. -/
theorem memLp_M_R_two_from_exact_transform
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m)
    (R : CorrelationMatrix p) :
    MemLp (GeneralRDecomposition.M_R m R) 2
      (standardGaussianDataMeasure m p) := by
  apply (memLp_two_iff_integrable_sq
    (GeneralRDecomposition.measurable_M_R m R).aestronglyMeasurable).2
  exact integrable_pow_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_M_R hm hpm R) 2

/-- Exact centering of `M_R` under the original Gaussian data measure. -/
theorem integral_M_R_eq_zero_from_exact_transform
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m)
    (R : CorrelationMatrix p) :
    ∫ z, GeneralRDecomposition.M_R m R z
        ∂standardGaussianDataMeasure m p = 0 := by
  have hW : Integrable (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det)
      (standardGaussianDataMeasure m p) :=
    (memLp_log_det_W0_two hm hpm).integrable (by norm_num)
  exact GeneralRDecomposition.integral_M_R_eq_zero R hW

/-- The actual transform is normalized at frequency zero. -/
@[simp]
theorem actualWishartComplexTransform_zero
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m)
    (R : CorrelationMatrix p) :
    actualWishartComplexTransform m R 0 = 1 := by
  have hmgf := complexMGF_M_R_imaginary hm hpm R 0
  simpa [complexMGF] using hmgf.symm

/-- Exact centering of the branch-free logarithmic derivative. -/
theorem actualWishartComplexLogDerivative_zero
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) :
    actualWishartComplexLogDerivative m R 0 = 0 := by
  have hm : 0 < m := by
    have hpNat := h.1
    have hpm := h.2
    omega
  have hW : Integrable (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det)
      (standardGaussianDataMeasure m p) :=
    (memLp_log_det_W0_two hm h.2).integrable (by norm_num)
  have hmean := GeneralRDecomposition.integral_M_R_eq_zero R hW
  have hr := wishartComplexMGFRadius_pos hm R
  have hzeroInterior : (0 : ℝ) ∈ interior
      (integrableExpSet (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p)) := by
    apply interior_maximal
    · intro t ht
      change -wishartComplexMGFRadius m R < t ∧
        t < wishartComplexMGFRadius m R at ht
      exact integrable_exp_mul_M_R_of_abs_lt_radius hm h.2 R
        (by simpa [abs_lt] using ht)
    · exact isOpen_Ioo
    · exact ⟨by linarith, by linarith⟩
  have hmgf0 := hasDerivAt_complexMGF
    (X := GeneralRDecomposition.M_R m R)
    (μ := standardGaussianDataMeasure m p)
    (z := (0 : ℂ)) hzeroInterior
  have hmgf : HasDerivAt
      (complexMGF (GeneralRDecomposition.M_R m R)
      (standardGaussianDataMeasure m p)) 0 0 := by
    apply hmgf0.congr_deriv
    simp only [zero_mul, Complex.exp_zero, mul_one]
    rw [integral_complex_ofReal, hmean, Complex.ofReal_zero]
  have hmem : (0 : ℂ) ∈ wishartComplexMGFStrip m R := by
    simpa using imaginary_mem_wishartComplexMGFStrip hm R 0
  have hevent :
      (complexMGF (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p)) =ᶠ[nhds (0 : ℂ)]
      actualWishartComplexTransform m R := by
    filter_upwards
      [(isOpen_wishartComplexMGFStrip m R).eventually_mem hmem] with z hz
    exact eqOn_complexMGF_M_R_actualWishartComplexTransform hm h.2 R hz
  have hmgfAsActual := hmgf.congr_of_eventuallyEq hevent.symm
  have hactual := hasDerivAt_actualWishartComplexTransform_axis hm h.2 R 0
  have hactual' : HasDerivAt (actualWishartComplexTransform m R)
      (actualWishartComplexLogDerivative m R 0 *
        actualWishartComplexTransform m R 0) 0 := by
    simpa using hactual
  have hderiv := hmgfAsActual.unique hactual'
  rw [actualWishartComplexTransform_zero hm h.2 R] at hderiv
  simpa using hderiv.symm

@[simp]
theorem actualWishartFrequencyLogDerivative_zero
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) :
    actualWishartFrequencyLogDerivative m R 0 = 0 := by
  simp [actualWishartFrequencyLogDerivative,
    actualWishartComplexLogDerivative_zero h R]

/-- Exact negative variance at the origin. -/
theorem actualWishartFrequencyLogDerivativeOne_zero
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) :
    actualWishartFrequencyLogDerivativeOne m R 0 =
      (-(generalRLeadingVarianceSq m R) : ℝ) := by
  unfold actualWishartFrequencyLogDerivativeOne
    actualWishartComplexLogDerivativeOne
  simp only [Complex.ofReal_zero, zero_mul]
  have hmNat : 0 < m := by
    have hpNat := h.1
    have hpm := h.2
    omega
  rw [wishartIdentityLogDerivativeOne_zero h,
    wishartPopulationCorrectionTwo_zero R
      (show (0 : ℝ) < m by exact_mod_cast hmNat)]
  unfold generalRLeadingVarianceSq generalRVarianceProxy
  push_cast
  ring

/-- Exact global third-derivative envelope for the actual leading term. -/
def generalRLeadingThirdEnvelope {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) : ℝ :=
  nullASeries m p + 16 * (p : ℝ) / (m : ℝ) ^ 3 +
    (12 * R.deviationEnergy) / (m : ℝ) ^ 2 +
    (8 * (Real.sqrt R.deviationEnergy * R.deviationEnergy)) /
      (m : ℝ) ^ 2

theorem norm_actualWishartFrequencyLogDerivativeTwo_le
    {m p : ℕ} (h : Admissible m p)
    (R : CorrelationMatrix p) (u : ℝ) :
    ‖actualWishartFrequencyLogDerivativeTwo m R u‖ ≤
      generalRLeadingThirdEnvelope m R := by
  have hmNat : 0 < m := by
    have hpNat := h.1
    have hpm := h.2
    omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmNat
  unfold actualWishartFrequencyLogDerivativeTwo
    actualWishartComplexLogDerivativeTwo generalRLeadingThirdEnvelope
  rw [norm_mul, norm_neg, Complex.norm_I,
    one_mul, wishartIdentityLogDerivativeTwo_axis]
  calc
    ‖wishartIdentityThirdAxis m p u +
        wishartPopulationCorrectionThree R (m : ℝ)
          ((u : ℂ) * Complex.I)‖ ≤
        ‖wishartIdentityThirdAxis m p u‖ +
          ‖wishartPopulationCorrectionThree R (m : ℝ)
            ((u : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ ≤ (nullASeries m p + 16 * (p : ℝ) / (m : ℝ) ^ 3) +
        ((12 * R.deviationEnergy) / (m : ℝ) ^ 2 +
          (8 * (Real.sqrt R.deviationEnergy * R.deviationEnergy)) /
            (m : ℝ) ^ 2) :=
      add_le_add (norm_wishartIdentityThirdAxis_le h u)
        (norm_wishartPopulationCorrectionThree_imaginary_le R hmR)
    _ = nullASeries m p + 16 * (p : ℝ) / (m : ℝ) ^ 3 +
        (12 * R.deviationEnergy) / (m : ℝ) ^ 2 +
        (8 * (Real.sqrt R.deviationEnergy * R.deviationEnergy)) /
          (m : ℝ) ^ 2 := by ring

end

end LogdetLean
