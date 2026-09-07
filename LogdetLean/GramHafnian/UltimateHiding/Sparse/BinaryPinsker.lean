import LogdetLean.GramHafnian.UltimateHiding.Sparse.TotalVariationInterface
import Mathlib.Analysis.Convex.Deriv

/-!
# Binary Pinsker inequality

This file proves the analytic step that was previously left as the proposition
`rnEventPinskerLowerBound`.  The scalar core is the four strong convexity of
binary negative entropy on `[0,1]`.  Applying Jensen separately on an event
and its complement gives the eventwise Radon Nikodym inequality, hence the
project's concrete probability total variation version of Pinsker.
-/

open MeasureTheory Set Real

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- Negative binary entropy, continuously extended to the endpoints. -/
def binaryEntropyPotential (x : ℝ) : ℝ :=
  x * Real.log x + (1 - x) * Real.log (1 - x)

/-- Subtracting the quadratic associated with four strong convexity. -/
def binaryPinskerCore (x : ℝ) : ℝ :=
  binaryEntropyPotential x - 2 * x ^ 2

def binaryPinskerCoreDeriv (x : ℝ) : ℝ :=
  Real.log x - Real.log (1 - x) - 4 * x

def binaryPinskerCoreDeriv2 (x : ℝ) : ℝ :=
  x⁻¹ + (1 - x)⁻¹ - 4

theorem continuous_binaryPinskerCore : Continuous binaryPinskerCore := by
  unfold binaryPinskerCore binaryEntropyPotential
  fun_prop

theorem hasDerivAt_binaryPinskerCore {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt binaryPinskerCore (binaryPinskerCoreDeriv x) x := by
  unfold binaryPinskerCore binaryEntropyPotential binaryPinskerCoreDeriv
  convert (Real.hasDerivAt_mul_log hx0).add
    ((Real.hasDerivAt_mul_log (sub_ne_zero.mpr hx1.symm)).comp x
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))) |>.sub
        ((hasDerivAt_const x 2).mul (hasDerivAt_pow 2 x)) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_binaryPinskerCoreDeriv {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt binaryPinskerCoreDeriv (binaryPinskerCoreDeriv2 x) x := by
  unfold binaryPinskerCoreDeriv binaryPinskerCoreDeriv2
  have honeSub : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hleft := Real.hasDerivAt_log hx0
  have hright := (Real.hasDerivAt_log honeSub).comp x
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
  have hlinear := (hasDerivAt_const x 4).mul (hasDerivAt_id x)
  convert (hleft.sub hright).sub hlinear using 1
  all_goals first | rfl | ring

theorem binaryPinskerCoreDeriv2_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ binaryPinskerCoreDeriv2 x := by
  unfold binaryPinskerCoreDeriv2
  have hx0 : 0 < x := hx.1
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hid : x⁻¹ + (1 - x)⁻¹ - 4 =
      (2 * x - 1) ^ 2 / (x * (1 - x)) := by
    field_simp
    ring
  rw [hid]
  positivity

/-- Binary negative entropy is four strongly convex on the probability
interval, stated in the equivalent convex core form. -/
theorem convexOn_binaryPinskerCore :
    ConvexOn ℝ (Icc (0 : ℝ) 1) binaryPinskerCore := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
    continuous_binaryPinskerCore.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_binaryPinskerCore hx.1.ne' hx.2.ne).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_binaryPinskerCoreDeriv hx.1.ne' hx.2.ne).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact binaryPinskerCoreDeriv2_nonneg hx

/-- The scalar binary relative entropy written with `klFun`. -/
def binaryKLDivergence (p q : ℝ) : ℝ :=
  q * InformationTheory.klFun (p / q) +
    (1 - q) * InformationTheory.klFun ((1 - p) / (1 - q))

def binaryEntropyPotentialDeriv (x : ℝ) : ℝ :=
  Real.log x - Real.log (1 - x)

/-- Supporting line inequality for the convex core, including both endpoints
for the first argument. -/
theorem binaryPinskerCore_tangent
    {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    binaryPinskerCore q + binaryPinskerCoreDeriv q * (p - q) ≤
      binaryPinskerCore p := by
  have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
  have hderiv := hasDerivAt_binaryPinskerCore hq.1.ne' hq.2.ne
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · have hslope := convexOn_binaryPinskerCore.slope_le_of_hasDerivAt
      hp hq' hpq hderiv
    rw [slope_def_field] at hslope
    have hmul := (div_le_iff₀ (sub_pos.mpr hpq)).mp hslope
    linarith
  · simp
  · have hslope := convexOn_binaryPinskerCore.le_slope_of_hasDerivAt
      hq' hp hqp hderiv
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hqp)).mp hslope
    linarith

/-- Four strong convexity in Bregman divergence form. -/
theorem binaryEntropyPotential_bregman_lower
    {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤
      binaryEntropyPotential p - binaryEntropyPotential q -
        binaryEntropyPotentialDeriv q * (p - q) := by
  have h := binaryPinskerCore_tangent hp hq
  unfold binaryPinskerCore binaryPinskerCoreDeriv at h
  unfold binaryEntropyPotentialDeriv
  nlinarith

/-- The `klFun` formula is the Bregman divergence of binary negative entropy.
The endpoint cases use the continuous convention `0 * log 0 = 0`. -/
theorem binaryKLDivergence_eq_bregman
    {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    binaryKLDivergence p q =
      binaryEntropyPotential p - binaryEntropyPotential q -
        binaryEntropyPotentialDeriv q * (p - q) := by
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  rcases eq_or_ne p 0 with rfl | hp0
  · unfold binaryKLDivergence binaryEntropyPotential binaryEntropyPotentialDeriv
    simp only [zero_div, sub_zero, InformationTheory.klFun_zero,
      zero_mul, one_mul, Real.log_zero, Real.log_one, add_zero]
    rw [InformationTheory.klFun_apply]
    rw [Real.log_div one_ne_zero hq1]
    simp only [Real.log_one, zero_sub]
    field_simp
    ring
  rcases eq_or_ne p 1 with rfl | hp1
  · unfold binaryKLDivergence binaryEntropyPotential binaryEntropyPotentialDeriv
    simp only [sub_self, zero_div, InformationTheory.klFun_zero,
      zero_mul, one_mul, Real.log_zero, Real.log_one, add_zero]
    rw [InformationTheory.klFun_apply]
    rw [Real.log_div one_ne_zero hq0]
    simp only [Real.log_one, zero_sub]
    field_simp
    ring
  · have hpOne : 1 - p ≠ 0 := sub_ne_zero.mpr hp1.symm
    unfold binaryKLDivergence binaryEntropyPotential binaryEntropyPotentialDeriv
    rw [InformationTheory.klFun_apply, InformationTheory.klFun_apply,
      Real.log_div hp0 hq0, Real.log_div hpOne hq1]
    field_simp
    ring

/-- Scalar binary Pinsker inequality in the probability convention. -/
theorem binary_pinsker
    {p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    (hqzero : q = 0 → p = 0) (hqone : q = 1 → p = 1) :
    2 * (p - q) ^ 2 ≤ binaryKLDivergence p q := by
  rcases eq_or_lt_of_le hq.1 with rfl | hq0
  · simp [hqzero rfl, binaryKLDivergence, InformationTheory.klFun_zero,
      InformationTheory.klFun_one]
  rcases eq_or_lt_of_le hq.2 with hq1 | hq1
  · have hp1 := hqone hq1
    subst p
    subst q
    simp [binaryKLDivergence, InformationTheory.klFun_one]
  · rw [binaryKLDivergence_eq_bregman hp ⟨hq0, hq1⟩]
    exact binaryEntropyPotential_bregman_lower hp ⟨hq0, hq1⟩

/-- Restricting both measures to the same measurable set preserves the
Radon Nikodym derivative on that restricted space. -/
theorem rnDeriv_restrict_both
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmunu : mu ≪ nu) {s : Set X} (hs : MeasurableSet s) :
    (mu.restrict s).rnDeriv (nu.restrict s) =ᵐ[nu.restrict s] mu.rnDeriv nu := by
  have hrest : mu.restrict s =
      (nu.restrict s).withDensity (mu.rnDeriv nu) := by
    rw [← restrict_withDensity hs,
      Measure.withDensity_rnDeriv_eq mu nu hmunu]
  rw [hrest]
  exact Measure.rnDeriv_withDensity₀ (nu.restrict s)
    (Measure.measurable_rnDeriv mu nu).aemeasurable

/-- Jensen's inequality on one cell of a measurable binary partition. -/
theorem binary_cell_kl_le_setIntegral
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmunu : mu ≪ nu)
    (hkl : Integrable
      (fun x ↦ InformationTheory.klFun (mu.rnDeriv nu x).toReal) nu)
    {s : Set X} (hs : MeasurableSet s) :
    nu.real s * InformationTheory.klFun (mu.real s / nu.real s) ≤
      ∫ x in s, InformationTheory.klFun (mu.rnDeriv nu x).toReal ∂nu := by
  have hrn := rnDeriv_restrict_both mu nu hmunu hs
  have hint : Integrable
      (fun x ↦ InformationTheory.klFun
        ((mu.restrict s).rnDeriv (nu.restrict s) x).toReal)
      (nu.restrict s) := by
    refine (integrable_congr ?_).mpr hkl.integrableOn
    filter_upwards [hrn] with x hx
    rw [hx]
  have hjensen := mul_le_integral_rnDeriv_of_ac
    InformationTheory.convexOn_klFun
    InformationTheory.continuous_klFun.continuousWithinAt
    hint (hmunu.restrict s)
  have hrnReal :
      (fun x ↦ InformationTheory.klFun
        ((mu.restrict s).rnDeriv (nu.restrict s) x).toReal) =ᵐ[nu.restrict s]
      (fun x ↦ InformationTheory.klFun (mu.rnDeriv nu x).toReal) := by
    filter_upwards [hrn] with x hx
    rw [hx]
  rw [integral_congr_ae hrnReal] at hjensen
  simpa [measureReal_def, hs] using hjensen

/-- The complete two cell Radon Nikodym inequality.  Finiteness of relative
entropy is expressed by integrability of the log likelihood ratio; this is
necessary because Mathlib's `ENNReal.toReal ∞` and undefined Bochner
integrals are both zero. -/
theorem rnEventPinskerLowerBound_of_integrable
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmunu : mu ≪ nu) (hllr : Integrable (llr mu nu) mu) :
    rnEventPinskerLowerBound mu nu := by
  have hkl : Integrable
      (fun x ↦ InformationTheory.klFun (mu.rnDeriv nu x).toReal) nu :=
    (InformationTheory.integrable_klFun_rnDeriv_iff hmunu).2 hllr
  intro s hs
  have hp : mu.real s ∈ Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hq : nu.real s ∈ Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hqzero : nu.real s = 0 → mu.real s = 0 := by
    intro hz
    rw [measureReal_eq_zero_iff] at hz ⊢
    exact hmunu hz
  have hqone : nu.real s = 1 → mu.real s = 1 := by
    intro hone
    have hnucompReal : nu.real sᶜ = 0 := by
      rw [measureReal_compl hs, probReal_univ, hone]
      ring
    have hnucomp : nu sᶜ = 0 := (measureReal_eq_zero_iff).mp hnucompReal
    have hmucomp : mu sᶜ = 0 := hmunu hnucomp
    have hmucompReal : mu.real sᶜ = 0 := (measureReal_eq_zero_iff).mpr hmucomp
    have hmass := measureReal_add_measureReal_compl (μ := mu) hs
    rw [probReal_univ, hmucompReal] at hmass
    linarith
  have hbinary := binary_pinsker hp hq hqzero hqone
  have hcell := binary_cell_kl_le_setIntegral mu nu hmunu hkl hs
  have hcellc := binary_cell_kl_le_setIntegral mu nu hmunu hkl hs.compl
  rw [measureReal_compl hs, measureReal_compl hs,
    probReal_univ, probReal_univ] at hcellc
  have hpartition : binaryKLDivergence (mu.real s) (nu.real s) ≤
      ∫ x in s, InformationTheory.klFun (mu.rnDeriv nu x).toReal ∂nu +
        ∫ x in sᶜ, InformationTheory.klFun (mu.rnDeriv nu x).toReal ∂nu := by
    exact add_le_add hcell hcellc
  have hfull : binaryKLDivergence (mu.real s) (nu.real s) ≤
      ∫ x, InformationTheory.klFun (mu.rnDeriv nu x).toReal ∂nu := by
    rw [← integral_add_compl hs hkl]
    exact hpartition
  rw [← event_difference_eq_setIntegral_rnDeriv_sub_one mu nu hmunu s]
  rw [sq_abs]
  exact hbinary.trans hfull

/-- Eventwise squared Pinsker with Mathlib's literal KL divergence. -/
theorem eventwisePinskerKLLowerBound_of_integrable
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmunu : mu ≪ nu) (hllr : Integrable (llr mu nu) mu) :
    eventwisePinskerKLLowerBound mu nu := by
  exact eventwisePinskerKLLowerBound_of_rn mu nu hmunu
    (rnEventPinskerLowerBound_of_integrable mu nu hmunu hllr)

/-- Concrete Pinsker theorem for the exact probability total variation
convention used in the sparse hiding development. -/
theorem probabilityTotalVariationLE_pinsker
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmunu : mu ≪ nu) (hllr : Integrable (llr mu nu) mu) :
    probabilityTotalVariationLE mu nu
      (Real.sqrt ((InformationTheory.klDiv mu nu).toReal / 2)) := by
  exact probabilityTotalVariationLE_of_eventwisePinskerKLLowerBound mu nu
    (eventwisePinskerKLLowerBound_of_integrable mu nu hmunu hllr)

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
