import LogdetLean.GramHafnian.CurrentPRL.MixtureDensity

/-!
# Centered disks maximize circular Gaussian mass

This is the two-dimensional Anderson inequality needed for literal
small-ball centering.  The proof is elementary: reflection in the midpoint
between the two disk centers bijects the two pieces of their symmetric
difference, preserves Lebesgue measure, and moves every point of the outer
piece toward the origin.  The exact radial Gaussian density then gives the
comparison.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Reflection in the midpoint `z / 2`. -/
def complexMidpointReflection (z x : ℂ) : ℂ := z - x

@[fun_prop] theorem measurable_complexMidpointReflection (z : ℂ) :
    Measurable (complexMidpointReflection z) := by
  unfold complexMidpointReflection
  fun_prop

theorem measurePreserving_complexMidpointReflection (z : ℂ) :
    MeasurePreserving (complexMidpointReflection z)
      (volume : Measure ℂ) (volume : Measure ℂ) := by
  have h := (measurePreserving_add_left (volume : Measure ℂ) z).comp
    (Measure.measurePreserving_neg (volume : Measure ℂ))
  change MeasurePreserving (fun x : ℂ ↦ z + -x)
    (volume : Measure ℂ) (volume : Measure ℂ)
  exact h

theorem complexMidpointReflection_preimage_centeredDiff
    (z : ℂ) (rho : ℝ) :
    complexMidpointReflection z ⁻¹'
        (closedBall 0 rho \ closedBall z rho) =
      closedBall z rho \ closedBall 0 rho := by
  ext x
  simp only [Set.mem_preimage, Set.mem_diff, mem_closedBall,
    complexMidpointReflection]
  constructor
  · rintro ⟨hzero, hz⟩
    constructor
    · simpa [dist_eq_norm, norm_sub_rev] using hzero
    · simpa [dist_eq_norm] using hz
  · rintro ⟨hz, hzero⟩
    constructor
    · simpa [dist_eq_norm, norm_sub_rev] using hz
    · simpa [dist_eq_norm] using hzero

theorem circularGaussianDensity_le_reflection
    (z : ℂ) (rho : ℝ) (x : ℂ)
    (hx : x ∈ closedBall z rho \ closedBall 0 rho) :
    LogdetLean.GramHafnian.currentPRLCircularGaussianDensity x ≤
      LogdetLean.GramHafnian.currentPRLCircularGaussianDensity
        (complexMidpointReflection z x) := by
  have hz : ‖z - x‖ ≤ rho := by
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hx.1
  have hxrho : rho < ‖x‖ := by
    simpa [mem_closedBall, dist_eq_norm, not_le] using hx.2
  have hnorm : ‖complexMidpointReflection z x‖ ≤ ‖x‖ := by
    dsimp [complexMidpointReflection]
    exact hz.trans hxrho.le
  unfold LogdetLean.GramHafnian.currentPRLCircularGaussianDensity
  apply ENNReal.ofReal_le_ofReal
  have hsquares : ‖complexMidpointReflection z x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  have hexp : Real.exp (-‖x‖ ^ 2) ≤
      Real.exp (-‖complexMidpointReflection z x‖ ^ 2) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hsquares)
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- A disk centered at the origin has at least as much standard circular
Gaussian mass as any translated disk of the same radius. -/
theorem circularGaussian_closedBall_le_centered
    (z : ℂ) (rho : ℝ) :
    LogdetLean.GramHafnian.circularGaussian (closedBall z rho) ≤
      LogdetLean.GramHafnian.circularGaussian (closedBall 0 rho) := by
  let dens := LogdetLean.GramHafnian.currentPRLCircularGaussianDensity
  let shifted := closedBall z rho
  let centered := closedBall (0 : ℂ) rho
  let outerShifted := shifted \ centered
  let outerCentered := centered \ shifted
  have hshifted : MeasurableSet shifted := measurableSet_closedBall
  have hcentered : MeasurableSet centered := measurableSet_closedBall
  have houterShifted : MeasurableSet outerShifted := hshifted.diff hcentered
  have houterCentered : MeasurableSet outerCentered := hcentered.diff hshifted
  have hdens : Measurable dens :=
    LogdetLean.GramHafnian.measurable_currentPRLCircularGaussianDensity
  have hreflect : MeasurePreserving (complexMidpointReflection z)
      (volume : Measure ℂ) (volume : Measure ℂ) :=
    measurePreserving_complexMidpointReflection z
  have hpre : complexMidpointReflection z ⁻¹' outerCentered = outerShifted := by
    simpa [outerCentered, outerShifted, centered, shifted] using
      complexMidpointReflection_preimage_centeredDiff z rho
  have houter :
      ((volume : Measure ℂ).withDensity dens) outerShifted ≤
        ((volume : Measure ℂ).withDensity dens) outerCentered := by
    rw [withDensity_apply _ houterShifted, withDensity_apply _ houterCentered]
    calc
      (∫⁻ x in outerShifted, dens x ∂(volume : Measure ℂ)) ≤
          ∫⁻ x in outerShifted, dens (complexMidpointReflection z x)
            ∂(volume : Measure ℂ) := by
        apply setLIntegral_mono (hdens.comp (measurable_complexMidpointReflection z))
        intro x hx
        exact circularGaussianDensity_le_reflection z rho x (by
          simpa [outerShifted, shifted, centered] using hx)
      _ = ∫⁻ x in outerCentered, dens x ∂(volume : Measure ℂ) := by
        rw [← hpre]
        exact hreflect.setLIntegral_comp_preimage houterCentered hdens
  rw [LogdetLean.GramHafnian.circularGaussian_eq_withDensity_currentPRL]
  have hshiftDecomp := measure_inter_add_diff
    (μ := (volume : Measure ℂ).withDensity dens) shifted hcentered
  have hcenterDecomp := measure_inter_add_diff
    (μ := (volume : Measure ℂ).withDensity dens) centered hshifted
  change ((volume : Measure ℂ).withDensity dens) shifted ≤
    ((volume : Measure ℂ).withDensity dens) centered
  rw [← hshiftDecomp, ← hcenterDecomp]
  rw [inter_comm centered shifted]
  simpa [add_comm] using add_le_add_left houter
    (((volume : Measure ℂ).withDensity dens) (shifted ∩ centered))

/-- Equivalent norm-event formulation. -/
theorem circularGaussian_norm_sub_le_centered
    (z : ℂ) (rho : ℝ) :
    LogdetLean.GramHafnian.circularGaussian {x : ℂ | ‖x - z‖ ≤ rho} ≤
      LogdetLean.GramHafnian.circularGaussian {x : ℂ | ‖x‖ ≤ rho} := by
  simpa [closedBall, dist_eq_norm, norm_sub_rev] using
    circularGaussian_closedBall_le_centered z rho

/-- The same centered-ball comparison after any nonnegative real scaling of
the circular Gaussian.  The zero-scale case is included. -/
theorem map_nonneg_smul_circularGaussian_norm_add_le_centered
    (scale : ℝ) (hscale : 0 ≤ scale) (b : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (LogdetLean.GramHafnian.circularGaussian.map
        (fun z : ℂ ↦ scale • z)) {z : ℂ | ‖z + b‖ ≤ rho} ≤
      (LogdetLean.GramHafnian.circularGaussian.map
        (fun z : ℂ ↦ scale • z)) {z : ℂ | ‖z‖ ≤ rho} := by
  have hleft : MeasurableSet {z : ℂ | ‖z + b‖ ≤ rho} :=
    measurableSet_le (by fun_prop) measurable_const
  have hright : MeasurableSet {z : ℂ | ‖z‖ ≤ rho} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.map_apply (by fun_prop) hleft,
    Measure.map_apply (by fun_prop) hright]
  by_cases hs0 : scale = 0
  · subst scale
    simp only [zero_smul, zero_add, Set.mem_setOf_eq]
    by_cases hb : ‖b‖ ≤ rho
    · simp [hb, hrho]
    · simp [hb]
  · have hspos : 0 < scale := lt_of_le_of_ne hscale (Ne.symm hs0)
    have hpreLeft :
        (fun z : ℂ ↦ scale • z) ⁻¹' {z : ℂ | ‖z + b‖ ≤ rho} =
          {z : ℂ | ‖z - ((-scale⁻¹) • b)‖ ≤ rho / scale} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      have harg : scale • z + b =
          scale • (z - ((-scale⁻¹) • b)) := by
        rw [smul_sub, smul_smul]
        have hmul : scale * -scale⁻¹ = -1 := by
          field_simp [hs0]
        rw [hmul, neg_one_smul, sub_neg_eq_add]
      rw [harg, norm_smul, Real.norm_eq_abs, abs_of_pos hspos,
        le_div_iff₀ hspos]
      exact ⟨fun h ↦ by simpa [mul_comm] using h,
        fun h ↦ by simpa [mul_comm] using h⟩
    have hpreRight :
        (fun z : ℂ ↦ scale • z) ⁻¹' {z : ℂ | ‖z‖ ≤ rho} =
          {z : ℂ | ‖z‖ ≤ rho / scale} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos,
        le_div_iff₀ hspos]
      exact ⟨fun h ↦ by simpa [mul_comm] using h,
        fun h ↦ by simpa [mul_comm] using h⟩
    rw [hpreLeft, hpreRight]
    exact circularGaussian_norm_sub_le_centered
      ((-scale⁻¹) • b) (rho / scale)

/-- A translated circular complex Gaussian linear form puts no more mass in
a disk than its centered version.  No nondegeneracy hypothesis is needed. -/
theorem iidCircularTransposeLinearForm_norm_add_le_centered
    {k : ℕ} (y : Fin k → ℂ) (b : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (Measure.pi fun _ : Fin k ↦ LogdetLean.GramHafnian.circularGaussian)
        {x | ‖LogdetLean.GramHafnian.iidCircularTransposeLinearForm y x + b‖ ≤ rho} ≤
      (Measure.pi fun _ : Fin k ↦ LogdetLean.GramHafnian.circularGaussian)
        {x | ‖LogdetLean.GramHafnian.iidCircularTransposeLinearForm y x‖ ≤ rho} := by
  let L := LogdetLean.GramHafnian.iidCircularTransposeLinearForm y
  let mu : Measure (Fin k → ℂ) :=
    Measure.pi fun _ : Fin k ↦ LogdetLean.GramHafnian.circularGaussian
  have hleft : MeasurableSet {z : ℂ | ‖z + b‖ ≤ rho} :=
    measurableSet_le (by fun_prop) measurable_const
  have hright : MeasurableSet {z : ℂ | ‖z‖ ≤ rho} :=
    measurableSet_le (by fun_prop) measurable_const
  change mu (L ⁻¹' {z : ℂ | ‖z + b‖ ≤ rho}) ≤
    mu (L ⁻¹' {z : ℂ | ‖z‖ ≤ rho})
  rw [← Measure.map_apply
      (LogdetLean.GramHafnian.measurable_iidCircularTransposeLinearForm y) hleft,
    ← Measure.map_apply
      (LogdetLean.GramHafnian.measurable_iidCircularTransposeLinearForm y) hright]
  have hlaw :=
    LogdetLean.GramHafnian.map_iidCircularTransposeLinearForm_eq_scaled_circular y
  change mu.map L {z : ℂ | ‖z + b‖ ≤ rho} ≤
    mu.map L {z : ℂ | ‖z‖ ≤ rho}
  rw [hlaw]
  exact map_nonneg_smul_circularGaussian_norm_add_le_centered
    (Real.sqrt (LogdetLean.GramHafnian.circularCoefficientEnergy y))
    (Real.sqrt_nonneg _) b rho hrho

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
