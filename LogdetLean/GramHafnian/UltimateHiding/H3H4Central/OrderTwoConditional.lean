import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.OrderTwoZeroExtension
import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.CentralPointwiseCalculus
import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.DominatedDifferentiation
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreLowMeasurability

/-!
# CONDITIONAL H3/H4 assembly from the order-two determinant theorem

The sole scientific premise in this module is the exact H5 law equality,
passed as a theorem argument.  The order-two boundary theorem is constructed
internally from `hN` and `hboundary`.
-/

open MeasureTheory Filter
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator Topology

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.CurrentPRL

/-- Exact H5, retained as a separate upstream premise. -/
abbrev ExactCanonicalH5OrderTwo (N K : ℕ) : Prop :=
  concreteUnscaledCOECornerLaw
      canonicalUnitaryHaarProbabilityFamily N K =
    coeCornerDeterminantDensityProbabilityMeasure N K

/-- Inverse normalization map to `unscaleCOECorner`. -/
def scaleCOECornerOrderTwo {N : ℕ} (K : ℕ)
    (C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  ((((Real.sqrt (K : ℝ)) : ℝ) : ℂ)) • C

theorem measurable_scaleCOECornerOrderTwo (N K : ℕ) :
    Measurable (scaleCOECornerOrderTwo (N := N) K) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [scaleCOECornerOrderTwo, Matrix.smul_apply]
  fun_prop

theorem sqrt_nat_pos_of_dense_boundary_orderTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    0 < Real.sqrt (K : ℝ) := by
  apply Real.sqrt_pos.2
  have hK : 0 < K := by omega
  exact_mod_cast hK

theorem scale_unscaleCOECornerOrderTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) :
    scaleCOECornerOrderTwo K (unscaleCOECorner K A) = A := by
  have hsqrt := sqrt_nat_pos_of_dense_boundary_orderTwo hboundary
  simp [scaleCOECornerOrderTwo, unscaleCOECorner, smul_smul, hsqrt.ne']

theorem unscale_scaleCOECornerOrderTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (C : ConcreteMatrixState N) :
    unscaleCOECorner K (scaleCOECornerOrderTwo K C) = C := by
  have hsqrt := sqrt_nat_pos_of_dense_boundary_orderTwo hboundary
  ext i j
  simp [scaleCOECornerOrderTwo, unscaleCOECorner, Matrix.smul_apply,
    hsqrt.ne']

/-- Exact H5, followed only by the inverse normalization map, identifies the
paper-scaled law. -/
theorem concreteScaledCOECornerLaw_eq_map_scale_of_exactH5_orderTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K) :
    concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K =
      Measure.map (scaleCOECornerOrderTwo (N := N) K)
        (coeCornerDeterminantDensityProbabilityMeasure N K) := by
  rw [← hH5]
  unfold concreteUnscaledCOECornerLaw
  rw [Measure.map_map (measurable_scaleCOECornerOrderTwo N K)
    (measurable_unscaleCOECorner N K)]
  have hcomp :
      scaleCOECornerOrderTwo (N := N) K ∘ unscaleCOECorner K = id := by
    funext A
    exact scale_unscaleCOECornerOrderTwo hboundary A
  rw [hcomp, Measure.map_id]

/-- Paper-normalized reconstruction from independent unscaled coordinates. -/
def scaledComplexSymmetricMatrixOfCoordinatesOrderTwo (N K : ℕ)
    (x : ComplexSymmetricCoordinates N) : ConcreteMatrixState N :=
  ((((Real.sqrt (K : ℝ)) : ℝ) : ℂ)) •
    complexSymmetricMatrixOfCoordinates x

theorem measurable_scaledComplexSymmetricMatrixOfCoordinatesOrderTwo
    (N K : ℕ) :
    Measurable (scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K) := by
  have hM := measurable_complexSymmetricMatrixOfCoordinates N
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  change Measurable (fun x : ComplexSymmetricCoordinates N =>
    ((((Real.sqrt (K : ℝ)) : ℝ) : ℂ)) *
      complexSymmetricMatrixOfCoordinates x i j)
  exact measurable_const.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM))

/-- Exact-H5 coordinate formula for every measurable event of the
paper-normalized matrix law. -/
theorem concreteScaledCOECornerLaw_real_eq_integral_orderTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K).real event =
      ∫ x, (scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K ⁻¹' event).indicator
        (coeCornerCoordinateProbabilityDensity N K) x
        ∂(complexSymmetricCoordinateVolume N) := by
  rw [concreteScaledCOECornerLaw_eq_map_scale_of_exactH5_orderTwo
    hboundary hH5]
  rw [map_measureReal_apply (measurable_scaleCOECornerOrderTwo N K) hevent]
  have hpre : MeasurableSet
      (scaleCOECornerOrderTwo (N := N) K ⁻¹' event) :=
    hevent.preimage (measurable_scaleCOECornerOrderTwo N K)
  rw [coeCornerDeterminantDensityProbabilityMeasure_real_eq_integral
    (scaleCOECornerOrderTwo (N := N) K ⁻¹' event) hpre]
  rfl

/-- Literal transported coordinate density before the determinant formula is
expanded. -/
def coeCentralLiteralTransportedCoordinateDensity (N K : ℕ)
    (t : ℝ) (x : ComplexSymmetricCoordinates N) : ℝ :=
  Real.exp (-2 * coeCentralRealDimensionScratch N * t) *
    coeCornerCoordinateProbabilityDensity N K
      (((((Real.exp (-2 * t) : ℝ) : ℂ))) • x)

theorem scaledComplexSymmetricMatrixOfCoordinatesOrderTwo_smul
    (N K : ℕ) (r : ℝ) (x : ComplexSymmetricCoordinates N) :
    scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K (r • x) =
      ((((r : ℝ) : ℂ))) •
        scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K x := by
  change scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K
      (((((r : ℝ) : ℂ))) • x) = _
  unfold scaledComplexSymmetricMatrixOfCoordinatesOrderTwo
  rw [complexSymmetricMatrixOfCoordinates_smul]
  simp only [smul_smul]
  congr 1
  ring

theorem exp_neg_two_smul_exp_two_smul_coordinates_orderTwo
    {N : ℕ} (t : ℝ) (x : ComplexSymmetricCoordinates N) :
    (((((Real.exp (-2 * t) : ℝ) : ℂ))) •
        (Real.exp (2 * t) • x)) = x := by
  ext i
  simp only [Pi.smul_apply]
  change (((Real.exp (-2 * t) : ℝ) : ℂ) *
      (((Real.exp (2 * t) : ℝ) : ℂ) * x i)) = x i
  have hsum : -2 * t + 2 * t = 0 := by ring
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, hsum]
  simp

theorem exp_two_scalarJacobianFactor_orderTwo (N : ℕ) (t : ℝ) :
    |((Real.exp (2 * t)) ^ (N * (N + 1)))⁻¹| =
      Real.exp (-2 * coeCentralRealDimensionScratch N * t) := by
  rw [abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos _) _))]
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  unfold coeCentralRealDimensionScratch
  push_cast
  ring

/-- Exact H5 plus the checked scalar Jacobian gives the moving-event path as
the fixed-coordinate integral of the literal transported density. -/
theorem coeCentralEventPath_eq_integral_literal_orderTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (t : ℝ) :
    concreteCentralEventPath N
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) event t =
      ∫ x, (scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K ⁻¹' event).indicator
          (coeCentralLiteralTransportedCoordinateDensity N K t) x
        ∂(complexSymmetricCoordinateVolume N) := by
  let scaled := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K
  let pre := scaled ⁻¹' event
  let r := Real.exp (2 * t)
  let f : ComplexSymmetricCoordinates N → ℝ :=
    fun x ↦ pre.indicator
      (fun y ↦ coeCornerCoordinateProbabilityDensity N K
        (((((Real.exp (-2 * t) : ℝ) : ℂ))) • y)) x
  have hupdate : Measurable
      (concreteCentralMatrixUpdate N t) :=
    Dense.measurable_concreteCentralMatrixUpdate N t
  have heventUpdate : MeasurableSet
      (concreteCentralMatrixUpdate N t ⁻¹' event) :=
    hevent.preimage hupdate
  rw [concreteCentralEventPath, concreteCentralAction,
    map_measureReal_apply hupdate hevent]
  rw [concreteScaledCOECornerLaw_real_eq_integral_orderTwo
    hboundary hH5 (concreteCentralMatrixUpdate N t ⁻¹' event) heventUpdate]
  have hpoint :
      (fun x ↦
        (scaled ⁻¹' (concreteCentralMatrixUpdate N t ⁻¹' event)).indicator
          (coeCornerCoordinateProbabilityDensity N K) x) =
        fun x ↦ f (r • x) := by
    funext x
    have hmem :
        r • x ∈ pre ↔
          x ∈ scaled ⁻¹' (concreteCentralMatrixUpdate N t ⁻¹' event) := by
      change scaled (r • x) ∈ event ↔
        concreteCentralMatrixUpdate N t (scaled x) ∈ event
      rw [show scaled (r • x) =
          ((((r : ℝ) : ℂ))) • scaled x by
        simpa only [scaled] using
          scaledComplexSymmetricMatrixOfCoordinatesOrderTwo_smul N K r x]
      rw [concreteCentralMatrixUpdate_eq_exp_two_smul]
    by_cases hx : x ∈
        scaled ⁻¹' (concreteCentralMatrixUpdate N t ⁻¹' event)
    · have hrx : r • x ∈ pre := hmem.2 hx
      simp only [Set.indicator_of_mem hx, f, Set.indicator_of_mem hrx]
      rw [show (((((Real.exp (-2 * t) : ℝ) : ℂ))) • (r • x)) = x by
        simpa only [r] using
          exp_neg_two_smul_exp_two_smul_coordinates_orderTwo t x]
    · have hrx : r • x ∉ pre := by
        intro h
        exact hx (hmem.1 h)
      simp only [Set.indicator_of_notMem hx, f, Set.indicator_of_notMem hrx]
  rw [show
      (fun x ↦
        (scaled ⁻¹' (concreteCentralMatrixUpdate N t ⁻¹' event)).indicator
          (coeCornerCoordinateProbabilityDensity N K) x) =
        fun x ↦ f (r • x) by exact hpoint]
  rw [integral_comp_smul_complexSymmetricCoordinateVolume N f r]
  rw [show |((r ^ (N * (N + 1)))⁻¹)| =
      Real.exp (-2 * coeCentralRealDimensionScratch N * t) by
    simpa only [r] using exp_two_scalarJacobianFactor_orderTwo N t]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ pre
  · simp only [f, Set.indicator_of_mem hx,
      coeCentralLiteralTransportedCoordinateDensity, pre, scaled]
  · simp only [f, Set.indicator_of_notMem hx, mul_zero,
      coeCentralLiteralTransportedCoordinateDensity, pre, scaled]

/-- The promoted order-zero jet is exactly the literal normalized
determinant density transported to fixed coordinates. -/
theorem coeCentralTransportedCoordinateDensity_eq_literal
    {N K : ℕ} (hN : 1 ≤ N)
    (t : ℝ) (x : ComplexSymmetricCoordinates N) :
    coeCentralTransportedCoordinateDensity N K t x =
      coeCentralLiteralTransportedCoordinateDensity N K t x := by
  classical
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
  let C := coeCentralTransportCornerScratch N (t, x)
  have hmatrix :
      complexSymmetricMatrixOfCoordinates
          (((((Real.exp (-2 * t) : ℝ) : ℂ))) • x) = C := by
    rw [complexSymmetricMatrixOfCoordinates_smul]
    rfl
  by_cases hs : x ∈ coeCentralTransportOpenSupportScratch N t
  · have hsupport : coeCornerSupport C := by
      apply (coeCornerSupport_iff_cstar_norm_lt_one_scratch hN C).2
      change ‖coeCentralTransportCornerScratch N (t, x)‖ < 1 at hs
      simpa only [C] using hs
    unfold coeCentralTransportedCoordinateDensity coeCentralTransportJet
      coeCentralTransportJetScratch
    rw [if_pos hs]
    change coeCentralTransportRawJetZeroScratch N K (t, x) = _
    unfold coeCentralTransportRawJetZeroScratch
      coeCentralTransportCoefficientScratch
      coeCentralLiteralTransportedCoordinateDensity
      coeCornerCoordinateProbabilityDensity
    unfold coeCornerDeterminantWeight
    rw [hmatrix]
    dsimp only
    rw [if_pos hsupport]
    have hto :
        (ENNReal.ofReal
          ((Matrix.det (1 - C.conjTranspose * C)).re.rpow
            (coeCornerDensityExponent N K))).toReal =
          (Matrix.det (1 - C.conjTranspose * C)).re.rpow
            (coeCornerDensityExponent N K) :=
      ENNReal.toReal_ofReal (Real.rpow_nonneg
        ((RCLike.pos_iff.mp hsupport.det_pos).1.le) _)
    rw [hto]
    unfold coeCentralTransportDetScratch coeCentralTransportGapScratch
    dsimp only [C]
    ring_nf
    rw [Real.rpow_eq_pow]
  · have hnotSupport : ¬coeCornerSupport C := by
      intro hsupport
      apply hs
      exact (coeCornerSupport_iff_cstar_norm_lt_one_scratch hN C).1 hsupport
    unfold coeCentralTransportedCoordinateDensity coeCentralTransportJet
      coeCentralTransportJetScratch
    rw [if_neg hs]
    unfold coeCentralLiteralTransportedCoordinateDensity
      coeCornerCoordinateProbabilityDensity
    unfold coeCornerDeterminantWeight
    rw [hmatrix]
    dsimp only
    rw [if_neg hnotSupport]
    simp

/-- Event transport in terms of the public, globally zero-extended order-zero
jet. -/
theorem coeCentralEventPath_eq_integral_jetZero_orderTwo
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (t : ℝ) :
    concreteCentralEventPath N
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) event t =
      ∫ x, (scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K ⁻¹' event).indicator
          (coeCentralTransportJet N K 0 t) x
        ∂(complexSymmetricCoordinateVolume N) := by
  rw [coeCentralEventPath_eq_integral_literal_orderTwo
    hboundary hH5 event hevent t]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈
      scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K ⁻¹' event
  · simp only [Set.indicator_of_mem hx]
    exact (coeCentralTransportedCoordinateDensity_eq_literal hN t x).symm
  · simp only [Set.indicator_of_notMem hx]

/-- Every public jet is integrable at every time, derived from its local
envelope rather than assumed in the public structure. -/
theorem integrable_coeCentralTransportJet
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (j : Fin 3) (t : ℝ) :
    Integrable (coeCentralTransportJet N K j t)
      (complexSymmetricCoordinateVolume N) := by
  let H := coeCentralTransport_orderTwo_zeroExtension hN hboundary
  obtain ⟨delta, hdelta, g, hgint, hbound⟩ := H.local_L1_envelope t
  have hmeas : AEStronglyMeasurable (coeCentralTransportJet N K j t)
      (complexSymmetricCoordinateVolume N) := by
    exact ((H.joint_continuous j).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply (hgint j).mono hmeas
  filter_upwards [] with x
  exact (hbound x j t (by simpa using hdelta.le)).trans (by
    simpa only [Real.norm_eq_abs] using le_abs_self (g j x))

/-- Local twice-dominated calculus for an arbitrary measurable event. -/
theorem coeCorner_centralEventPath_local_calculus_orderTwo_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (t0 : ℝ) :
    ∃ s : Set ℝ, IsOpen s ∧ t0 ∈ s ∧
      ContDiffOn ℝ 2
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) s ∧
      ∀ t ∈ s,
        iteratedDeriv 1
            (concreteCentralEventPath N
              (concreteScaledCOECornerLaw
                canonicalUnitaryHaarProbabilityFamily N K) event) t =
          ∫ x, (scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K ⁻¹' event).indicator
              (coeCentralTransportJet N K 1 t) x
            ∂(complexSymmetricCoordinateVolume N) ∧
        iteratedDeriv 2
            (concreteCentralEventPath N
              (concreteScaledCOECornerLaw
                canonicalUnitaryHaarProbabilityFamily N K) event) t =
          ∫ x, (scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K ⁻¹' event).indicator
              (coeCentralTransportJet N K 2 t) x
            ∂(complexSymmetricCoordinateVolume N) := by
  let H := coeCentralTransport_orderTwo_zeroExtension hN hboundary
  let pre := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K ⁻¹' event
  let F : Fin 3 → ℝ → ComplexSymmetricCoordinates N → ℝ :=
    fun j t ↦ pre.indicator (coeCentralTransportJet N K j t)
  obtain ⟨delta, hdelta, g, hgint, hgenv⟩ := H.local_L1_envelope t0
  let s : Set ℝ := Set.Ioo (t0 - delta) (t0 + delta)
  have hs : IsOpen s := isOpen_Ioo
  have ht0 : t0 ∈ s := by
    change t0 - delta < t0 ∧ t0 < t0 + delta
    constructor <;> linarith
  have hpre : MeasurableSet pre :=
    hevent.preimage
      (measurable_scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K)
  have hmeas : ∀ j t, AEStronglyMeasurable (F j t)
      (complexSymmetricCoordinateVolume N) := by
    intro j t
    exact (((H.joint_continuous j).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable).indicator hpre
  have hint : ∀ j t, Integrable (F j t)
      (complexSymmetricCoordinateVolume N) := by
    intro j t
    exact (integrable_coeCentralTransportJet hN hboundary j t).indicator hpre
  have hinterval : ∀ t ∈ s, |t - t0| ≤ delta := by
    intro t ht
    change t0 - delta < t ∧ t < t0 + delta at ht
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hbound1 :
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N), ∀ t ∈ s,
        ‖F 1 t x‖ ≤ g 1 x := by
    filter_upwards [] with x
    intro t ht
    exact (show ‖F 1 t x‖ ≤ ‖coeCentralTransportJet N K 1 t x‖ by
      simpa only [F] using
        (norm_indicator_le_norm_self
          (s := pre) (coeCentralTransportJet N K 1 t) x)).trans
        (hgenv x 1 t (hinterval t ht))
  have hbound2 :
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N), ∀ t ∈ s,
        ‖F 2 t x‖ ≤ g 2 x := by
    filter_upwards [] with x
    intro t ht
    exact (show ‖F 2 t x‖ ≤ ‖coeCentralTransportJet N K 2 t x‖ by
      simpa only [F] using
        (norm_indicator_le_norm_self
          (s := pre) (coeCentralTransportJet N K 2 t) x)).trans
        (hgenv x 2 t (hinterval t ht))
  have hderiv1 :
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N), ∀ t ∈ s,
        HasDerivAt (fun u ↦ F 0 u x) (F 1 t x) t := by
    filter_upwards [] with x
    intro t _
    by_cases hxp : x ∈ pre
    · simp only [F, Set.indicator_of_mem hxp]
      convert H.derivative_chain (j := ⟨0, by norm_num⟩) x t using 1 <;>
        norm_num
    · simp only [F, Set.indicator_of_notMem hxp]
      exact hasDerivAt_const t 0
  have hderiv2 :
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N), ∀ t ∈ s,
        HasDerivAt (fun u ↦ F 1 u x) (F 2 t x) t := by
    filter_upwards [] with x
    intro t _
    by_cases hxp : x ∈ pre
    · simp only [F, Set.indicator_of_mem hxp]
      convert H.derivative_chain (j := ⟨1, by norm_num⟩) x t using 1 <;>
        norm_num
    · simp only [F, Set.indicator_of_notMem hxp]
      exact hasDerivAt_const t 0
  have hcont2 :
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
        ContinuousOn (fun t ↦ F 2 t x) s := by
    filter_upwards [] with x
    have huncurry := H.joint_continuous (⟨2, by norm_num⟩ : Fin 3)
    have hconst : Continuous (fun _ : ℝ => x) := continuous_const
    have hpair : Continuous (fun t : ℝ => (t, x)) :=
      continuous_id.prodMk hconst
    have hxcont' := huncurry.comp hpair
    have hxcont : Continuous (fun t ↦
        coeCentralTransportJet N K 2 t x) := by
      convert hxcont' using 1
      funext u
      apply congrArg (fun j : Fin 3 =>
        coeCentralTransportJet N K j u x)
      apply Fin.ext
      rfl
    by_cases hxp : x ∈ pre
    · simpa only [F, Set.indicator_of_mem hxp] using hxcont.continuousOn
    · simp only [F, Set.indicator_of_notMem hxp]
      exact continuousOn_const
  have hDCT := contDiffOn_two_integral_of_dominated_with_derivatives
    (mu := complexSymmetricCoordinateVolume N) (s := s)
    (F := F 0) (F₁ := F 1) (F₂ := F 2) (g₁ := g 1) (g₂ := g 2)
    hs (fun t _ ↦ hmeas 0 t) (fun t _ ↦ hint 0 t)
    (fun t _ ↦ hmeas 1 t) (fun t _ ↦ hmeas 2 t)
    (hgint 1) (hgint 2) hbound1 hbound2 hderiv1 hderiv2 hcont2
  have hpath :
      concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event =
        fun t ↦ ∫ x, F 0 t x ∂(complexSymmetricCoordinateVolume N) := by
    funext t
    simpa only [F, pre] using
      coeCentralEventPath_eq_integral_jetZero_orderTwo
        hN hboundary hH5 event hevent t
  refine ⟨s, hs, ht0, ?_, ?_⟩
  · rw [hpath]
    exact hDCT.1
  · intro t ht
    rw [hpath]
    simpa only [F, pre] using hDCT.2 t ht

/-- **CONDITIONAL H3 (order two).**  This has the exact original H3
conclusion and retains exact H5 as its sole upstream scientific premise. -/
theorem coeCorner_centralEventPath_contDiff_external_derived_orderTwo_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 2
      (concreteCentralEventPath N
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) event) := by
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨s, hs, ht0, hcont, _⟩ :=
    coeCorner_centralEventPath_local_calculus_orderTwo_conditional
      hN hboundary hH5 event hevent t0
  exact hcont.contDiffAt (hs.mem_nhds ht0)

/-! ## Exact-H5 function transport and measurable central scores -/

/-- Exact H5 transports every measurable real function of the scaled corner
to independent complex-symmetric coordinates. -/
theorem integral_concreteScaledCOECornerLaw_eq_coordinates_orderTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K)
    (f : ConcreteMatrixState N → ℝ) (hf : Measurable f) :
    ∫ A, f A ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) =
      ∫ x, f (scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K x) *
          coeCornerCoordinateProbabilityDensity N K x
        ∂(complexSymmetricCoordinateVolume N) := by
  rw [concreteScaledCOECornerLaw_eq_map_scale_of_exactH5_orderTwo
    hboundary hH5]
  rw [integral_map_of_stronglyMeasurable
    (measurable_scaleCOECornerOrderTwo N K) hf.stronglyMeasurable]
  rw [integral_coeCornerDeterminantDensityProbabilityMeasure_eq_coordinates
    (fun C ↦ f (scaleCOECornerOrderTwo K C))
    (hf.comp (measurable_scaleCOECornerOrderTwo N K))]
  rfl

theorem measurable_concreteCOETraceOne_orderTwo (N K : ℕ) :
    Measurable (concreteCOETraceOne N K) := by
  have hY := measurable_concreteCOEY_internal N K
  unfold concreteCOETraceOne concreteRealTrace
  simp only [Matrix.trace, Matrix.diag_apply]
  fun_prop

theorem measurable_concreteCOETraceTwo_orderTwo (N K : ℕ) :
    Measurable (concreteCOETraceTwo N K) := by
  have hY := measurable_concreteCOEY_internal N K
  unfold concreteCOETraceTwo concreteRealTrace
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  fun_prop

theorem measurable_concreteCentralLogScoreOne_orderTwo (N K : ℕ) :
    Measurable (concreteCentralLogScoreOne N K) := by
  have h₁ := measurable_concreteCOETraceOne_orderTwo N K
  unfold concreteCentralLogScoreOne
  fun_prop

theorem measurable_concreteCentralLogScoreTwo_orderTwo (N K : ℕ) :
    Measurable (concreteCentralLogScoreTwo N K) := by
  have h₁ := measurable_concreteCOETraceOne_orderTwo N K
  have h₂ := measurable_concreteCOETraceTwo_orderTwo N K
  unfold concreteCentralLogScoreTwo
  fun_prop

theorem measurable_concreteCentralDensityScoreTwo_orderTwo (N K : ℕ) :
    Measurable (concreteCentralDensityScoreTwo N K) := by
  have h₁ := measurable_concreteCentralLogScoreOne_orderTwo N K
  have h₂ := measurable_concreteCentralLogScoreTwo_orderTwo N K
  unfold concreteCentralDensityScoreTwo secondDensityBell
  fun_prop

/-! ## Scalar Bell calculus at time zero -/

private theorem iteratedDeriv_one_exp_comp_at_orderTwo
    (g : ℝ → ℝ) {x : ℝ} (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (Real.exp ∘ g) x =
      Real.exp (g x) * iteratedDeriv 1 g x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hg' : HasDerivAt g (deriv g x) x :=
    (hg.differentiableAt (by norm_num)).hasDerivAt
  simpa [Function.comp_def] using hg'.exp.deriv

private theorem iteratedDeriv_two_exp_comp_at_orderTwo
    (g : ℝ → ℝ) {x : ℝ} (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (Real.exp ∘ g) x =
      Real.exp (g x) *
        (iteratedDeriv 1 g x ^ 2 + iteratedDeriv 2 g x) := by
  rw [iteratedDeriv_comp_two Real.contDiff_exp.contDiffAt hg]
  simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.deriv_exp, Function.iterate_one]
  ring

/-- The symmetric-coordinate Jacobian contribution plus the first raw
log-determinant derivative is exactly the explicit first central score. -/
theorem central_log_det_one_with_jacobian_eq_logScoreOne_orderTwo
    {N K : ℕ} (A : ConcreteMatrixState N) :
    -2 * coeCentralRealDimensionScratch N +
        coeCornerDensityExponent N K *
          (4 * (Matrix.trace (concreteCOEZ K A)).re) =
      concreteCentralLogScoreOne N K A := by
  unfold coeCentralRealDimensionScratch concreteCentralLogScoreOne
    concreteCOETraceOne concreteRealTrace concreteCOEY
    coeCornerDensityExponent concreteCOEExponent
  rw [Matrix.trace_smul]
  norm_num [Complex.mul_re]
  push_cast
  ring

/-- The positive, unnormalized part of the transported coordinate density;
the constant inverse raw mass is deliberately omitted. -/
def coeCentralUnnormalizedTransportProfileOrderTwo (N K : ℕ)
    (x : ComplexSymmetricCoordinates N) (t : ℝ) : ℝ :=
  Real.exp (-2 * coeCentralRealDimensionScratch N * t) *
    (coeCentralTransportDetScratch N (t, x)) ^
      (coeCornerDensityExponent N K)

/-- On the open support, the first two derivatives of the positive profile
are its value times the explicit first and second density scores. -/
theorem coeCentralUnnormalizedTransportProfile_timeZero_scores_orderTwo
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (x : ComplexSymmetricCoordinates N)
    (hx : x ∈ coeCentralTransportOpenSupportScratch N 0) :
    let A := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K x
    iteratedDeriv 1
        (coeCentralUnnormalizedTransportProfileOrderTwo N K x) 0 =
        concreteCentralLogScoreOne N K A *
          coeCentralUnnormalizedTransportProfileOrderTwo N K x 0 ∧
      iteratedDeriv 2
        (coeCentralUnnormalizedTransportProfileOrderTwo N K x) 0 =
        concreteCentralDensityScoreTwo N K A *
          coeCentralUnnormalizedTransportProfileOrderTwo N K x 0 := by
  let C := complexSymmetricMatrixOfCoordinates x
  let A := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K x
  let q : ℝ → ℝ := fun t ↦ coeCentralTransportDetScratch N (t, x)
  let p : ℝ := coeCornerDensityExponent N K
  let d : ℝ := coeCentralRealDimensionScratch N
  let profile : ℝ → ℝ :=
    coeCentralUnnormalizedTransportProfileOrderTwo N K x
  let L : ℝ → ℝ := fun t ↦ -2 * d * t + p * Real.log (q t)
  have hCA : unscaleCOECorner K A = C := by
    change unscaleCOECorner K (scaleCOECornerOrderTwo K C) = C
    exact unscale_scaleCOECornerOrderTwo hboundary C
  have hsupportC : coeCornerSupport C := by
    apply (coeCornerSupport_iff_cstar_norm_lt_one_scratch hN C).2
    simpa [C, coeCentralTransportOpenSupportScratch,
      coeCentralTransportCornerScratch] using hx
  have hsymmA : (unscaleCOECorner K A).IsSymm := by
    rw [hCA]
    exact complexSymmetricMatrixOfCoordinates_isSymm x
  have hsupportA : coeCornerSupport (unscaleCOECorner K A) := by
    rwa [hCA]
  have hqpath : q = fun t ↦ centeredMovedDetTwo
      (1 : ConcreteMatrixState N) C t := by
    funext t
    simpa [q, C, coeCentralTransportDetScratch,
      coeCentralTransportGapScratch, coeCentralTransportCornerScratch] using
      (centeredMovedDetTwo_one_eq_exp_neg_two_smul C t).symm
  have hq0 : 0 < q 0 := by
    have hpos := (RCLike.lt_iff_re_im.mp hsupportC.det_pos).1
    simpa [q, C, coeCentralTransportDetScratch,
      coeCentralTransportGapScratch, coeCentralTransportCornerScratch] using hpos
  have hqcd : ContDiff ℝ ⊤ q := by
    simpa only [q, Function.comp_def, id_eq] using
      (contDiff_coeCentralTransportDetScratch N).comp
      (contDiff_id.prodMk contDiff_const)
  have hqpos : ∀ᶠ t in 𝓝 0, 0 < q t :=
    continuousAt_const.eventually_lt hqcd.continuous.continuousAt hq0
  have hqpow : ContDiff ℝ 2 (fun t ↦ (q t) ^ p) := by
    have hpair : ContDiff ℝ 2
        (fun t : ℝ ↦ ((t, x) : ℝ × ComplexSymmetricCoordinates N)) :=
      contDiff_id.prodMk contDiff_const
    have h := (contDiff_coeCentralTransportDet_rpow_scratch N K
      (n := 2) (coeCentral_exponent_two_le_scratch hboundary)).comp
        hpair
    simpa only [q, p, Function.comp_def, Nat.cast_ofNat] using h
  have hexp : ContDiff ℝ 2
      (fun t : ℝ ↦ Real.exp (-2 * d * t)) := by
    fun_prop
  have hprofile : ContDiff ℝ 2 profile := by
    change ContDiff ℝ 2
      (fun t ↦ Real.exp (-2 * d * t) * (q t) ^ p)
    exact hexp.mul hqpow
  have hprofile0 : 0 < profile 0 := by
    dsimp only [profile, coeCentralUnnormalizedTransportProfileOrderTwo,
      d, q, p]
    exact mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos hq0 (coeCornerDensityExponent N K))
  have hprofilePos : ∀ᶠ t in 𝓝 0, 0 < profile t :=
    continuousAt_const.eventually_lt hprofile.continuous.continuousAt hprofile0
  have hprofileExp : profile =ᶠ[𝓝 0]
      Real.exp ∘ (fun t ↦ Real.log (profile t)) := by
    filter_upwards [hprofilePos] with t ht
    simp only [Function.comp_apply]
    exact (Real.exp_log ht).symm
  have hlogProfile : ContDiffAt ℝ 2
      (fun t ↦ Real.log (profile t)) 0 :=
    hprofile.contDiffAt.log hprofile0.ne'
  have hlogeq : (fun t ↦ Real.log (profile t)) =ᶠ[𝓝 0] L := by
    filter_upwards [hqpos] with t ht
    have hpow : 0 < (q t) ^ p := Real.rpow_pos_of_pos ht p
    dsimp only [profile, coeCentralUnnormalizedTransportProfileOrderTwo,
      L, d, q, p]
    rw [Real.log_mul (Real.exp_ne_zero _) hpow.ne', Real.log_exp,
      Real.log_rpow ht]
  have hlogq1 : iteratedDeriv 1 (fun t ↦ Real.log (q t)) 0 =
      4 * (Matrix.trace (concreteCOEZ K A)).re := by
    have h := central_log_det_one_raw_checked A hsymmA hsupportA
    rw [hCA] at h
    rw [hqpath]
    exact h
  have hlogq2 : p * iteratedDeriv 2 (fun t ↦ Real.log (q t)) 0 =
      concreteCentralLogScoreTwo N K A := by
    have h := central_log_det_two_times_exponent_eq_logScoreTwo
      hboundary A hsymmA hsupportA
    rw [hCA] at h
    rw [hqpath]
    exact h
  have hL1 : iteratedDeriv 1 L 0 =
      concreteCentralLogScoreOne N K A := by
    have hlogqAt : ContDiffAt ℝ 1 (fun t ↦ Real.log (q t)) 0 :=
      (hqcd.contDiffAt.log hq0.ne').of_le (by norm_num)
    have hlinCD : ContDiffAt ℝ 1 (fun t : ℝ ↦ -2 * d * t) 0 := by
      fun_prop
    have hpartCD : ContDiffAt ℝ 1
        (fun t ↦ p * Real.log (q t)) 0 :=
      contDiffAt_const.mul hlogqAt
    rw [show L = (fun t : ℝ ↦ -2 * d * t) +
        (fun t ↦ p * Real.log (q t)) by rfl]
    rw [iteratedDeriv_add hlinCD hpartCD,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
      hlogq1]
    simpa [iteratedDeriv_fun_id] using
      central_log_det_one_with_jacobian_eq_logScoreOne_orderTwo A
  have hL2 : iteratedDeriv 2 L 0 =
      concreteCentralLogScoreTwo N K A := by
    have hlinCD : ContDiffAt ℝ 2 (fun t : ℝ ↦ -2 * d * t) 0 := by
      fun_prop
    have hlogqCD : ContDiffAt ℝ 2 (fun t ↦ Real.log (q t)) 0 :=
      (hqcd.contDiffAt.log hq0.ne').of_le (by norm_num)
    have hpartCD : ContDiffAt ℝ 2
        (fun t ↦ p * Real.log (q t)) 0 :=
      contDiffAt_const.mul hlogqCD
    rw [show L = (fun t : ℝ ↦ -2 * d * t) +
        (fun t ↦ p * Real.log (q t)) by rfl]
    rw [iteratedDeriv_add hlinCD hpartCD,
      iteratedDeriv_const_mul_field]
    simpa [iteratedDeriv_fun_id] using hlogq2
  have hlog1 : iteratedDeriv 1 (fun t ↦ Real.log (profile t)) 0 =
      concreteCentralLogScoreOne N K A :=
    (hlogeq.iteratedDeriv_eq 1).trans hL1
  have hlog2 : iteratedDeriv 2 (fun t ↦ Real.log (profile t)) 0 =
      concreteCentralLogScoreTwo N K A :=
    (hlogeq.iteratedDeriv_eq 2).trans hL2
  have hbell1 := iteratedDeriv_one_exp_comp_at_orderTwo
    (fun t ↦ Real.log (profile t))
      (hlogProfile.of_le (by norm_num))
  rw [← hprofileExp.iteratedDeriv_eq 1, Real.exp_log hprofile0,
    hlog1] at hbell1
  have hbell2 := iteratedDeriv_two_exp_comp_at_orderTwo
    (fun t ↦ Real.log (profile t)) hlogProfile
  rw [← hprofileExp.iteratedDeriv_eq 2, Real.exp_log hprofile0,
    hlog1, hlog2] at hbell2
  dsimp only [A]
  constructor
  · simpa only [profile, mul_comm] using hbell1
  · simpa only [profile, concreteCentralDensityScoreTwo,
      secondDensityBell, mul_comm] using hbell2

/-! ## Time-zero identification of the global jets with the scores -/

/-- On the interior support, the explicit raw first and second jets are the
raw density times the two central scores.  This theorem connects the checked
determinant formulas to the scalar Bell calculation above. -/
theorem coeCentralTransportRawJet_timeZero_scores_orderTwo
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (x : ComplexSymmetricCoordinates N)
    (hx : x ∈ coeCentralTransportOpenSupportScratch N 0) :
    let A := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K x
    coeCentralTransportRawJetOneScratch N K (0, x) =
        concreteCentralLogScoreOne N K A *
          coeCentralTransportRawJetZeroScratch N K (0, x) ∧
      coeCentralTransportRawJetTwoScratch N K (0, x) =
        concreteCentralDensityScoreTwo N K A *
          coeCentralTransportRawJetZeroScratch N K (0, x) := by
  let m : ℝ := (coeCornerRawMass N K)⁻¹.toReal
  let profile : ℝ → ℝ :=
    coeCentralUnnormalizedTransportProfileOrderTwo N K x
  let rawZero : ℝ → ℝ := fun t ↦
    coeCentralTransportRawJetZeroScratch N K (t, x)
  let rawOne : ℝ → ℝ := fun t ↦
    coeCentralTransportRawJetOneScratch N K (t, x)
  have hrawZero : rawZero = fun t ↦ m * profile t := by
    funext t
    dsimp only [rawZero, m, profile,
      coeCentralTransportRawJetZeroScratch,
      coeCentralTransportCoefficientScratch,
      coeCentralUnnormalizedTransportProfileOrderTwo]
    ring
  have hrawOneDeriv : ∀ t, deriv rawZero t = rawOne t := by
    intro t
    exact (hasDerivAt_coeCentralTransportRawJetZeroScratch
      hboundary x t).deriv
  have hrawOneDerivFun : deriv rawZero = rawOne := by
    funext t
    exact hrawOneDeriv t
  have hrawOne :
      coeCentralTransportRawJetOneScratch N K (0, x) =
        m * iteratedDeriv 1 profile 0 := by
    calc
      coeCentralTransportRawJetOneScratch N K (0, x) =
          iteratedDeriv 1 rawZero 0 := by
        rw [iteratedDeriv_one, hrawOneDerivFun]
      _ = iteratedDeriv 1 (fun t ↦ m * profile t) 0 := by rw [hrawZero]
      _ = m * iteratedDeriv 1 profile 0 := by
        rw [iteratedDeriv_const_mul_field]
  have hrawTwo :
      coeCentralTransportRawJetTwoScratch N K (0, x) =
        m * iteratedDeriv 2 profile 0 := by
    calc
      coeCentralTransportRawJetTwoScratch N K (0, x) =
          iteratedDeriv 2 rawZero 0 := by
        rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
          iteratedDeriv_one, hrawOneDerivFun]
        exact (hasDerivAt_coeCentralTransportRawJetOneScratch
          hboundary x 0).deriv.symm
      _ = iteratedDeriv 2 (fun t ↦ m * profile t) 0 := by rw [hrawZero]
      _ = m * iteratedDeriv 2 profile 0 := by
        rw [iteratedDeriv_const_mul_field]
  have hrawZeroAt :
      coeCentralTransportRawJetZeroScratch N K (0, x) =
        m * profile 0 := by
    exact congrFun hrawZero 0
  obtain ⟨hprofileOne, hprofileTwo⟩ :=
    coeCentralUnnormalizedTransportProfile_timeZero_scores_orderTwo
      hN hboundary x hx
  constructor
  · rw [hrawOne, hprofileOne, hrawZeroAt]
    ring
  · rw [hrawTwo, hprofileTwo, hrawZeroAt]
    ring

/-- The same score identities for the public zero-extended jets.  Outside
the support all three jets vanish, so the identities remain literal and
global. -/
theorem coeCentralTransportJet_timeZero_scores_orderTwo
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (x : ComplexSymmetricCoordinates N) :
    let A := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K x
    coeCentralTransportJet N K 1 0 x =
        concreteCentralLogScoreOne N K A *
          coeCentralTransportJet N K 0 0 x ∧
      coeCentralTransportJet N K 2 0 x =
        concreteCentralDensityScoreTwo N K A *
          coeCentralTransportJet N K 0 0 x := by
  classical
  by_cases hx : x ∈ coeCentralTransportOpenSupportScratch N 0
  · simpa [coeCentralTransportJet, coeCentralTransportJetScratch,
      coeCentralTransportRawJetScratch, hx] using
      coeCentralTransportRawJet_timeZero_scores_orderTwo
        hN hboundary x hx
  · simp [coeCentralTransportJet, coeCentralTransportJetScratch, hx]

/-- At time zero, the public order-zero jet is the normalized determinant
density in the fixed independent coordinates. -/
theorem coeCentralTransportJet_zero_timeZero_eq_coordinateDensity_orderTwo
    {N K : ℕ} (hN : 1 ≤ N)
    (x : ComplexSymmetricCoordinates N) :
    coeCentralTransportJet N K 0 0 x =
      coeCornerCoordinateProbabilityDensity N K x := by
  change coeCentralTransportedCoordinateDensity N K 0 x = _
  rw [coeCentralTransportedCoordinateDensity_eq_literal hN 0 x]
  simp [coeCentralLiteralTransportedCoordinateDensity]

/-- Pointwise coordinate form of the two central score identities. -/
theorem coeCentralTransportJet_timeZero_eq_scores_mul_density_orderTwo
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (x : ComplexSymmetricCoordinates N) :
    let A := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K x
    coeCentralTransportJet N K 1 0 x =
        concreteCentralLogScoreOne N K A *
          coeCornerCoordinateProbabilityDensity N K x ∧
      coeCentralTransportJet N K 2 0 x =
        concreteCentralDensityScoreTwo N K A *
          coeCornerCoordinateProbabilityDensity N K x := by
  have h := coeCentralTransportJet_timeZero_scores_orderTwo
    hN hboundary x
  rw [coeCentralTransportJet_zero_timeZero_eq_coordinateDensity_orderTwo
    hN x] at h
  exact h

/-! ## CONDITIONAL exact H4 endpoint -/

/-- **CONDITIONAL H4 (order two).**  This has the exact original H4
conclusion and retains exact H5 as its sole upstream scientific premise. -/
theorem coeCorner_centralEventPath_derivatives_external_derived_orderTwo_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hH5 : ExactCanonicalH5OrderTwo N K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 1
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) 0 =
      ∫ A, event.indicator (concreteCentralLogScoreOne N K) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
    iteratedDeriv 2
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) 0 =
      ∫ A, event.indicator (concreteCentralDensityScoreTwo N K) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  let scaled := scaledComplexSymmetricMatrixOfCoordinatesOrderTwo N K
  let pre := scaled ⁻¹' event
  obtain ⟨s, hs, hzero, _, hderivs⟩ :=
    coeCorner_centralEventPath_local_calculus_orderTwo_conditional
      hN hboundary hH5 event hevent 0
  obtain ⟨hderivOne, hderivTwo⟩ := hderivs 0 hzero
  have hscoreOneMeas :
      Measurable (event.indicator (concreteCentralLogScoreOne N K)) :=
    (measurable_concreteCentralLogScoreOne_orderTwo N K).indicator hevent
  have hscoreTwoMeas :
      Measurable (event.indicator (concreteCentralDensityScoreTwo N K)) :=
    (measurable_concreteCentralDensityScoreTwo_orderTwo N K).indicator hevent
  have htransportOne :=
    integral_concreteScaledCOECornerLaw_eq_coordinates_orderTwo
      hboundary hH5 (event.indicator (concreteCentralLogScoreOne N K))
        hscoreOneMeas
  have htransportTwo :=
    integral_concreteScaledCOECornerLaw_eq_coordinates_orderTwo
      hboundary hH5 (event.indicator (concreteCentralDensityScoreTwo N K))
        hscoreTwoMeas
  have hcoordinateOne :
      (∫ x, pre.indicator (coeCentralTransportJet N K 1 0) x
          ∂(complexSymmetricCoordinateVolume N)) =
        ∫ x, (event.indicator (concreteCentralLogScoreOne N K))
              (scaled x) * coeCornerCoordinateProbabilityDensity N K x
          ∂(complexSymmetricCoordinateVolume N) := by
    apply integral_congr_ae
    filter_upwards [] with x
    have hpoint :=
      (coeCentralTransportJet_timeZero_eq_scores_mul_density_orderTwo
        hN hboundary x).1
    by_cases hx : scaled x ∈ event
    · have hxpre : x ∈ pre := by exact hx
      simp only [Set.indicator_of_mem hxpre, Set.indicator_of_mem hx]
      exact hpoint
    · have hxpre : x ∉ pre := by exact hx
      simp only [Set.indicator_of_notMem hxpre,
        Set.indicator_of_notMem hx]
      simp
  have hcoordinateTwo :
      (∫ x, pre.indicator (coeCentralTransportJet N K 2 0) x
          ∂(complexSymmetricCoordinateVolume N)) =
        ∫ x, (event.indicator (concreteCentralDensityScoreTwo N K))
              (scaled x) * coeCornerCoordinateProbabilityDensity N K x
          ∂(complexSymmetricCoordinateVolume N) := by
    apply integral_congr_ae
    filter_upwards [] with x
    have hpoint :=
      (coeCentralTransportJet_timeZero_eq_scores_mul_density_orderTwo
        hN hboundary x).2
    by_cases hx : scaled x ∈ event
    · have hxpre : x ∈ pre := by exact hx
      simp only [Set.indicator_of_mem hxpre, Set.indicator_of_mem hx]
      exact hpoint
    · have hxpre : x ∉ pre := by exact hx
      simp only [Set.indicator_of_notMem hxpre,
        Set.indicator_of_notMem hx]
      simp
  constructor
  · calc
      iteratedDeriv 1
          (concreteCentralEventPath N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) event) 0 =
          ∫ x, pre.indicator (coeCentralTransportJet N K 1 0) x
            ∂(complexSymmetricCoordinateVolume N) := by
        simpa only [pre, scaled] using hderivOne
      _ = ∫ x, (event.indicator (concreteCentralLogScoreOne N K))
              (scaled x) * coeCornerCoordinateProbabilityDensity N K x
            ∂(complexSymmetricCoordinateVolume N) := hcoordinateOne
      _ = ∫ A, event.indicator (concreteCentralLogScoreOne N K) A
            ∂(concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) := by
        simpa only [scaled] using htransportOne.symm
  · calc
      iteratedDeriv 2
          (concreteCentralEventPath N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) event) 0 =
          ∫ x, pre.indicator (coeCentralTransportJet N K 2 0) x
            ∂(complexSymmetricCoordinateVolume N) := by
        simpa only [pre, scaled] using hderivTwo
      _ = ∫ x, (event.indicator (concreteCentralDensityScoreTwo N K))
              (scaled x) * coeCornerCoordinateProbabilityDensity N K x
            ∂(complexSymmetricCoordinateVolume N) := hcoordinateTwo
      _ = ∫ A, event.indicator (concreteCentralDensityScoreTwo N K) A
            ∂(concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) := by
        simpa only [scaled] using htransportTwo.symm

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
