import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_ColumnParameterAlgebra
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarGramSecondMoment
import LogdetLean.GaussianSphereDirection
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# The one-column Jiang Haar-corner density

This file proves the `N = 1` base case of Jiang's raw Haar-corner density
from normalized Haar invariance, the uniform-sphere law of a Haar column,
the elementary Beta radial law, and polar coordinates.  It does not use
`jiang_2009_prop2_1_unscaledTallHaarCorner_density`.
-/

open MeasureTheory ProbabilityTheory Matrix Set Metric
open scoped ENNReal BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding.Dense

local instance h19BaseColumnEuclideanBorel (K : ℕ) :
    BorelSpace (EuclideanSpace ℂ (Fin K)) := by infer_instance

/-! ## Reconstructing the top coordinates from the Beta/sphere parameter -/

/-- Reconstruct a complex vector from the deleted-energy parameter `q` and
its independent unit direction. -/
def h19BaseColumnReconstruct (K : ℕ)
    (p : ℝ × ComplexUnitSphere K) : EuclideanSpace ℂ (Fin K) :=
  Real.sqrt (1 - p.1) • p.2.1

theorem measurable_h19BaseColumnReconstruct (K : ℕ) :
    Measurable (h19BaseColumnReconstruct K) := by
  unfold h19BaseColumnReconstruct
  fun_prop

theorem h19BaseColumnReconstruct_h1AmbientSphereParameter
    {K r : ℕ} (hK : 1 ≤ K) (z : ComplexUnitSphere (K + r)) :
    h19BaseColumnReconstruct K (h1AmbientSphereParameter (r := r) hK z) =
      h1TopCoordinates z.1 := by
  let S := h1TopRealSubspace K r
  let x := h1TopCoordinates z.1
  let top := ‖S.orthogonalProjectionOnto z.1‖ ^ 2
  let tail := ‖S.orthogonal.orthogonalProjectionOnto z.1‖ ^ 2
  have hcoord := h1TopRealIsometry_projection_eq_coordinates z.1
  have htop : top = ‖x‖ ^ 2 := by
    have h := congrArg (fun y : EuclideanSpace ℂ (Fin K) ↦ ‖y‖ ^ 2) hcoord
    simpa [top, x] using h
  have hzNorm : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hpyth : top + tail = 1 := by
    have h := S.norm_sq_eq_add_norm_sq_projection z.1
    rw [hzNorm] at h
    norm_num at h
    simpa [top, tail] using h.symm
  have hq :
      1 - (h1AmbientSphereParameter (r := r) hK z).1 = ‖x‖ ^ 2 := by
    unfold h1AmbientSphereParameter h1AmbientGaussianParameter
      h1TopTailDataToParameter h1AmbientTopTailData
      h1TopDirectionEnergy LogdetLean.gammaRatio
    dsimp only
    change 1 - tail / (tail + top) = ‖x‖ ^ 2
    rw [show tail + top = 1 by linarith [hpyth], div_one]
    linarith [hpyth, htop]
  have hv :
      (h1AmbientSphereParameter (r := r) hK z).2 =
        h1GaussianComplexSphereDirection hK x := by
    unfold h1AmbientSphereParameter h1AmbientGaussianParameter
      h1TopTailDataToParameter h1AmbientTopTailData
      h1TopDirectionEnergy
    dsimp only
    exact congrArg (h1GaussianComplexSphereDirection hK) hcoord
  rw [h19BaseColumnReconstruct, hq, hv]
  have hsqrt : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [hsqrt]
  change ‖x‖ • (h1GaussianComplexSphereDirection hK x).1 = x
  by_cases hx : x = 0
  · simp [hx]
  · rw [coe_h1GaussianComplexSphereDirection_of_ne hK hx,
      h1_unitDirection_eq_inv_norm_smul x hx]
    rw [smul_smul]
    field_simp [norm_ne_zero_iff.mpr hx]
    simp

/-- The top `K` coordinates of a uniform vector on the complex sphere in
dimension `K+r` are reconstructed from an independent
`Beta(r,K) × sphere(K)` parameter. -/
theorem map_h1TopCoordinates_complexUnitSphereProbabilityMeasure
    {K r : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r) :
    Measure.map (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1)
        (complexUnitSphereProbabilityMeasure (K + r)) =
      Measure.map (h19BaseColumnReconstruct K)
        ((betaMeasure (r : ℝ) (K : ℝ)).prod
          (complexUnitSphereProbabilityMeasure K)) := by
  have hparam := map_h1AmbientSphereParameter_uniform
    (N := K) (r := r) hK hr
  have htop : Measurable
      (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1) := by
    unfold h1TopCoordinates
    fun_prop
  calc
    Measure.map (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1)
        (complexUnitSphereProbabilityMeasure (K + r)) =
      Measure.map
          (h19BaseColumnReconstruct K ∘
            h1AmbientSphereParameter (r := r) hK)
          (complexUnitSphereProbabilityMeasure (K + r)) := by
        apply Measure.map_congr
        filter_upwards with z
        exact (h19BaseColumnReconstruct_h1AmbientSphereParameter hK z).symm
    _ = Measure.map (h19BaseColumnReconstruct K)
        (Measure.map (h1AmbientSphereParameter (r := r) hK)
          (complexUnitSphereProbabilityMeasure (K + r))) := by
        rw [Measure.map_map (measurable_h19BaseColumnReconstruct K)
          (measurable_h1AmbientSphereParameter (r := r) hK)]
    _ = Measure.map (h19BaseColumnReconstruct K)
        ((betaMeasure (r : ℝ) (K : ℝ)).prod
          (complexUnitSphereProbabilityMeasure K)) := by rw [hparam]

/-! ## The explicit ball density and its polar factorization -/

/-- The elementary one-column normalizer
`pi^(-K) (K+r-1)!/(r-1)!`. -/
def h19BaseColumnNormalizer (K r : ℕ) : ℝ :=
  (Real.pi ^ K)⁻¹ *
    (Nat.factorial (K + r - 1) : ℝ) /
      (Nat.factorial (r - 1) : ℝ)

/-- The explicit open-ball density.  Replacing `< 1` by `≤ 1` does not
change the resulting Lebesgue-density measure. -/
def h19BaseColumnVectorPDF (K r : ℕ)
    (x : EuclideanSpace ℂ (Fin K)) : ℝ≥0∞ :=
  if ‖x‖ < 1 then
    ENNReal.ofReal
      (h19BaseColumnNormalizer K r * (1 - ‖x‖ ^ 2) ^ (r - 1))
  else 0

theorem measurable_h19BaseColumnVectorPDF (K r : ℕ) :
    Measurable (h19BaseColumnVectorPDF K r) := by
  unfold h19BaseColumnVectorPDF
  apply Measurable.ite
  · exact measurableSet_Iio.preimage measurable_id.norm
  · exact (measurable_const.mul
      ((measurable_const.sub (measurable_id.norm.pow_const 2)).pow_const _)).ennreal_ofReal
  · exact measurable_const

/-- The same density as a function of the positive polar radius. -/
def h19BaseColumnRayPDF (K r : ℕ) (rho : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  if rho.1 < 1 then
    ENNReal.ofReal
      (h19BaseColumnNormalizer K r * (1 - rho.1 ^ 2) ^ (r - 1))
  else 0

theorem measurable_h19BaseColumnRayPDF (K r : ℕ) :
    Measurable (h19BaseColumnRayPDF K r) := by
  unfold h19BaseColumnRayPDF
  apply Measurable.ite
  · exact measurableSet_Iio.preimage measurable_subtype_coe
  · exact (measurable_const.mul
      ((measurable_const.sub (measurable_subtype_coe.pow_const 2)).pow_const _)).ennreal_ofReal
  · exact measurable_const

private theorem h19BaseColumnVectorPDF_polar {K r : ℕ}
    (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin K)))) :
    h19BaseColumnVectorPDF K r (x : EuclideanSpace ℂ (Fin K)) =
      h19BaseColumnRayPDF K r
        (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin K)) x).2 := by
  unfold h19BaseColumnVectorPDF h19BaseColumnRayPDF
  rw [homeomorphUnitSphereProd_apply_snd_coe]

/-- Polar coordinates turn the explicit one-column ball density into surface
measure times its one-dimensional radial density. -/
theorem map_polar_h19BaseColumnVectorDensity {K r : ℕ} (hK : 1 ≤ K) :
    Measure.map (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin K)))
        (((volume : Measure (EuclideanSpace ℂ (Fin K))).comap
          (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin K))) →
            EuclideanSpace ℂ (Fin K))).withDensity
          (fun x ↦ h19BaseColumnVectorPDF K r x.1)) =
      ((volume : Measure (EuclideanSpace ℂ (Fin K))).toSphere).prod
        ((Measure.volumeIoiPow (2 * K - 1)).withDensity
          (h19BaseColumnRayPDF K r)) := by
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp (by omega)
  have hpolar :=
    (volume : Measure (EuclideanSpace ℂ (Fin K))).measurePreserving_homeomorphUnitSphereProd
  have htilt := LogdetLean.measurePreserving_map_withDensity_comp hpolar
    (fun z : sphere (0 : EuclideanSpace ℂ (Fin K)) 1 × Ioi (0 : ℝ) ↦
      h19BaseColumnRayPDF K r z.2)
    ((measurable_h19BaseColumnRayPDF K r).comp measurable_snd)
  rw [finrank_complexEuclideanSpace_real] at htilt
  rw [prod_withDensity_right (measurable_h19BaseColumnRayPDF K r)]
  rw [← htilt]
  congr 2
  funext x
  exact h19BaseColumnVectorPDF_polar x

/-- Reinserting the puncture gives the ambient explicit density measure. -/
theorem map_subtype_h19BaseColumnVectorDensity {K r : ℕ} (hK : 1 ≤ K) :
    Measure.map
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin K))) →
          EuclideanSpace ℂ (Fin K))
        (((volume : Measure (EuclideanSpace ℂ (Fin K))).comap
          (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin K))) →
            EuclideanSpace ℂ (Fin K))).withDensity
          (fun x ↦ h19BaseColumnVectorPDF K r x.1)) =
      (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp (by omega)
  have hsub : MeasurePreserving
      (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin K))) →
        EuclideanSpace ℂ (Fin K))
      ((volume : Measure (EuclideanSpace ℂ (Fin K))).comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin K))) →
          EuclideanSpace ℂ (Fin K))) volume := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe
      (measurableSet_singleton (0 : EuclideanSpace ℂ (Fin K))).compl,
      restrict_compl_singleton]
  simpa only [Function.comp_apply, Function.comp_def] using
    LogdetLean.measurePreserving_map_withDensity_comp hsub
      (h19BaseColumnVectorPDF K r)
      (measurable_h19BaseColumnVectorPDF K r)

/-! ## The elementary one-dimensional Beta/radius change of variables -/

private theorem betaPDF_one_sub (a b x : ℝ) :
    betaPDF a b (1 - x) = betaPDF b a x := by
  unfold betaPDF betaPDFReal
  have hmem : (0 < 1 - x ∧ 1 - x < 1) ↔ (0 < x ∧ x < 1) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hx : 0 < x ∧ x < 1
  · rw [if_pos (hmem.mpr hx), if_pos hx]
    congr 1
    unfold beta
    rw [add_comm a b, mul_comm (Real.Gamma a) (Real.Gamma b)]
    ring
  · rw [if_neg (not_congr hmem |>.mpr hx), if_neg hx]

/-- Reflection about `1/2` swaps the two Beta parameters. -/
theorem map_one_sub_betaMeasure (a b : ℝ) :
    Measure.map (fun x : ℝ ↦ 1 - x) (betaMeasure a b) =
      betaMeasure b a := by
  have hp := (volume : Measure ℝ).measurePreserving_sub_left 1
  have hm : Measurable (fun x : ℝ ↦ betaPDF a b (1 - x)) := by
    exact (measurable_betaPDFReal a b).ennreal_ofReal.comp (by fun_prop)
  have htilt := LogdetLean.measurePreserving_map_withDensity_comp hp
    (fun x : ℝ ↦ betaPDF a b (1 - x)) hm
  rw [betaMeasure, betaMeasure]
  have htarget : (fun x : ℝ ↦ betaPDF a b (1 - x)) = betaPDF b a := by
    funext x
    exact betaPDF_one_sub a b x
  have hsource :
      (fun x : ℝ ↦ betaPDF a b (1 - x)) ∘ (fun x : ℝ ↦ 1 - x) =
        betaPDF a b := by
    funext x
    simp
  rw [hsource, htarget] at htilt
  exact htilt

/-- Ordinary Lebesgue density of `sqrt Y` for `Y ~ Beta(K,r)`. -/
def h19BaseColumnRadiusPDF (K r : ℕ) (rho : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * rho) * betaPDF (K : ℝ) (r : ℝ) (rho ^ 2)

theorem measurable_h19BaseColumnRadiusPDF (K r : ℕ) :
    Measurable (h19BaseColumnRadiusPDF K r) := by
  unfold h19BaseColumnRadiusPDF
  exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
    ((measurable_betaPDFReal (K : ℝ) (r : ℝ)).ennreal_ofReal.comp (by fun_prop))

private theorem sq_image_Ioi_zero :
    (fun x : ℝ ↦ x ^ 2) '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 < x at hx
    exact sq_pos_of_pos hx
  · intro hy
    refine ⟨Real.sqrt y, Real.sqrt_pos.2 hy, ?_⟩
    exact Real.sq_sqrt hy.le

private theorem injOn_sq_Ioi_zero :
    InjOn (fun x : ℝ ↦ x ^ 2) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  change x ^ 2 = y ^ 2 at hxy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with hxy | hxy
  · exact hxy
  · exfalso
    nlinarith

private theorem hasDerivAt_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

private theorem lintegral_sq_Ioi (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in Ioi (0 : ℝ), g y) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * x) * g (x ^ 2) := by
  calc
    (∫⁻ y in Ioi (0 : ℝ), g y) =
        ∫⁻ y in (fun x : ℝ ↦ x ^ 2) '' Ioi 0, g y := by
      rw [sq_image_Ioi_zero]
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |2 * x| * g (x ^ 2) := by
      exact lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
        (fun x _ ↦ (hasDerivAt_sq x).hasDerivWithinAt)
        injOn_sq_Ioi_zero g
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * x) * g (x ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      rw [abs_of_pos (mul_pos (by norm_num) hx)]

private theorem lintegral_eq_setLIntegral_Ioi_of_zero_nonpos
    (g : ℝ → ℝ≥0∞) (hg : ∀ x, x ≤ 0 → g x = 0) :
    (∫⁻ x, g x) = ∫⁻ x in Ioi (0 : ℝ), g x := by
  calc
    (∫⁻ x, g x) =
        (∫⁻ x in Ioi (0 : ℝ), g x) +
          ∫⁻ x in (Ioi (0 : ℝ))ᶜ, g x :=
      (lintegral_add_compl g measurableSet_Ioi).symm
    _ = (∫⁻ x in Ioi (0 : ℝ), g x) + 0 := by
      congr 1
      rw [setLIntegral_eq_zero measurableSet_Ioi.compl]
      intro x hx
      exact hg x (by simpa using hx)
    _ = ∫⁻ x in Ioi (0 : ℝ), g x := add_zero _

/-- Squaring the elementary positive-radius density gives `Beta(K,r)`. -/
theorem map_sq_h19BaseColumnRadiusDensity (K r : ℕ) :
    Measure.map (fun rho : ℝ ↦ rho ^ 2)
        ((volume : Measure ℝ).withDensity
          (h19BaseColumnRadiusPDF K r)) =
      betaMeasure (K : ℝ) (r : ℝ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hbeta : Measurable (betaPDF (K : ℝ) (r : ℝ)) := by
    exact (measurable_betaPDFReal (K : ℝ) (r : ℝ)).ennreal_ofReal
  rw [lintegral_map hf (by fun_prop : Measurable (fun rho : ℝ ↦ rho ^ 2))]
  change (∫⁻ rho : ℝ, (f ∘ fun x : ℝ ↦ x ^ 2) rho
      ∂(volume : Measure ℝ).withDensity (h19BaseColumnRadiusPDF K r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _
      (measurable_h19BaseColumnRadiusPDF K r) (hf.comp (by fun_prop)),
    betaMeasure,
    lintegral_withDensity_eq_lintegral_mul _
      hbeta hf]
  change (∫⁻ rho : ℝ,
      h19BaseColumnRadiusPDF K r rho * f (rho ^ 2)) =
    ∫⁻ y : ℝ, betaPDF (K : ℝ) (r : ℝ) y * f y
  have hLzero : ∀ rho : ℝ, rho ≤ 0 →
      h19BaseColumnRadiusPDF K r rho * f (rho ^ 2) = 0 := by
    intro rho hrho
    unfold h19BaseColumnRadiusPDF
    rw [ENNReal.ofReal_eq_zero.mpr (by linarith), zero_mul, zero_mul]
  have hRzero : ∀ y : ℝ, y ≤ 0 →
      betaPDF (K : ℝ) (r : ℝ) y * f y = 0 := by
    intro y hy
    rw [betaPDF_eq_zero_of_nonpos hy, zero_mul]
  rw [lintegral_eq_setLIntegral_Ioi_of_zero_nonpos _ hLzero,
    lintegral_eq_setLIntegral_Ioi_of_zero_nonpos _ hRzero,
    lintegral_sq_Ioi
      (fun y : ℝ ↦ betaPDF (K : ℝ) (r : ℝ) y * f y)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun rho _ ↦ ?_
  simp only [h19BaseColumnRadiusPDF, mul_assoc]

/-- The positive-radius measure, kept on the ambient real line for convenient
composition with the Beta reflection and square-root maps. -/
def h19BaseColumnRadiusMeasure (K r : ℕ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity (h19BaseColumnRadiusPDF K r)

private theorem ae_pos_h19BaseColumnRadiusMeasure (K r : ℕ) :
    ∀ᵐ rho ∂h19BaseColumnRadiusMeasure K r, 0 < rho := by
  unfold h19BaseColumnRadiusMeasure
  refine (ae_withDensity_iff (measurable_h19BaseColumnRadiusPDF K r)).2 ?_
  filter_upwards with rho
  intro hne
  by_contra hpos
  apply hne
  unfold h19BaseColumnRadiusPDF
  rw [ENNReal.ofReal_eq_zero.mpr (by push_neg at hpos; linarith), zero_mul]

/-- Taking the positive square root of `Beta(K,r)` gives the radius density. -/
theorem map_sqrt_betaMeasure_eq_h19BaseColumnRadiusMeasure (K r : ℕ) :
    Measure.map Real.sqrt (betaMeasure (K : ℝ) (r : ℝ)) =
      h19BaseColumnRadiusMeasure K r := by
  rw [← map_sq_h19BaseColumnRadiusDensity K r]
  rw [Measure.map_map (by fun_prop : Measurable Real.sqrt)
    (by fun_prop : Measurable (fun rho : ℝ ↦ rho ^ 2))]
  rw [Measure.map_congr]
  · rw [Measure.map_id]
    rfl
  · filter_upwards [ae_pos_h19BaseColumnRadiusMeasure K r] with rho hrho
    change Real.sqrt (rho ^ 2) = id rho
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrho]
    rfl

/-- The exact radius occurring in the one-column sphere decomposition has the
explicit positive-radius density above. -/
theorem map_sqrt_one_sub_betaMeasure_eq_h19BaseColumnRadiusMeasure (K r : ℕ) :
    Measure.map (fun q : ℝ ↦ Real.sqrt (1 - q))
        (betaMeasure (r : ℝ) (K : ℝ)) =
      h19BaseColumnRadiusMeasure K r := by
  calc
    Measure.map (fun q : ℝ ↦ Real.sqrt (1 - q))
        (betaMeasure (r : ℝ) (K : ℝ)) =
      Measure.map Real.sqrt
        (Measure.map (fun q : ℝ ↦ 1 - q)
          (betaMeasure (r : ℝ) (K : ℝ))) := by
        have hfun : (fun q : ℝ ↦ Real.sqrt (1 - q)) =
            Real.sqrt ∘ (fun q : ℝ ↦ 1 - q) := rfl
        rw [hfun]
        exact (Measure.map_map (μ := betaMeasure (r : ℝ) (K : ℝ))
          (by fun_prop : Measurable Real.sqrt)
          (by fun_prop : Measurable (fun q : ℝ ↦ 1 - q))).symm
    _ = Measure.map Real.sqrt (betaMeasure (K : ℝ) (r : ℝ)) := by
      rw [map_one_sub_betaMeasure]
    _ = h19BaseColumnRadiusMeasure K r :=
      map_sqrt_betaMeasure_eq_h19BaseColumnRadiusMeasure K r

/-! ## Normalization of the polar product -/

private theorem beta_nat_eq_factorial_ratio {K r : ℕ}
    (hK : 1 ≤ K) (hr : 1 ≤ r) :
    beta (K : ℝ) (r : ℝ) =
      (Nat.factorial (K - 1) : ℝ) *
        (Nat.factorial (r - 1) : ℝ) /
          (Nat.factorial (K + r - 1) : ℝ) := by
  have hGammaK : Real.Gamma (K : ℝ) =
      (Nat.factorial (K - 1) : ℝ) := by
    have hcast : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
      norm_cast
      omega
    rw [← hcast]
    exact Real.Gamma_nat_eq_factorial (K - 1)
  have hGammar : Real.Gamma (r : ℝ) =
      (Nat.factorial (r - 1) : ℝ) := by
    have hcast : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by
      norm_cast
      omega
    rw [← hcast]
    exact Real.Gamma_nat_eq_factorial (r - 1)
  have hGammaKr : Real.Gamma ((K : ℝ) + (r : ℝ)) =
      (Nat.factorial (K + r - 1) : ℝ) := by
    have hcast : ((K + r - 1 : ℕ) : ℝ) + 1 =
        (K : ℝ) + (r : ℝ) := by
      norm_cast
      omega
    rw [← hcast]
    exact Real.Gamma_nat_eq_factorial (K + r - 1)
  simp only [beta, hGammaK, hGammar, hGammaKr]

private theorem h19BaseColumnNormalizer_surfaceFactor {K r : ℕ}
    (hK : 1 ≤ K) (hr : 1 ≤ r) :
    h19BaseColumnNormalizer K r *
        (2 * Real.pi ^ K / (Nat.factorial (K - 1) : ℝ)) =
      2 / beta (K : ℝ) (r : ℝ) := by
  rw [beta_nat_eq_factorial_ratio hK hr]
  unfold h19BaseColumnNormalizer
  have hpi : Real.pi ^ K ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hKfac : (Nat.factorial (K - 1) : ℝ) ≠ 0 := by positivity
  have hrfac : (Nat.factorial (r - 1) : ℝ) ≠ 0 := by positivity
  have hKrfac : (Nat.factorial (K + r - 1) : ℝ) ≠ 0 := by positivity
  field_simp [hpi, hKfac, hrfac, hKrfac]

private theorem h19BaseColumnSphereSurfaceMass {K : ℕ} (hK : 1 ≤ K) :
    ((volume : Measure (EuclideanSpace ℂ (Fin K))).toSphere) univ =
      ENNReal.ofReal
        (2 * Real.pi ^ K / (Nat.factorial (K - 1) : ℝ)) := by
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp (by omega)
  rw [Measure.toSphere_apply_univ]
  rw [finrank_complexEuclideanSpace_real]
  rw [InnerProductSpace.volume_ball_of_dim_even
    (E := EuclideanSpace ℂ (Fin K)) (k := K)
    (finrank_complexEuclideanSpace_real K) 0 1]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  have hKfac : (Nat.factorial K : ℝ) ≠ 0 := by positivity
  have hKm1fac : (Nat.factorial (K - 1) : ℝ) ≠ 0 := by positivity
  have hKcast : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hfac : (Nat.factorial K : ℝ) =
      (K : ℝ) * (Nat.factorial (K - 1) : ℝ) := by
    rw [show K = (K - 1) + 1 by omega, Nat.factorial_succ]
    norm_num
  rw [hfac]
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_mul
    (by positivity : 0 ≤ (((2 * K : ℕ) : ℝ)))]
  congr 1
  field_simp [hKcast, hKm1fac]
  norm_num [Nat.cast_mul]
  ring

private theorem h19BaseColumn_pow_radius {K : ℕ} (hK : 1 ≤ K) (rho : ℝ) :
    rho ^ (2 * K - 1) = rho * (rho ^ 2) ^ (K - 1) := by
  calc
    rho ^ (2 * K - 1) = rho ^ (2 * (K - 1) + 1) := by
      congr 1
      omega
    _ = rho ^ (2 * (K - 1)) * rho := by rw [pow_add, pow_one]
    _ = (rho ^ 2) ^ (K - 1) * rho := by rw [pow_mul]
    _ = rho * (rho ^ 2) ^ (K - 1) := by ring

private theorem h19BaseColumnPolarRadius_density {K r : ℕ}
    (hK : 1 ≤ K) (hr : 1 ≤ r) (rho : Ioi (0 : ℝ)) :
    ((volume : Measure (EuclideanSpace ℂ (Fin K))).toSphere univ) *
        (ENNReal.ofReal (rho.1 ^ (2 * K - 1)) *
          h19BaseColumnRayPDF K r rho) =
      h19BaseColumnRadiusPDF K r rho.1 := by
  rw [h19BaseColumnSphereSurfaceMass hK]
  by_cases hrho : rho.1 < 1
  · have hrho0 : 0 < rho.1 := rho.2
    have hrhoSq0 : 0 < rho.1 ^ 2 := sq_pos_of_pos hrho0
    have hrhoSq1 : rho.1 ^ 2 < 1 := by nlinarith
    unfold h19BaseColumnRayPDF h19BaseColumnRadiusPDF
    rw [if_pos hrho, betaPDF_of_pos_lt_one hrhoSq0 hrhoSq1]
    have hsurface : 0 ≤
        2 * Real.pi ^ K / (Nat.factorial (K - 1) : ℝ) := by positivity
    have hpow : 0 ≤ rho.1 ^ (2 * K - 1) := by positivity
    have hnormalizer : 0 ≤ h19BaseColumnNormalizer K r := by
      unfold h19BaseColumnNormalizer
      positivity
    have htail : 0 ≤ (1 - rho.1 ^ 2) ^ (r - 1) := by positivity
    have hbetaPart : 0 ≤
        (1 / beta (K : ℝ) (r : ℝ)) *
          (rho.1 ^ 2) ^ ((K : ℝ) - 1) *
            (1 - rho.1 ^ 2) ^ ((r : ℝ) - 1) := by
      have hb : 0 < beta (K : ℝ) (r : ℝ) :=
        beta_pos (by exact_mod_cast hK) (by exact_mod_cast hr)
      positivity
    rw [← ENNReal.ofReal_mul hpow]
    rw [← ENNReal.ofReal_mul hsurface]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * rho.1)]
    congr 1
    have hKexp : (K : ℝ) - 1 = ((K - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hK]
      norm_num
    have hrexp : (r : ℝ) - 1 = ((r - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hr]
      norm_num
    rw [hKexp, hrexp, Real.rpow_natCast, Real.rpow_natCast]
    calc
      (2 * Real.pi ^ K / (Nat.factorial (K - 1) : ℝ)) *
          (rho.1 ^ (2 * K - 1) *
            (h19BaseColumnNormalizer K r * (1 - rho.1 ^ 2) ^ (r - 1))) =
        (h19BaseColumnNormalizer K r *
            (2 * Real.pi ^ K / (Nat.factorial (K - 1) : ℝ))) *
          rho.1 ^ (2 * K - 1) * (1 - rho.1 ^ 2) ^ (r - 1) := by ring
      _ = (2 / beta (K : ℝ) (r : ℝ)) *
          rho.1 ^ (2 * K - 1) * (1 - rho.1 ^ 2) ^ (r - 1) := by
        rw [h19BaseColumnNormalizer_surfaceFactor hK hr]
      _ = (2 * rho.1) *
          ((1 / beta (K : ℝ) (r : ℝ)) *
            (rho.1 ^ 2) ^ (K - 1) *
              (1 - rho.1 ^ 2) ^ (r - 1)) := by
        rw [h19BaseColumn_pow_radius hK]
        ring
  · have hrho1 : 1 ≤ rho.1 := le_of_not_gt hrho
    have hrhoSq1 : 1 ≤ rho.1 ^ 2 := by nlinarith [rho.2]
    unfold h19BaseColumnRayPDF h19BaseColumnRadiusPDF
    rw [if_neg hrho, betaPDF_eq_zero_of_one_le hrhoSq1]
    simp

/-- The radial part of the normalized sphere/Beta product is exactly the
surface-mass multiple of the radial part of polar Lebesgue measure. -/
theorem h19BaseColumnPositiveRadiusMeasure_eq_surface_smul {K r : ℕ}
    (hK : 1 ≤ K) (hr : 1 ≤ r) :
    (((volume : Measure (EuclideanSpace ℂ (Fin K))).toSphere) univ) •
        ((Measure.volumeIoiPow (2 * K - 1)).withDensity
          (h19BaseColumnRayPDF K r)) =
      ((volume : Measure ℝ).comap
          (Subtype.val : Ioi (0 : ℝ) → ℝ)).withDensity
        (fun rho ↦ h19BaseColumnRadiusPDF K r rho.1) := by
  unfold Measure.volumeIoiPow
  rw [← withDensity_mul _
    (by fun_prop : Measurable (fun rho : Ioi (0 : ℝ) ↦
      ENNReal.ofReal (rho.1 ^ (2 * K - 1))))
    (measurable_h19BaseColumnRayPDF K r)]
  rw [← withDensity_smul
    (((volume : Measure (EuclideanSpace ℂ (Fin K))).toSphere) univ)
    (((measurable_subtype_coe.pow_const (2 * K - 1)).ennreal_ofReal).mul
      (measurable_h19BaseColumnRayPDF K r))]
  apply withDensity_congr_ae
  filter_upwards with rho
  exact h19BaseColumnPolarRadius_density hK hr rho

/-- The positive-radius version of the square-root Beta law. -/
def h19BaseColumnPositiveRadiusMeasure (K r : ℕ) :
    Measure (Ioi (0 : ℝ)) :=
  ((volume : Measure ℝ).comap
      (Subtype.val : Ioi (0 : ℝ) → ℝ)).withDensity
    (fun rho ↦ h19BaseColumnRadiusPDF K r rho.1)

/-- Forgetting positivity sends the positive-radius measure to the ambient
radius measure. -/
theorem map_h19BaseColumnPositiveRadiusMeasure (K r : ℕ) :
    Measure.map (Subtype.val : Ioi (0 : ℝ) → ℝ)
        (h19BaseColumnPositiveRadiusMeasure K r) =
      h19BaseColumnRadiusMeasure K r := by
  have hsub := measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (s := Ioi (0 : ℝ)) measurableSet_Ioi
  have htilt := LogdetLean.measurePreserving_map_withDensity_comp hsub
    (h19BaseColumnRadiusPDF K r)
    (measurable_h19BaseColumnRadiusPDF K r)
  unfold h19BaseColumnPositiveRadiusMeasure h19BaseColumnRadiusMeasure
  change Measure.map (Subtype.val : Ioi (0 : ℝ) → ℝ)
      (((volume : Measure ℝ).comap Subtype.val).withDensity
        (h19BaseColumnRadiusPDF K r ∘ Subtype.val)) = _
  rw [htilt]
  rw [← restrict_withDensity measurableSet_Ioi]
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_pos_h19BaseColumnRadiusMeasure K r)

/-- After normalization, the sphere/Beta polar product is exactly the polar
form of the explicit Lebesgue density. -/
theorem h19BaseColumnSphereProbability_prod_positiveRadius {K r : ℕ}
    (hK : 1 ≤ K) (hr : 1 ≤ r) :
    (complexUnitSphereProbabilityMeasure K).prod
        (h19BaseColumnPositiveRadiusMeasure K r) =
      ((volume : Measure (EuclideanSpace ℂ (Fin K))).toSphere).prod
        ((Measure.volumeIoiPow (2 * K - 1)).withDensity
          (h19BaseColumnRayPDF K r)) := by
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp (by omega)
  let sigma : Measure (ComplexUnitSphere K) :=
    (volume : Measure (EuclideanSpace ℂ (Fin K))).toSphere
  let ray : Measure (Ioi (0 : ℝ)) :=
    (Measure.volumeIoiPow (2 * K - 1)).withDensity
      (h19BaseColumnRayPDF K r)
  let s : ℝ≥0∞ := sigma univ
  have hpos : s • ray = h19BaseColumnPositiveRadiusMeasure K r := by
    simpa only [s, sigma, ray, h19BaseColumnPositiveRadiusMeasure] using
      h19BaseColumnPositiveRadiusMeasure_eq_surface_smul hK hr
  have hsne : s ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mpr
    dsimp [s, sigma]
    exact Measure.toSphere_ne_zero
      (volume : Measure (EuclideanSpace ℂ (Fin K)))
  have hstop : s ≠ ∞ := measure_ne_top sigma univ
  change (s⁻¹ • sigma).prod (h19BaseColumnPositiveRadiusMeasure K r) =
    sigma.prod ray
  rw [← hpos, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.inv_mul_cancel hsne hstop, one_smul]

/-- Sampling an independent uniform direction and the positive Beta radius
produces the explicit complex-ball Lebesgue density. -/
theorem map_smul_h19BaseColumnSphereProbability_positiveRadius {K r : ℕ}
    (hK : 1 ≤ K) (hr : 1 ≤ r) :
    Measure.map
        (fun p : ComplexUnitSphere K × Ioi (0 : ℝ) ↦ p.2.1 • p.1.1)
        ((complexUnitSphereProbabilityMeasure K).prod
          (h19BaseColumnPositiveRadiusMeasure K r)) =
      (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp (by omega)
  let E := EuclideanSpace ℂ (Fin K)
  let polar := homeomorphUnitSphereProd E
  let punctured : Measure ({0}ᶜ : Set E) :=
    ((volume : Measure E).comap
      (Subtype.val : ({0}ᶜ : Set E) → E)).withDensity
        (fun x ↦ h19BaseColumnVectorPDF K r x.1)
  have hpolar : Measure.map polar punctured =
      ((volume : Measure E).toSphere).prod
        ((Measure.volumeIoiPow (2 * K - 1)).withDensity
          (h19BaseColumnRayPDF K r)) := by
    simpa only [E, polar, punctured] using
      map_polar_h19BaseColumnVectorDensity (K := K) (r := r) hK
  have hprod := h19BaseColumnSphereProbability_prod_positiveRadius
    (K := K) (r := r) hK hr
  have hinv : Measure.map polar.symm
      ((complexUnitSphereProbabilityMeasure K).prod
        (h19BaseColumnPositiveRadiusMeasure K r)) = punctured := by
    rw [hprod, ← hpolar]
    rw [Measure.map_map polar.symm.measurable polar.measurable]
    calc
      Measure.map (polar.symm ∘ polar) punctured =
          Measure.map id punctured := by
        apply Measure.map_congr
        filter_upwards with x
        exact polar.symm_apply_apply x
      _ = punctured := Measure.map_id
  calc
    Measure.map
        (fun p : ComplexUnitSphere K × Ioi (0 : ℝ) ↦ p.2.1 • p.1.1)
        ((complexUnitSphereProbabilityMeasure K).prod
          (h19BaseColumnPositiveRadiusMeasure K r)) =
      Measure.map (Subtype.val : ({0}ᶜ : Set E) → E)
        (Measure.map polar.symm
          ((complexUnitSphereProbabilityMeasure K).prod
            (h19BaseColumnPositiveRadiusMeasure K r))) := by
        rw [Measure.map_map measurable_subtype_coe polar.symm.measurable]
        apply Measure.map_congr
        filter_upwards with p
        exact homeomorphUnitSphereProd_symm_apply_coe E p
    _ = Measure.map (Subtype.val : ({0}ᶜ : Set E) → E) punctured := by
      rw [hinv]
    _ = (volume : Measure E).withDensity
        (h19BaseColumnVectorPDF K r) := by
      simpa only [E, punctured] using
        map_subtype_h19BaseColumnVectorDensity (K := K) (r := r) hK

/-- The original `Beta(r,K) × sphere(K)` reconstruction therefore has the
explicit complex-ball Lebesgue density. -/
theorem map_h19BaseColumnReconstruct_betaSphere {K r : ℕ}
    (hK : 1 ≤ K) (hr : 1 ≤ r) :
    Measure.map (h19BaseColumnReconstruct K)
        ((betaMeasure (r : ℝ) (K : ℝ)).prod
          (complexUnitSphereProbabilityMeasure K)) =
      (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
  let betaMu := betaMeasure (r : ℝ) (K : ℝ)
  let sphereMu := complexUnitSphereProbabilityMeasure K
  let radiusMu := h19BaseColumnRadiusMeasure K r
  let positiveMu := h19BaseColumnPositiveRadiusMeasure K r
  let radius : ℝ → ℝ := fun q ↦ Real.sqrt (1 - q)
  let assemble : ComplexUnitSphere K × ℝ → EuclideanSpace ℂ (Fin K) :=
    fun p ↦ p.2 • p.1.1
  let _ : IsProbabilityMeasure betaMu :=
    isProbabilityMeasureBeta (by exact_mod_cast hr) (by exact_mod_cast hK)
  let _ : IsProbabilityMeasure sphereMu :=
    complexUnitSphereProbabilityMeasure_isProbability hK
  have hradius : Measure.map radius betaMu = radiusMu := by
    simpa only [radius, betaMu, radiusMu] using
      map_sqrt_one_sub_betaMeasure_eq_h19BaseColumnRadiusMeasure K r
  let _ : IsProbabilityMeasure radiusMu := by
    rw [← hradius]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hpositive :
      Measure.map (Subtype.val : Ioi (0 : ℝ) → ℝ) positiveMu = radiusMu := by
    simpa only [positiveMu, radiusMu] using
      map_h19BaseColumnPositiveRadiusMeasure K r
  let _ : IsProbabilityMeasure positiveMu := by
    refine ⟨?_⟩
    have hmass := congrArg (fun mu : Measure ℝ ↦ mu univ) hpositive
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ] at hmass
    simpa using hmass
  have hjoint :
      Measure.map (fun p : ℝ × ComplexUnitSphere K ↦ (p.2, radius p.1))
          (betaMu.prod sphereMu) = sphereMu.prod radiusMu := by
    calc
      Measure.map (fun p : ℝ × ComplexUnitSphere K ↦ (p.2, radius p.1))
          (betaMu.prod sphereMu) =
        Measure.map (Prod.swap ∘ Prod.map radius id)
          (betaMu.prod sphereMu) := by
            congr 1
      _ = Measure.map Prod.swap
          (Measure.map (Prod.map radius id) (betaMu.prod sphereMu)) := by
        rw [Measure.map_map measurable_swap (by fun_prop)]
      _ = Measure.map Prod.swap
          ((Measure.map radius betaMu).prod (Measure.map id sphereMu)) := by
        rw [Measure.map_prod_map betaMu sphereMu (by fun_prop) measurable_id]
      _ = Measure.map Prod.swap (radiusMu.prod sphereMu) := by
        rw [hradius, Measure.map_id]
      _ = sphereMu.prod radiusMu := Measure.prod_swap
  calc
    Measure.map (h19BaseColumnReconstruct K) (betaMu.prod sphereMu) =
      Measure.map assemble
        (Measure.map
          (fun p : ℝ × ComplexUnitSphere K ↦ (p.2, radius p.1))
          (betaMu.prod sphereMu)) := by
        rw [Measure.map_map (by fun_prop : Measurable assemble) (by fun_prop)]
        apply Measure.map_congr
        filter_upwards with p
        rfl
    _ = Measure.map assemble (sphereMu.prod radiusMu) := by rw [hjoint]
    _ = Measure.map assemble
        (sphereMu.prod
          (Measure.map (Subtype.val : Ioi (0 : ℝ) → ℝ) positiveMu)) := by
      rw [hpositive]
    _ = Measure.map assemble
        (Measure.map
          (Prod.map id (Subtype.val : Ioi (0 : ℝ) → ℝ))
          (sphereMu.prod positiveMu)) := by
      rw [← Measure.map_prod_map sphereMu positiveMu measurable_id
        measurable_subtype_coe, Measure.map_id]
    _ = Measure.map
        (assemble ∘ Prod.map id (Subtype.val : Ioi (0 : ℝ) → ℝ))
        (sphereMu.prod positiveMu) := by
      rw [Measure.map_map (by fun_prop : Measurable assemble) (by fun_prop)]
    _ = Measure.map
        (fun p : ComplexUnitSphere K × Ioi (0 : ℝ) ↦ p.2.1 • p.1.1)
        (sphereMu.prod positiveMu) := by
      congr 1
    _ = (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
      simpa only [sphereMu, positiveMu] using
        map_smul_h19BaseColumnSphereProbability_positiveRadius
          (K := K) (r := r) hK hr

/-! ## Coordinate volume on a raw complex column -/

/-- Uncurrying a finite real coordinate array preserves product Lebesgue
volume.  This is the bookkeeping bridge between coordinatewise complex
Lebesgue measure and the real orthonormal coordinates of complex Euclidean
space. -/
private theorem measurePreserving_h19BaseColumnRealUncurry (K : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.curry (Fin K) (Fin 2) ℝ).symm
      (volume : Measure (Fin K → Fin 2 → ℝ))
      (volume : Measure (Fin K × Fin 2 → ℝ)) := by
  let e := (MeasurableEquiv.curry (Fin K) (Fin 2) ℝ).symm
  refine ⟨e.measurable, ?_⟩
  rw [show (volume : Measure (Fin K → Fin 2 → ℝ)) =
      Measure.pi (fun _ : Fin K ↦
        Measure.pi (fun _ : Fin 2 ↦ (volume : Measure ℝ))) by
        simp only [MeasureTheory.volume_pi],
    show (volume : Measure (Fin K × Fin 2 → ℝ)) =
      Measure.pi (fun _ : Fin K × Fin 2 ↦ (volume : Measure ℝ)) by
        exact MeasureTheory.volume_pi]
  apply (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [Measure.map_apply e.measurable
    (MeasurableSet.univ_pi hs)]
  have hpre :
      e ⁻¹' (univ.pi s) =
        univ.pi (fun i : Fin K ↦ univ.pi fun j : Fin 2 ↦ s (i, j)) := by
    ext x
    simp [e, MeasurableEquiv.curry]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type'
    (fun i j ↦ (volume : Measure ℝ) (s (i, j)))).symm

/-- Raw complex coordinates, separated into one flat family of real and
imaginary coordinates. -/
private def h19BaseColumnRawRealCoordinates (K : ℕ) :
    (Fin K → ℂ) ≃ᵐ (Fin K × Fin 2 → ℝ) :=
  (MeasurableEquiv.piCongrRight
      (fun _ : Fin K ↦ Complex.measurableEquivPi)).trans
    (MeasurableEquiv.curry (Fin K) (Fin 2) ℝ).symm

/-- Coordinatewise complex Lebesgue measure becomes ordinary real product
Lebesgue measure under real/imaginary separation. -/
private theorem measurePreserving_h19BaseColumnRawRealCoordinates (K : ℕ) :
    MeasurePreserving (h19BaseColumnRawRealCoordinates K)
      (volume : Measure (Fin K → ℂ))
      (volume : Measure (Fin K × Fin 2 → ℝ)) := by
  have hcoord : MeasurePreserving
      (fun x : Fin K → ℂ ↦ fun i ↦ Complex.measurableEquivPi (x i))
      (volume : Measure (Fin K → ℂ))
      (volume : Measure (Fin K → Fin 2 → ℝ)) :=
    volume_preserving_pi
      (fun _ : Fin K ↦ Complex.volume_preserving_equiv_pi)
  exact (measurePreserving_h19BaseColumnRealUncurry K).comp hcoord

/-- The real orthonormal coordinates of a complex Euclidean vector. -/
private def h19BaseColumnEuclideanRealCoordinates (K : ℕ) :
    EuclideanSpace ℂ (Fin K) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin K × Fin 2) :=
  ((Pi.orthonormalBasis
    (fun _ : Fin K ↦ Complex.orthonormalBasisOneI)).reindex
      (Equiv.sigmaEquivProd (Fin K) (Fin 2))).repr

/-- Forgetting the Euclidean wrapper on a complex column preserves the
canonical Lebesgue measure exactly. -/
theorem measurePreserving_h19BaseColumnOfLp (K : ℕ) :
    MeasurePreserving
      (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ))
      (volume : Measure (EuclideanSpace ℂ (Fin K)))
      (volume : Measure (Fin K → ℂ)) := by
  let eRaw := h19BaseColumnRawRealCoordinates K
  let eEuc := h19BaseColumnEuclideanRealCoordinates K
  have hRaw := measurePreserving_h19BaseColumnRawRealCoordinates K
  have hEuc : MeasurePreserving eEuc :=
    LinearIsometryEquiv.measurePreserving eEuc
  have hFlat := PiLp.volume_preserving_ofLp (Fin K × Fin 2)
  have htotal : MeasurePreserving
      (eRaw.symm ∘ WithLp.ofLp ∘ eEuc)
      (volume : Measure (EuclideanSpace ℂ (Fin K)))
      (volume : Measure (Fin K → ℂ)) :=
    hRaw.symm.comp (hFlat.comp hEuc)
  refine htotal.congr (by fun_prop) ?_
  filter_upwards with x
  funext i
  change Complex.measurableEquivPi.symm
      (fun j : Fin 2 ↦ WithLp.ofLp (eEuc x) (i, j)) =
    WithLp.ofLp x i
  apply Complex.measurableEquivPi.injective
  rw [Complex.measurableEquivPi.apply_symm_apply]
  funext j
  change
    (((Pi.orthonormalBasis
        (fun _ : Fin K ↦ Complex.orthonormalBasisOneI)).reindex
          (Equiv.sigmaEquivProd (Fin K) (Fin 2))).repr x) (i, j) =
      Complex.measurableEquivPi (WithLp.ofLp x i) j
  rw [OrthonormalBasis.repr_reindex]
  change
    (Pi.orthonormalBasis
        (fun _ : Fin K ↦ Complex.orthonormalBasisOneI)).repr x ⟨i, j⟩ =
      Complex.measurableEquivPi (WithLp.ofLp x i) j
  rw [show x = WithLp.toLp 2 (WithLp.ofLp x) by rfl,
    Pi.orthonormalBasis_repr,
    Complex.orthonormalBasisOneI_repr_apply]
  rfl

/-- The explicit density written on the raw column type used by the
successor-column induction. -/
def h19BaseColumnRawPDF (K r : ℕ) (u : Fin K → ℂ) : ℝ≥0∞ :=
  h19BaseColumnVectorPDF K r (WithLp.toLp 2 u)

theorem measurable_h19BaseColumnRawPDF (K r : ℕ) :
    Measurable (h19BaseColumnRawPDF K r) := by
  exact (measurable_h19BaseColumnVectorPDF K r).comp
    (WithLp.measurable_toLp 2 (Fin K → ℂ))

/-- Identity equivalence from the curried complex-coordinate measurable
space to the explicit matrix measurable-space instance. -/
private def h19BaseCurriedComplexMatrixMeasurableEquiv (K N : ℕ) :
    (Fin K → Fin N → ℂ) ≃ᵐ Matrix (Fin K) (Fin N) ℂ where
  toFun x := Matrix.of x
  invFun X i j := X i j
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun x : Fin K → Fin N → ℂ ↦ x)
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin K → Fin N → ℂ ↦ x)
    fun_prop

/-- Package a raw complex column as a `K × 1` matrix. -/
def h19BaseColumnMatrixMeasurableEquiv (K : ℕ) :
    (Fin K → ℂ) ≃ᵐ Matrix (Fin K) (Fin 1) ℂ :=
  (MeasurableEquiv.piCongrRight fun _ : Fin K ↦
    (MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℂ)).symm).trans
      (h19BaseCurriedComplexMatrixMeasurableEquiv K 1)

@[simp]
theorem h19BaseColumnMatrixMeasurableEquiv_apply
    {K : ℕ} (u : Fin K → ℂ) (i : Fin K) (j : Fin 1) :
    h19BaseColumnMatrixMeasurableEquiv K u i j = u i := by
  change (MeasurableEquiv.piUnique
    (fun _ : Fin 1 ↦ ℂ)).symm (u i) j = u i
  rw [MeasurableEquiv.piUnique_symm_apply]
  exact Subsingleton.elim j 0 ▸ rfl

@[simp]
theorem h19BaseColumnMatrixMeasurableEquiv_symm_apply
    {K : ℕ} (X : Matrix (Fin K) (Fin 1) ℂ) (i : Fin K) :
    (h19BaseColumnMatrixMeasurableEquiv K).symm X i = X i 0 := by
  change (MeasurableEquiv.piUnique
    (fun _ : Fin 1 ↦ ℂ)) (fun j ↦ X i j) = X i 0
  rw [MeasurableEquiv.piUnique_apply]
  rfl

/-- The singleton-column packaging preserves the literal rectangular
coordinate volume. -/
theorem measurePreserving_h19BaseColumnMatrixMeasurableEquiv (K : ℕ) :
    MeasurePreserving (h19BaseColumnMatrixMeasurableEquiv K)
      (volume : Measure (Fin K → ℂ))
      (complexRectangularLebesgueVolume K 1) := by
  have hrows : MeasurePreserving
      (fun u : Fin K → ℂ ↦
        fun i ↦ (MeasurableEquiv.piUnique
          (fun _ : Fin 1 ↦ ℂ)).symm (u i))
      (volume : Measure (Fin K → ℂ))
      (volume : Measure (Fin K → Fin 1 → ℂ)) :=
    volume_preserving_pi (fun _ : Fin K ↦
      (volume_preserving_piUnique (fun _ : Fin 1 ↦ ℂ)).symm)
  have hmatrix : MeasurePreserving
      (h19BaseCurriedComplexMatrixMeasurableEquiv K 1)
      (Measure.pi fun _ : Fin K ↦
        Measure.pi fun _ : Fin 1 ↦ (volume : Measure ℂ))
      (complexRectangularLebesgueVolume K 1) := by
    refine ⟨(h19BaseCurriedComplexMatrixMeasurableEquiv K 1).measurable, ?_⟩
    ext s hs
    rw [Measure.map_apply
      (h19BaseCurriedComplexMatrixMeasurableEquiv K 1).measurable hs]
    rfl
  exact hmatrix.comp hrows

/-- The explicit one-column density on Jiang's literal matrix type. -/
def h19BaseColumnMatrixPDF (K r : ℕ)
    (X : Matrix (Fin K) (Fin 1) ℂ) : ℝ≥0∞ :=
  h19BaseColumnRawPDF K r
    ((h19BaseColumnMatrixMeasurableEquiv K).symm X)

theorem measurable_h19BaseColumnMatrixPDF (K r : ℕ) :
    Measurable (h19BaseColumnMatrixPDF K r) := by
  exact (measurable_h19BaseColumnRawPDF K r).comp
    (h19BaseColumnMatrixMeasurableEquiv K).symm.measurable

/-- Transporting the raw column density to a singleton-column matrix keeps
the reference measure literally equal to Jiang's rectangular Lebesgue
measure. -/
theorem map_h19BaseColumnMatrixMeasurableEquiv_withDensity
    (K r : ℕ) :
    Measure.map (h19BaseColumnMatrixMeasurableEquiv K)
        ((volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawPDF K r)) =
      (complexRectangularLebesgueVolume K 1).withDensity
        (h19BaseColumnMatrixPDF K r) := by
  have htilt := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnMatrixMeasurableEquiv K)
    (h19BaseColumnMatrixPDF K r)
    (measurable_h19BaseColumnMatrixPDF K r)
  have hcomp :
      h19BaseColumnMatrixPDF K r ∘
          h19BaseColumnMatrixMeasurableEquiv K =
        h19BaseColumnRawPDF K r := by
    funext u
    simp [h19BaseColumnMatrixPDF]
  simpa only [hcomp] using htilt

/-! ## Identification with Jiang's displayed `N = 1` formula -/

/-- Squared Euclidean length of the unique column of a `K × 1` matrix. -/
def h19BaseColumnMatrixNormSq {K : ℕ}
    (X : Matrix (Fin K) (Fin 1) ℂ) : ℝ :=
  ∑ i, Complex.normSq (X i 0)

theorem h19BaseColumn_norm_sq_toLp {K : ℕ} (u : Fin K → ℂ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin K))‖ ^ 2 =
      ∑ i, Complex.normSq (u i) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.sq_norm (u i)

theorem h19BaseColumnMatrixNormSq_equiv_symm {K : ℕ}
    (X : Matrix (Fin K) (Fin 1) ℂ) :
    h19BaseColumnMatrixNormSq X =
      ‖(WithLp.toLp 2
        ((h19BaseColumnMatrixMeasurableEquiv K).symm X) :
          EuclideanSpace ℂ (Fin K))‖ ^ 2 := by
  rw [h19BaseColumn_norm_sq_toLp]
  unfold h19BaseColumnMatrixNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [h19BaseColumnMatrixMeasurableEquiv_symm_apply]

/-- In one column, the Gram determinant is the scalar unit-ball defect. -/
theorem h19BaseColumn_det_one_sub_gram {K : ℕ}
    (X : Matrix (Fin K) (Fin 1) ℂ) :
    (Matrix.det (1 - X.conjTranspose * X)).re =
      1 - h19BaseColumnMatrixNormSq X := by
  rw [Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.isValue, if_true]
  unfold h19BaseColumnMatrixNormSq
  have hsum :
      (∑ i, star (X i 0) * X i 0) =
        (((∑ i, Complex.normSq (X i 0) : ℝ) : ℂ)) := by
    calc
      (∑ i, star (X i 0) * X i 0) =
          ∑ i, ((Complex.normSq (X i 0) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Complex.normSq_eq_conj_mul_self.symm
      _ = (((∑ i, Complex.normSq (X i 0) : ℝ) : ℂ)) := by
        exact (Complex.ofReal_sum Finset.univ
          (fun i ↦ Complex.normSq (X i 0))).symm
  rw [hsum]
  simp

/-- For a singleton column index, Jiang's positive-semidefinite support is
exactly the scalar unit-ball inequality. -/
theorem h19BaseColumn_jiangSupport_iff {K : ℕ}
    (X : Matrix (Fin K) (Fin 1) ℂ) :
    jiangUnscaledTallHaarCornerSupport X ↔
      h19BaseColumnMatrixNormSq X ≤ 1 := by
  have hgram :
      (X.conjTranspose * X) 0 0 =
        ((h19BaseColumnMatrixNormSq X : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    unfold h19BaseColumnMatrixNormSq
    calc
      (∑ x, star (X x 0) * X x 0) =
          ∑ x, ((Complex.normSq (X x 0) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Complex.normSq_eq_conj_mul_self.symm
      _ = (((∑ x, Complex.normSq (X x 0) : ℝ) : ℂ)) := by
        exact (Complex.ofReal_sum Finset.univ
          (fun i ↦ Complex.normSq (X i 0))).symm
  have hquad (v : Fin 1 → ℂ) :
      (star v ⬝ᵥ ((1 - X.conjTranspose * X) *ᵥ v)).re =
        Complex.normSq (v 0) *
          (1 - h19BaseColumnMatrixNormSq X) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Pi.star_apply,
      Matrix.sub_apply, Matrix.one_apply, Fin.isValue, if_true, hgram]
    have hcomplex :
        star (v 0) *
            ((1 - ((h19BaseColumnMatrixNormSq X : ℝ) : ℂ)) * v 0) =
          ((Complex.normSq (v 0) *
            (1 - h19BaseColumnMatrixNormSq X) : ℝ) : ℂ) := by
      have hvnorm : star (v 0) * v 0 =
          ((Complex.normSq (v 0) : ℝ) : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      calc
        star (v 0) *
            ((1 - ((h19BaseColumnMatrixNormSq X : ℝ) : ℂ)) * v 0) =
          (star (v 0) * v 0) *
            (1 - ((h19BaseColumnMatrixNormSq X : ℝ) : ℂ)) := by ring
        _ = ((Complex.normSq (v 0) : ℝ) : ℂ) *
            (1 - ((h19BaseColumnMatrixNormSq X : ℝ) : ℂ)) := by rw [hvnorm]
        _ = ((Complex.normSq (v 0) *
            (1 - h19BaseColumnMatrixNormSq X) : ℝ) : ℂ) := by
          push_cast
          rfl
    rw [hcomplex]
    rfl
  unfold jiangUnscaledTallHaarCornerSupport
  constructor
  · intro h
    have hv := h (fun _ : Fin 1 ↦ 1)
    rw [hquad] at hv
    simpa using hv
  · intro h v
    have hvnonneg : 0 ≤ Complex.normSq (v 0) := Complex.normSq_nonneg _
    have hdefect : 0 ≤ 1 - h19BaseColumnMatrixNormSq X := sub_nonneg.mpr h
    have hprod := mul_nonneg hvnonneg hdefect
    rw [hquad]
    exact hprod

/-- Jiang's singleton-column normalizer is exactly the elementary polar
normalizer above. -/
theorem h19BaseColumnNormalizer_eq_jiang {K r : ℕ} (hr : 1 ≤ r) :
    jiangUnscaledTallHaarCornerNormalizer (K + r) K 1 =
      h19BaseColumnNormalizer K r := by
  unfold jiangUnscaledTallHaarCornerNormalizer h19BaseColumnNormalizer
  simp only [Nat.mul_one, Fin.prod_univ_one, Fin.val_zero, zero_add,
    Nat.cast_factorial]
  have hsub : K + r - 1 - K = r - 1 := by omega
  rw [hsub]
  ring

/-- Closed-ball spelling of the same vector density.  It differs from the
open-ball spelling only on the unit sphere. -/
def h19BaseColumnVectorClosedPDF (K r : ℕ)
    (x : EuclideanSpace ℂ (Fin K)) : ℝ≥0∞ :=
  if ‖x‖ ≤ 1 then
    ENNReal.ofReal
      (h19BaseColumnNormalizer K r * (1 - ‖x‖ ^ 2) ^ (r - 1))
  else 0

theorem measurable_h19BaseColumnVectorClosedPDF (K r : ℕ) :
    Measurable (h19BaseColumnVectorClosedPDF K r) := by
  unfold h19BaseColumnVectorClosedPDF
  apply Measurable.ite
  · exact measurableSet_Iic.preimage measurable_id.norm
  · exact (measurable_const.mul
      ((measurable_const.sub (measurable_id.norm.pow_const 2)).pow_const _)).ennreal_ofReal
  · exact measurable_const

/-- The open- and closed-ball spellings define exactly the same Lebesgue
density measure. -/
theorem withDensity_h19BaseColumnVectorClosedPDF_eq
    {K r : ℕ} (hK : 1 ≤ K) :
    (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorClosedPDF K r) =
      (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
  letI : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp (by omega)
  apply withDensity_congr_ae
  have hsphere :
      (volume : Measure (EuclideanSpace ℂ (Fin K)))
          (sphere (0 : EuclideanSpace ℂ (Fin K)) 1) = 0 :=
    Measure.addHaar_sphere
      (volume : Measure (EuclideanSpace ℂ (Fin K))) 0 1
  have haway :
      (sphere (0 : EuclideanSpace ℂ (Fin K)) 1)ᶜ ∈
        ae (volume : Measure (EuclideanSpace ℂ (Fin K))) :=
    mem_ae_iff.mpr (by simpa using hsphere)
  filter_upwards [haway] with x hx
  have hne : ‖x‖ ≠ 1 := by
    intro h
    exact hx (mem_sphere_zero_iff_norm.mpr h)
  unfold h19BaseColumnVectorClosedPDF h19BaseColumnVectorPDF
  by_cases hlt : ‖x‖ < 1
  · rw [if_pos hlt.le, if_pos hlt]
  · have hgt : 1 < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    rw [if_neg (not_le.mpr hgt), if_neg hlt]

/-- Closed-ball density on raw complex-column coordinates. -/
def h19BaseColumnRawClosedPDF (K r : ℕ) (u : Fin K → ℂ) : ℝ≥0∞ :=
  h19BaseColumnVectorClosedPDF K r (WithLp.toLp 2 u)

theorem measurable_h19BaseColumnRawClosedPDF (K r : ℕ) :
    Measurable (h19BaseColumnRawClosedPDF K r) := by
  exact (measurable_h19BaseColumnVectorClosedPDF K r).comp
    (WithLp.measurable_toLp 2 (Fin K → ℂ))

/-- Closed-ball density on Jiang's singleton-column matrix coordinates. -/
def h19BaseColumnMatrixClosedPDF (K r : ℕ)
    (X : Matrix (Fin K) (Fin 1) ℂ) : ℝ≥0∞ :=
  h19BaseColumnRawClosedPDF K r
    ((h19BaseColumnMatrixMeasurableEquiv K).symm X)

theorem measurable_h19BaseColumnMatrixClosedPDF (K r : ℕ) :
    Measurable (h19BaseColumnMatrixClosedPDF K r) := by
  exact (measurable_h19BaseColumnRawClosedPDF K r).comp
    (h19BaseColumnMatrixMeasurableEquiv K).symm.measurable

/-- Pointwise, Jiang's displayed `N = 1` density is exactly the closed-ball
spelling of the elementary polar density. -/
theorem jiangUnscaledTallHaarCornerPDF_add_one_eq_baseClosedPDF
    {K r : ℕ} (hr : 1 ≤ r)
    (X : Matrix (Fin K) (Fin 1) ℂ) :
    jiangUnscaledTallHaarCornerPDF (K + r) K 1 X =
      h19BaseColumnMatrixClosedPDF K r X := by
  have hexp : K + r - K - 1 = r - 1 := by omega
  unfold jiangUnscaledTallHaarCornerPDF h19BaseColumnMatrixClosedPDF
    h19BaseColumnRawClosedPDF h19BaseColumnVectorClosedPDF
  rw [h19BaseColumn_jiangSupport_iff,
    h19BaseColumn_det_one_sub_gram,
    h19BaseColumnNormalizer_eq_jiang hr, hexp,
    h19BaseColumnMatrixNormSq_equiv_symm]
  let x : EuclideanSpace ℂ (Fin K) :=
    WithLp.toLp 2 ((h19BaseColumnMatrixMeasurableEquiv K).symm X)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hiff : ‖x‖ ^ 2 ≤ 1 ↔ ‖x‖ ≤ 1 := by
    constructor <;> intro h <;> nlinarith
  change (if ‖x‖ ^ 2 ≤ 1 then _ else _) =
    if ‖x‖ ≤ 1 then _ else _
  by_cases h : ‖x‖ ≤ 1
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hs ↦ h (hiff.mp hs)), if_neg h]

/-- Consequently the open-ball base PDF and Jiang's literal closed-support
PDF define the same rectangular Lebesgue-density measure. -/
theorem withDensity_h19BaseColumnMatrixPDF_eq_jiang
    {K r : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r) :
    (complexRectangularLebesgueVolume K 1).withDensity
        (h19BaseColumnMatrixPDF K r) =
      (complexRectangularLebesgueVolume K 1).withDensity
        (jiangUnscaledTallHaarCornerPDF (K + r) K 1) := by
  have hopenRaw := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnOfLp K)
    (h19BaseColumnRawPDF K r)
    (measurable_h19BaseColumnRawPDF K r)
  have hclosedRaw := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnOfLp K)
    (h19BaseColumnRawClosedPDF K r)
    (measurable_h19BaseColumnRawClosedPDF K r)
  have hopenComp :
      h19BaseColumnRawPDF K r ∘
          (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)) =
        h19BaseColumnVectorPDF K r := by
    funext x
    rfl
  have hclosedComp :
      h19BaseColumnRawClosedPDF K r ∘
          (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)) =
        h19BaseColumnVectorClosedPDF K r := by
    funext x
    rfl
  rw [hopenComp] at hopenRaw
  rw [hclosedComp] at hclosedRaw
  have hraw :
      (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawPDF K r) =
        (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawClosedPDF K r) := by
    calc
      (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawPDF K r) =
        Measure.map WithLp.ofLp
          ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
            (h19BaseColumnVectorPDF K r)) := hopenRaw.symm
      _ = Measure.map WithLp.ofLp
          ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
            (h19BaseColumnVectorClosedPDF K r)) := by
        rw [withDensity_h19BaseColumnVectorClosedPDF_eq hK]
      _ = (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawClosedPDF K r) := hclosedRaw
  have hclosedMatrix := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnMatrixMeasurableEquiv K)
    (h19BaseColumnMatrixClosedPDF K r)
    (measurable_h19BaseColumnMatrixClosedPDF K r)
  have hclosedMatrixComp :
      h19BaseColumnMatrixClosedPDF K r ∘
          h19BaseColumnMatrixMeasurableEquiv K =
        h19BaseColumnRawClosedPDF K r := by
    funext u
    simp [h19BaseColumnMatrixClosedPDF]
  rw [hclosedMatrixComp] at hclosedMatrix
  calc
    (complexRectangularLebesgueVolume K 1).withDensity
        (h19BaseColumnMatrixPDF K r) =
      Measure.map (h19BaseColumnMatrixMeasurableEquiv K)
        ((volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawPDF K r)) :=
      (map_h19BaseColumnMatrixMeasurableEquiv_withDensity K r).symm
    _ = Measure.map (h19BaseColumnMatrixMeasurableEquiv K)
        ((volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawClosedPDF K r)) := by rw [hraw]
    _ = (complexRectangularLebesgueVolume K 1).withDensity
        (h19BaseColumnMatrixClosedPDF K r) := hclosedMatrix
    _ = (complexRectangularLebesgueVolume K 1).withDensity
        (jiangUnscaledTallHaarCornerPDF (K + r) K 1) := by
      congr 1
      funext X
      exact (jiangUnscaledTallHaarCornerPDF_add_one_eq_baseClosedPDF hr X).symm

/-! ## Uniform-sphere and Haar-column density endpoints -/

/-- The top `K` coordinates of a uniform vector in the complex sphere of
dimension `K+r` have the explicit complex-ball density. -/
theorem map_h1TopCoordinates_complexUnitSphereProbabilityMeasure_withDensity
    {K r : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r) :
    Measure.map (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1)
        (complexUnitSphereProbabilityMeasure (K + r)) =
      (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
  rw [map_h1TopCoordinates_complexUnitSphereProbabilityMeasure hK hr,
    map_h19BaseColumnReconstruct_betaSphere hK hr]

/-- Every fixed Haar column has the same literal top-coordinate Lebesgue
density.  This is the vector-valued `N=1` base case. -/
theorem map_topCoordinates_haarColumnSphere_withDensity
    {K r : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r) (j : Fin (K + r)) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin (K + r)) ℂ ↦
          h1TopCoordinates (haarColumnSphere (by omega : 1 ≤ K + r) j U).1)
        (unitaryHaarProbabilityMeasure (K + r)) =
      (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) := by
  let hKr : 1 ≤ K + r := by omega
  have hcol := map_haarColumnSphere_unitaryHaarProbabilityMeasure hKr j
  have htop : Measurable
      (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1) := by
    unfold h1TopCoordinates
    fun_prop
  calc
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin (K + r)) ℂ ↦
          h1TopCoordinates (haarColumnSphere hKr j U).1)
        (unitaryHaarProbabilityMeasure (K + r)) =
      Measure.map (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1)
        (Measure.map (haarColumnSphere hKr j)
          (unitaryHaarProbabilityMeasure (K + r))) := by
        rw [Measure.map_map htop (measurable_haarColumnSphere hKr j)]
        apply Measure.map_congr
        filter_upwards with U
        rfl
    _ = Measure.map (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1)
        (complexUnitSphereProbabilityMeasure (K + r)) := by rw [hcol]
    _ = (volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
        (h19BaseColumnVectorPDF K r) :=
      map_h1TopCoordinates_complexUnitSphereProbabilityMeasure_withDensity hK hr

/-- The same fixed-Haar-column result on literal raw complex coordinates.
The reference measure is the coordinatewise product of complex Lebesgue
measure, rather than an abstract pushforward. -/
theorem map_topCoordinates_haarColumnSphere_raw_withDensity
    {K r : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r) (j : Fin (K + r)) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin (K + r)) ℂ ↦
          WithLp.ofLp
            (h1TopCoordinates
              (haarColumnSphere (by omega : 1 ≤ K + r) j U).1))
        (unitaryHaarProbabilityMeasure (K + r)) =
      (volume : Measure (Fin K → ℂ)).withDensity
        (h19BaseColumnRawPDF K r) := by
  let source : Matrix.unitaryGroup (Fin (K + r)) ℂ →
      EuclideanSpace ℂ (Fin K) :=
    fun U ↦ h1TopCoordinates
      (haarColumnSphere (by omega : 1 ≤ K + r) j U).1
  have hsource : Measurable source := by
    have htop : Measurable
        (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1) := by
      unfold h1TopCoordinates
      fun_prop
    exact htop.comp
      (measurable_haarColumnSphere (by omega : 1 ≤ K + r) j)
  have hv := map_topCoordinates_haarColumnSphere_withDensity hK hr j
  have htilt := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnOfLp K)
    (h19BaseColumnRawPDF K r)
    (measurable_h19BaseColumnRawPDF K r)
  have hcomp :
      h19BaseColumnRawPDF K r ∘
          (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)) =
        h19BaseColumnVectorPDF K r := by
    funext x
    rfl
  rw [hcomp] at htilt
  calc
    Measure.map (fun U ↦ WithLp.ofLp (source U))
        (unitaryHaarProbabilityMeasure (K + r)) =
      Measure.map WithLp.ofLp
        (Measure.map source (unitaryHaarProbabilityMeasure (K + r))) := by
          rw [Measure.map_map
            (measurePreserving_h19BaseColumnOfLp K).measurable hsource]
          apply Measure.map_congr
          filter_upwards with U
          rfl
    _ = Measure.map WithLp.ofLp
        ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
          (h19BaseColumnVectorPDF K r)) := by
            rw [hv]
    _ = (volume : Measure (Fin K → ℂ)).withDensity
        (h19BaseColumnRawPDF K r) := htilt

/-- The literal `K × 1` upper-left Haar corner has the singleton-column
matrix version of the explicit ball density. -/
theorem jiangUnscaledTallHaarCornerLaw_add_one_withDensity_basePDF
    {K r : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r) :
    jiangUnscaledTallHaarCornerLaw (K + r) K 1 =
      (complexRectangularLebesgueVolume K 1).withDensity
        (h19BaseColumnMatrixPDF K r) := by
  let hKr : 1 ≤ K + r := by omega
  let hKM : K ≤ K + r := Nat.le_add_right K r
  let h1M : 1 ≤ K + r := hKr
  let j0 : Fin (K + r) := Fin.castLE h1M (0 : Fin 1)
  let raw : Matrix.unitaryGroup (Fin (K + r)) ℂ → Fin K → ℂ :=
    fun U ↦ WithLp.ofLp
      (h1TopCoordinates (haarColumnSphere hKr j0 U).1)
  have hraw := map_topCoordinates_haarColumnSphere_raw_withDensity
    hK hr j0
  have hrawMeas : Measurable raw := by
    have htop : Measurable
        (fun z : ComplexUnitSphere (K + r) ↦ h1TopCoordinates z.1) := by
      unfold h1TopCoordinates
      fun_prop
    exact (WithLp.measurable_ofLp 2 (Fin K → ℂ)).comp
      (htop.comp (measurable_haarColumnSphere hKr j0))
  calc
    jiangUnscaledTallHaarCornerLaw (K + r) K 1 =
        Measure.map (h19BaseColumnMatrixMeasurableEquiv K)
          (Measure.map raw (unitaryHaarProbabilityMeasure (K + r))) := by
      rw [jiangUnscaledTallHaarCornerLaw,
        dif_pos (show K ≤ K + r ∧ 1 ≤ K + r from ⟨hKM, h1M⟩)]
      rw [Measure.map_map
        (h19BaseColumnMatrixMeasurableEquiv K).measurable
        hrawMeas]
      apply Measure.map_congr
      filter_upwards with U
      ext i j
      simp only [Function.comp_apply]
      rw [h19BaseColumnMatrixMeasurableEquiv_apply]
      unfold jiangUnscaledTallHaarCornerMatrix topLeftUnitaryBlock raw
      change
        (U : Matrix (Fin (K + r)) (Fin (K + r)) ℂ)
            (Fin.castLE hKM i) (Fin.castLE h1M j) =
          (haarColumnSphere hKr j0 U).1 (Fin.castAdd r i)
      rw [haarColumnSphere_apply]
      have hi : Fin.castLE hKM i = Fin.castAdd r i := by
        apply Fin.ext
        rfl
      have hj : Fin.castLE h1M j = j0 := by
        apply Fin.ext
        exact Subsingleton.elim j 0 ▸ rfl
      rw [hi, hj]
    _ = Measure.map (h19BaseColumnMatrixMeasurableEquiv K)
        ((volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawPDF K r)) := by
      rw [hraw]
    _ = (complexRectangularLebesgueVolume K 1).withDensity
        (h19BaseColumnMatrixPDF K r) :=
      map_h19BaseColumnMatrixMeasurableEquiv_withDensity K r

/-- Foundations-only `N = 1` case of Jiang Proposition 2.1, first in the
canonical ambient spelling `M = K+r`. -/
theorem jiang_2009_prop2_1_unscaledTallHaarCorner_density_N1_add
    {K r : ℕ} (hK : 0 < K) (hr : 1 ≤ r) :
    jiangUnscaledTallHaarCornerLaw (K + r) K 1 =
      (complexRectangularLebesgueVolume K 1).withDensity
        (jiangUnscaledTallHaarCornerPDF (K + r) K 1) := by
  calc
    jiangUnscaledTallHaarCornerLaw (K + r) K 1 =
        (complexRectangularLebesgueVolume K 1).withDensity
          (h19BaseColumnMatrixPDF K r) :=
      jiangUnscaledTallHaarCornerLaw_add_one_withDensity_basePDF hK hr
    _ = (complexRectangularLebesgueVolume K 1).withDensity
        (jiangUnscaledTallHaarCornerPDF (K + r) K 1) :=
      withDensity_h19BaseColumnMatrixPDF_eq_jiang hK hr

/-- Foundations-only theorem matching the raw Jiang density axiom exactly
after specializing its column count to `N = 1`. -/
theorem jiang_2009_prop2_1_unscaledTallHaarCorner_density_N1
    {M K : ℕ} (hK : 0 < K) (hs : K + 1 ≤ M) :
    jiangUnscaledTallHaarCornerLaw M K 1 =
      (complexRectangularLebesgueVolume K 1).withDensity
        (jiangUnscaledTallHaarCornerPDF M K 1) := by
  let r := M - K
  have hr : 1 ≤ r := by
    dsimp [r]
    omega
  have hsum : K + r = M := by
    dsimp [r]
    omega
  rw [← hsum]
  exact jiang_2009_prop2_1_unscaledTallHaarCorner_density_N1_add hK hr

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
