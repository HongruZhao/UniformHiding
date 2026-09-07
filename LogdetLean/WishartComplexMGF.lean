import LogdetLean.WishartActualComplexBridge
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
# The exact complex MGF and characteristic function of `M_R`

The preceding modules derive the real MGF from the original Gaussian row
model and identify its finite product with the branch-safe complex Gamma
product.  This file uses Mathlib's holomorphy theorem for `complexMGF` and the
one-variable identity principle to continue that real identity to a vertical
strip.  Since the whole imaginary axis lies in the strip, the result includes
the exact characteristic function.

This is the analytic-continuation step in Zhao, arXiv:2608.00565v1,
Lemma 5.4.  The continuation mechanism is the same as Mathlib's
`ProbabilityTheory.eqOn_complexMGF_of_mgf'`; unlike that theorem, the second
analytic function here is an explicit Gamma product rather than the complex
MGF of a second random variable.
-/

namespace LogdetLean

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

/-- Sum of the positive spectral weights `1 + lambda_i(R-I)`.  We only use
it as a convenient finite upper bound for every individual weight. -/
def wishartSpectralMass {p : ℕ} (R : CorrelationMatrix p) : ℝ :=
  ∑ i, (1 + R.deviationEigenvalues i)

theorem wishartSpectralMass_nonneg {p : ℕ} (R : CorrelationMatrix p) :
    0 ≤ wishartSpectralMass R := by
  unfold wishartSpectralMass
  exact Finset.sum_nonneg fun i _ ↦
    (R.one_add_deviationEigenvalue_pos i).le

theorem wishartSpectralWeight_le_mass {p : ℕ}
    (R : CorrelationMatrix p) (i : Fin p) :
    1 + R.deviationEigenvalues i ≤ wishartSpectralMass R := by
  unfold wishartSpectralMass
  exact Finset.single_le_sum
    (fun j _ ↦ (R.one_add_deviationEigenvalue_pos j).le)
    (Finset.mem_univ i)

/-- An explicit positive half-width on which every Gamma shape and every
spectral Laplace rate stays in the open right half-plane. -/
def wishartComplexMGFRadius {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) : ℝ :=
  min (1 / 4 : ℝ)
    ((m : ℝ) / (4 * (1 + wishartSpectralMass R)))

theorem wishartComplexMGFRadius_pos {m p : ℕ} (hm : 0 < m)
    (R : CorrelationMatrix p) :
    0 < wishartComplexMGFRadius m R := by
  unfold wishartComplexMGFRadius
  apply lt_min
  · norm_num
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmass := wishartSpectralMass_nonneg R
    positivity

private theorem transform_domain_of_abs_lt_radius
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {t : ℝ}
    (ht : |t| < wishartComplexMGFRadius m R) :
    (∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t) ∧
      (∀ n < p,
        0 < (1 / 2 : ℝ) + wishartSpectralTiltCoefficient m R t n) := by
  have hr_quarter : wishartComplexMGFRadius m R ≤ (1 / 4 : ℝ) :=
    min_le_left _ _
  have hr_rate : wishartComplexMGFRadius m R ≤
      (m : ℝ) / (4 * (1 + wishartSpectralMass R)) :=
    min_le_right _ _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · intro n hn
    have hnm : n < m := lt_of_lt_of_le hn hp
    have hsub : 1 ≤ m - n := Nat.one_le_iff_ne_zero.mpr
      (Nat.sub_ne_zero_iff_lt.mpr hnm)
    have hshape : (1 / 2 : ℝ) ≤ (((m - n : ℕ) : ℝ) / 2) := by
      exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
        (by exact_mod_cast hsub)
    have htneg : -(1 / 4 : ℝ) < t := by
      exact neg_lt_of_abs_lt (ht.trans_le hr_quarter)
    linarith
  · intro n hn
    rw [wishartSpectralTiltCoefficient]
    simp only [hn, dite_true]
    let i : Fin p := ⟨n, hn⟩
    have hweight : 0 < 1 + R.deviationEigenvalues i :=
      R.one_add_deviationEigenvalue_pos i
    have hweight_le :
        1 + R.deviationEigenvalues i ≤ 1 + wishartSpectralMass R := by
      linarith [wishartSpectralWeight_le_mass R i]
    have hden : 0 < 4 * (1 + wishartSpectralMass R) := by
      have := wishartSpectralMass_nonneg R
      positivity
    have hmass_one : 0 < 1 + wishartSpectralMass R := by
      linarith [wishartSpectralMass_nonneg R]
    have htbound :
        |t| < (m : ℝ) / (4 * (1 + wishartSpectralMass R)) :=
      ht.trans_le hr_rate
    have hscaled :
        |t| * (1 + R.deviationEigenvalues i) / (m : ℝ) < 1 / 4 := by
      have hmul :
          |t| * (1 + R.deviationEigenvalues i) < (m : ℝ) / 4 := by
        calc
          |t| * (1 + R.deviationEigenvalues i) ≤
              |t| * (1 + wishartSpectralMass R) := by
                gcongr
          _ < ((m : ℝ) / (4 * (1 + wishartSpectralMass R))) *
                (1 + wishartSpectralMass R) := by
              exact mul_lt_mul_of_pos_right htbound hmass_one
          _ = (m : ℝ) / 4 := by
              field_simp [ne_of_gt hmass_one]
      rw [div_lt_iff₀ hmR]
      nlinarith
    have hlower :
        -(1 / 4 : ℝ) <
          t * (1 + R.deviationEigenvalues i) / (m : ℝ) := by
      calc
        -(1 / 4 : ℝ) <
            -(|t| * (1 + R.deviationEigenvalues i) / (m : ℝ)) := by
              linarith
        _ ≤ t * (1 + R.deviationEigenvalues i) / (m : ℝ) := by
          have habs : -|t| ≤ t := neg_abs_le t
          have hmul := mul_le_mul_of_nonneg_right habs hweight.le
          rw [show
            -(|t| * (1 + R.deviationEigenvalues i) / (m : ℝ)) =
              (-|t| * (1 + R.deviationEigenvalues i)) / (m : ℝ) by ring]
          exact (div_le_div_iff_of_pos_right hmR).mpr hmul
    dsimp [i] at hlower ⊢
    linarith

/-- The explicit branch-safe continuation of the actual real MGF. -/
def actualWishartComplexTransform {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (z : ℂ) : ℂ :=
  Complex.exp
      (z * ((-(GeneralRDecomposition.W0LogDetMean m p) + (p : ℝ) : ℝ) : ℂ)) *
    complexWishartCorrelationTransform R m z

theorem actualWishartComplexTransform_ofReal
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {t : ℝ}
    (ht : |t| < wishartComplexMGFRadius m R) :
    ((∫ z, Real.exp (t * GeneralRDecomposition.M_R m R z)
        ∂standardGaussianDataMeasure m p : ℝ) : ℂ) =
      actualWishartComplexTransform m R (t : ℂ) := by
  obtain ⟨hshape, hrate⟩ :=
    transform_domain_of_abs_lt_radius hm hp R ht
  rw [ofReal_integral_exp_mul_M_R_eq_complexWishartCorrelationTransform
    hm hp R hshape hrate]
  unfold actualWishartComplexTransform
  congr 1
  push_cast
  ring_nf

theorem integrable_exp_mul_M_R_of_abs_lt_radius
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {t : ℝ}
    (ht : |t| < wishartComplexMGFRadius m R) :
    Integrable
      (fun z ↦ Real.exp (t * GeneralRDecomposition.M_R m R z))
      (standardGaussianDataMeasure m p) := by
  obtain ⟨hshape, hrate⟩ :=
    transform_domain_of_abs_lt_radius hm hp R ht
  exact integrable_exp_mul_M_R hm hp R hshape hrate

/-! ## Holomorphic continuation to the imaginary axis -/

/-- The connected open vertical strip on which both the probabilistic
complex MGF and the explicit finite Gamma product are holomorphic. -/
def wishartComplexMGFStrip {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) : Set ℂ :=
  Complex.re ⁻¹' Ioo (-wishartComplexMGFRadius m R)
    (wishartComplexMGFRadius m R)

theorem isOpen_wishartComplexMGFStrip {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) :
    IsOpen (wishartComplexMGFStrip m R) := by
  exact isOpen_Ioo.preimage Complex.continuous_re

theorem isPreconnected_wishartComplexMGFStrip {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) :
    IsPreconnected (wishartComplexMGFStrip m R) := by
  exact (convex_Ioo _ _).linear_preimage Complex.reLm |>.isPreconnected

theorem imaginary_mem_wishartComplexMGFStrip
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (u : ℝ) :
    (u : ℂ) * Complex.I ∈ wishartComplexMGFStrip m R := by
  have hr := wishartComplexMGFRadius_pos hm R
  constructor <;> simpa using hr

private theorem differentiableAt_complexWishartDiagonalStageExponent
    {m r : ℝ} {z : ℂ}
    (hrate : 0 < (((m / 2 : ℝ) : ℂ) + (r : ℂ) * z).re) :
    DifferentiableAt ℂ (complexWishartDiagonalStageExponent m r) z := by
  have haff : DifferentiableAt ℂ
      (fun w : ℂ ↦ ((m / 2 : ℝ) : ℂ) + (r : ℂ) * w) z := by
    fun_prop
  have hslit : ((m / 2 : ℝ) : ℂ) + (r : ℂ) * z ∈
      Complex.slitPlane := Or.inl hrate
  have hlog : DifferentiableAt ℂ
      (fun w : ℂ ↦ Complex.log
        (((m / 2 : ℝ) : ℂ) + (r : ℂ) * w)) z :=
    haff.clog hslit
  unfold complexWishartDiagonalStageExponent
  dsimp
  have hleft : DifferentiableAt ℂ
      (fun w : ℂ ↦
        (((m / 2) * Real.log (m / 2) : ℝ) : ℂ) +
          w * (Real.log m : ℂ)) z :=
    (differentiableAt_const _).add
      (differentiableAt_id.mul_const (Real.log m : ℂ))
  have hright : DifferentiableAt ℂ
      (fun w : ℂ ↦ (((m / 2 : ℝ) : ℂ) + w) *
        Complex.log (((m / 2 : ℝ) : ℂ) + (r : ℂ) * w)) z :=
    ((differentiableAt_const _).add differentiableAt_id).mul hlog
  exact hleft.sub hright

private theorem differentiableAt_complexWishartDiagonalStageTransform
    {m n : ℕ} {r : ℝ} {z : ℂ}
    (hshape : 0 <
      (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + z).re)
    (hrate : 0 <
      ((((m : ℝ) / 2 : ℝ) : ℂ) + (r : ℂ) * z).re) :
    DifferentiableAt ℂ
      (complexWishartDiagonalStageTransform m n r) z := by
  have hgamma : DifferentiableAt ℂ
      (fun w : ℂ ↦ Complex.Gamma
        (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + w)) z := by
    have hout : DifferentiableAt ℂ Complex.Gamma
        (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + z) := by
      apply Complex.differentiableAt_Gamma
      intro k heq
      have hre := congrArg Complex.re heq
      simp at hre
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hs : 0 < (((m - n : ℕ) : ℝ) / 2) + z.re := by
        simpa using hshape
      linarith
    exact hout.comp z (by fun_prop)
  have hexponent : DifferentiableAt ℂ
      (complexWishartDiagonalStageExponent (m : ℝ) r) z :=
    differentiableAt_complexWishartDiagonalStageExponent hrate
  unfold complexWishartDiagonalStageTransform
  exact (hgamma.div_const _).mul hexponent.cexp

private theorem differentiableOn_actualWishartComplexTransform_strip
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) :
    DifferentiableOn ℂ (actualWishartComplexTransform m R)
      (wishartComplexMGFStrip m R) := by
  intro z hz
  have hzabs : |z.re| < wishartComplexMGFRadius m R := by
    simpa [wishartComplexMGFStrip, abs_lt] using hz
  obtain ⟨hshape, hrate⟩ :=
    transform_domain_of_abs_lt_radius hm hp R hzabs
  have hprod : DifferentiableAt ℂ
      (complexWishartCorrelationTransform R m) z := by
    unfold complexWishartCorrelationTransform
    apply DifferentiableAt.fun_finsetProd
    intro i _hi
    apply differentiableAt_complexWishartDiagonalStageTransform
    · simpa using hshape i i.2
    · have hrate_i := hrate i i.2
      rw [wishartSpectralTiltCoefficient_fin] at hrate_i
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmR
      have hfactor :
          (m : ℝ) / 2 +
              (1 + R.deviationEigenvalues i) * z.re =
            (m : ℝ) *
              ((1 / 2 : ℝ) +
                z.re * (1 + R.deviationEigenvalues i) / (m : ℝ)) := by
        field_simp [hm_ne]
      have : 0 < (m : ℝ) / 2 +
          (1 + R.deviationEigenvalues i) * z.re := by
        rw [hfactor]
        positivity
      simpa using this
  unfold actualWishartComplexTransform
  exact (by fun_prop : DifferentiableAt ℂ
    (fun w : ℂ ↦ Complex.exp
      (w * ((-(GeneralRDecomposition.W0LogDetMean m p) +
        (p : ℝ) : ℝ) : ℂ))) z).mul hprod |>.differentiableWithinAt

theorem analyticOnNhd_actualWishartComplexTransform_strip
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) :
    AnalyticOnNhd ℂ (actualWishartComplexTransform m R)
      (wishartComplexMGFStrip m R) :=
  (differentiableOn_actualWishartComplexTransform_strip hm hp R).analyticOnNhd
    (isOpen_wishartComplexMGFStrip m R)

private theorem strip_re_mem_interior_integrableExpSet
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {z : ℂ}
    (hz : z ∈ wishartComplexMGFStrip m R) :
    z.re ∈ interior
      (integrableExpSet (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p)) := by
  apply interior_maximal _ isOpen_Ioo hz
  intro t ht
  exact integrable_exp_mul_M_R_of_abs_lt_radius hm hp R
    (by simpa [abs_lt] using ht)

theorem analyticOnNhd_complexMGF_M_R_strip
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) :
    AnalyticOnNhd ℂ
      (complexMGF (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p))
      (wishartComplexMGFStrip m R) := by
  exact analyticOnNhd_complexMGF.mono fun z hz ↦
    strip_re_mem_interior_integrableExpSet hm hp R hz

/-- Analytic continuation of the exact real MGF identity to the whole
vertical strip. -/
theorem eqOn_complexMGF_M_R_actualWishartComplexTransform
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) :
    EqOn
      (complexMGF (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p))
      (actualWishartComplexTransform m R)
      (wishartComplexMGFStrip m R) := by
  let X := GeneralRDecomposition.M_R m R
  let mu := standardGaussianDataMeasure m p
  let T := actualWishartComplexTransform m R
  let U := wishartComplexMGFStrip m R
  have hX : AnalyticOnNhd ℂ (complexMGF X mu) U := by
    simpa [X, mu, U] using analyticOnNhd_complexMGF_M_R_strip hm hp R
  have hT : AnalyticOnNhd ℂ T U := by
    simpa [T, U] using
      analyticOnNhd_actualWishartComplexTransform_strip hm hp R
  have hzero : (0 : ℂ) ∈ U := by
    have hr := wishartComplexMGFRadius_pos hm R
    simpa [U, wishartComplexMGFStrip] using And.intro hr hr
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hT
    (by simpa [U] using isPreconnected_wishartComplexMGFStrip m R)
    hzero ?_
  have hevent : ∀ᶠ x : ℝ in 𝓝 0,
      |x| < wishartComplexMGFRadius m R := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨wishartComplexMGFRadius m R,
      wishartComplexMGFRadius_pos hm R, ?_⟩
    intro y hy
    simpa [Real.dist_eq] using hy
  have h_real : ∃ᶠ x : ℝ in
      nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
      complexMGF X mu x = T x := by
    have heq : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ,
        complexMGF X mu x = T x := by
      filter_upwards [hevent.filter_mono inf_le_left] with x hx
      rw [complexMGF_ofReal]
      simpa [X, mu, T, mgf] using
        actualWishartComplexTransform_ofReal hm hp R hx
    exact heq.frequently
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · change Tendsto (Complex.ofReal ∘ xs) atTop
        (𝓝 (Complex.ofReal 0))
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hx_tendsto.1
    · simpa using hx_tendsto.2
  · simpa [X, mu, T] using hx_eq n

/-- Exact complex MGF of the actual Gaussian statistic on the imaginary
axis. -/
theorem complexMGF_M_R_imaginary
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) (u : ℝ) :
    complexMGF (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p) ((u : ℂ) * Complex.I) =
      actualWishartComplexTransform m R ((u : ℂ) * Complex.I) :=
  eqOn_complexMGF_M_R_actualWishartComplexTransform hm hp R
    (imaginary_mem_wishartComplexMGFStrip hm R u)

/-- Exact characteristic function of `M_R` under the original Gaussian row
model.  No Wishart distribution is postulated: every preceding law identity
was proved as a pushforward from `standardGaussianDataMeasure`. -/
theorem charFun_map_M_R
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) (u : ℝ) :
    charFun
        (Measure.map (GeneralRDecomposition.M_R m R)
          (standardGaussianDataMeasure m p)) u =
      actualWishartComplexTransform m R ((u : ℂ) * Complex.I) := by
  rw [← complexMGF_mul_I
    (GeneralRDecomposition.measurable_M_R m R).aemeasurable]
  exact complexMGF_M_R_imaginary hm hp R u

end

end LogdetLean
