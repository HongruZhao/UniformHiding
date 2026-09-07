import LogdetLean.ElementaryVarianceRatio
import LogdetLean.NullUniformEdgeworthTarget
import LogdetLean.GeneralRSequentialCLT
import LogdetLean.NormalScaleComparison
import LogdetLean.WishartLogDetMoments
import LogdetLean.GeneralRRadialMoments
import Mathlib.Tactic

/-!
# Elementary-normalized central limit theorems

This file completes Lemma 5.6 and Corollary 3.5 of Hongru Zhao,
"On the Log Determinant of Sample Correlation Matrices under Gaussianity",
arXiv:2608.00565v1 (2026), printed pp. 8, 19, and 28--30.

The exact finite normalization uses the digamma center
`nullCenterDigammaSeries` and the trigamma variance `nullVSeries`.  The
paper-facing normalization replaces them by the elementary closed formulas
`elementaryNullCenterReal` and `elementaryNullVarianceReal`.  We first prove
the deterministic asymptotic equivalence, then transport the already proved
exact-normalization CLT by an explicit affine Kolmogorov bound.
-/

namespace LogdetLean

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Topology

/-! ## Positivity and a useful lower bound for the elementary variance -/

private def negLogQuadraticRemainder (x : ℝ) : ℝ :=
  -2 * (x + Real.log (1 - x)) - x ^ 2

private theorem hasDerivAt_negLogQuadraticRemainder
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt negLogQuadraticRemainder
      (2 * x ^ 2 / (1 - x)) x := by
  unfold negLogQuadraticRemainder
  have hne : 1 - x ≠ 0 := by linarith
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 - y) (-1) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have h' := h.congr_deriv (show (0 : ℝ) - 1 = -1 by norm_num)
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards [] with y
    rfl
  have hlog : HasDerivAt (fun y : ℝ ↦ Real.log (1 - y))
      (-(1 / (1 - x))) x := by
    simpa only [Function.comp_def, one_div, mul_neg, mul_one] using
      (Real.hasDerivAt_log hne).comp x hinner
  have h := (((hasDerivAt_id x).add hlog).const_mul (-2)).sub
    ((hasDerivAt_id x).pow 2)
  have hder :
      -2 * (1 + -(1 / (1 - x))) -
          (2 : ℝ) * x ^ (2 - 1) * 1 = 2 * x ^ 2 / (1 - x) := by
    field_simp [hne]
    ring
  refine (h.congr_deriv hder).congr_of_eventuallyEq ?_
  filter_upwards [] with y
  rfl

/-- The second-order logarithmic inequality needed in the dilute regime.
It is proved directly by monotonicity of the remainder, rather than invoked
as an asymptotic Taylor expansion. -/
theorem sq_le_neg_two_mul_add_log_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ^ 2 ≤ -2 * (x + Real.log (1 - x)) := by
  have hcont : ContinuousOn negLogQuadraticRemainder (Set.Ico 0 1) := by
    intro y hy
    exact (hasDerivAt_negLogQuadraticRemainder hy.1 hy.2).continuousAt.continuousWithinAt
  have hmono : MonotoneOn negLogQuadraticRemainder (Set.Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico (0 : ℝ) 1) hcont
      (f' := fun y ↦ 2 * y ^ 2 / (1 - y))
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa only [interior_Ico, mem_Ioo] using hy
      exact (hasDerivAt_negLogQuadraticRemainder hy'.1.le hy'.2).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := by
        simpa only [interior_Ico, mem_Ioo] using hy
      exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg y))
        (sub_nonneg.mpr hy'.2.le)
  have h := hmono (show 0 ∈ Set.Ico (0 : ℝ) 1 by norm_num)
    (show x ∈ Set.Ico (0 : ℝ) 1 by exact ⟨hx0, hx1⟩) hx0
  simpa [negLogQuadraticRemainder] using h

/-- In every strict admissible dimension, the elementary variance is
positive and dominates `(p/m)^2`. -/
theorem elementaryNullVarianceReal_ge_ratio_sq
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    ((p : ℝ) / (m : ℝ)) ^ 2 ≤
      elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  have hm : 0 < (m : ℝ) := by
    have hp2 : 2 ≤ p := h.1
    have hpN : 0 < p := by omega
    have hmN : 0 < m := hpN.trans_le h.2
    exact_mod_cast hmN
  have hp0 : 0 ≤ (p : ℝ) / (m : ℝ) := by positivity
  have hp1 : (p : ℝ) / (m : ℝ) < 1 := by
    exact (div_lt_one hm).2 (by exact_mod_cast hstrict)
  unfold elementaryNullVarianceReal
  exact sq_le_neg_two_mul_add_log_one_sub hp0 hp1

theorem elementaryNullVarianceReal_pos
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    0 < elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  have hlower := elementaryNullVarianceReal_ge_ratio_sq h hstrict
  have hp : 0 < (p : ℝ) / (m : ℝ) := by
    have hp2 : 2 ≤ p := h.1
    have hpN : 0 < p := by omega
    have hmN : 0 < m := hpN.trans_le h.2
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hpN
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmN
    exact div_pos hpR hmR
  exact lt_of_lt_of_le (sq_pos_of_pos hp) hlower

/-- The paper's elementary null standard deviation. -/
def elementaryNullScale (m p : ℕ) : ℝ :=
  Real.sqrt (elementaryNullVarianceReal (m : ℝ) (p : ℝ))

theorem elementaryNullScale_pos
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    0 < elementaryNullScale m p := by
  exact Real.sqrt_pos.2 (elementaryNullVarianceReal_pos h hstrict)

/-- Near the hard edge (`(m-p)^2 ≤ p`), the elementary variance already
dominates `log p - 2`.  This is the finite inequality behind the fixed-gap
part of Appendix E. -/
theorem log_dimension_sub_two_le_elementaryNullVarianceReal
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hgapSq : (m - p) ^ 2 ≤ p) :
    Real.log (p : ℝ) - 2 ≤
      elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  let d := m - p
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hdpos : 0 < d := by dsimp [d]; omega
  have hmpos : 0 < m := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hdpow : (d : ℝ) ^ 2 ≤ (p : ℝ) := by exact_mod_cast hgapSq
  have hlogdpow : Real.log ((d : ℝ) ^ 2) ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (d : ℝ) ^ 2 ∈ Set.Ioi 0 by exact sq_pos_of_pos hdR)
      (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR) hdpow
  have hlogd : 2 * Real.log (d : ℝ) ≤ Real.log (p : ℝ) := by
    rw [Real.log_pow] at hlogdpow
    norm_num at hlogdpow
    simpa [mul_comm] using hlogdpow
  have hlogpm : Real.log (p : ℝ) ≤ Real.log (m : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hpR hmR (by exact_mod_cast hpm)
  have hgaplog : Real.log (p : ℝ) / 2 ≤ gapLogReal (m : ℝ) (d : ℝ) := by
    unfold gapLogReal
    rw [Real.log_div hmR.ne' hdR.ne']
    linarith
  have hratio : (p : ℝ) / (m : ℝ) ≤ 1 :=
    (div_le_one hmR).2 (by exact_mod_cast hpm)
  have hrewrite := elementaryNullVarianceReal_gap_rewrite
    hmR hdR (show (p : ℝ) = (m : ℝ) - (d : ℝ) by
      dsimp [d]
      rw [Nat.cast_sub hpm]
      ring)
  rw [hrewrite]
  linarith

/-- An explicit one-variable envelope for the normalized centering error. -/
def elementaryCenterErrorEnvelope (p : ℕ) : ℝ :=
  42 / Real.sqrt (Real.log (p : ℝ) - 2) +
    42 * (1 / Real.sqrt (p : ℝ) + 1 / (p : ℝ))

/-- Finite uniform centering comparison.  The proof splits only on whether
the integer gap is below or above `sqrt p`; both resulting bounds are kept
in the single envelope above. -/
theorem abs_centerDifference_div_elementaryNullScale_le
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hlog : 2 < Real.log (p : ℝ)) :
    |(nullCenterDigammaSeries m p -
        elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
          elementaryNullScale m p| ≤ elementaryCenterErrorEnvelope p := by
  let d := m - p
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hdpos : 0 < d := by dsimp [d]; omega
  have hmpos : 0 < m := by omega
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hscale : 0 < elementaryNullScale m p :=
    elementaryNullScale_pos h hstrict
  have hcenter :=
    abs_nullCenterDigammaSeries_sub_elementaryNullCenterReal_le_inv_gap
      h hstrict
  rw [show ((m - p : ℕ) : ℝ) = (d : ℝ) by rfl] at hcenter
  rw [abs_div, abs_of_pos hscale]
  by_cases hgapSq : d ^ 2 ≤ p
  · have hvar := log_dimension_sub_two_le_elementaryNullVarianceReal
      h hstrict (by simpa [d] using hgapSq)
    have hbase : 0 < Real.log (p : ℝ) - 2 := by linarith
    have hsqrt : Real.sqrt (Real.log (p : ℝ) - 2) ≤
        elementaryNullScale m p := by
      unfold elementaryNullScale
      exact Real.sqrt_le_sqrt hvar
    have hcenter42 :
        |nullCenterDigammaSeries m p -
          elementaryNullCenterReal (m : ℝ) (p : ℝ)| ≤ 42 := by
      have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
      calc
        |nullCenterDigammaSeries m p -
            elementaryNullCenterReal (m : ℝ) (p : ℝ)| ≤
            42 / (d : ℝ) := hcenter
        _ ≤ 42 := by
          exact (div_le_iff₀ hdR).2 (by nlinarith)
    have hquot :
        |nullCenterDigammaSeries m p -
          elementaryNullCenterReal (m : ℝ) (p : ℝ)| /
            elementaryNullScale m p ≤
          42 / Real.sqrt (Real.log (p : ℝ) - 2) := by
      calc
        _ ≤ 42 / elementaryNullScale m p :=
          (div_le_div_iff_of_pos_right hscale).2 hcenter42
        _ ≤ 42 / Real.sqrt (Real.log (p : ℝ) - 2) := by
          gcongr
    unfold elementaryCenterErrorEnvelope
    exact hquot.trans (le_add_of_nonneg_right (by positivity))
  · have hgapSq' : (p : ℝ) < (d : ℝ) ^ 2 := by
      exact_mod_cast (Nat.lt_of_not_ge hgapSq)
    have hsqrtp : Real.sqrt (p : ℝ) < (d : ℝ) := by
      exact (Real.sqrt_lt' hdR).2 hgapSq'
    have hscaleLower : (p : ℝ) / (m : ℝ) ≤
        elementaryNullScale m p := by
      have hvar := elementaryNullVarianceReal_ge_ratio_sq h hstrict
      have hratio0 : 0 ≤ (p : ℝ) / (m : ℝ) := by positivity
      unfold elementaryNullScale
      calc
        (p : ℝ) / (m : ℝ) =
            Real.sqrt (((p : ℝ) / (m : ℝ)) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hratio0]
        _ ≤ Real.sqrt
            (elementaryNullVarianceReal (m : ℝ) (p : ℝ)) :=
          Real.sqrt_le_sqrt hvar
    have hratioPos : 0 < (p : ℝ) / (m : ℝ) := div_pos hpR hmR
    have hquot :
        |nullCenterDigammaSeries m p -
          elementaryNullCenterReal (m : ℝ) (p : ℝ)| /
            elementaryNullScale m p ≤
          42 * (1 / Real.sqrt (p : ℝ) + 1 / (p : ℝ)) := by
      calc
        _ ≤ (42 / (d : ℝ)) / elementaryNullScale m p :=
          (div_le_div_iff_of_pos_right hscale).2 hcenter
        _ ≤ (42 / (d : ℝ)) / ((p : ℝ) / (m : ℝ)) := by
          gcongr
        _ = 42 * (1 / (d : ℝ) + 1 / (p : ℝ)) := by
          have hcast : (m : ℝ) = (p : ℝ) + (d : ℝ) := by
            dsimp [d]
            rw [Nat.cast_sub hpm]
            ring
          rw [hcast]
          field_simp [hdR.ne', hpR.ne', hmR.ne']
        _ ≤ 42 * (1 / Real.sqrt (p : ℝ) + 1 / (p : ℝ)) := by
          gcongr
    unfold elementaryCenterErrorEnvelope
    exact hquot.trans (le_add_of_nonneg_left (by positivity))

/-- The explicit centering-error envelope tends to zero. -/
theorem tendsto_elementaryCenterErrorEnvelope_zero :
    Tendsto elementaryCenterErrorEnvelope atTop (nhds 0) := by
  have hcast : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hlogsub : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ) - 2)
      atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-2 : ℝ) hlog
  have hinvlogsqrt : Tendsto
      (fun p : ℕ ↦ (Real.sqrt (Real.log (p : ℝ) - 2))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hlogsub)
  have hinvsqrt : Tendsto
      (fun p : ℕ ↦ (Real.sqrt (p : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hcast)
  have hinv : Tendsto (fun p : ℕ ↦ ((p : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcast
  unfold elementaryCenterErrorEnvelope
  simpa [div_eq_mul_inv] using
    hinvlogsqrt.const_mul 42 |>.add
      ((hinvsqrt.add hinv).const_mul 42)

/-- Lemma 5.6, centering part, for every eventually strict admissible
triangular array. -/
theorem tendsto_centerDifference_div_elementaryNullScale
    (mseq pseq : ℕ → ℕ)
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hstrict : ∀ᶠ n in atTop, pseq n < mseq n) :
    Tendsto (fun n ↦
      (nullCenterDigammaSeries (mseq n) (pseq n) -
        elementaryNullCenterReal (mseq n : ℝ) (pseq n : ℝ)) /
          elementaryNullScale (mseq n) (pseq n)) atTop (nhds 0) := by
  have hlog : Tendsto (fun n ↦ Real.log (pseq n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hp)
  have hlogEventually : ∀ᶠ n in atTop, 2 < Real.log (pseq n : ℝ) :=
    (tendsto_atTop.1 hlog 3).mono fun n hn ↦ by linarith
  have henv := tendsto_elementaryCenterErrorEnvelope_zero.comp hp
  have hsqueeze : Tendsto (fun n ↦
      |(nullCenterDigammaSeries (mseq n) (pseq n) -
        elementaryNullCenterReal (mseq n : ℝ) (pseq n : ℝ)) /
          elementaryNullScale (mseq n) (pseq n)|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ abs_nonneg _
    · filter_upwards [hadm, hstrict, hlogEventually] with n hn hs hl
      exact abs_centerDifference_div_elementaryNullScale_le hn hs hl
    · exact henv
  apply (tendsto_zero_iff_abs_tendsto_zero (fun n ↦
    (nullCenterDigammaSeries (mseq n) (pseq n) -
      elementaryNullCenterReal (mseq n : ℝ) (pseq n : ℝ)) /
        elementaryNullScale (mseq n) (pseq n))).2
  simpa [Function.comp_def] using hsqueeze

/-! ## The elementary-normalized null statistic -/

/-- The statistic in Corollary 3.5 in the identity-correlation case. -/
def elementaryZ0mpStatistic (m p : ℕ) :
    NestedTuple (ObservationSpace (m + 1)) p → ℝ :=
  fun z ↦
    (Real.log (centeredSampleCorrelationDet (m + 1) p z) -
        elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
      elementaryNullScale m p

theorem measurable_elementaryZ0mpStatistic (m p : ℕ) :
    Measurable (elementaryZ0mpStatistic m p) := by
  unfold elementaryZ0mpStatistic
  exact ((measurable_log.comp
    (measurable_centeredSampleCorrelationDet (Nat.zero_lt_succ m))).sub
      measurable_const).div_const _

/-- Pointwise affine relation between elementary and exact normalization. -/
theorem elementaryZ0mpStatistic_eq_affine_exact
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) (z :
      NestedTuple (ObservationSpace (m + 1)) p) :
    elementaryZ0mpStatistic m p z =
      (Real.sqrt (nullVSeries m p) / elementaryNullScale m p) *
          Z0mpStatistic m p z +
        (nullCenterDigammaSeries m p -
          elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
            elementaryNullScale m p := by
  have hexact : Real.sqrt (nullVSeries m p) ≠ 0 :=
    (sqrt_nullVSeries_pos h).ne'
  have helem : elementaryNullScale m p ≠ 0 :=
    (elementaryNullScale_pos h hstrict).ne'
  unfold elementaryZ0mpStatistic Z0mpStatistic
  field_simp [hexact, helem]
  ring

/-- Exact pushforward relation: the elementary-normalized null law is an
explicit affine image of the exact standardized law. -/
theorem map_elementaryZ0mpStatistic_eq_map_affine_standardizedNullLaw
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    Measure.map (elementaryZ0mpStatistic m p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
      Measure.map
        (fun y ↦
          (Real.sqrt (nullVSeries m p) / elementaryNullScale m p) * y +
            (nullCenterDigammaSeries m p -
              elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
                elementaryNullScale m p)
        (standardizedNullLaw m p) := by
  let a : ℝ := Real.sqrt (nullVSeries m p) / elementaryNullScale m p
  let b : ℝ := (nullCenterDigammaSeries m p -
    elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
      elementaryNullScale m p
  let g : ℝ → ℝ := fun y ↦ a * y + b
  have hg : Measurable g := by fun_prop
  calc
    Measure.map (elementaryZ0mpStatistic m p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) =
      Measure.map (g ∘ Z0mpStatistic m p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m + 1))) p) := by
        apply Measure.map_congr
        filter_upwards [] with z
        exact (elementaryZ0mpStatistic_eq_affine_exact h hstrict z).trans
          (by rfl)
    _ = Measure.map g
        (Measure.map (Z0mpStatistic m p)
          (nestedProductMeasure
            (stdGaussian (ObservationSpace (m + 1))) p)) :=
      (Measure.map_map hg (measurable_Z0mpStatistic m p)).symm
    _ = Measure.map g (standardizedNullLaw m p) := by
      rw [map_Z0mpStatistic_eq_standardizedNullLaw m p h.2]

/-- The exact standardized null law converges to standard Gaussian in
Kolmogorov distance along every eventually admissible array. -/
theorem tendsto_kolmogorovDistance_standardizedNullLaw_zero
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ kolmogorovDistance
      (standardizedNullLaw (m p) p) (gaussianReal 0 1))
      atTop (nhds 0) := by
  have hlam := tendsto_nullLambdaSeries_zero_of_eventually_admissible m hadm
  have hrem := tendsto_nullUniformEdgeworthRelativeRemainder_zero m hadm
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hupper : Tendsto (fun p ↦
      nullLambdaSeries (m p) p / (6 * Real.sqrt (2 * Real.pi)) +
        nullLambdaSeries (m p) p *
          nullUniformEdgeworthRelativeRemainder (m p) p)
      atTop (nhds 0) := by
    convert (hlam.div_const (6 * Real.sqrt (2 * Real.pi))).add
      (hlam.mul hrem) using 1 <;> norm_num
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun p ↦
      kolmogorovDistance_nonneg _ _
  · filter_upwards [hadm] with p hp
    have hfinite := uniformNullSharpKolmogorov_finite hp
    have hlead0 : 0 ≤ nullLambdaSeries (m p) p /
        (6 * Real.sqrt (2 * Real.pi)) := by
      exact div_nonneg (nullLambdaSeries_pos hp).le (by positivity)
    have herr0 : 0 ≤ nullLambdaSeries (m p) p *
        nullUniformEdgeworthRelativeRemainder (m p) p :=
      (abs_nonneg _).trans hfinite
    have hdiffle := (le_abs_self
      (kolmogorovDistance (standardizedNullLaw (m p) p)
        (gaussianReal 0 1) -
          nullLambdaSeries (m p) p /
            (6 * Real.sqrt (2 * Real.pi)))).trans hfinite
    show kolmogorovDistance (standardizedNullLaw (m p) p)
        (gaussianReal 0 1) ≤
      nullLambdaSeries (m p) p / (6 * Real.sqrt (2 * Real.pi)) +
        nullLambdaSeries (m p) p *
          nullUniformEdgeworthRelativeRemainder (m p) p
    linarith
  · exact hupper

/-! ## Identifying the exact general-`R` center with the polygamma center -/

/-- The uncentered `m`-coordinate residual model has the same exact
log-Beta law as the centered `m+1`-observation model. -/
theorem map_log_det_sampleCorrelationMatrix_standard_eq_logBetaSumLaw
    {m p : ℕ} (hpm : p ≤ m) :
    Measure.map
        (fun z : GaussianData m p ↦
          Real.log (sampleCorrelationMatrix z).det)
        (standardGaussianDataMeasure m p) = logBetaSumLaw m p := by
  let E := ObservationSpace m
  let F : (Fin p → E) → ℝ := fun v ↦ Real.log (normalizedGram v).det
  have hF : Measurable F := by
    dsimp [F, E]
    exact (measurable_det_normalizedGram
      (E := ObservationSpace m) p).log
  calc
    Measure.map
        (fun z : GaussianData m p ↦
          Real.log (sampleCorrelationMatrix z).det)
        (standardGaussianDataMeasure m p) =
      Measure.map F
        (Measure.map dataColumns (standardGaussianDataMeasure m p)) := by
          rw [Measure.map_map hF measurable_dataColumns]
          rfl
    _ = Measure.map F
        (Measure.pi fun _ : Fin p ↦ stdGaussian E) := by
          rw [map_dataColumns_standardGaussianDataMeasure]
    _ = Measure.map F
        (Measure.map (nestedTupleToFin (α := E) p)
          (nestedProductMeasure (stdGaussian E) p)) := by
          rw [map_nestedTupleToFin_nestedProductMeasure]
    _ = Measure.map (F ∘ nestedTupleToFin (α := E) p)
        (nestedProductMeasure (stdGaussian E) p) :=
          Measure.map_map hF (measurable_nestedTupleToFin p)
    _ = Measure.map (Real.log ∘ nestedNormalizedGramDet (E := E) p)
        (nestedProductMeasure (stdGaussian E) p) := by rfl
    _ = Measure.map Real.log
        (Measure.map (nestedNormalizedGramDet (E := E) p)
          (nestedProductMeasure (stdGaussian E) p)) :=
          (Measure.map_map measurable_log
            ((measurable_det_normalizedGram (E := E) p).comp
              (measurable_nestedTupleToFin p))).symm
    _ = Measure.map Real.log
        (Measure.map (nestedRealProduct p)
          (nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p)) := by
          rw [map_gaussianNormalizedGramDet_eq_map_product_betaFactors
            m p (by simp [E]) hpm]
    _ = Measure.map (Real.log ∘ nestedRealProduct p)
        (nestedProductMeasureFamily
          (gaussianGramSchmidtFactorMeasure m) p) :=
          Measure.map_map measurable_log (measurable_nestedRealProduct p)
    _ = logBetaSumLaw m p :=
          map_log_nestedRealProduct_gaussianFactors_eq_logBetaSumLaw hpm

theorem correlateRows_identity {m p : ℕ} (z : GaussianData m p) :
    correlateRows (CorrelationMatrix.identity p) z = z := by
  ext k i
  simp [correlateRows, CorrelationMatrix.correlateObservation,
    CorrelationMatrix.covarianceSqrt]

/-- The deterministic center used by the general-`R` decomposition is
exactly `log det R` plus the finite digamma null center. -/
theorem generalRLogDetCenter_eq_logDet_add_nullCenterDigammaSeries
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    GeneralRDecomposition.logDetCenter m R =
      Real.log R.val.det + nullCenterDigammaSeries m p := by
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hW : Integrable (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.W0 z).det)
      (standardGaussianDataMeasure m p) :=
    (memLp_log_det_W0_two hm h.2).integrable (by norm_num)
  have hQ : ∀ i : Fin p, Integrable (fun z : GaussianData m p ↦
      Real.log (GeneralRDecomposition.Q (CorrelationMatrix.identity p) z i))
      (standardGaussianDataMeasure m p) := fun i ↦
    GeneralRDecomposition.integrable_log_Q hm
      (CorrelationMatrix.identity p) i
  have hcenterIdentity :=
    (GeneralRDecomposition.integrable_log_det_sampleCorrelation_and_integral_eq_center
      hm h.2 (CorrelationMatrix.identity p) hW hQ).2
  have hsampleIdentity :
      GeneralRDecomposition.sampleCorrelation
          (CorrelationMatrix.identity p) =
        (sampleCorrelationMatrix : GaussianData m p →
          Matrix (Fin p) (Fin p) ℝ) := by
    funext z
    unfold GeneralRDecomposition.sampleCorrelation
    rw [correlateRows_identity]
  rw [hsampleIdentity] at hcenterIdentity
  have hlaw := map_log_det_sampleCorrelationMatrix_standard_eq_logBetaSumLaw
    h.2
  have hint :
      (∫ z : GaussianData m p,
        Real.log (sampleCorrelationMatrix z).det
          ∂standardGaussianDataMeasure m p) =
        ∫ x : ℝ, x ∂logBetaSumLaw m p := by
    have hmeas : Measurable (fun z : GaussianData m p ↦
        Real.log (sampleCorrelationMatrix z).det) :=
      measurable_det_sampleCorrelationMatrix.log
    rw [← hlaw]
    rw [integral_map hmeas.aemeasurable (by fun_prop)]
  have hnull : (∫ x : ℝ, x ∂logBetaSumLaw m p) =
      nullCenterDigammaSeries m p := by
    rw [← nullCenter_eq_nullCenterDigammaSeries h.2]
    rfl
  have hbase : GeneralRDecomposition.W0LogDetMean m p -
      (p : ℝ) * GeneralRDecomposition.chiSquareLogMean m =
        nullCenterDigammaSeries m p := by
    rw [← hnull, ← hint, hcenterIdentity]
    simp [GeneralRDecomposition.logDetCenter]
  unfold GeneralRDecomposition.logDetCenter
  rw [add_sub_assoc, hbase]

/-! ## Elementary normalization for a general population correlation -/

/-- Closed-form center in Corollary 3.5. -/
def elementaryGeneralRCenter {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  Real.log R.val.det + elementaryNullCenterReal (m : ℝ) (p : ℝ)

/-- Closed-form variance proxy in Corollary 3.5. -/
def elementaryGeneralRVarianceSq {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRVarianceProxy m
    (elementaryNullVarianceReal (m : ℝ) (p : ℝ)) R.deviationEnergy

/-- Closed-form standard deviation in Corollary 3.5. -/
def elementaryGeneralRScale {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  Real.sqrt (elementaryGeneralRVarianceSq m R)

theorem elementaryGeneralRVarianceSq_pos
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (R : CorrelationMatrix p) :
    0 < elementaryGeneralRVarianceSq m R := by
  unfold elementaryGeneralRVarianceSq generalRVarianceProxy
  have hnull := elementaryNullVarianceReal_pos h hstrict
  have hm : 0 < (m : ℝ) := by
    have hp2 : 2 ≤ p := h.1
    have hpm : p ≤ m := h.2
    exact_mod_cast (show 0 < m by omega)
  exact add_pos_of_pos_of_nonneg hnull
    (div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg) hm.le)

theorem elementaryGeneralRScale_pos
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (R : CorrelationMatrix p) :
    0 < elementaryGeneralRScale m R := by
  exact Real.sqrt_pos.2 (elementaryGeneralRVarianceSq_pos h hstrict R)

/-- The actual general-correlation statistic with the elementary center and
scale of Corollary 3.5. -/
def elementaryZRmpStatistic {p : ℕ} (m : ℕ) (R : CorrelationMatrix p)
    (z : GaussianData m p) : ℝ :=
  (Real.log (GeneralRDecomposition.sampleCorrelation R z).det -
      elementaryGeneralRCenter m R) /
    elementaryGeneralRScale m R

theorem measurable_elementaryZRmpStatistic
    {m p : ℕ} (R : CorrelationMatrix p) :
    Measurable (elementaryZRmpStatistic m R) := by
  unfold elementaryZRmpStatistic
  exact ((GeneralRDecomposition.measurable_log_det_sampleCorrelation R).sub
    measurable_const).div_const _

/-- Pointwise affine relation between the elementary and exact general-`R`
normalizations. -/
theorem elementaryZRmpStatistic_eq_affine_exact
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (R : CorrelationMatrix p) (z : GaussianData m p) :
    elementaryZRmpStatistic m R z =
      (generalRProxyScale m R / elementaryGeneralRScale m R) *
          ZRmpStatistic m R z +
        (nullCenterDigammaSeries m p -
          elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
            elementaryGeneralRScale m R := by
  have hexact : generalRProxyScale m R ≠ 0 :=
    (generalRProxyScale_pos h R).ne'
  have helem : elementaryGeneralRScale m R ≠ 0 :=
    (elementaryGeneralRScale_pos h hstrict R).ne'
  have hcenter := generalRLogDetCenter_eq_logDet_add_nullCenterDigammaSeries
    h R
  unfold elementaryZRmpStatistic ZRmpStatistic elementaryGeneralRCenter
  rw [hcenter]
  field_simp [hexact, helem]
  ring

/-- Exact pushforward relation for the general-`R` elementary statistic. -/
theorem map_elementaryZRmpStatistic_eq_map_affine_exact
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (R : CorrelationMatrix p) :
    Measure.map (elementaryZRmpStatistic m R)
        (standardGaussianDataMeasure m p) =
      Measure.map
        (fun y ↦
          (generalRProxyScale m R / elementaryGeneralRScale m R) * y +
            (nullCenterDigammaSeries m p -
              elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
                elementaryGeneralRScale m R)
        (Measure.map (ZRmpStatistic m R)
          (standardGaussianDataMeasure m p)) := by
  let a : ℝ := generalRProxyScale m R / elementaryGeneralRScale m R
  let b : ℝ := (nullCenterDigammaSeries m p -
    elementaryNullCenterReal (m : ℝ) (p : ℝ)) /
      elementaryGeneralRScale m R
  let g : ℝ → ℝ := fun y ↦ a * y + b
  have hg : Measurable g := by fun_prop
  calc
    Measure.map (elementaryZRmpStatistic m R)
        (standardGaussianDataMeasure m p) =
      Measure.map (g ∘ ZRmpStatistic m R)
        (standardGaussianDataMeasure m p) := by
          apply Measure.map_congr
          filter_upwards [] with z
          exact (elementaryZRmpStatistic_eq_affine_exact h hstrict R z).trans
            (by rfl)
    _ = Measure.map g
        (Measure.map (ZRmpStatistic m R)
          (standardGaussianDataMeasure m p)) :=
      (Measure.map_map hg (measurable_ZRmpStatistic R)).symm

theorem elementaryNullScale_le_elementaryGeneralRScale
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (R : CorrelationMatrix p) :
    elementaryNullScale m p ≤ elementaryGeneralRScale m R := by
  unfold elementaryNullScale elementaryGeneralRScale
    elementaryGeneralRVarianceSq generalRVarianceProxy
  apply Real.sqrt_le_sqrt
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg) hm)

/-- The center replacement remains negligible after the larger general-`R`
elementary normalization, uniformly over arbitrary correlation arrays. -/
theorem tendsto_centerDifference_div_elementaryGeneralRScale
    (mseq pseq : ℕ → ℕ)
    (R : (n : ℕ) → CorrelationMatrix (pseq n))
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hstrict : ∀ᶠ n in atTop, pseq n < mseq n) :
    Tendsto (fun n ↦
      (nullCenterDigammaSeries (mseq n) (pseq n) -
        elementaryNullCenterReal (mseq n : ℝ) (pseq n : ℝ)) /
          elementaryGeneralRScale (mseq n) (R n)) atTop (nhds 0) := by
  have hnull := tendsto_centerDifference_div_elementaryNullScale
    mseq pseq hp hadm hstrict
  have habsNull := continuous_abs.continuousAt.tendsto.comp hnull
  have hsqueeze : Tendsto (fun n ↦
      |(nullCenterDigammaSeries (mseq n) (pseq n) -
        elementaryNullCenterReal (mseq n : ℝ) (pseq n : ℝ)) /
          elementaryGeneralRScale (mseq n) (R n)|) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n ↦
      |(nullCenterDigammaSeries (mseq n) (pseq n) -
        elementaryNullCenterReal (mseq n : ℝ) (pseq n : ℝ)) /
          elementaryNullScale (mseq n) (pseq n)|)
    · exact Filter.Eventually.of_forall fun n ↦ abs_nonneg _
    · filter_upwards [hadm, hstrict] with n hn hs
      have hnullScale := elementaryNullScale_pos hn hs
      have hgeneralScale := elementaryGeneralRScale_pos hn hs (R n)
      have hscale := elementaryNullScale_le_elementaryGeneralRScale
        hn hs (R n)
      rw [abs_div, abs_of_pos hgeneralScale, abs_div,
        abs_of_pos hnullScale]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hnullScale hscale
    · simpa [Function.comp_def] using habsNull
  apply (tendsto_zero_iff_abs_tendsto_zero (fun n ↦
    (nullCenterDigammaSeries (mseq n) (pseq n) -
      elementaryNullCenterReal (mseq n : ℝ) (pseq n : ℝ)) /
        elementaryGeneralRScale (mseq n) (R n))).2
  simpa [Function.comp_def] using hsqueeze

/-! ## Scale equivalence -/

/-- Lemma 5.6 in standard-deviation form for the null model. -/
theorem tendsto_sqrtNullVSeries_div_elementaryNullScale
    (mseq pseq : ℕ → ℕ)
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hstrict : ∀ᶠ n in atTop, pseq n < mseq n) :
    Tendsto (fun n ↦
      Real.sqrt (nullVSeries (mseq n) (pseq n)) /
        elementaryNullScale (mseq n) (pseq n)) atTop (nhds 1) := by
  have hratio := tendsto_nullVSeries_div_elementaryNullVarianceReal
    mseq pseq hp hadm hstrict
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hsqrt' : Tendsto (fun n ↦ Real.sqrt
      (nullVSeries (mseq n) (pseq n) /
        elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ)))
      atTop (nhds 1) := by
    change Tendsto (fun n ↦ Real.sqrt
      (nullVSeries (mseq n) (pseq n) /
        elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ)))
      atTop (nhds (Real.sqrt 1)) at hsqrt
    simpa using hsqrt
  apply hsqrt'.congr'
  filter_upwards [hadm] with n hn
  rw [Real.sqrt_div (nullVSeries_nonneg hn.2)]
  rfl

/-- Adding the same nonnegative correlation-energy term preserves the
exact-to-elementary variance-ratio limit. -/
theorem tendsto_generalRProxyVarianceSq_div_elementaryGeneralRVarianceSq
    (mseq pseq : ℕ → ℕ)
    (R : (n : ℕ) → CorrelationMatrix (pseq n))
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hstrict : ∀ᶠ n in atTop, pseq n < mseq n) :
    Tendsto (fun n ↦
      generalRProxyVarianceSq (mseq n) (R n) /
        elementaryGeneralRVarianceSq (mseq n) (R n))
      atTop (nhds 1) := by
  have hnull := tendsto_nullVSeries_div_elementaryNullVarianceReal
    mseq pseq hp hadm hstrict
  have hnullSub : Tendsto (fun n ↦
      nullVSeries (mseq n) (pseq n) /
        elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ) - 1)
      atTop (nhds 0) := by
    simpa using hnull.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  have habsNull : Tendsto (fun n ↦
      |nullVSeries (mseq n) (pseq n) /
        elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ) - 1|)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      continuous_abs.continuousAt.tendsto.comp hnullSub
  have habs : Tendsto (fun n ↦
      |generalRProxyVarianceSq (mseq n) (R n) /
          elementaryGeneralRVarianceSq (mseq n) (R n) - 1|)
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n ↦
      |nullVSeries (mseq n) (pseq n) /
          elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ) - 1|)
    · exact Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
    · filter_upwards [hadm, hstrict] with n hn hs
      have hm : 0 < (mseq n : ℝ) := by
        have hp2 : 2 ≤ pseq n := hn.1
        have hpm : pseq n ≤ mseq n := hn.2
        exact_mod_cast (show 0 < mseq n by omega)
      have hE := elementaryNullVarianceReal_pos hn hs
      have hc : 0 ≤ 2 * (R n).deviationEnergy / (mseq n : ℝ) :=
        div_nonneg (mul_nonneg (by norm_num) (R n).deviationEnergy_nonneg) hm.le
      simpa [generalRProxyVarianceSq, elementaryGeneralRVarianceSq,
        generalRVarianceProxy] using
          abs_ratio_add_same_nonneg_le hE hc
    · simpa [Function.comp_def] using habsNull
  have hsub : Tendsto (fun n ↦
      generalRProxyVarianceSq (mseq n) (R n) /
          elementaryGeneralRVarianceSq (mseq n) (R n) - 1)
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero (fun n ↦
      generalRProxyVarianceSq (mseq n) (R n) /
        elementaryGeneralRVarianceSq (mseq n) (R n) - 1)).2
    simpa [Function.comp_def] using habs
  have hsum : Tendsto (fun n ↦
      1 + (generalRProxyVarianceSq (mseq n) (R n) /
        elementaryGeneralRVarianceSq (mseq n) (R n) - 1))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hsub : Tendsto (fun n ↦
      (1 : ℝ) + (generalRProxyVarianceSq (mseq n) (R n) /
        elementaryGeneralRVarianceSq (mseq n) (R n) - 1))
      atTop (nhds (1 + 0)))
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun n ↦ by ring

/-- Lemma 5.6 in standard-deviation form for arbitrary correlation arrays. -/
theorem tendsto_generalRProxyScale_div_elementaryGeneralRScale
    (mseq pseq : ℕ → ℕ)
    (R : (n : ℕ) → CorrelationMatrix (pseq n))
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hstrict : ∀ᶠ n in atTop, pseq n < mseq n) :
    Tendsto (fun n ↦
      generalRProxyScale (mseq n) (R n) /
        elementaryGeneralRScale (mseq n) (R n)) atTop (nhds 1) := by
  have hratio :=
    tendsto_generalRProxyVarianceSq_div_elementaryGeneralRVarianceSq
      mseq pseq R hp hadm hstrict
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hsqrt' : Tendsto (fun n ↦ Real.sqrt
      (generalRProxyVarianceSq (mseq n) (R n) /
        elementaryGeneralRVarianceSq (mseq n) (R n)))
      atTop (nhds 1) := by
    change Tendsto (fun n ↦ Real.sqrt
      (generalRProxyVarianceSq (mseq n) (R n) /
        elementaryGeneralRVarianceSq (mseq n) (R n)))
      atTop (nhds (Real.sqrt 1)) at hsqrt
    simpa using hsqrt
  apply hsqrt'.congr'
  filter_upwards [hadm] with n hn
  rw [Real.sqrt_div (generalRProxyVarianceSq_pos hn (R n)).le]
  rfl

/-! ## A reusable affine Kolmogorov transfer -/

/-- A positive scale change followed by a deterministic shift.  The first
cost is the exact logarithmic normal-scale comparison; the second is the
standard Gaussian density bound applied to the deterministic coupling. -/
theorem kolmogorovDistance_map_affine_standardGaussian_le
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {c b : ℝ} (hc : 0 < c) :
    kolmogorovDistance (mu.map (fun y ↦ c * y + b))
        (gaussianReal 0 1) ≤
      kolmogorovDistance mu (gaussianReal 0 1) +
        |Real.log c| / Real.sqrt (2 * Real.pi) +
          |b| / Real.sqrt (2 * Real.pi) := by
  let X : ℝ → ℝ := fun y ↦ c * y + b
  let Y : ℝ → ℝ := fun y ↦ c * y
  have hX : Measurable X := by fun_prop
  have hY : Measurable Y := by fun_prop
  have hbad : mu.real (couplingBadEvent X Y |b|) ≤ 0 := by
    have hempty : couplingBadEvent X Y |b| = ∅ := by
      ext y
      simp [couplingBadEvent, X, Y]
    rw [hempty]
    simp
  have hshift := kolmogorovDistance_standardGaussian_le_of_coupling
    mu hX hY (abs_nonneg b) hbad
  have hscale := kolmogorovDistance_map_const_mul_standardGaussian_le
    mu hc
  change kolmogorovDistance (mu.map X) (gaussianReal 0 1) ≤ _
  calc
    kolmogorovDistance (mu.map X) (gaussianReal 0 1) ≤
        kolmogorovDistance (mu.map Y) (gaussianReal 0 1) + 0 +
          |b| / Real.sqrt (2 * Real.pi) := hshift
    _ ≤ kolmogorovDistance mu (gaussianReal 0 1) +
        |Real.log c| / Real.sqrt (2 * Real.pi) +
          |b| / Real.sqrt (2 * Real.pi) := by
      dsimp [Y]
      linarith

/-! ## Corollary 3.5: elementary-normalized CLTs -/

/-- Identity-correlation part of Corollary 3.5, strengthened from weak
convergence to convergence in Kolmogorov distance. -/
theorem tendsto_kolmogorovDistance_elementaryZ0mpStatistic_zero
    (m : ℕ → ℕ)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p)
    (hstrict : ∀ᶠ p in atTop, p < m p) :
    Tendsto (fun p ↦ kolmogorovDistance
      (Measure.map (elementaryZ0mpStatistic (m p) p)
        (nestedProductMeasure
          (stdGaussian (ObservationSpace (m p + 1))) p))
      (gaussianReal 0 1)) atTop (nhds 0) := by
  have hscale := tendsto_sqrtNullVSeries_div_elementaryNullScale
    m id tendsto_id hadm hstrict
  have hcenter := tendsto_centerDifference_div_elementaryNullScale
    m id tendsto_id hadm hstrict
  have hexact := tendsto_kolmogorovDistance_standardizedNullLaw_zero m hadm
  have hlogscale : Tendsto (fun p ↦
      |Real.log (Real.sqrt (nullVSeries (m p) p) /
        elementaryNullScale (m p) p)|) atTop (nhds 0) := by
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hscale
    have habs := continuous_abs.continuousAt.tendsto.comp hlog
    simpa [Function.comp_def] using habs
  have habscenter : Tendsto (fun p ↦
      |(nullCenterDigammaSeries (m p) p -
        elementaryNullCenterReal (m p : ℝ) (p : ℝ)) /
          elementaryNullScale (m p) p|) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      continuous_abs.continuousAt.tendsto.comp hcenter
  have hden : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hupper : Tendsto (fun p ↦
      kolmogorovDistance (standardizedNullLaw (m p) p)
          (gaussianReal 0 1) +
        |Real.log (Real.sqrt (nullVSeries (m p) p) /
          elementaryNullScale (m p) p)| /
            Real.sqrt (2 * Real.pi) +
        |(nullCenterDigammaSeries (m p) p -
          elementaryNullCenterReal (m p : ℝ) (p : ℝ)) /
            elementaryNullScale (m p) p| /
              Real.sqrt (2 * Real.pi)) atTop (nhds 0) := by
    simpa using (hexact.add (hlogscale.div_const _)).add
      (habscenter.div_const _)
  apply squeeze_zero' (g := fun p ↦
      kolmogorovDistance (standardizedNullLaw (m p) p)
          (gaussianReal 0 1) +
        |Real.log (Real.sqrt (nullVSeries (m p) p) /
          elementaryNullScale (m p) p)| /
            Real.sqrt (2 * Real.pi) +
        |(nullCenterDigammaSeries (m p) p -
          elementaryNullCenterReal (m p : ℝ) (p : ℝ)) /
            elementaryNullScale (m p) p| /
              Real.sqrt (2 * Real.pi))
  · exact Filter.Eventually.of_forall fun p ↦
      kolmogorovDistance_nonneg _ _
  · filter_upwards [hadm, hstrict] with p hp hs
    rw [map_elementaryZ0mpStatistic_eq_map_affine_standardizedNullLaw hp hs]
    let _ : IsProbabilityMeasure (standardizedNullLaw (m p) p) :=
      isProbabilityMeasure_standardizedNullLaw hp.2
    exact kolmogorovDistance_map_affine_standardGaussian_le
      (standardizedNullLaw (m p) p)
      (div_pos (sqrt_nullVSeries_pos hp)
        (elementaryNullScale_pos hp hs))
  · exact hupper

/-- General-correlation Corollary 3.5, equation (3.9), strengthened to
Kolmogorov convergence and uniform over arbitrary correlation-matrix arrays.
The only additional restriction is the one inherent in the printed
elementary formula: `p<m` eventually. -/
theorem tendsto_kolmogorovDistance_elementaryZRmpStatistic_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p)
    (hstrict : ∀ᶠ p in atTop, p < m p) :
    Tendsto (fun p ↦ kolmogorovDistance
      (Measure.map (elementaryZRmpStatistic (m p) (R p))
        (standardGaussianDataMeasure (m p) p))
      (gaussianReal 0 1)) atTop (nhds 0) := by
  have hscale := tendsto_generalRProxyScale_div_elementaryGeneralRScale
    m id R tendsto_id hadm hstrict
  have hcenter := tendsto_centerDifference_div_elementaryGeneralRScale
    m id R tendsto_id hadm hstrict
  have hexact := tendsto_kolmogorovDistance_ZRmpStatistic_zero m R hadm
  have hlogscale : Tendsto (fun p ↦
      |Real.log (generalRProxyScale (m p) (R p) /
        elementaryGeneralRScale (m p) (R p))|) atTop (nhds 0) := by
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hscale
    have habs := continuous_abs.continuousAt.tendsto.comp hlog
    simpa [Function.comp_def] using habs
  have habscenter : Tendsto (fun p ↦
      |(nullCenterDigammaSeries (m p) p -
        elementaryNullCenterReal (m p : ℝ) (p : ℝ)) /
          elementaryGeneralRScale (m p) (R p)|) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      continuous_abs.continuousAt.tendsto.comp hcenter
  have hupper : Tendsto (fun p ↦
      kolmogorovDistance
          (Measure.map (ZRmpStatistic (m p) (R p))
            (standardGaussianDataMeasure (m p) p))
          (gaussianReal 0 1) +
        |Real.log (generalRProxyScale (m p) (R p) /
          elementaryGeneralRScale (m p) (R p))| /
            Real.sqrt (2 * Real.pi) +
        |(nullCenterDigammaSeries (m p) p -
          elementaryNullCenterReal (m p : ℝ) (p : ℝ)) /
            elementaryGeneralRScale (m p) (R p)| /
              Real.sqrt (2 * Real.pi)) atTop (nhds 0) := by
    simpa using (hexact.add (hlogscale.div_const _)).add
      (habscenter.div_const _)
  apply squeeze_zero' (g := fun p ↦
      kolmogorovDistance
          (Measure.map (ZRmpStatistic (m p) (R p))
            (standardGaussianDataMeasure (m p) p))
          (gaussianReal 0 1) +
        |Real.log (generalRProxyScale (m p) (R p) /
          elementaryGeneralRScale (m p) (R p))| /
            Real.sqrt (2 * Real.pi) +
        |(nullCenterDigammaSeries (m p) p -
          elementaryNullCenterReal (m p : ℝ) (p : ℝ)) /
            elementaryGeneralRScale (m p) (R p)| /
              Real.sqrt (2 * Real.pi))
  · exact Filter.Eventually.of_forall fun p ↦
      kolmogorovDistance_nonneg _ _
  · filter_upwards [hadm, hstrict] with p hp hs
    rw [map_elementaryZRmpStatistic_eq_map_affine_exact hp hs (R p)]
    let _ : IsProbabilityMeasure
        (Measure.map (ZRmpStatistic (m p) (R p))
          (standardGaussianDataMeasure (m p) p)) :=
      Measure.isProbabilityMeasure_map
        (measurable_ZRmpStatistic (R p)).aemeasurable
    exact kolmogorovDistance_map_affine_standardGaussian_le
      (Measure.map (ZRmpStatistic (m p) (R p))
        (standardGaussianDataMeasure (m p) p))
      (div_pos (generalRProxyScale_pos hp (R p))
        (elementaryGeneralRScale_pos hp hs (R p)))
  · exact hupper

/-- Pointwise-CDF form of the paper's general elementary-normalized CLT. -/
theorem tendsto_cdf_elementaryZRmpStatistic
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p)
    (hstrict : ∀ᶠ p in atTop, p < m p) (x : ℝ) :
    Tendsto (fun p ↦ cdf
      (Measure.map (elementaryZRmpStatistic (m p) (R p))
        (standardGaussianDataMeasure (m p) p)) x)
      atTop (nhds (cdf (gaussianReal 0 1) x)) := by
  exact tendsto_cdf_of_tendsto_kolmogorovDistance
    (fun p ↦ Measure.map (elementaryZRmpStatistic (m p) (R p))
      (standardGaussianDataMeasure (m p) p))
    (gaussianReal 0 1)
    (tendsto_kolmogorovDistance_elementaryZRmpStatistic_zero
      m R hadm hstrict) x

end

end LogdetLean
