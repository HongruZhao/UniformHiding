import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.PaperEndpoint
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PastCofactorBridge

/-!
# Exact proof equations for the Wick angular obstruction

Every displayed equation in the proof of Theorem V.4 has a dedicated
declaration here.  The statements use the literal angular and Gaussian laws
from the theorem, not surrogate random variables.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace LogdetLean.GramHafnian.WickAngularLowerBound

noncomputable section

/-- Equation `eq:wick-vector-representation`: the vector valued Wick
representation used at the start of the proof. -/
theorem eq_wick_vector_representation
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k) :
    WithLp.toLp 2 (pastCofactorCombination hn
        (RadialLowerBoundAlt.directionColumns hn u)) =
      ∫ g, wickVector hn u g ∂standardRealGaussianVector k := by
  exact (integral_wickVector_eq_pastCofactorCombination hn u).symm

/-- Equation `eq:wick-coordinate-representation`: the coordinate Wick
identity together with the literal cofactor sum. -/
theorem eq_wick_coordinate_representation
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k)
    (p : Fin k) :
    ((∫ g, wickVector hn u g p ∂standardRealGaussianVector k) =
        ∑ j : RadialLowerBoundAlt.CofactorIdx n hn,
          RadialLowerBoundAlt.directionColumns hn u j p *
            pastHafnianCofactorVector hn
              (RadialLowerBoundAlt.directionColumns hn u) j) ∧
      (∑ j : RadialLowerBoundAlt.CofactorIdx n hn,
          RadialLowerBoundAlt.directionColumns hn u j p *
            pastHafnianCofactorVector hn
              (RadialLowerBoundAlt.directionColumns hn u) j) =
        pastCofactorCombination hn
          (RadialLowerBoundAlt.directionColumns hn u) p := by
  let A := RadialLowerBoundAlt.directionColumns hn u
  have hsum := congrFun (Wishart.pastComplexColumnMatrix_mulVec_cofactor hn A) p
  have hsum' :
      (∑ j : RadialLowerBoundAlt.CofactorIdx n hn,
          A j p * pastHafnianCofactorVector hn A j) =
        pastCofactorCombination hn A p := by
    simpa [Wishart.pastComplexColumnMatrix, Matrix.mulVec, dotProduct] using hsum
  constructor
  · calc
      (∫ g, wickVector hn u g p ∂standardRealGaussianVector k) =
          pastCofactorCombination hn A p :=
        integral_wickVector_apply_eq_pastCofactorCombination hn u p
      _ = ∑ j : RadialLowerBoundAlt.CofactorIdx n hn,
          A j p * pastHafnianCofactorVector hn A j := hsum'.symm
  · exact hsum'

/-- Equation `eq:wick-minkowski-chain`: the exact Wick norm identity,
Minkowski estimate, independent coordinate expectation, and real Gaussian
radial moment appearing in the proof. -/
theorem eq_wick_minkowski_chain
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (∫ u,
        ‖∫ g, wickVector hn u g ∂standardRealGaussianVector k‖
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
        ∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn u)
          ∂(RadialLowerBoundAlt.angularMeasure hn) ∧
      (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn u)
          ∂(RadialLowerBoundAlt.angularMeasure hn)) ≤
        ∫ g : Fin k → ℝ,
          ‖WithLp.toLp 2 g‖ *
            ∏ _j : RadialLowerBoundAlt.CofactorIdx n hn,
              ∫ v : RadialLowerBoundAlt.Direction k,
                ‖sphereTransposeLinearForm (fun p ↦ (g p : ℂ)) v‖
                ∂circularGaussianSphereProbability k
          ∂standardRealGaussianVector k ∧
      (∫ g : Fin k → ℝ,
          ‖WithLp.toLp 2 g‖ *
            ∏ _j : RadialLowerBoundAlt.CofactorIdx n hn,
              ∫ v : RadialLowerBoundAlt.Direction k,
                ‖sphereTransposeLinearForm (fun p ↦ (g p : ℂ)) v‖
                ∂circularGaussianSphereProbability k
          ∂standardRealGaussianVector k) =
        sphereCoordinateAbsMean k ^ (2 * n - 1) *
          (∫ g : Fin k → ℝ, ‖WithLp.toLp 2 g‖ ^ (2 * n)
            ∂standardRealGaussianVector k) ∧
      sphereCoordinateAbsMean k ^ (2 * n - 1) *
          (∫ g : Fin k → ℝ, ‖WithLp.toLp 2 g‖ ^ (2 * n)
            ∂standardRealGaussianVector k) =
        sphereCoordinateAbsMean k ^ (2 * n - 1) *
          dimensionProduct k n := by
  letI : IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    ⟨circularGaussianSphereProbability_apply_univ hk⟩
  have hrad := integral_norm_pow_two_mul_standardRealGaussianVector hk n
  let middle : ℝ :=
    ∫ g : Fin k → ℝ,
      ‖WithLp.toLp 2 g‖ *
        ∏ _j : RadialLowerBoundAlt.CofactorIdx n hn,
          ∫ v : RadialLowerBoundAlt.Direction k,
            ‖sphereTransposeLinearForm (fun p ↦ (g p : ℂ)) v‖
            ∂circularGaussianSphereProbability k
      ∂standardRealGaussianVector k
  have hmiddle : middle =
      sphereCoordinateAbsMean k ^ (2 * n - 1) * dimensionProduct k n := by
    calc
      middle = ∫ g : Fin k → ℝ,
          ∫ u, wickNormIntegrand hn (g, u)
            ∂(RadialLowerBoundAlt.angularMeasure hn)
          ∂standardRealGaussianVector k := by
        apply integral_congr_ae
        filter_upwards [] with g
        unfold wickNormIntegrand RadialLowerBoundAlt.angularMeasure
        simp only [Prod.fst, Prod.snd]
        rw [integral_const_mul]
        congr 1
        symm
        exact integral_fintype_prod_eq_prod
          (μ := fun _ : RadialLowerBoundAlt.CofactorIdx n hn ↦
            circularGaussianSphereProbability k)
          (fun _j : RadialLowerBoundAlt.CofactorIdx n hn ↦
            fun v : RadialLowerBoundAlt.Direction k ↦
              ‖sphereTransposeLinearForm (fun p ↦ (g p : ℂ)) v‖)
      _ = sphereCoordinateAbsMean k ^ (2 * n - 1) * dimensionProduct k n :=
        integral_realGaussian_integral_angular_wickNorm hn hk
  have hbound := integral_sqrt_angularEnergy_le_wickSqrtMomentBound hn hk
  rw [wickSqrtMomentBound_eq_sphereMean_pow_mul_dimensionProduct hk,
    ← hmiddle] at hbound
  refine ⟨?_, hbound, ?_, by rw [hrad]⟩
  · apply integral_congr_ae
    filter_upwards [] with u
    rw [integral_wickVector_eq_pastCofactorCombination hn u,
      sqrt_angularEnergy_eq_norm_cofactorCombination hn u]
  · change middle = _
    rw [hrad]
    exact hmiddle

/-- Equation `eq:wick-angular-first-moment`: the exact first angular moment
in the notation of Theorem V.4. -/
theorem eq_wick_angular_first_moment
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (∫ u, RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      (((2 * n - 1).doubleFactorial : ℕ) : ℝ) * dimensionProduct k n /
        (k : ℝ) ^ (2 * n - 1) := by
  rw [← oddPairingNat_eq_doubleFactorial n]
  simpa only [closedFirstMoment] using
    integral_angularEnergy_eq_closedFirstMoment_div_pow hn hk

/-- Equation `eq:wick-cauchy-chain`: the two Cauchy Schwarz steps after
squaring, specialized to the literal angular energy. -/
theorem eq_wick_cauchy_chain
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k)
    (hpos : ∀ᵐ u ∂(RadialLowerBoundAlt.angularMeasure
        (n := n) (k := k) hn),
      0 < RadialLowerBoundAlt.angularEnergy hn u)
    (hinv : Integrable
      (fun u ↦ (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)⁻¹)
      (RadialLowerBoundAlt.angularMeasure hn)) :
    (1 ≤
        (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
            (n := n) (k := k) hn u)
            ∂(RadialLowerBoundAlt.angularMeasure hn)) ^ 2 *
          ∫ u, (RadialLowerBoundAlt.angularEnergy
            (n := n) (k := k) hn u)⁻¹
            ∂(RadialLowerBoundAlt.angularMeasure hn)) ∧
      (1 ≤
        (∫ u, RadialLowerBoundAlt.angularEnergy
            (n := n) (k := k) hn u
            ∂(RadialLowerBoundAlt.angularMeasure hn)) *
          ∫ u, (RadialLowerBoundAlt.angularEnergy
            (n := n) (k := k) hn u)⁻¹
            ∂(RadialLowerBoundAlt.angularMeasure hn)) := by
  letI : ∀ _ : RadialLowerBoundAlt.CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : IsProbabilityMeasure
      (RadialLowerBoundAlt.angularMeasure (k := k) hn) := by
    unfold RadialLowerBoundAlt.angularMeasure
    infer_instance
  constructor
  · exact one_le_sq_integral_sqrt_mul_integral_inv
      (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn)
      (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn)
      (RadialLowerBoundAlt.measurable_angularEnergy hn).aestronglyMeasurable
      hpos (RadialLowerBoundAlt.integrable_angularEnergy hn hk) hinv
  · exact one_le_integral_mul_integral_inv
      (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn)
      (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn)
      (RadialLowerBoundAlt.measurable_angularEnergy hn).aestronglyMeasurable
      hpos (RadialLowerBoundAlt.integrable_angularEnergy hn hk) hinv

/-- Equation `eq:wick-half-integer-gamma`: the exact half integer Gamma
identity in the normalization printed in Theorem V.4. -/
theorem eq_wick_half_integer_gamma
    (k : ℕ) (hk : 0 < k) :
    sphereCoordinateAbsMean k =
      (4 : ℝ) ^ k /
        (2 * (k : ℝ) * (Nat.centralBinom k : ℝ)) := by
  rw [sphereCoordinateAbsMean_eq_centralBinom k hk]
  have hpow : (4 : ℝ) ^ k =
      2 * (2 : ℝ) ^ (2 * k - 1) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hsucc : 2 * k - 1 + 1 = 2 * k := by omega
    calc
      (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (2 * k - 1 + 1) := by rw [hsucc]
      _ = (2 : ℝ) ^ (2 * k - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (2 * k - 1) := by ring
  rw [hpow]
  ring

/-- Equation `eq:wick-ratio-recurrence`: every identity and inequality in the
analytic ratio argument, including the two elementary lower bounds. -/
theorem eq_wick_ratio_recurrence
    {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) (hkn : 3 * k ≤ n) :
    angularBaseQ (k + 1) = angularBaseQ k *
        (((2 * k + 1 : ℕ) : ℚ) ^ 2 / (4 * k * (k + 1) : ℕ)) ∧
      (9 / 8 : ℚ) ≤ angularBaseQ k ∧
      (6 / 7 : ℚ) ≤ ((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ) ∧
      wickScalarRatioQ k (n + 1) / wickScalarRatioQ k n =
        (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
          (4 * k * (Nat.centralBinom k : ℚ) ^ 2 / 16 ^ k) ^ 2 ∧
      (243 / 224 : ℚ) ≤
        (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
          (4 * k * (Nat.centralBinom k : ℚ) ^ 2 / 16 ^ k) ^ 2 ∧
      (500 / 499 : ℚ) < 243 / 224 := by
  have hsucc := angularBaseQ_succ k (by omega)
  have hbase := nine_eighths_le_angularBaseQ hk
  have hdim := six_sevenths_le_dimension_step (show 0 < k by omega) hkn
  have hratio : wickScalarRatioQ k (n + 1) / wickScalarRatioQ k n =
      (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
        (4 * k * (Nat.centralBinom k : ℚ) ^ 2 / 16 ^ k) ^ 2 := by
    rw [wickScalarRatioQ_succ_n (by omega) hn, angularBaseQ]
    exact mul_div_cancel_left₀ _
      (ne_of_gt (wickScalarRatioQ_pos (n := n) (by omega)))
  have hbaseSq : (9 / 8 : ℚ) ^ 2 ≤ angularBaseQ k ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hbase 2
  have hlower : (243 / 224 : ℚ) ≤
      (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
        angularBaseQ k ^ 2 := by
    calc
      (243 / 224 : ℚ) = (6 / 7 : ℚ) * (9 / 8 : ℚ) ^ 2 := by norm_num
      _ ≤ (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
          angularBaseQ k ^ 2 :=
        mul_le_mul hdim hbaseSq (by positivity) (by positivity)
  refine ⟨hsucc, hbase, hdim, hratio, ?_, by norm_num⟩
  simpa only [angularBaseQ] using hlower

/-- Equation `eq:wick-finite-base-cases`: the three finite statements
printed immediately before the final induction. -/
theorem eq_wick_finite_certificates :
    (∀ k : ℕ, 2 ≤ k → k ≤ 333 →
      (500 / 499 : ℚ) ^ 1000 ≤ wickScalarRatioQ k 1000) ∧
      (500 / 499 : ℚ) ^ 1002 ≤ wickScalarRatioQ 334 1002 ∧
      (500 / 499 : ℚ) ^ 1005 ≤ wickScalarRatioQ 335 1005 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hklo hkhi
    simpa only [expStepQ] using
      expStepQ_pow_1000_le_wickScalarRatioQ hklo hkhi
  · simpa only [expStepQ] using boundary_base_334
  · simpa only [expStepQ] using boundary_base_335

/-- Equation `eq:wick-boundary-recurrence`: the two step boundary
recurrence used for the even and odd inductions. -/
theorem eq_wick_boundary_recurrence
    {k : ℕ} (hk : 334 ≤ k) :
    (500 / 499 : ℚ) ^ 6 * wickScalarRatioQ k (3 * k) ≤
      wickScalarRatioQ (k + 2) (3 * (k + 2)) := by
  simpa only [expStepQ] using boundary_two_step_growth hk

/-- Equation `eq:wick-exponential-chain`: both comparisons in the final
finite certificate chain. -/
theorem eq_wick_exponential_chain
    {k n : ℕ} (hn : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n) :
    Real.exp ((n : ℝ) / 500) ≤ (((500 / 499 : ℚ) ^ n : ℚ) : ℝ) ∧
      (((500 / 499 : ℚ) ^ n : ℚ) : ℝ) ≤
        (wickScalarRatioQ k n : ℝ) := by
  constructor
  · calc
      Real.exp ((n : ℝ) / 500) = Real.exp (1 / 500 : ℝ) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (expStepQ : ℝ) ^ n :=
        pow_le_pow_left₀ (Real.exp_pos _).le exp_one_div_500_le_expStepQ n
      _ = (((500 / 499 : ℚ) ^ n : ℚ) : ℝ) := by
        rw [Rat.cast_pow]
        rfl
  · exact_mod_cast expStepQ_pow_le_wickScalarRatioQ hn hklo hkhi

end

end LogdetLean.GramHafnian.WickAngularLowerBound
