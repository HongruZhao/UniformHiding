import LogdetLean.GramHafnian.SymmetricGaussianLimit.SmallBallTransfer
import LogdetLean.GramHafnian.SymmetricGaussianLimit.ShiftedWeakLimit
import LogdetLean.GramHafnian.SymmetricGaussianLimit.ComplexMatrixCLT

/-!
# Paper-facing endpoints for the symmetric-Gaussian limit

The concrete fixed dimensional complex transpose Gram matrix central limit
theorem and its continuous hafnian image are proved unconditionally in
`ComplexMatrixCLT`.  The reusable abstract transfer theorems below retain
explicit weak convergence premises so they can also be applied to other
models.  Given scalar convergence, the existing sharp finite bound transfers
with coefficient `b_n`; the arbitrary independent factor shift bound
transfers with coefficient `e b_n`.
-/

open Filter MeasureTheory Metric
open scoped BigOperators

namespace LogdetLean.GramHafnian.SymmetricGaussianLimit

noncomputable section

open LocalAnticoncentration

/-- The standard deviation of `k^{-n/2} H_{k,n}`, written without fractional
powers. -/
def finiteNormalizedSigma (k n : ℕ) : ℝ :=
  Real.sqrt (closedFirstMoment k n / (k : ℝ) ^ n)

theorem finiteNormalizedSigma_pos (k n : ℕ) (hk : 0 < k) :
    0 < finiteNormalizedSigma k n := by
  unfold finiteNormalizedSigma
  exact Real.sqrt_pos.2
    (div_pos (closedFirstMoment_pos k n hk) (by positivity))

theorem tendsto_finiteNormalizedSigma (n : ℕ) :
    Tendsto (fun k : ℕ ↦ finiteNormalizedSigma k n) atTop
      (nhds (symmetricGaussianSigma n)) :=
  tendsto_sqrt_closedFirstMoment_div_pow n

/-- The coefficient supplied by the currently kernel-checked independent
factor-shift theorem. -/
def finiteIndependentShiftCoefficient (k n : ℕ) : ℝ :=
  Real.exp 1 * paperBkn k n

/-- Its fixed-degree limit. -/
def limitingIndependentShiftCoefficient (n : ℕ) : ℝ :=
  Real.exp 1 * symmetricGaussianCoefficient n

theorem tendsto_finiteIndependentShiftCoefficient
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun k : ℕ ↦ finiteIndependentShiftCoefficient k n) atTop
      (nhds (limitingIndependentShiftCoefficient n)) := by
  exact (tendsto_finiteCoefficient n hn).const_mul (Real.exp 1)

/-- The fourth power subsequence used literally in Appendix D is cofinal. -/
theorem tendsto_fourthPower_atTop :
    Tendsto (fun m : ℕ ↦ m ^ 4) atTop atTop :=
  tendsto_pow_atTop (by norm_num)

/-- Literal product form of the normalized finite variance used in the
printed scale limit.  The positive row dimension is the paper's operative
range. -/
theorem closedFirstMoment_div_pow_eq_paper_product
    (k n : ℕ) (hk : 0 < k) :
    closedFirstMoment k n / (k : ℝ) ^ n =
      symmetricGaussianSigmaSq n *
        ∏ q ∈ Finset.range n, (1 + 2 * (q : ℝ) / (k : ℝ)) := by
  rw [closedFirstMoment_div_pow_eq, varianceCorrection]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  push_cast
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp [hkR]

/-- Exact paper bundle for the normalized scale and coefficient display: the
finite product identity, its fixed degree limit, and the coefficient limit. -/
def result_eq_symmetric_scale_coefficient_limit :=
  And.intro (@closedFirstMoment_div_pow_eq_paper_product)
    (And.intro (@tendsto_closedFirstMoment_div_pow)
      (@tendsto_finiteCoefficient))

/-- Abstract weak-limit endpoint for the unperturbed symmetric-Gaussian
small-ball theorem.  Supplying the Gram CLT is the remaining probabilistic
obligation. -/
theorem symmetricGaussianSmallBall_of_weakLimit
    (n : ℕ) (hn : 1 ≤ n)
    (muSeq : ℕ → ProbabilityMeasure ℂ) (mu : ProbabilityMeasure ℂ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (z : ℂ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      (muSeq k : Measure ℂ)
          (Metric.closedBall z (eps * finiteNormalizedSigma k n)) ≤
        ENNReal.ofReal (paperBkn k n * eps ^ 2))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (mu : Measure ℂ)
        (Metric.closedBall z (eps * symmetricGaussianSigma n)) ≤
      ENNReal.ofReal (symmetricGaussianCoefficient n * eps ^ 2) := by
  apply normalized_closedBall_measure_le_of_weakLimit
    muSeq mu (fun k ↦ finiteNormalizedSigma k n)
    (symmetricGaussianSigma n) (fun k ↦ paperBkn k n)
    (symmetricGaussianCoefficient n) hmu
    (tendsto_finiteNormalizedSigma n) (symmetricGaussianSigma_pos n)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
      exact finiteNormalizedSigma_pos k n hk)
    (tendsto_finiteCoefficient n hn) z hfinite eps heps

/-- Complete continuous mapping and small ball transfer for the fixed degree
matrix limit used in the manuscript proof of Theorem I.3.  The sole
probabilistic input is `hMatrix`, the weak convergence of the normalized
transpose Gram matrix laws.  Everything after that matrix central limit
theorem, including the literal hafnian pushforward and the normalized closed
disk transfer, is proved here. -/
theorem symmetricGaussianHafnianSmallBall_of_matrixWeakLimit
    {E : Type*} [MeasurableSpace E] [SeminormedAddCommGroup E]
    [SecondCountableTopology E] [BorelSpace E]
    (n : ℕ) (hn : 1 ≤ n)
    (toMatrix : E → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (htoMatrix : Continuous toMatrix)
    (matrixLawSeq : ℕ → ProbabilityMeasure E)
    (matrixLimitLaw : ProbabilityMeasure E)
    (hMatrix : Tendsto matrixLawSeq atTop (nhds matrixLimitLaw))
    (z : ℂ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      ((matrixLawSeq k).map
          ((continuous_hafnian n).comp htoMatrix).measurable.aemeasurable :
        ProbabilityMeasure ℂ)
          (Metric.closedBall z (eps * finiteNormalizedSigma k n)) ≤
        ENNReal.ofReal (paperBkn k n * eps ^ 2))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (matrixLimitLaw.map
        ((continuous_hafnian n).comp htoMatrix).measurable.aemeasurable :
      ProbabilityMeasure ℂ)
        (Metric.closedBall z (eps * symmetricGaussianSigma n)) ≤
      ENNReal.ofReal (symmetricGaussianCoefficient n * eps ^ 2) := by
  let muSeq : ℕ → ProbabilityMeasure ℂ := fun k ↦
    (matrixLawSeq k).map
      ((continuous_hafnian n).comp htoMatrix).measurable.aemeasurable
  let mu : ProbabilityMeasure ℂ :=
    matrixLimitLaw.map
      ((continuous_hafnian n).comp htoMatrix).measurable.aemeasurable
  have hmu : Tendsto muSeq atTop (nhds mu) := by
    simpa [muSeq, mu] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        matrixLawSeq matrixLimitLaw hMatrix
          ((continuous_hafnian n).comp htoMatrix)
  simpa [mu] using
    (symmetricGaussianSmallBall_of_weakLimit
      n hn muSeq mu hmu z (by simpa [muSeq] using hfinite) eps heps)

/-- Abstract weak-limit endpoint for an arbitrary independent additive
complex-symmetric perturbation.  The finite input-factor theorem contributes
the factor `e`, so its exact limiting coefficient is `e b_n`. -/
theorem independentAdditiveShiftSmallBall_of_weakLimit
    (n : ℕ) (hn : 1 ≤ n)
    (muSeq : ℕ → ProbabilityMeasure ℂ) (mu : ProbabilityMeasure ℂ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (z : ℂ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      (muSeq k : Measure ℂ)
          (Metric.closedBall z (eps * finiteNormalizedSigma k n)) ≤
        ENNReal.ofReal
          (finiteIndependentShiftCoefficient k n * eps ^ 2))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (mu : Measure ℂ)
        (Metric.closedBall z (eps * symmetricGaussianSigma n)) ≤
      ENNReal.ofReal
        (limitingIndependentShiftCoefficient n * eps ^ 2) := by
  apply normalized_closedBall_measure_le_of_weakLimit
    muSeq mu (fun k ↦ finiteNormalizedSigma k n)
    (symmetricGaussianSigma n)
    (fun k ↦ finiteIndependentShiftCoefficient k n)
    (limitingIndependentShiftCoefficient n) hmu
    (tendsto_finiteNormalizedSigma n) (symmetricGaussianSigma_pos n)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
      exact finiteNormalizedSigma_pos k n hk)
    (tendsto_finiteIndependentShiftCoefficient n hn) z hfinite eps heps

/-- Composite endpoint used by the revised proof of Corollary I.4.  All
random objects live on the literal independent product probability space.
The cited unshifted matrix convergence is the explicit premise `hweak`; a
single finite random cross term is multiplied by `m⁻¹`, so no moment premise
is introduced.  The theorem then performs continuous hafnian mapping and the
normalized closed disk Portmanteau transfer in one checked statement. -/
theorem independentAdditiveShiftHafnianSmallBall_fixedCross_of_weakLimit
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SecondCountableTopology E] [BorelSpace E]
    (n : ℕ) (hn : 1 ≤ n)
    (kSeq : ℕ → ℕ) (hkSeq : Tendsto kSeq atTop atTop)
    (toMatrix : E → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (htoMatrix : Continuous toMatrix)
    (base : ProbabilityMeasure Omega)
    (shift limitLaw : ProbabilityMeasure E)
    (X : ℕ → Omega → E) (hX : ∀ m, Measurable (X m))
    (hweak : Tendsto
      (fun m ↦ base.map (hX m).aemeasurable)
      atTop (nhds limitLaw))
    (cross : Omega × E → E)
    (hcross : AEStronglyMeasurable cross
      ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
    (z : ℂ)
    (hfinite : ∀ᶠ m : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      (Measure.map
        (fun p : Omega × E ↦ hafnian
          (toMatrix (X m p.1 + p.2 + (m : ℂ)⁻¹ • cross p)))
        ((base.prod shift : ProbabilityMeasure (Omega × E)) :
          Measure (Omega × E)))
        (Metric.closedBall z (eps * finiteNormalizedSigma (kSeq m) n)) ≤
          ENNReal.ofReal
            (finiteIndependentShiftCoefficient (kSeq m) n * eps ^ 2))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (Measure.map
      (fun p : E × E ↦ hafnian (toMatrix (p.1 + p.2)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)))
      (Metric.closedBall z (eps * symmetricGaussianSigma n)) ≤
        ENNReal.ofReal
          (limitingIndependentShiftCoefficient n * eps ^ 2) := by
  let hdist :=
    independentAdditiveShiftHafnian_fixedCross_noMoments_tendstoInDistribution_of_weakLimit
      n toMatrix htoMatrix base shift limitLaw X hX hweak cross hcross
  let muSeq : ℕ → ProbabilityMeasure ℂ := fun m ↦
    ⟨Measure.map
      (fun p : Omega × E ↦ hafnian
        (toMatrix (X m p.1 + p.2 + (m : ℂ)⁻¹ • cross p)))
      ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)),
      Measure.isProbabilityMeasure_map (hdist.forall_aemeasurable m)⟩
  let mu : ProbabilityMeasure ℂ :=
    ⟨Measure.map
      (fun p : E × E ↦ hafnian (toMatrix (p.1 + p.2)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)),
      Measure.isProbabilityMeasure_map hdist.aemeasurable_limit⟩
  have hmu : Tendsto muSeq atTop (nhds mu) := by
    exact hdist.tendsto
  refine normalized_closedBall_measure_le_of_weakLimit
    muSeq mu (fun m ↦ finiteNormalizedSigma (kSeq m) n)
    (symmetricGaussianSigma n)
    (fun m ↦ finiteIndependentShiftCoefficient (kSeq m) n)
    (limitingIndependentShiftCoefficient n) hmu
    ((tendsto_finiteNormalizedSigma n).comp hkSeq)
    (symmetricGaussianSigma_pos n) ?_
    ((tendsto_finiteIndependentShiftCoefficient n hn).comp hkSeq)
    z ?_ eps heps
  · filter_upwards
      [hkSeq.eventually (eventually_gt_atTop (0 : ℕ))] with m hm
    exact finiteNormalizedSigma_pos (kSeq m) n hm
  · simpa [muSeq] using hfinite

/-- The exact `k = m^4` specialization used by the revised proof of
Corollary I.4.  This removes the last implicit subsequence substitution from
the paper to Lean crosswalk. -/
theorem independentAdditiveShiftHafnianSmallBall_fourthPower_fixedCross_of_weakLimit
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SecondCountableTopology E] [BorelSpace E]
    (n : ℕ) (hn : 1 ≤ n)
    (toMatrix : E → Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (htoMatrix : Continuous toMatrix)
    (base : ProbabilityMeasure Omega)
    (shift limitLaw : ProbabilityMeasure E)
    (X : ℕ → Omega → E) (hX : ∀ m, Measurable (X m))
    (hweak : Tendsto
      (fun m ↦ base.map (hX m).aemeasurable)
      atTop (nhds limitLaw))
    (cross : Omega × E → E)
    (hcross : AEStronglyMeasurable cross
      ((base.prod shift : ProbabilityMeasure (Omega × E)) :
        Measure (Omega × E)))
    (z : ℂ)
    (hfinite : ∀ᶠ m : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      (Measure.map
        (fun p : Omega × E ↦ hafnian
          (toMatrix (X m p.1 + p.2 + (m : ℂ)⁻¹ • cross p)))
        ((base.prod shift : ProbabilityMeasure (Omega × E)) :
          Measure (Omega × E)))
        (Metric.closedBall z
          (eps * finiteNormalizedSigma (m ^ 4) n)) ≤
          ENNReal.ofReal
            (finiteIndependentShiftCoefficient (m ^ 4) n * eps ^ 2))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (Measure.map
      (fun p : E × E ↦ hafnian (toMatrix (p.1 + p.2)))
      ((limitLaw.prod shift : ProbabilityMeasure (E × E)) :
        Measure (E × E)))
      (Metric.closedBall z (eps * symmetricGaussianSigma n)) ≤
        ENNReal.ofReal
          (limitingIndependentShiftCoefficient n * eps ^ 2) := by
  exact independentAdditiveShiftHafnianSmallBall_fixedCross_of_weakLimit
    n hn (fun m ↦ m ^ 4) tendsto_fourthPower_atTop
    toMatrix htoMatrix base shift limitLaw X hX hweak cross hcross
    z hfinite eps heps

end

end LogdetLean.GramHafnian.SymmetricGaussianLimit
