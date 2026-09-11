import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import LogdetLean.GramHafnian.ThreePaper.RelativeAccuracyApplicationEndpoints

/-! Photon-pair weights and their normalized probability law.
The starting single-mode weights are those of the adopted squeezed-vacuum
model. The total law will be derived by convolution, not assumed. -/
open scoped BigOperators
open MeasureTheory Set Filter Polynomial
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 1600000

def pairCoefficient (a : ℝ) (n : ℕ) : ℝ := Ring.multichoose a n

theorem pairCoefficient_eq_product (a : ℝ) (n : ℕ) :
    pairCoefficient a n = (∏ j ∈ Finset.range n, (a + j)) / n.factorial := by
  have hp : (ascPochhammer ℝ n).eval a = ∏ j ∈ Finset.range n, (a + j) := by
    induction n with
    | zero => simp
    | succ n ih => simp [ascPochhammer_succ_right, ih, Finset.prod_range_succ]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  rw [nsmul_eq_mul, ascPochhammer_smeval_eq_eval, hp] at h
  apply (eq_div_iff (by positivity : (n.factorial : ℝ) ≠ 0)).2
  simpa [pairCoefficient, mul_comm] using h

theorem pairCoefficient_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ pairCoefficient a n := by
  rw [pairCoefficient_eq_product]
  positivity

theorem pairCoefficient_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < pairCoefficient a n := by
  rw [pairCoefficient_eq_product]
  positivity

/-- Generalized binomial series with its actual sum. -/
theorem pairCoefficient_hasSum (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n ↦ pairCoefficient a n * x ^ n) (1 / (1 - x) ^ a) := by
  have hb : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq] using hx
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum hb
  simpa [FormalMultilinearSeries.ofScalars, pairCoefficient, Ring.multichoose_eq] using h

/-- Negative-binomial pair mass with shape `a` and squeezing parameter `x`. -/
def pairMass (a x : ℝ) (n : ℕ) : ℝ :=
  pairCoefficient a n * x ^ n * (1 - x) ^ a

theorem pairMass_nonneg {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc 0 1) (n : ℕ) :
    0 ≤ pairMass a x n := by
  unfold pairMass
  exact mul_nonneg (mul_nonneg (pairCoefficient_nonneg ha _) (pow_nonneg hx.1 _))
    (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

theorem pairMass_hasSum_one {a x : ℝ} (hx : x ∈ Ico 0 1) :
    HasSum (pairMass a x) 1 := by
  have h := (pairCoefficient_hasSum a (x := x) (by simpa only [abs_of_nonneg hx.1] using hx.2)).mul_right ((1-x)^a)
  have hh : (1 - x) ^ a ≠ 0 := (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) a).ne'
  change HasSum (fun n ↦ pairCoefficient a n * x^n * (1-x)^a) 1
  simpa only [one_div, inv_mul_cancel₀ hh] using h

/-- A genuine normalized PMF, constructed from the proved binomial sum. -/
def photonPairPMF (a x : ℝ) (ha : 0 ≤ a) (hx : x ∈ Ico 0 1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (pairMass a x n), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg (pairMass_nonneg ha ⟨hx.1, hx.2.le⟩)
      (pairMass_hasSum_one hx).summable, (pairMass_hasSum_one hx).tsum_eq]
    simp⟩

@[simp] theorem photonPairPMF_mass (a x : ℝ) (ha : 0 ≤ a) (hx : x ∈ Ico 0 1) (n : ℕ) :
    (photonPairPMF a x ha hx n).toReal = pairMass a x n :=
  ENNReal.toReal_ofReal (pairMass_nonneg ha ⟨hx.1, hx.2.le⟩ n)

private theorem choose_neg_eq (a : ℝ) (n : ℕ) :
    Ring.choose (-a) n = (-1 : ℝ)^n * pairCoefficient a n := by
  simp [Ring.choose_neg', pairCoefficient, Units.smul_def]

/-- Exact convolution of the rising-factorial coefficients. -/
theorem pairCoefficient_add (a b : ℝ) (n : ℕ) :
    pairCoefficient (a+b) n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      pairCoefficient a ij.1 * pairCoefficient b ij.2 := by
  have h := Ring.add_choose_eq (r := -a) (s := -b) n (Commute.all _ _)
  rw [show -a + -b = -(a+b) by ring, choose_neg_eq] at h
  have hs : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, Ring.choose (-a) ij.1 * Ring.choose (-b) ij.2) =
      (-1:ℝ)^n * ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        pairCoefficient a ij.1 * pairCoefficient b ij.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [choose_neg_eq, choose_neg_eq]
    have hn := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    calc
      _ = ((-1:ℝ)^ij.1 * (-1:ℝ)^ij.2) *
          (pairCoefficient a ij.1 * pairCoefficient b ij.2) := by ring
      _ = _ := by rw [← pow_add, hn]
  rw [hs] at h
  exact (mul_left_cancel₀ (pow_ne_zero n (by norm_num))) h

/-- Convolution of two independent pair-count laws adds their shapes. -/
theorem pairMass_add {a b x : ℝ} (hx : x < 1) (n : ℕ) :
    pairMass (a+b) x n = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      pairMass a x ij.1 * pairMass b x ij.2 := by
  unfold pairMass
  rw [pairCoefficient_add, Finset.sum_mul, Finset.sum_mul,
    Real.rpow_add (sub_pos.mpr hx)]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← hn, pow_add]
  ring

/-- Sum of two independent natural-number-valued random variables. -/
def independentPairSum (p q : PMF ℕ) : PMF ℕ :=
  p.bind fun i ↦ q.bind fun j ↦ PMF.pure (i+j)

theorem independentPairSum_apply (p q : PMF ℕ) (n : ℕ) :
    independentPairSum p q n =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, p ij.1 * q ij.2 := by
  classical
  simp only [independentPairSum, PMF.bind_apply, PMF.pure_apply,
    mul_ite, mul_one, mul_zero]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  have hh : (fun ij : ℕ × ℕ ↦ p ij.1 * (if n = ij.1 + ij.2 then q ij.2 else 0)) =
      (fun ij : ℕ × ℕ ↦ if ij.1+ij.2=n then p ij.1*q ij.2 else 0) := by
    funext ij
    by_cases h : ij.1+ij.2=n
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hh]
  rw [tsum_eq_sum (s := Finset.HasAntidiagonal.antidiagonal n)]
  · apply Finset.sum_congr rfl
    intro ij hij
    simp [Finset.HasAntidiagonal.mem_antidiagonal.mp hij]
  · intro ij hij
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    simp [hij]

theorem photonPairPMF_add (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ∈ Ico 0 1) :
    independentPairSum (photonPairPMF a x ha hx) (photonPairPMF b x hb hx) =
      photonPairPMF (a+b) x (add_nonneg ha hb) hx := by
  ext n
  rw [independentPairSum_apply]
  change (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
    ENNReal.ofReal (pairMass a x ij.1) * ENNReal.ofReal (pairMass b x ij.2)) =
    ENNReal.ofReal (pairMass (a+b) x n)
  rw [pairMass_add hx.2]
  rw [ENNReal.ofReal_sum_of_nonneg (fun ij _ ↦ mul_nonneg
    (pairMass_nonneg ha ⟨hx.1,hx.2.le⟩ _) (pairMass_nonneg hb ⟨hx.1,hx.2.le⟩ _))]
  apply Finset.sum_congr rfl
  intro ij _
  exact (ENNReal.ofReal_mul (pairMass_nonneg ha ⟨hx.1,hx.2.le⟩ _)).symm

/-- Independent squeezed inputs, accumulated one input at a time. -/
def squeezedInputPairCount (x : ℝ) (hx : x ∈ Ico 0 1) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | K+1 => independentPairSum (squeezedInputPairCount x hx K)
      (photonPairPMF (1/2) x (by norm_num) hx)

/-- The shape-zero law is the zero-pair point mass. -/
theorem photonPairPMF_zero (x : ℝ) (hx : x ∈ Ico 0 1) :
    photonPairPMF 0 x (le_refl _) hx = PMF.pure 0 := by
  ext n
  change ENNReal.ofReal (pairMass 0 x n) = PMF.pure 0 n
  cases n with
  | zero => simp [pairMass, pairCoefficient]
  | succ n => simp [pairMass, pairCoefficient]

/-- The normalized total photon-pair law for K independent squeezed modes.
This discharges the negative-binomial identification, including odd K. -/
theorem squeezedInputPairCount_eq (x : ℝ) (hx : x ∈ Ico 0 1) (K : ℕ) :
    squeezedInputPairCount x hx K = photonPairPMF ((K:ℝ)/2) x (by positivity) hx := by
  induction K with
  | zero => simpa [squeezedInputPairCount] using (photonPairPMF_zero x hx).symm
  | succ K ih =>
    rw [squeezedInputPairCount, ih, photonPairPMF_add]
    congr 1
    push_cast
    ring

end
end GBSHiding
