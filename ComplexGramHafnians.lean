import Challenge
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FinalTheorem
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Normalization
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.SecondMoment
import LogdetLean.GramHafnian.RankTwoCentralBinomial

/-! Proofs of the complete public specifications. No project axiom is added. -/

open MeasureTheory Filter
open scoped BigOperators Nat ENNReal Topology
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.SymmetricGaussianHafnian

namespace ComplexGramHafnians
noncomputable section

/-- The complete finite complex Gram result, for `n ≥ 1` and `k ≥ 4n`. -/
theorem theorem2_1 (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    Theorem21 n k := by
  have hkpos : 0 < k := by omega
  refine {
    rmsPositive := gramHafnianSigma_pos k n hkpos
    exactSecondMoment := ?_
    rmsSquared := ?_
    shiftedSmallBall := ?_
    limitingCoefficientFormula := paperBn_eq_gamma n
    coefficientProduct := paperBkn_eq_product k n hn
    coefficientBound := paperBkn_le_sharper k n hn hk
    coefficientLimit := tendsto_shiftedAnticoncentrationConstant_fixed_degree n hn
    logarithmicRemainder := ?_
  }
  · simpa only [actualGramFirstMomentReal, gramHafnianObservable,
      closedFirstMoment, dimensionProduct, oddPairingNat_eq_doubleFactorial] using
      actualGramFirstMomentReal_eq_closedFirstMoment k n hkpos
  · simpa only [closedFirstMoment, dimensionProduct,
      oddPairingNat_eq_doubleFactorial] using gramHafnianSigma_sq k n hkpos
  · intro z epsilon hepsilon
    exact gaussianGramHafnianShiftedAnticoncentration_min n k hn hk z epsilon hepsilon
  · intro hk8
    refine ⟨finiteCoefficientLogRemainder k n,
      shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hk, ?_⟩
    exact (abs_finiteCoefficientLogRemainder_le hn hk).trans
      (finiteCoefficientRemainderEnvelope_le_largeDimension hn hk8)

private theorem symmetricCoefficient_eq (n : ℕ) (hn : 1 ≤ n) :
    coefficient n = paperBn n := by
  exact (coefficient_centralBinomial n hn).trans
    (limitingAnticoncentrationConstant_eq_centralBinomial n hn).symm

private theorem fullMatrixSecondMoment (n : ℕ) :
    (∫ p, Complex.normSq (fullSymmetricHafnian p)
      ∂complexSymmetricGaussianFullMatrixLaw n) = (oddPairingNat n : ℝ) := by
  have hmeas : Measurable
      (fun x : Edge (Fin (2 * n)) → ℂ ↦ Complex.normSq (edgeHafnian x)) := by
    fun_prop
  have hmap := integral_map
    (μ := complexSymmetricGaussianFullMatrixLaw n)
    measurable_fst.aemeasurable hmeas.aestronglyMeasurable
  rw [complexSymmetricGaussianFullMatrixLaw_map_offDiagonal n] at hmap
  rw [show (fun p : ComplexFullSymmetricCoordinates n ↦
      Complex.normSq (fullSymmetricHafnian p)) =
      (fun p ↦ Complex.normSq (edgeHafnian p.1)) by
    funext p
    rw [fullSymmetricHafnian_eq_edgeHafnian]]
  exact hmap.symm.trans (integral_normSq_edgeHafnian n)

private theorem fullMatrixSmallBall (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (complexSymmetricGaussianFullMatrixLaw n).real
      {p | ‖fullSymmetricHafnian p - z‖ ≤ epsilon * sigma n} ≤
      min 1 (paperBn n * epsilon ^ 2) := by
  let E : Set (Edge (Fin (2 * n)) → ℂ) :=
    {x | ‖edgeHafnian x - z‖ ≤ epsilon * sigma n}
  have hE : MeasurableSet E := by
    dsimp [E]
    measurability
  have h := symmetricHafnian_shifted_smallBall n hn z epsilon hepsilon
  rw [symmetricCoefficient_eq n hn] at h
  have hnonneg : 0 ≤ paperBn n * epsilon ^ 2 := by
    rw [← symmetricCoefficient_eq n hn, coefficient_centralBinomial n hn]
    positivity
  have hfinite : min (1 : ℝ≥0∞) (ENNReal.ofReal (paperBn n * epsilon ^ 2)) ≠ ∞ :=
    (lt_of_le_of_lt (min_le_left _ _) ENNReal.one_lt_top).ne
  have hreal := ENNReal.toReal_mono hfinite h
  simp only [ENNReal.toReal_min ENNReal.one_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_ofReal hnonneg] at hreal
  change (edgeGaussian (Fin (2 * n))).real E ≤ _ at hreal
  rw [← complexSymmetricGaussianFullMatrixLaw_map_offDiagonal n] at hreal
  rw [Measure.real, Measure.map_apply measurable_fst hE] at hreal
  simpa only [Measure.real, Set.preimage_ofPred_eq, E,
    fullSymmetricHafnian_eq_edgeHafnian] using hreal

/-- The complete independent symmetric Gaussian result, for `n ≥ 1`. -/
theorem theorem2_3 (n : ℕ) (hn : 1 ≤ n) : Theorem23 n := by
  refine {
    rmsPositive := ?_
    exactSecondMoment := ?_
    rmsSquared := ?_
    shiftedSmallBall := fullMatrixSmallBall n hn
    coefficientFormula := paperBn_eq_gamma n
    coefficientLimit := tendsto_shiftedAnticoncentrationConstant_fixed_degree n hn
    elementaryCoefficient := ?_
  }
  · exact Real.sqrt_pos.mpr (by exact_mod_cast oddPairingNat_pos n)
  · simpa only [oddPairingNat_eq_doubleFactorial] using fullMatrixSecondMoment n
  · simpa only [oddPairingNat_eq_doubleFactorial] using sigma_sq n
  · have h := paperBn_le_two_div_sqrt_pi_mul_sqrt n hn
    simpa only [Real.sqrt_div (Nat.cast_nonneg n), div_mul_eq_mul_div,
      mul_div_assoc] using h

end
end ComplexGramHafnians
