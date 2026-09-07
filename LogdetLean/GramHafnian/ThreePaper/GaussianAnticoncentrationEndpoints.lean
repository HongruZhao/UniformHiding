import LogdetLean.GramHafnian.ShiftedAnticoncentration.FinalTheorem
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.LiteralFourierStep
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.GeneralBilinearGaussian
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.Divergence
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.ScoreTransformPairing
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.HermitianRankOneDecomposition
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialLowerBound.LiteralEndpointAlt
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.ConditionalInverseDensity.RadialAngular
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialLowerBound.InverseIntegrabilityEquivalence
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.ProofEquations
import LogdetLean.GramHafnian.ShiftedAnticoncentration.IndependentFactorShiftPaperEndpoint
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.FullMatrix
import LogdetLean.GramHafnian.SymmetricGaussianLimit.PaperEndpoints
import LogdetLean.GramHafnian.LocalAnticoncentration.CoefficientPaperEndpoints
import LogdetLean.GramHafnian.LocalAnticoncentration.ConditionalOnVariance
import LogdetLean.GramHafnian.LocalAnticoncentration.RegularizedWishart
import LogdetLean.GramHafnian.LocalAnticoncentration.DensitySupNorm
import LogdetLean.GramHafnian.LocalAnticoncentration.LocalSharpness
import LogdetLean.GramHafnian.MatrixLawEndpoints.GenericPreservedCoordinateInverseVariance
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Tactic

/-!
# Paper-facing endpoints for matrix-law anticoncentration

This module contains only Gaussian Gram-hafnian anticoncentration material.
In particular, its import closure contains no uniformly-hiding module.  It
adds the literal adapters that were formerly implicit in the paper-to-Lean
crosswalk: the conjugated Fourier coefficient, the affine transpose-Gram
fiber and its algebraic kernel, the two regularized rank-one traces, and the
finite-dimensional Gaussian cutoff integration-by-parts engine.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder ENNReal

namespace LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.PaperEndpoints

noncomputable section

open Wishart
open LocalAnticoncentration
open MatrixLawEndpoints
open RadialLowerBoundAlt
open SymmetricGaussianHafnian
open SymmetricGaussianLimit

/-! ## Main finite theorem and polynomial regime -/

/-- Complete clean bundle for `thm:main-finite`. -/
theorem result_thm_main_finite
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    gramHafnianSigma k n ^ 2 =
        (oddPairingNat n : ℝ) *
          ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ) ∧
      (∀ z : ℂ, ∀ eps : ℝ, 0 ≤ eps →
        gramHafnianShiftedSmallBallProbability k n z eps ≤
          min 1 (paperBkn k n * eps ^ 2)) ∧
      paperBn n =
        2 * Real.Gamma ((n : ℝ) + 1 / 2) /
          (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) ∧
      paperBkn k n =
        paperBn n * ((k : ℝ) / ((k : ℝ) - 1)) *
          ((2 : ℝ) ^ (n - 1) / (4 : ℝ) ^ (n - 1)) *
          (Real.Gamma ((k : ℝ) / 2 + (n : ℝ)) /
            Real.Gamma ((k : ℝ) / 2 + 1)) *
          (Real.Gamma (((k : ℝ) - 4 * (n : ℝ) + 1) / 4) /
            Real.Gamma (((k : ℝ) - 3) / 4)) ∧
      paperBkn k n ≤ paperBn n * Real.exp
        ((3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) +
          9 * (n : ℝ) ^ 3 /
            ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1))) ∧
      Filter.Tendsto (fun j : ℕ ↦ paperBkn j n)
        Filter.atTop (nhds (paperBn n)) ∧
      (8 * n ≤ k → ∃ theta : ℝ,
        paperBkn k n = paperBn n *
          Real.exp (3 * (n : ℝ) ^ 2 / (k : ℝ) + theta) ∧
        |theta| ≤ 2 / (k : ℝ) + 94 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2) ∧
      (∀ (kseq : ℕ → ℕ) {D : ℝ}, 0 < D →
        (∀ᶠ j : ℕ in Filter.atTop, 0 < kseq j) →
        (∀ᶠ j : ℕ in Filter.atTop,
          (j : ℝ) ^ 2 / (kseq j : ℝ) ≤ D * Real.log (j : ℝ)) →
        Filter.Tendsto
          (fun j : ℕ ↦ finiteCoefficientLogRemainder (kseq j) j)
          Filter.atTop (nhds 0)) ∧
      Filter.Tendsto
        (fun j : ℕ ↦ paperBn j /
          (2 * Real.sqrt ((j : ℝ) / Real.pi)))
        Filter.atTop (nhds 1) := by
  refine ⟨eq3_variance_product k n (by omega), ?_,
    paperBn_eq_gamma n, paperBkn_eq_gamma k n hn hk,
    paperBkn_le_sharper k n hn hk,
    tendsto_shiftedAnticoncentrationConstant_fixed_degree n hn,
    ?_, ?_, ?_⟩
  · intro z eps heps
    exact eq4_shifted_small_ball n k hn hk z eps heps
  · intro hk8
    refine ⟨finiteCoefficientLogRemainder k n,
      shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hk, ?_⟩
    exact (abs_finiteCoefficientLogRemainder_le hn hk).trans
      (finiteCoefficientRemainderEnvelope_le_largeDimension hn hk8)
  · intro kseq D hD hkpos hscale
    exact tendsto_finiteCoefficientLogRemainder_of_log_scale
      kseq hD hkpos hscale
  · have hfun :
        (fun j : ℕ ↦ paperBn j /
          (2 * Real.sqrt ((j : ℝ) / Real.pi))) =
        (fun j : ℕ ↦ paperBn j /
          (2 * Real.sqrt (j : ℝ) / Real.sqrt Real.pi)) := by
      funext j
      rw [Real.sqrt_div (Nat.cast_nonneg j)]
      ring
    rw [hfun]
    exact limitingAnticoncentrationConstant_ratio_tendsto_one

/-- Complete Article bundle for the independent random matrix shift
corollary: the exact Laplace chain and the normalized probability-capped
small-ball estimate. -/
def result_cor_independent_matrix_shift :=
  And.intro (@independentFactorShift_laplace_chain)
    (@independentFactorShift_normalizedSmallBall)

/-! ## Direct independent symmetric Gaussian endpoints -/

/-- The direct independent-edge coefficient is exactly the coefficient
`b_n` used in the Article. -/
theorem symmetricGaussianCoefficient_eq_paperBn
    (n : ℕ) (hn : 1 ≤ n) :
    SymmetricGaussianHafnian.coefficient n = paperBn n := by
  calc
    SymmetricGaussianHafnian.coefficient n =
        (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n :=
      SymmetricGaussianHafnian.coefficient_centralBinomial n hn
    _ = limitingAnticoncentrationConstant n :=
      (limitingAnticoncentrationConstant_eq_centralBinomial n hn).symm
    _ = paperBn n := rfl

/-! ### Human-readable direct cofactor bridge -/

/-- The paper-indexed literal cofactor vector on the odd background with
`2r-1` vertices. -/
abbrev paperSymmetricCofactorVector (r : ℕ)
    (x : Edge (Fin (2 * r - 1)) → ℂ) : Fin (2 * r - 1) → ℂ :=
  edgeCofactor x

/-- The squared Euclidean energy of the paper-indexed cofactor vector. -/
abbrev paperSymmetricCofactorEnergy (r : ℕ)
    (x : Edge (Fin (2 * r - 1)) → ℂ) : ℝ :=
  edgeCofactorEnergy x

/-- The extended inverse moment used in the direct symmetric Gaussian proof. -/
abbrev paperSymmetricCofactorInverseMoment (r : ℕ) : ℝ≥0∞ :=
  ennInverseMoment (edgeGaussian (Fin (2 * r - 1))) edgeCofactorEnergy

/-- Exact definitional bundle for the displayed cofactor vector and energy. -/
theorem eq_paper_symmetricCofactor_definitions
    (r : ℕ) (x : Edge (Fin (2 * r - 1)) → ℂ) :
    paperSymmetricCofactorVector r x = edgeCofactor x ∧
      paperSymmetricCofactorEnergy r x =
        ∑ j, ‖paperSymmetricCofactorVector r x j‖ ^ 2 := by
  exact ⟨rfl, rfl⟩

/-- Exact one-based base case and inverse-moment recurrence printed in the
direct symmetric Gaussian proof. -/
theorem result_paper_symmetricCofactor_inverse_recurrence :
    (∀ x : Edge (Fin 1) → ℂ, paperSymmetricCofactorEnergy 1 x = 1) ∧
      paperSymmetricCofactorInverseMoment 1 = 1 ∧
        ∀ r : ℕ, 2 ≤ r →
          paperSymmetricCofactorInverseMoment r ≤
            paperSymmetricCofactorInverseMoment (r - 1) *
              ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹) := by
  constructor
  · intro x
    simpa [paperSymmetricCofactorEnergy] using edgeCofactorEnergy_fin_one x
  constructor
  · simpa [paperSymmetricCofactorInverseMoment, cofactorInverseMoment] using
      cofactorInverseMoment_zero
  · intro r hr
    have h := cofactorInverseMoment_step (r - 2)
    unfold cofactorInverseMoment at h
    have hleft : 2 * (r - 2 + 1) + 1 = 2 * r - 1 := by omega
    have hright : 2 * (r - 2) + 1 = 2 * (r - 1) - 1 := by omega
    rw [hleft, hright] at h
    have hfactor : (2 : ℝ) * ((r - 2 : ℕ) : ℝ) + 2 =
        2 * (r : ℝ) - 2 := by
      rw [Nat.cast_sub hr]
      ring
    rw [hfactor] at h
    exact h

/-- Exact iterated inverse-moment estimate, including the literal `W_1=1`
base through the preceding recurrence. -/
theorem result_paper_symmetricCofactor_inverse_iteration
    (n : ℕ) (hn : 1 ≤ n) :
    paperSymmetricCofactorInverseMoment n ≤
      ENNReal.ofReal
        (((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ))⁻¹) := by
  have h := symmetricCofactor_inverseMoment_le n hn
  rw [inverseBound_closed n hn] at h
  exact h

/-- Exact normalized inverse-moment chain in the paper's double-factorial,
Gamma, and `b_n` normalizations. -/
theorem result_paper_symmetricCofactor_normalized_chain
    (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (sigma n ^ 2) * paperSymmetricCofactorInverseMoment n ≤
        ENNReal.ofReal
          (((((2 * n - 1).doubleFactorial : ℕ) : ℝ) /
            ((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ)))) ∧
      (((((2 * n - 1).doubleFactorial : ℕ) : ℝ) /
          ((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ))) =
        2 * Real.Gamma ((n : ℝ) + 1 / 2) /
          (Real.sqrt Real.pi * Real.Gamma (n : ℝ))) ∧
      (2 * Real.Gamma ((n : ℝ) + 1 / 2) /
          (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) = paperBn n) := by
  let ratio : ℝ :=
    ((((2 * n - 1).doubleFactorial : ℕ) : ℝ) /
      ((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ)))
  have hratioCoefficient : ratio = SymmetricGaussianHafnian.coefficient n := by
    rw [show ratio = (oddPairingNat n : ℝ) /
        ((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ)) by
      dsimp [ratio]
      rw [oddPairingNat_eq_doubleFactorial]]
    exact (SymmetricGaussianHafnian.coefficient_closed n hn).symm
  have hratioBn : ratio = paperBn n :=
    hratioCoefficient.trans (symmetricGaussianCoefficient_eq_paperBn n hn)
  have hgammaBn :
      2 * Real.Gamma ((n : ℝ) + 1 / 2) /
          (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) = paperBn n :=
    (paperBn_eq_gamma n).symm
  have hproductRatio :
      (oddPairingNat n : ℝ) *
          (((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ))⁻¹) = ratio := by
    calc
      _ = SymmetricGaussianHafnian.coefficient n := by
        rw [SymmetricGaussianHafnian.coefficient,
          SymmetricGaussianHafnian.inverseBound_closed n hn]
      _ = ratio := hratioCoefficient.symm
  have hscaled :
      ENNReal.ofReal (sigma n ^ 2) * paperSymmetricCofactorInverseMoment n ≤
        ENNReal.ofReal ratio := by
    calc
      _ ≤ ENNReal.ofReal (sigma n ^ 2) *
          ENNReal.ofReal
            (((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ))⁻¹) :=
        mul_le_mul le_rfl
          (result_paper_symmetricCofactor_inverse_iteration n hn) bot_le bot_le
      _ = ENNReal.ofReal
          (sigma n ^ 2 *
            (((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ))⁻¹)) := by
        rw [ENNReal.ofReal_mul (sq_nonneg (sigma n))]
      _ = ENNReal.ofReal ratio := by
        congr 1
        rw [sigma_sq]
        exact hproductRatio
  refine ⟨?_, ?_, hgammaBn⟩
  · simpa [ratio] using hscaled
  · calc
      ((((2 * n - 1).doubleFactorial : ℕ) : ℝ) /
          ((2 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ))) =
          paperBn n := by simpa [ratio] using hratioBn
      _ = 2 * Real.Gamma ((n : ℝ) + 1 / 2) /
          (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) := paperBn_eq_gamma n

/-- Exact scalar law and centered-disk comparison used at each star in the
independent perturbation argument. -/
def result_paper_symmetricStar_scalar_centering :=
  And.intro (@map_iidCircularTransposeLinearForm_eq_scaled_circular)
    (@iidCircularTransposeLinearForm_norm_add_le_centered)

/-- Exact paper-facing form of the direct independent complex symmetric
Gaussian hafnian theorem.  The diagonal variables are omitted because the
ordinary hafnian never uses diagonal entries. -/
theorem result_thm_symmetric_gaussian_anticoncentration
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (SymmetricGaussianHafnian.edgeGaussian (Fin (2 * n)))
      {x | ‖SymmetricGaussianHafnian.edgeHafnian x - z‖ ≤
        eps * SymmetricGaussianHafnian.sigma n} ≤
      min 1 (ENNReal.ofReal (paperBn n * eps ^ 2)) := by
  rw [← symmetricGaussianCoefficient_eq_paperBn n hn]
  exact SymmetricGaussianHafnian.symmetricHafnian_shifted_smallBall
    n hn z eps heps

/-- Exact paper-facing arbitrary independent additive perturbation theorem
for the off-diagonal edge array.  The perturbation law may have arbitrary
dependence and no moment or boundedness assumption. -/
theorem result_cor_symmetric_gaussian_perturbation
    (n : ℕ) (hn : 1 ≤ n)
    (nu : Measure (SymmetricGaussianHafnian.Edge (Fin (2 * n)) → ℂ))
    [IsProbabilityMeasure nu]
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    ((SymmetricGaussianHafnian.edgeGaussian (Fin (2 * n))).prod nu)
      {p | ‖SymmetricGaussianHafnian.edgeHafnian (p.2 + p.1) - z‖ ≤
        eps * SymmetricGaussianHafnian.sigma n} ≤
      min 1 (ENNReal.ofReal (paperBn n * eps ^ 2)) := by
  rw [← symmetricGaussianCoefficient_eq_paperBn n hn]
  simpa using
    (SymmetricGaussianHafnian.symmetricHafnian_independentShift_scaled_smallBall
      n hn 1 zero_lt_one nu z eps heps)

/-- Exact full matrix form of the direct independent complex symmetric
Gaussian hafnian theorem.  The diagonal law has complex variance two, and
the diagonal invariance adapter reduces the event to the direct edge theorem. -/
theorem result_thm_symmetric_gaussian_fullMatrix_anticoncentration
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (complexSymmetricGaussianFullMatrixLaw n)
      {p | ‖fullSymmetricHafnian p - z‖ ≤
        eps * SymmetricGaussianHafnian.sigma n} ≤
      min 1 (ENNReal.ofReal (paperBn n * eps ^ 2)) := by
  let E : Set (Edge (Fin (2 * n)) → ℂ) :=
    {x | ‖edgeHafnian x - z‖ ≤ eps * SymmetricGaussianHafnian.sigma n}
  have hE : MeasurableSet E := by
    dsimp [E]
    measurability
  have h := result_thm_symmetric_gaussian_anticoncentration
    n hn z eps heps
  rw [← complexSymmetricGaussianFullMatrixLaw_map_offDiagonal n] at h
  rw [Measure.map_apply measurable_fst hE] at h
  simpa [E, fullSymmetricHafnian_eq_edgeHafnian] using h

/-- Theorem I.3 together with the coefficient bound printed
immediately after it. -/
theorem result_thm_symmetric_gaussian_fullMatrix_anticoncentration_with_coefficient
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (complexSymmetricGaussianFullMatrixLaw n)
        {p | ‖fullSymmetricHafnian p - z‖ ≤
          eps * SymmetricGaussianHafnian.sigma n} ≤
        min 1 (ENNReal.ofReal (paperBn n * eps ^ 2)) ∧
      paperBn n ≤ (2 / Real.sqrt Real.pi) * Real.sqrt (n : ℝ) ∧
      Filter.Tendsto
        (fun j : ℕ ↦ paperBn j /
          (2 * Real.sqrt ((j : ℝ) / Real.pi)))
        Filter.atTop (nhds 1) := by
  exact ⟨result_thm_symmetric_gaussian_fullMatrix_anticoncentration
      n hn z eps heps,
    paperBn_le_two_div_sqrt_pi_mul_sqrt n hn,
    paperBn_ratio_tendsto_one⟩

/-- Exact full matrix form of the arbitrary independent additive perturbation
corollary.  Arbitrary diagonal entries and diagonal perturbations disappear
by the kernel checked diagonal invariance identity. -/
theorem result_cor_symmetric_gaussian_fullMatrix_perturbation
    (n : ℕ) (hn : 1 ≤ n)
    (nu : Measure (ComplexFullSymmetricCoordinates n))
    [IsProbabilityMeasure nu]
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    ((complexSymmetricGaussianFullMatrixLaw n).prod nu)
      {p | ‖fullSymmetricHafnian
          (addFullSymmetricCoordinates p.2 p.1) - z‖ ≤
        eps * SymmetricGaussianHafnian.sigma n} ≤
      min 1 (ENNReal.ofReal (paperBn n * eps ^ 2)) := by
  let nuEdge : Measure (Edge (Fin (2 * n)) → ℂ) := nu.map Prod.fst
  letI : IsProbabilityMeasure nuEdge :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  let E : Set ((Edge (Fin (2 * n)) → ℂ) ×
      (Edge (Fin (2 * n)) → ℂ)) :=
    {p | ‖edgeHafnian (p.2 + p.1) - z‖ ≤
      eps * SymmetricGaussianHafnian.sigma n}
  have hE : MeasurableSet E := by
    dsimp [E]
    measurability
  have hmap :
      ((complexSymmetricGaussianFullMatrixLaw n).prod nu).map
          (Prod.map Prod.fst Prod.fst) =
        (edgeGaussian (Fin (2 * n))).prod nuEdge := by
    calc
      ((complexSymmetricGaussianFullMatrixLaw n).prod nu).map
          (Prod.map Prod.fst Prod.fst) =
          ((complexSymmetricGaussianFullMatrixLaw n).map Prod.fst).prod
            (nu.map Prod.fst) :=
        (Measure.map_prod_map _ _ measurable_fst measurable_fst).symm
      _ = (edgeGaussian (Fin (2 * n))).prod nuEdge := by
        rw [complexSymmetricGaussianFullMatrixLaw_map_offDiagonal]
  have h := result_cor_symmetric_gaussian_perturbation
    n hn nuEdge z eps heps
  rw [← hmap] at h
  rw [Measure.map_apply (measurable_fst.prodMap measurable_fst) hE] at h
  simpa [E, fullSymmetricHafnian_add_eq_edgeHafnian] using h

/-- Exact sequence form of `cor:polynomial`, including the admissible
parameter assumptions printed as labeled equations. -/
theorem result_cor_polynomial
    (A D : ℝ) (hA : 0 < A) (hD : 0 < D)
    (kseq : ℕ → ℕ)
    (hkpos : ∀ᶠ n : ℕ in Filter.atTop, 0 < kseq n)
    (hscale : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    (∃ gamma : ℝ, 0 < gamma ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ z : ℂ,
        gramHafnianShiftedSmallBallProbability (kseq n) n z
            ((n : ℝ) ^ (-gamma)) ≤ (n : ℝ) ^ (-A)) ∧
    (∀ gamma : ℝ, (A + 3 * D + (1 / 2 : ℝ)) / 2 < gamma →
      ∀ᶠ n : ℕ in Filter.atTop, ∀ z : ℂ,
        gramHafnianShiftedSmallBallProbability (kseq n) n z
            ((n : ℝ) ^ (-gamma)) ≤ (n : ℝ) ^ (-A)) := by
  let gamma : ℝ := (A + 3 * D + (1 / 2 : ℝ)) / 2 + 1
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hmargin : (A + 3 * D + (1 / 2 : ℝ)) / 2 < gamma := by
    dsimp [gamma]
    linarith
  refine ⟨⟨gamma, hgamma,
    gaussianGramHafnianShiftedAnticoncentration_polynomial_sharp
      kseq hA hD hmargin hkpos hscale⟩, ?_⟩
  intro beta hbeta
  exact gaussianGramHafnianShiftedAnticoncentration_polynomial_sharp
    kseq hA hD hbeta hkpos hscale

/-! ## Conditional mixture and Fourier bundles -/

def result_prop_conditional_mixture :=
  And.intro (@eq7_last_column_expansion)
    (And.intro (@eq7_fixed_past_gaussian_law)
      (@gramHafnian_hasCondDistrib_given_pastCofactorV))

def result_prop_exact_second_moment :=
  And.intro (@eq3_variance_is_actual_second_moment)
    (@eq3_variance_product)

def result_lem_bilinear_interpolation :=
  And.intro
    (@bilinearGaussianIntegral_eq_spectral_completedSquareKernel)
    (@bilinearGaussianIntegral_endpoints_pos_and_geometric)

def result_prop_cofactor_compression :=
  And.intro
    (@finiteGramCofactorCharacteristic_radial_compression)
    (@oddHafnianCofactorCharacteristic_singleton_first)

def result_prop_fourier_to_laplace :=
  And.intro (@pastCofactorWInverseMoment_le_fourier)
    (@eq9_fourier)

/-! ## Literal cofactor energies and Wishart coordinates -/

theorem eq_Wr_Vr_definition {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    pastCofactorW hr A =
        ∑ j : OddCofactorIndex r hr,
          Complex.normSq (pastHafnianCofactorVector hr A j) ∧
      pastCofactorV hr A =
        ∑ i : Fin k, ‖pastCofactorCombination hr A i‖ ^ 2 := by
  constructor
  · exact pastCofactorW_eq_sum_normSq hr A
  · rw [pastCofactorV_eq_coefficientEnergy]
    rfl

theorem eq_inverse_moment_definitions
    {k r : ℕ} (hr : 1 ≤ r) :
    pastCofactorVInverseMoment k r =
        ∫⁻ A, ENNReal.ofReal ((pastCofactorV hr A)⁻¹)
          ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k) ∧
      pastCofactorWInverseMoment k r =
        ∫⁻ A, ENNReal.ofReal ((pastCofactorW hr A)⁻¹)
          ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k) := by
  constructor
  · rw [pastCofactorVInverseMoment_eq hr]
    rfl
  · rw [pastCofactorWInverseMoment_eq hr]
    rfl

theorem eq_wishart_gram_coordinate_maps
    {m : Type*} (P C D : Matrix m m ℝ) :
    sOfRealBlocks P C D = (fun i j ↦
        ((P i j - D i j : ℝ) : ℂ) +
          Complex.I * ((C i j + C j i : ℝ) : ℂ)) ∧
      qOfRealBlocks P C D = (fun i j ↦
        ((P i j + D i j : ℝ) : ℂ) +
          Complex.I * ((C i j - C j i : ℝ) : ℂ)) :=
  ⟨rfl, rfl⟩

theorem eq_two_gram_coordinates
    {k m : Type*} [Fintype k] [Fintype m] [DecidableEq m]
    (X Y : Matrix k m ℝ) :
    transposeGramMatrix (complexOfRealPair X Y) =
        sOfRealBlocks (X.transpose * X) (X.transpose * Y)
          (Y.transpose * Y) ∧
      hermitianGram (complexOfRealPair X Y) =
        qOfRealBlocks (X.transpose * X) (X.transpose * Y)
          (Y.transpose * Y) :=
  ⟨transposeGramMatrix_complexOfRealPair X Y,
    hermitianGram_complexOfRealPair X Y⟩

theorem eq_inverse_gram_coordinate_map
    {m : Type*} (Q S : Matrix m m ℂ) :
    recoverU Q S = (fun i j ↦ ((Q i j).re + (S i j).re) / 2) ∧
      recoverV Q S = (fun i j ↦ ((Q i j).re - (S i j).re) / 2) ∧
      recoverC Q S = (fun i j ↦ ((S i j).im + (Q i j).im) / 2) := by
  constructor
  · funext i j
    simp [recoverU]
    ring
  constructor
  · funext i j
    simp [recoverV]
    ring
  · funext i j
    simp [recoverC]
    ring

/-! ## Bounded score and deterministic Schur geometry -/

def extendSymmetricScalarRule {m : ℕ}
    (u : SymmetricComplexMatrix m → ℝ)
    (S : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  u (symmetricComplexMatrixProjection S)

theorem measurable_extendSymmetricScalarRule {m : ℕ}
    {u : SymmetricComplexMatrix m → ℝ} (hu : Measurable u) :
    Measurable (extendSymmetricScalarRule u) :=
  hu.comp measurable_symmetricComplexMatrixProjection

@[simp] theorem extendSymmetricScalarRule_preservedCoordinate
    {k m : ℕ} (u : SymmetricComplexMatrix m → ℝ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    extendSymmetricScalarRule u (preservedSCoordinate R) =
      u (preservedSymmetricCoordinate R) := by
  unfold extendSymmetricScalarRule
  congr 1
  apply Subtype.ext
  exact symmetricComplexMatrixProjection_of_isSymm
    (preservedSymmetricCoordinate R).property

/-- Literal symmetric-subspace bounded-Borel score endpoint. -/
theorem result_prop_bounded_preserved_S_score
    {k m : ℕ}
    (u : SymmetricComplexMatrix m → ℝ) (hu : Measurable u)
    (C : ℝ) (huC : ∀ S, |u S| ≤ C)
    {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (hgap : 2 * m + 1 < k) :
    Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          u (preservedSymmetricCoordinate R) *
            (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
        (halfGaussianMatrixSum k (Fin m)) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          u (preservedSymmetricCoordinate R) * Matrix.trace (scoreDeltaM H))
        (halfGaussianMatrixSum k (Fin m)) ∧
      ((∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          u (preservedSymmetricCoordinate R) *
            (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
          ∂halfGaussianMatrixSum k (Fin m)) =
        Matrix.trace (scoreDeltaM H) *
          ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
            u (preservedSymmetricCoordinate R)
            ∂halfGaussianMatrixSum k (Fin m)) := by
  have hdata := bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
    (extendSymmetricScalarRule u)
    (measurable_extendSymmetricScalarRule hu) C
    (by intro S; exact huC (symmetricComplexMatrixProjection S))
    hH (by simpa [two_mul] using hgap)
  simp only [preservedSWeight,
    extendSymmetricScalarRule_preservedCoordinate] at hdata
  refine ⟨hdata.1, hdata.2.1, ?_⟩
  rw [hdata.2.2]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with R
  ring

theorem coupledSchurComplement_le_hermitianGram
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix n m ℂ)
    (hA : Function.Injective (complexConjugateColumnPair A).mulVec) :
    coupledSchurComplement A ≤ hermitianGram A := by
  have hK := coupledGramKernel_posDef A hA
  have hD : ((hermitianGram A).map star).PosDef := by
    rw [coupledGramKernel_eq_fromBlocks_adjoint] at hK
    convert hK.submatrix (e := Sum.inr) Sum.inr_injective using 1 <;>
      ext i j <;> rfl
  exact schurComplement22_le _ _ hD

theorem hermitianGram_posDef_of_complexConjugateColumnPair_injective
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix n m ℂ)
    (hA : Function.Injective (complexConjugateColumnPair A).mulVec) :
    (hermitianGram A).PosDef := by
  have hK := coupledGramKernel_posDef A hA
  rw [coupledGramKernel_eq_fromBlocks_adjoint] at hK
  convert hK.submatrix (e := Sum.inl) Sum.inl_injective using 1 <;>
    ext i j <;> rfl

/-- One endpoint for all assertions of the deterministic Schur proposition. -/
theorem result_prop_deterministic_schur_order
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix n m ℂ)
    (hA : Function.Injective (complexConjugateColumnPair A).mulVec) :
    (coupledSchurComplement A).PosDef ∧
      coupledSchurComplement A ≤ hermitianGram A ∧
      (hermitianGram A)⁻¹ ≤ (coupledSchurComplement A)⁻¹ ∧
      Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹ =
        (coupledSchurComplement A)⁻¹ ∧
      ∀ c : m → ℂ,
        vectorNormSq c ^ 2 ≤
          quadraticFormReal (hermitianGram A) c *
            quadraticFormReal (hermitianGram A)⁻¹ c := by
  refine ⟨coupledSchurComplement_posDef A hA,
    coupledSchurComplement_le_hermitianGram A hA,
    hermitianGram_inverse_le_coupledSchur_inverse A hA,
    coupledKernel_inverse_toBlocks11 A hA, ?_⟩
  exact matrix_cauchy_schwarz
    (hermitianGram_posDef_of_complexConjugateColumnPair_injective A hA)

def result_thm_preserved_coordinate_inverse_variance :=
  @eq_preserved_coordinate_inverse_variance_symmetricDomain

def result_cor_self_coupled_direction :=
  And.intro (@pastCofactorVInverseMoment_le_wishart)
    (@eq10_wishart)

def result_prop_inverse_variance := @eq11_inverse_variance

/-! ## Matrix-valued regularized score on the symmetric domain -/

def preservedCoordinateRegularizedRankOneOnS {m : ℕ}
    (δ : ℝ) (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (S : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (vectorNormSq (c S) + δ)⁻¹ ^ 2 • hermitianRankOne (c S)

theorem eq_matrix_valued_preserved_score
    {k m : ℕ} {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) {δ : ℝ} (hδ : 0 < δ)
    (hgap : 2 * m + 1 < k) :
    (let μ := halfGaussianMatrixSum k (Fin m)
     let a := inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m)
     (∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        a * Matrix.trace ((realWishartGram R)⁻¹ *
          scoreDeltaM (preservedCoordinateRegularizedRankOneOnS δ c
            (preservedSCoordinate R))) ∂μ) =
      ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        Matrix.trace
          (scoreDeltaM (preservedCoordinateRegularizedRankOneOnS δ c
            (preservedSCoordinate R))) ∂μ) := by
  dsimp only
  let μ := halfGaussianMatrixSum k (Fin m)
  let a := inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m)
  have hre (i j : Fin m) :=
    preservedCoordinate_realCoordinate_score_pair hδ hgap hc i j
  have him (i j : Fin m) :=
    preservedCoordinate_imagCoordinate_score_pair hδ hgap hc i j
  have hvariable :
      (∫ R, preservedCoordinateRegularizedWeight δ c R *
          (a * Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM
              (hermitianRankOne (preservedCoordinateVector c R)))) ∂μ) =
        ∫ R, preservedCoordinateRegularizedWeight δ c R *
          Matrix.trace
            (scoreDeltaM
              (hermitianRankOne (preservedCoordinateVector c R))) ∂μ := by
    exact integral_variable_rankOne_score_eq_of_coordinate_scores
      μ (fun R ↦ (realWishartGram R)⁻¹)
      (preservedCoordinateRegularizedWeight δ c)
      (preservedCoordinateVector c) a
      (fun i j ↦ (hre i j).1) (fun i j ↦ (him i j).1)
      (fun i j ↦ (hre i j).2.1) (fun i j ↦ (him i j).2.1)
      (fun i j ↦ (hre i j).2.2) (fun i j ↦ (him i j).2.2)
  calc
    (∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        a * Matrix.trace ((realWishartGram R)⁻¹ *
          scoreDeltaM (preservedCoordinateRegularizedRankOneOnS δ c
            (preservedSCoordinate R))) ∂μ) =
        ∫ R, preservedCoordinateRegularizedWeight δ c R *
          (a * Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM
              (hermitianRankOne (preservedCoordinateVector c R)))) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with R
      simp only [preservedCoordinateRegularizedRankOneOnS,
        preservedCoordinateRegularizedWeight, preservedCoordinateW,
        preservedCoordinateVector, scoreDeltaM_real_smul,
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      ring
    _ = ∫ R, preservedCoordinateRegularizedWeight δ c R *
          Matrix.trace
            (scoreDeltaM
              (hermitianRankOne (preservedCoordinateVector c R))) ∂μ :=
      hvariable
    _ = ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        Matrix.trace
          (scoreDeltaM (preservedCoordinateRegularizedRankOneOnS δ c
            (preservedSCoordinate R))) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with R
      simp only [preservedCoordinateRegularizedRankOneOnS,
        preservedCoordinateRegularizedWeight, preservedCoordinateW,
        preservedCoordinateVector, scoreDeltaM_real_smul,
        Matrix.trace_smul, smul_eq_mul]

theorem eq_regularized_coupled_inverse_identity
    {k m : ℕ} (hgap : 2 * m + 1 < k)
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) (δ : ℝ) (hδ : 0 < δ) :
    (∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        preservedCoordinateXi c R /
          (preservedCoordinateW c R + δ) ^ 2
        ∂halfGaussianMatrixSum k (Fin m)) =
      (((k : ℝ) - 2 * m - 1)⁻¹) *
        ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          preservedCoordinateW c R /
            (preservedCoordinateW c R + δ) ^ 2
          ∂halfGaussianMatrixSum k (Fin m) :=
  (preservedCoordinate_regularized_integral_data hgap hc δ hδ).2.2

def preservedSymmetricRegularizedRankOneOnS {m : ℕ}
    (δ : ℝ) (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (S : SymmetricComplexMatrix m) : Matrix (Fin m) (Fin m) ℂ :=
  (vectorNormSq (c S) + δ)⁻¹ ^ 2 • hermitianRankOne (c S)

@[simp] theorem preservedRegularizedRankOne_extendSymmetricRule
    {k m : ℕ} (δ : ℝ)
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateRegularizedRankOneOnS δ
        (extendSymmetricPreservedRule c) (preservedSCoordinate R) =
      preservedSymmetricRegularizedRankOneOnS δ c
        (preservedSymmetricCoordinate R) := by
  have hcval :
      c (symmetricComplexMatrixProjection (preservedSCoordinate R)) =
        c (preservedSymmetricCoordinate R) := by
    congr 1
    apply Subtype.ext
    exact symmetricComplexMatrixProjection_of_isSymm
      (preservedSymmetricCoordinate R).property
  unfold preservedCoordinateRegularizedRankOneOnS
    preservedSymmetricRegularizedRankOneOnS extendSymmetricPreservedRule
  rw [hcval]

theorem eq_matrix_valued_preserved_score_symmetricDomain
    {k m : ℕ} {c : SymmetricComplexMatrix m → Fin m → ℂ}
    (hc : Measurable c) {δ : ℝ} (hδ : 0 < δ)
    (hgap : 2 * m + 1 < k) :
    (let μ := halfGaussianMatrixSum k (Fin m)
     let a := inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m)
     (∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        a * Matrix.trace ((realWishartGram R)⁻¹ *
          scoreDeltaM (preservedSymmetricRegularizedRankOneOnS δ c
            (preservedSymmetricCoordinate R))) ∂μ) =
      ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        Matrix.trace
          (scoreDeltaM (preservedSymmetricRegularizedRankOneOnS δ c
            (preservedSymmetricCoordinate R))) ∂μ) := by
  simpa only [preservedRegularizedRankOne_extendSymmetricRule] using
    (eq_matrix_valued_preserved_score
      (measurable_extendSymmetricPreservedRule hc) hδ hgap)

def preservedSymmetricCoordinateXi {k m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  quadraticFormReal
    (Matrix.toBlocks₁₁
      (coupledGramKernel (complexOfRealMatrix R))⁻¹)
    (preservedSymmetricCoordinateVector c R)

@[simp] theorem preservedCoordinateXi_extendSymmetricRule
    {k m : ℕ} (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateXi (extendSymmetricPreservedRule c) R =
      preservedSymmetricCoordinateXi c R := by
  rw [preservedCoordinateXi, preservedSymmetricCoordinateXi,
    preservedCoordinateVector_extendSymmetricRule]

theorem eq_regularized_coupled_inverse_identity_symmetricDomain
    {k m : ℕ} (hgap : 2 * m + 1 < k)
    {c : SymmetricComplexMatrix m → Fin m → ℂ}
    (hc : Measurable c) (δ : ℝ) (hδ : 0 < δ) :
    (∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        preservedSymmetricCoordinateXi c R /
          (preservedSymmetricCoordinateW c R + δ) ^ 2
        ∂halfGaussianMatrixSum k (Fin m)) =
      (((k : ℝ) - 2 * m - 1)⁻¹) *
        ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          preservedSymmetricCoordinateW c R /
            (preservedSymmetricCoordinateW c R + δ) ^ 2
          ∂halfGaussianMatrixSum k (Fin m) := by
  simpa only [preservedCoordinateXi_extendSymmetricRule,
    preservedCoordinateW_extendSymmetricRule] using
      (eq_regularized_coupled_inverse_identity hgap
        (measurable_extendSymmetricPreservedRule hc) δ hδ)

/-! ## Cofactor Schur chain and inverse-moment closure -/

theorem eq_cofactor_schur_cauchy
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hfull : Function.Injective
      (complexConjugateColumnPair (pastComplexColumnMatrix hr A)).mulVec) :
    pastCofactorW hr A ^ 2 ≤
        pastCofactorV hr A *
          quadraticFormReal
            (hermitianGram (pastComplexColumnMatrix hr A))⁻¹
            (pastHafnianCofactorVector hr A) ∧
      pastCofactorV hr A *
          quadraticFormReal
            (hermitianGram (pastComplexColumnMatrix hr A))⁻¹
            (pastHafnianCofactorVector hr A) ≤
        pastCofactorV hr A * pastCoupledInverseQuadratic hr A := by
  let B := pastComplexColumnMatrix hr A
  let c := pastHafnianCofactorVector hr A
  have hK : (coupledGramKernel B).PosDef :=
    coupledGramKernel_posDef B hfull
  have hQ : (hermitianGram B).PosDef := by
    convert hK.submatrix (e := Sum.inl) Sum.inl_injective using 1 <;>
      ext i j <;> rfl
  have hmono : quadraticFormReal (hermitianGram B)⁻¹ c ≤
      quadraticFormReal (coupledSchurComplement B)⁻¹ c :=
    quadraticFormReal_mono
      (hermitianGram_inverse_le_coupledSchur_inverse B hfull) c
  constructor
  · calc
      pastCofactorW hr A ^ 2 = vectorNormSq c ^ 2 := by
        rw [vectorNormSq_pastHafnianCofactorVector hr A]
      _ ≤ quadraticFormReal (hermitianGram B) c *
            quadraticFormReal (hermitianGram B)⁻¹ c :=
        matrix_cauchy_schwarz hQ c
      _ = pastCofactorV hr A *
            quadraticFormReal (hermitianGram B)⁻¹ c := by
        rw [quadraticFormReal_hermitianGram_past_eq_pastCofactorV hr A]
  · calc
      pastCofactorV hr A *
          quadraticFormReal (hermitianGram B)⁻¹ c ≤
        pastCofactorV hr A *
          quadraticFormReal (coupledSchurComplement B)⁻¹ c :=
        mul_le_mul_of_nonneg_left hmono (pastCofactorV_nonneg hr A)
      _ = pastCofactorV hr A * pastCoupledInverseQuadratic hr A := by
        rw [pastCoupledInverseQuadratic,
          coupledKernel_inverse_toBlocks11 B hfull]

/-- Literal unnormalized probability conclusion of `cor:raw-small-ball`. -/
theorem result_cor_raw_small_ball
    {n k : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (circularGaussianColumnMatrixMeasure n k).real
        {X | ‖gramHafnianObservable n k X - z‖ ≤ rho} ≤
      rho ^ 2 / ((k : ℝ) - 1) *
        ∏ r ∈ Finset.Icc 2 n,
          ((((2 : ℝ) * r - 2) * ((k : ℝ) - 4 * r + 1))⁻¹) := by
  let μ := circularGaussianColumnMatrixMeasure n k
  let E := {X | ‖gramHafnianObservable n k X - z‖ ≤ rho}
  have hVpos : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦
      circularGaussianVector k), 0 < pastCofactorV hn A :=
    ae_pastCofactorV_pos_paperRange hn hk
  have h8 := eq8_disk_bound hn hVpos z rho hrho
  have h11 := eq11_inverse_variance k n hn hk
  rw [pastCofactorVInverseMoment_eq hn] at h11
  have hENN : μ E ≤ ENNReal.ofReal (rho ^ 2) *
      ENNReal.ofReal (inverseVarianceBound k n) := by
    calc
      μ E ≤ ENNReal.ofReal (rho ^ 2) *
          ennInverseMoment
            (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
            (pastCofactorV hn) := h8
      _ ≤ ENNReal.ofReal (rho ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n) := by gcongr
  have htop : ENNReal.ofReal (rho ^ 2) *
      ENNReal.ofReal (inverseVarianceBound k n) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hENN
  change μ.real E ≤ _
  rw [measureReal_def]
  calc
    (μ E).toReal ≤
        (ENNReal.ofReal (rho ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n)).toReal := hreal
    _ = rho ^ 2 * inverseVarianceBound k n := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg rho),
        ENNReal.toReal_ofReal]
      exact inverseVarianceBound_nonneg_of_le hk hn le_rfl
    _ = _ := by
      unfold inverseVarianceBound inverseVarianceStep
      ring

/-- A clean aggregate for every mathematical component of
`cor:exact-local-power`; all conjuncts are imported from the Gaussian-mixture
density modules. -/
def result_cor_exact_local_power :=
  And.intro (@map_gramHafnianObservable_eq_withDensity_real)
    (And.intro (@continuous_localAnticoncentrationGramHafnianDensity)
      (And.intro (@localAnticoncentrationGramHafnianDensity_pos)
        (And.intro (@localAnticoncentrationGramHafnianDensity_eq_of_norm_eq)
          (And.intro (@localAnticoncentrationGramHafnianDensity_antitone_norm)
            (And.intro (@localAnticoncentrationGramHafnianDensitySupNorm_eq_at_zero)
              (And.intro
                (@pi_sigma_sq_mul_localAnticoncentrationGramHafnianDensitySupNorm_le)
                (@gramHafnian_normalized_shrinkingDisk_limit_density)))))))

/-! ## Radial contribution to the zero-center coefficient -/

/-- Exact radial--angular factorization and the complete lower-bound chain
used in the Article.  The ordinary inverse moment is finite under the same
`k >= 4 n` hypothesis as the main theorem. -/
theorem result_cor_radial_lower_bound
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    (closedFirstMoment k n *
        ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
          ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      cofactorRadialFactor k n *
        ((∫ u, angularEnergy (n := n) (k := k) hn u ∂angularMeasure hn) *
          ∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹
            ∂angularMeasure hn) ∧
      Real.exp ((n : ℝ) / (k : ℝ)) ≤
        Real.exp (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) ∧
      Real.exp (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) ≤
        cofactorRadialFactor k n ∧
      cofactorRadialFactor k n ≤
        ((∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
            ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) *
          ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
            ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) ∧
      cofactorRadialFactor k n ≤
        Real.exp (2 * (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ))) := by
  have hchain := literalRadialLowerBound_fullChain hn hk
  exact ⟨literalLambda_eq_radial_mul_angularMomentProduct hn hk,
    hchain.1, hchain.2.1, hchain.2.2,
    cofactorRadialFactor_le_exp_two_mul k n (by omega)⟩

/-! ## Revised exact-hypothesis density and radial endpoints -/

/-- Paper-facing bundle for the revised density corollary.  Unlike the older
paper-range bundle, every analytic conclusion is parameterized directly by
almost-sure positivity and integrability of the inverse conditional variance. -/
def result_cor_exact_local_power_of_inverse :=
  And.intro (@map_gramHafnianObservable_eq_withDensity_real_of_inverse)
    (And.intro (@continuous_localAnticoncentrationGramHafnianDensity_of_inverse)
      (And.intro (@localAnticoncentrationGramHafnianDensity_pos_of_inverse)
        (And.intro (@localAnticoncentrationGramHafnianDensity_antitone_norm_of_inverse)
          (And.intro (@gramHafnian_normalized_shrinkingDisk_limit_density_of_inverse)
            (@gramHafnian_normalized_shrinkingDisk_limit_coefficient_pos_of_inverse)))))

/-- Paper-facing bundle for the revised radial and angular lemma.  It includes
the exact inverse-integrability equivalence at `k >= 2`, its finite radial
factor, separate homogeneity, and the lower-bound chain.  Almost-sure
positivity is retained by the paper-facing reduction so that ordinary Lean
inversion represents the extended reciprocal used in the Article. -/
def result_lemma_radial_angular_factorization_of_inverse :=
  And.intro (@RadialLowerBoundAlt.paperInverseIntegrabilityReduction)
    (And.intro
      (@RadialLowerBoundAlt.integral_inv_pastCofactorV_eq_radial_inverse_mul_angular)
      (And.intro (@RadialLowerBoundAlt.pastCofactorV_splitPolarReconstruct)
        (And.intro
          (@RadialLowerBoundAlt.literalLambda_eq_radial_mul_angularMomentProduct_of_k_ge_two)
          (@RadialLowerBoundAlt.literalRadialLowerBound_fullChain_of_inverse))))

/-! ## Wick angular obstruction -/

/-- Paper-facing bundle for the exact rational Wick ratio, its unconditional
extended actual-law angular lower bound, the universal lower bound by one,
and the finite `n >= 1000`, `3 k <= n` exponential obstruction. -/
def result_thm_wick_angular_obstruction :=
  And.intro
    (@WickAngularLowerBound.wickScalarRatioQ_cast_eq_wickAngularRatio)
    (And.intro
      (@WickAngularLowerBound.wickAngularRatioENN_le_angularConditionNumberENN)
      (And.intro
        (@WickAngularLowerBound.one_le_angularConditionNumberENN)
        (And.intro
          (@WickAngularLowerBound.exp_n_div_500_le_angularConditionNumberENN)
          (@WickAngularLowerBound.exp_n_div_500_le_literalLambda_of_inverse))))

private theorem one_le_of_thousand_le_for_density {n : ℕ}
    (hn : 1000 ≤ n) : 1 ≤ n := by
  omega

/-- Density-at-zero form of the finite Wick obstruction.  The quantity with
the exponential lower bound is the dimensionless normalized density
`pi * sigma_{k,n}^2 * f_{k,n}(0)`, not the raw planar density `f_{k,n}(0)`.
The positivity and inverse-integrability hypotheses ensure that the displayed
mixture function is the density of the Gram-hafnian law. -/
theorem result_thm_wick_normalized_density_at_zero_obstruction
    {k n : ℕ} (hn : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n)
    (hVpos :
      ∀ᵐ A : CofactorIdx n (one_le_of_thousand_le_for_density hn) → (Fin k → ℂ)
        ∂(Measure.pi fun _ : CofactorIdx n (one_le_of_thousand_le_for_density hn) ↦
          circularGaussianVector k),
        0 < pastCofactorV (one_le_of_thousand_le_for_density hn) A)
    (hInv : Integrable
      (fun A : CofactorIdx n (one_le_of_thousand_le_for_density hn) → (Fin k → ℂ) ↦
        (pastCofactorV (one_le_of_thousand_le_for_density hn) A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n (one_le_of_thousand_le_for_density hn) ↦
        circularGaussianVector k)) :
    Real.exp ((n : ℝ) / 500) ≤
        Real.pi * gramHafnianSigma k n ^ 2 *
          localAnticoncentrationGramHafnianDensity (k := k)
            (one_le_of_thousand_le_for_density hn) 0 ∧
      Real.exp ((n : ℝ) / 500) /
          (Real.pi * gramHafnianSigma k n ^ 2) ≤
        localAnticoncentrationGramHafnianDensity (k := k)
          (one_le_of_thousand_le_for_density hn) 0 := by
  let hn1 : 1 ≤ n := by omega
  let ν : Measure (CofactorIdx n hn1 → (Fin k → ℂ)) :=
    Measure.pi fun _ : CofactorIdx n hn1 ↦ circularGaussianVector k
  let I : ℝ := ∫ A : CofactorIdx n hn1 → (Fin k → ℂ),
    (pastCofactorV hn1 A)⁻¹ ∂ν
  have hLambda : Real.exp ((n : ℝ) / 500) ≤ closedFirstMoment k n * I := by
    simpa only [hn1, ν, I] using
      WickAngularLowerBound.exp_n_div_500_le_literalLambda_of_inverse
        hn hklo hkhi hVpos hInv
  have hzero :
      Real.pi * localAnticoncentrationGramHafnianDensity (k := k) hn1 0 = I := by
    rw [pi_mul_localAnticoncentrationGramHafnianDensity_eq_localSharpnessCoefficient]
    dsimp [localAnticoncentrationLocalSharpnessCoefficient, I, ν]
    apply integral_congr_ae
    filter_upwards [] with A
    simp
  have hsigma : gramHafnianSigma k n ^ 2 = closedFirstMoment k n :=
    gramHafnianSigma_sq k n (by omega)
  have hnormalized : Real.exp ((n : ℝ) / 500) ≤
      Real.pi * gramHafnianSigma k n ^ 2 *
        localAnticoncentrationGramHafnianDensity (k := k) hn1 0 := by
    calc
      Real.exp ((n : ℝ) / 500) ≤ closedFirstMoment k n * I := hLambda
      _ = gramHafnianSigma k n ^ 2 *
            (Real.pi * localAnticoncentrationGramHafnianDensity (k := k) hn1 0) := by
        rw [hsigma, hzero]
      _ = Real.pi * gramHafnianSigma k n ^ 2 *
            localAnticoncentrationGramHafnianDensity (k := k) hn1 0 := by ring
  have hden : 0 < Real.pi * gramHafnianSigma k n ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_pos (gramHafnianSigma_pos k n (by omega)))
  refine ⟨hnormalized, (div_le_iff₀ hden).2 ?_⟩
  calc
    Real.exp ((n : ℝ) / 500) ≤ Real.pi * gramHafnianSigma k n ^ 2 *
        localAnticoncentrationGramHafnianDensity (k := k) hn1 0 := hnormalized
    _ = localAnticoncentrationGramHafnianDensity (k := k) hn1 0 *
        (Real.pi * gramHafnianSigma k n ^ 2) := by ring

/-- Complete fixed parameter formalization of Theorem V.4.  It contains the
exact rational identity, the unconditional extended angular obstruction,
the certified finite range, and the conditional density conclusion. -/
theorem result_thm_wick_angular_obstruction_complete
    {k n : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (WickAngularLowerBound.wickScalarRatioQ k n : ℝ) =
        WickAngularLowerBound.wickAngularRatio k n ∧
      max 1 (WickAngularLowerBound.wickAngularRatioENN k n) ≤
        WickAngularLowerBound.angularConditionNumberENN (k := k) hn ∧
      ∀ (hn1000 : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n),
        ENNReal.ofReal (Real.exp ((n : ℝ) / 500)) ≤
            WickAngularLowerBound.angularConditionNumberENN (k := k) hn ∧
          ∀
            (hVpos :
              ∀ᵐ A : CofactorIdx n
                    (one_le_of_thousand_le_for_density hn1000) → (Fin k → ℂ)
                ∂(Measure.pi fun _ : CofactorIdx n
                    (one_le_of_thousand_le_for_density hn1000) ↦
                  circularGaussianVector k),
                0 < pastCofactorV
                  (one_le_of_thousand_le_for_density hn1000) A)
            (hInv : Integrable
              (fun A : CofactorIdx n
                    (one_le_of_thousand_le_for_density hn1000) → (Fin k → ℂ) ↦
                (pastCofactorV
                  (one_le_of_thousand_le_for_density hn1000) A)⁻¹)
              (Measure.pi fun _ : CofactorIdx n
                  (one_le_of_thousand_le_for_density hn1000) ↦
                circularGaussianVector k)),
            Real.exp ((n : ℝ) / 500) ≤
                Real.pi * gramHafnianSigma k n ^ 2 *
                  localAnticoncentrationGramHafnianDensity (k := k)
                    (one_le_of_thousand_le_for_density hn1000) 0 ∧
              Real.exp ((n : ℝ) / 500) /
                  (Real.pi * gramHafnianSigma k n ^ 2) ≤
                localAnticoncentrationGramHafnianDensity (k := k)
                  (one_le_of_thousand_le_for_density hn1000) 0 := by
  refine ⟨WickAngularLowerBound.wickScalarRatioQ_cast_eq_wickAngularRatio
      k n hk, ?_, ?_⟩
  · exact max_le
      (WickAngularLowerBound.one_le_angularConditionNumberENN hn hk)
      (WickAngularLowerBound.wickAngularRatioENN_le_angularConditionNumberENN
        hn hk)
  · intro hn1000 hklo hkhi
    refine ⟨?_, ?_⟩
    · simpa using
        (WickAngularLowerBound.exp_n_div_500_le_angularConditionNumberENN
          hn1000 hklo hkhi)
    · intro hVpos hInv
      exact result_thm_wick_normalized_density_at_zero_obstruction
        hn1000 hklo hkhi hVpos hInv

/-! ## Wishart cutoff appendix endpoints -/

theorem eq_lifted_field_identities
    {k m : Type*} [Fintype k] [Fintype m]
    [DecidableEq k] [DecidableEq m]
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hD : D.IsSymm) (hM : IsUnit (realWishartGram R).det) :
    (steinVectorFieldValue R D).transpose * R +
          R.transpose * steinVectorFieldValue R D = D ∧
      rectangularCoordinateTrace (steinVectorFieldLinearization R D) =
        (((Fintype.card k : ℝ) - (Fintype.card m : ℝ) - 1) / 2) *
          Matrix.trace ((realWishartGram R)⁻¹ * D) ∧
      2 * realFrobeniusInner R (steinVectorFieldValue R D) =
        Matrix.trace D := by
  exact ⟨gram_firstVariation_steinVectorFieldValue R hD hM,
    rectangularCoordinateTrace_steinVectorFieldLinearization R D hM,
    two_mul_frobenius_steinVectorFieldValue R D hM⟩

private theorem scoreDeltaM_one_fin (m : ℕ) :
    scoreDeltaM (1 : Matrix (Fin m) (Fin m) ℂ) =
      (1 / 2 : ℝ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [scoreDeltaM, realBlockMatrix, scoreDeltaU, scoreDeltaV, scoreDeltaC,
      recoverU, recoverV, recoverC, Matrix.one_apply, Matrix.smul_apply] <;>
    split_ifs <;> simp_all

theorem eq_real_wishart_inverse_trace
    {k m : ℕ} (hgap : 2 * m + 1 < k) :
    (∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        Matrix.trace (realWishartGram R)⁻¹
        ∂halfGaussianMatrixSum k (Fin m)) =
      4 * (m : ℝ) / ((k : ℝ) - 2 * (m : ℝ) - 1) := by
  have hdata := bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
    (k := k) (I := Fin m)
    (fun _ : Matrix (Fin m) (Fin m) ℂ ↦ (1 : ℝ)) measurable_const 1
    (by intro S; norm_num)
    (H := (1 : Matrix (Fin m) (Fin m) ℂ)) Matrix.isHermitian_one
    (by simpa [two_mul] using hgap)
  have heq := hdata.2.2
  rw [scoreDeltaM_one_fin m] at heq
  simp only [preservedSWeight, one_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_one, smul_eq_mul] at heq
  have hden : (0 : ℝ) < (k : ℝ) - 2 * (m : ℝ) - 1 := by
    have hkR : ((2 * m + 1 : ℕ) : ℝ) < (k : ℝ) := by
      exact_mod_cast hgap
    push_cast at hkR
    linarith
  have ha : inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) =
      ((k : ℝ) - 2 * (m : ℝ) - 1) / 2 := by
    simp [inverseGramScoreCoefficient]
    ring
  rw [ha] at heq
  have htraceOne : Matrix.trace
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) = 2 * (m : ℝ) := by
    simp [Matrix.trace]
    ring
  have hcoeff : inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) ≠ 0 := by
    rw [ha]
    positivity
  have hsolved := integral_inverseGram_trace_eq_of_score_identity
    (halfGaussianMatrixSum k (Fin m))
    (fun _ : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦ (1 : ℝ))
    (scoreDeltaM (1 : Matrix (Fin m) (Fin m) ℂ)) hcoeff hdata.2.2
  rw [scoreDeltaM_one_fin m] at hsolved
  simp only [one_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    smul_eq_mul, htraceOne] at hsolved
  rw [integral_const_mul] at hsolved
  rw [ha] at hsolved
  have hprob : IsProbabilityMeasure (halfGaussianMatrixSum k (Fin m)) :=
    inferInstance
  simp only [integral_const, measureReal_def, IsProbabilityMeasure.measure_univ,
    ENNReal.toReal_one, one_smul] at hsolved
  calc
    (∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
        Matrix.trace (realWishartGram R)⁻¹
        ∂halfGaussianMatrixSum k (Fin m)) =
        2 * (1 / 2 * ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          Matrix.trace (realWishartGram R)⁻¹
          ∂halfGaussianMatrixSum k (Fin m)) := by ring
    _ = 2 * ((((k : ℝ) - 2 * (m : ℝ) - 1) / 2)⁻¹ *
          (1 / 2 * (2 * (m : ℝ)))) := by rw [hsolved]
    _ = 2 * (((k : ℝ) - 2 * (m : ℝ) - 1) / 2)⁻¹ * (m : ℝ) := by ring
    _ = 4 * (m : ℝ) / ((k : ℝ) - 2 * (m : ℝ) - 1) := by
      field_simp [hden.ne']
      <;> ring

def fixedHermitianScoreDifference {k : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (H : Matrix I I ℂ)
    (R : Matrix (Fin k) (I ⊕ I) ℝ) : ℝ :=
  inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
      Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H) -
    Matrix.trace (scoreDeltaM H)

def scoreSignedMeasureSymmetric {k m : ℕ}
    (H : Matrix (Fin m) (Fin m) ℂ) :
    SignedMeasure (SymmetricComplexMatrix m) :=
  VectorMeasure.map
    ((halfGaussianMatrixSum k (Fin m)).withDensityᵥ
      (fixedHermitianScoreDifference (k := k) H))
    preservedSymmetricCoordinate

theorem eq_score_signed_measure_symmetricDomain
    {k m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (hgap : 2 * m + 1 < k)
    (E : Set (SymmetricComplexMatrix m)) (hE : MeasurableSet E) :
    scoreSignedMeasureSymmetric (k := k) H E =
      ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ in
          preservedSymmetricCoordinate ⁻¹' E,
        fixedHermitianScoreDifference (k := k) H R
        ∂halfGaussianMatrixSum k (Fin m) := by
  have hcard : Fintype.card (Fin m ⊕ Fin m) + 1 < k := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hdata :=
    bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
      (fun _ : Matrix (Fin m) (Fin m) ℂ ↦ (1 : ℝ)) measurable_const 1
      (by intro S; norm_num) hH hcard
  have hleft : Integrable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
      (halfGaussianMatrixSum k (Fin m)) := by
    simpa [preservedSWeight] using hdata.1
  have hright : Integrable
      (fun _R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        Matrix.trace (scoreDeltaM H))
      (halfGaussianMatrixSum k (Fin m)) := by
    simpa [preservedSWeight] using hdata.2.1
  have hdiff : Integrable (fixedHermitianScoreDifference (k := k) H)
      (halfGaussianMatrixSum k (Fin m)) := by
    unfold fixedHermitianScoreDifference
    change Integrable
      ((fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
            Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)) -
        (fun _R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          Matrix.trace (scoreDeltaM H)))
        (halfGaussianMatrixSum k (Fin m))
    exact hleft.sub hright
  rw [scoreSignedMeasureSymmetric,
    VectorMeasure.map_apply _ measurable_preservedSymmetricCoordinate hE,
    withDensityᵥ_apply hdiff
      (hE.preimage measurable_preservedSymmetricCoordinate)]

theorem result_lem_wishart_boundary_regularity
    {k m : ℕ}
    (psi : SymmetricComplexMatrix m → ℝ)
    (hpsi : Continuous psi) (hpsiMeas : Measurable psi)
    (hpsiSupport : HasCompactSupport psi)
    {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian)
    (hgap : 2 * m + 1 < k) :
    Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          psi (preservedSymmetricCoordinate R) *
            (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H)))
        (halfGaussianMatrixSum k (Fin m)) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          psi (preservedSymmetricCoordinate R) * Matrix.trace (scoreDeltaM H))
        (halfGaussianMatrixSum k (Fin m)) ∧
      ((∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          psi (preservedSymmetricCoordinate R) *
            (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
              Matrix.trace ((realWishartGram R)⁻¹ * scoreDeltaM H))
          ∂halfGaussianMatrixSum k (Fin m)) =
        Matrix.trace (scoreDeltaM H) *
          ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
            psi (preservedSymmetricCoordinate R)
            ∂halfGaussianMatrixSum k (Fin m)) := by
  obtain ⟨C, hC⟩ :=
    hpsi.bounded_above_of_compact_support hpsiSupport
  exact result_prop_bounded_preserved_S_score psi
    hpsiMeas C (by simpa [Real.norm_eq_abs] using hC)
    hH hgap

/-! ## Literal Fourier convention -/

/-- The characteristic function in the paper's convention
`E exp(i Re(z^* C_r))`.  The lower-level Fourier API takes the coefficient
of `C_r` directly, hence the literal adapter `w_i = conj(z_i)` appears here. -/
def paperOddCofactorCharacteristic
    {r k : ℕ} (hr : 1 ≤ r) : (Fin (2 * r - 1) → ℂ) → ℂ :=
  fun z ↦ oddCofactorRawCharacteristic (k := k) hr (fun i ↦ star (z i))

/-- Named definitional endpoint for `eq:phi-definition`, including the
literal coefficient change `w = conj z`. -/
theorem eq_phi_definition
    {r k : ℕ} (hr : 1 ≤ r) (z : Fin (2 * r - 1) → ℂ) :
    paperOddCofactorCharacteristic (k := k) hr z =
      oddCofactorRawCharacteristic (k := k) hr (fun i ↦ star (z i)) :=
  rfl

/-! ## Affine transpose-Gram fiber -/

/-- The literal fiber used in the paper: the positive-definite real Gram
cone intersected with an affine level set of the preserved transpose-Gram
coordinate. -/
def transposeGramFiber {m : ℕ}
    (s : Matrix (Fin m) (Fin m) ℂ) :
    Set (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :=
  {M | M.PosDef ∧ sCoordinateOfRealGram M = s}

/-- The exact algebraic kernel statement used in place of introducing an
irrelevant manifold tangent-space library.  A symmetric block direction
preserves the linear transpose-Gram coordinate iff it is `scoreDeltaM H` for
a Hermitian direction `H`. -/
theorem eq_fiber_kernel_algebraic
    {m : Type*} [Fintype m]
    {U C V : Matrix m m ℝ}
    (hU : U.IsSymm) (hV : V.IsSymm) :
    sOfRealBlocks U C V = 0 ↔
      ∃ H : Matrix m m ℂ,
        H.IsHermitian ∧
        scoreDeltaU H = U ∧
        scoreDeltaC H = C ∧
        scoreDeltaV H = V := by
  constructor
  · intro hS
    let H : Matrix m m ℂ := qOfRealBlocks U C V
    have hH : H.IsHermitian := qOfRealBlocks_isHermitian hU hV
    refine ⟨H, hH, ?_, ?_, ?_⟩
    · simpa [H, scoreDeltaU, hS] using
        (recoverU_qsOfRealBlocks U C V)
    · simpa [H, scoreDeltaC, hS] using
        (recoverC_qsOfRealBlocks U C V)
    · simpa [H, scoreDeltaV, hS] using
        (recoverV_qsOfRealBlocks U C V)
  · rintro ⟨H, hH, hHU, hHC, hHV⟩
    rw [← hHU, ← hHC, ← hHV]
    exact sOf_scoreDelta hH

/-- Literal block formula for the Hermitian direction used in the affine
fiber proposition. -/
theorem scoreDeltaM_eq_half_real_im_blocks
    {m : Type*} [Fintype m] [DecidableEq m]
    (H : Matrix m m ℂ) (hH : H.IsHermitian) :
    scoreDeltaM H =
      (2 : ℝ)⁻¹ • Matrix.fromBlocks (H.map Complex.re) (H.map Complex.im)
        (-(H.map Complex.im)) (H.map Complex.re) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [scoreDeltaM, realBlockMatrix, scoreDeltaU, recoverU]
    ring
  · simp [scoreDeltaM, realBlockMatrix, scoreDeltaC, recoverC]
    ring
  · have hij := hH.apply i j
    have him := congrArg Complex.im hij
    simp [scoreDeltaM, realBlockMatrix, scoreDeltaC, recoverC] at him ⊢
    linarith
  · have hij := hH.apply i j
    have hre := congrArg Complex.re hij
    simp [scoreDeltaM, realBlockMatrix, scoreDeltaV, recoverV] at hre ⊢
    linarith

/-- One exact endpoint for every assertion of the revised affine-kernel
proposition: the block direction, the two coordinate derivatives, its trace,
and the complete kernel characterization. -/
theorem result_prop_transpose_gram_fiber_affine_kernel
    {m : Type*} [Fintype m] [DecidableEq m]
    (H : Matrix m m ℂ) (hH : H.IsHermitian) :
    scoreDeltaM H =
        (2 : ℝ)⁻¹ • Matrix.fromBlocks (H.map Complex.re) (H.map Complex.im)
          (-(H.map Complex.im)) (H.map Complex.re) ∧
      sOfRealBlocks (scoreDeltaU H) (scoreDeltaC H) (scoreDeltaV H) = 0 ∧
      qOfRealBlocks (scoreDeltaU H) (scoreDeltaC H) (scoreDeltaV H) = H ∧
      ((Matrix.trace (scoreDeltaM H) : ℝ) : ℂ) = Matrix.trace H ∧
      ∀ (U C V : Matrix m m ℝ), U.IsSymm → V.IsSymm →
        (sOfRealBlocks U C V = 0 ↔
          ∃ J : Matrix m m ℂ,
            J.IsHermitian ∧ scoreDeltaU J = U ∧
              scoreDeltaC J = C ∧ scoreDeltaV J = V) := by
  refine ⟨scoreDeltaM_eq_half_real_im_blocks H hH,
    sOf_scoreDelta hH, qOf_scoreDelta hH, scoreDeltaM_trace hH, ?_⟩
  intro U C V hU hV
  exact eq_fiber_kernel_algebraic hU hV

/-! ## Literal scalar rank-one traces -/

/-- The rank-one direction `c c^*/(W+δ)^2`, before making `c` depend on the
preserved coordinate. -/
def regularizedRankOneDirection {m : Type*} [Fintype m]
    (δ : ℝ) (c : m → ℂ) : Matrix m m ℂ :=
  (vectorNormSq c + δ)⁻¹ ^ 2 • hermitianRankOne c

/-- Exact scalar wrapper for `eq:rank-one-score-trace` and
`eq:rank-one-direction-trace`. -/
theorem trace_scoreDeltaM_regularizedRankOneDirection
    {m : Type*} [Fintype m] [DecidableEq m]
    (δ : ℝ) (c : m → ℂ) :
    Matrix.trace (scoreDeltaM (regularizedRankOneDirection δ c)) =
      vectorNormSq c / (vectorNormSq c + δ) ^ 2 := by
  simp only [regularizedRankOneDirection, scoreDeltaM_real_smul,
    Matrix.trace_smul, trace_scoreDeltaM_hermitianRankOne_eq_vectorNormSq,
    smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

/-- Exact scalar wrapper for `eq:rank-one-inverse-score-trace` and
`eq:rank-one-real-complex-score`. -/
theorem realPairGram_inverse_regularizedRankOne_score_trace_eq_coupledSchur
    {k m : Type*} [Fintype k] [Fintype m]
    [DecidableEq k] [DecidableEq m]
    (X Y : Matrix k m ℝ) (c : m → ℂ) (δ : ℝ)
    (hM : IsUnit (realPairGram X Y).det)
    (hfull : Function.Injective
      (complexConjugateColumnPair (complexOfRealPair X Y)).mulVec) :
    Matrix.trace
        ((realPairGram X Y)⁻¹ *
          scoreDeltaM (regularizedRankOneDirection δ c)) =
      2 * quadraticFormReal
          (coupledSchurComplement (complexOfRealPair X Y))⁻¹ c /
        (vectorNormSq c + δ) ^ 2 := by
  simp only [regularizedRankOneDirection, scoreDeltaM_real_smul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [realPairGram_inverse_rankOne_score_trace_eq_coupledSchur
    X Y c hM hfull]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-! ## Cutoff Gaussian integration by parts -/

/-- Exact field-independent engine used at `eq:cutoff-gaussian-ibp` after
vectorizing the real matrix and taking the scalar components of the cutoff
field.  The hypotheses are the coordinate slice derivative and integrability
conditions needed for the displayed identity. -/
def eq_cutoff_gaussian_ibp := @integral_halfGaussianPi_divergence

end

end LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.PaperEndpoints
