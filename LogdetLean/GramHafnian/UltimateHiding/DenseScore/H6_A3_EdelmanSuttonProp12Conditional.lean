import A3.Proposition12Proof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_BetaJacobiCore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_DeterministicBetaJacobiTransforms
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# A3 Edelman--Sutton Proposition 1.2: source-faithful unordered atom and H6 adapters

The beta-Jacobi probability measure used here was defined, before this atom,
by normalizing its displayed density by its own integral in
`H6_A2Prime_ForresterEq17ConversionConditional`.  This module imports the full proved A3 theorem.  Its arguments retain the paper variables
`n`, `a`, `b`, `beta`, and `c_i`.

The real and complex Gaussian source laws and the generalized singular values
are concrete definitions.  All substitutions `n=N`, `a=1`, `b=K-2N`, and
`beta=1`, as well as every symmetric-test and power-sum transport, are separate
theorems.  No project Gaussian-source identification and no H6 endpoint is
asserted here; the full A3 law is supplied by `A3.Proposition12Proof`.
-/

open scoped BigOperators MatrixOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra
open LogdetLean.GramHafnian.LocalAnticoncentration

/-! ## Unordered consequences, kept below the source atom -/

/-- Applying a measurable permutation-invariant test to A3 is an unordered
consequence; no ordered selector or collision assumption is used. -/
theorem A3_edelmanSutton_unordered_symmetric_test
    {γ : Type} [MeasurableSpace γ]
    {n a b : ℕ} {beta : ℝ}
    (hn : 1 ≤ n) (hbeta : beta = 1 ∨ beta = 2)
    (F : (Fin n → ℝ) → γ)
    (_hF : Measurable F) (_hSym : IsA2SymmetricTest F) :
    Measure.map
        (F ∘ edelmanSuttonSquaredGSVCoordinates n a b beta)
        (edelmanSuttonGaussianPairLaw n a b beta) =
      Measure.map F
        (betaJacobiProbabilityMeasure n (a : ℝ) (b : ℝ) beta) := by
  exact (A3_edelmanSutton_proposition_1_2
    n a b beta hn hbeta).symmetric_test_law F _hF _hSym

/-- Collision membership is invariant under coordinate permutations. -/
theorem betaJacobiCollisionSet_permute_iff
    {n : ℕ} (sigma : Equiv.Perm (Fin n)) (lambda_i : Fin n → ℝ) :
    a2PermuteCoordinates sigma lambda_i ∈ betaJacobiCollisionSet n ↔
      lambda_i ∈ betaJacobiCollisionSet n := by
  constructor
  · rintro ⟨i, j, hij, heq⟩
    refine ⟨sigma i, sigma j, ?_, ?_⟩
    · exact fun h ↦ hij (sigma.injective h)
    · simpa [a2PermuteCoordinates] using heq
  · rintro ⟨i, j, hij, heq⟩
    refine ⟨sigma.symm i, sigma.symm j, ?_, ?_⟩
    · exact fun h ↦ hij (sigma.symm.injective h)
    · simpa [a2PermuteCoordinates] using heq

/-- Real-valued indicator used to recover collision probabilities from the
source-faithful symmetric-test law. -/
def betaJacobiCollisionIndicator (n : ℕ) (lambda_i : Fin n → ℝ) : ℝ :=
  (betaJacobiCollisionSet n).indicator (fun _ ↦ 1) lambda_i

theorem measurable_betaJacobiCollisionIndicator (n : ℕ) :
    Measurable (betaJacobiCollisionIndicator n) := by
  unfold betaJacobiCollisionIndicator
  apply measurable_const.indicator
  classical
  unfold betaJacobiCollisionSet
  measurability

theorem betaJacobiCollisionIndicator_symmetric (n : ℕ) :
    IsA2SymmetricTest (betaJacobiCollisionIndicator n) := by
  intro sigma lambda_i
  by_cases hcollision : lambda_i ∈ betaJacobiCollisionSet n
  · have hperm : a2PermuteCoordinates sigma lambda_i ∈
        betaJacobiCollisionSet n :=
      (betaJacobiCollisionSet_permute_iff sigma lambda_i).2 hcollision
    simp [betaJacobiCollisionIndicator, hcollision, hperm]
  · have hperm : a2PermuteCoordinates sigma lambda_i ∉
        betaJacobiCollisionSet n := by
      intro h
      exact hcollision
        ((betaJacobiCollisionSet_permute_iff sigma lambda_i).1 h)
    simp [betaJacobiCollisionIndicator, hcollision, hperm]

theorem betaJacobiCollisionIndicator_eq_one_iff
    {n : ℕ} (lambda_i : Fin n → ℝ) :
    betaJacobiCollisionIndicator n lambda_i = 1 ↔
      lambda_i ∈ betaJacobiCollisionSet n := by
  by_cases hcollision : lambda_i ∈ betaJacobiCollisionSet n
  · simp [betaJacobiCollisionIndicator, hcollision]
  · simp [betaJacobiCollisionIndicator, hcollision]

/-- Collision nullity is a proved consequence of the symmetric-test A3 law
and the internal finite-union-of-hyperplanes proof for beta-Jacobi. -/
theorem A3_edelmanSutton_squaredGSV_collision_null
    {n a b : ℕ} {beta : ℝ}
    (hn : 1 ≤ n) (hbeta : beta = 1 ∨ beta = 2) :
    Measure.map (edelmanSuttonSquaredGSVCoordinates n a b beta)
        (edelmanSuttonGaussianPairLaw n a b beta)
        (betaJacobiCollisionSet n) = 0 := by
  let coordinates := edelmanSuttonSquaredGSVCoordinates n a b beta
  let source := edelmanSuttonGaussianPairLaw n a b beta
  let target := betaJacobiProbabilityMeasure n (a : ℝ) (b : ℝ) beta
  let indicator := betaJacobiCollisionIndicator n
  have hA3 := A3_edelmanSutton_proposition_1_2
    n a b beta hn hbeta
  have hcoordinates : Measurable coordinates := hA3.measurable_squaredGSV
  have hindicator : Measurable indicator := by
    simpa [indicator] using measurable_betaJacobiCollisionIndicator n
  have hsymmetric : IsA2SymmetricTest indicator := by
    simpa [indicator] using betaJacobiCollisionIndicator_symmetric n
  have hlaw := hA3.symmetric_test_law indicator hindicator hsymmetric
  have happ := congrArg (fun μ : Measure ℝ ↦ μ ({1} : Set ℝ)) hlaw
  rw [Measure.map_apply (hindicator.comp hcoordinates)
      (MeasurableSet.singleton 1),
    Measure.map_apply hindicator (MeasurableSet.singleton 1)] at happ
  have hcollisionMeasurable : MeasurableSet (betaJacobiCollisionSet n) := by
    classical
    unfold betaJacobiCollisionSet
    measurability
  have hsourcePreimage :
      (indicator ∘ coordinates) ⁻¹' ({1} : Set ℝ) =
        coordinates ⁻¹' betaJacobiCollisionSet n := by
    ext omega
    exact betaJacobiCollisionIndicator_eq_one_iff (coordinates omega)
  have htargetPreimage :
      indicator ⁻¹' ({1} : Set ℝ) = betaJacobiCollisionSet n := by
    ext lambda_i
    exact betaJacobiCollisionIndicator_eq_one_iff lambda_i
  have heq :
      source (coordinates ⁻¹' betaJacobiCollisionSet n) =
        target (betaJacobiCollisionSet n) := by
    rw [hsourcePreimage, htargetPreimage] at happ
    simpa [source, target] using happ
  rw [Measure.map_apply hcoordinates hcollisionMeasurable, heq]
  exact betaJacobi_collision_null_proved n (a : ℝ) (b : ℝ) beta

/-! ## Explicit H6-variable substitution and transports -/

/-- Every arithmetic substitution from the literal A3 dimensions to the H6
variables is proved outside the atom. -/
theorem H6_A3_literal_parameter_substitution
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    N + (K - 2 * N) = K - N ∧
      ((1 : ℕ) : ℝ) = 1 ∧
      (((K - 2 * N : ℕ) : ℝ)) =
        (K : ℝ) - 2 * (N : ℝ) := by
  constructor
  · omega
  constructor
  · norm_num
  · rw [Nat.cast_sub h2NK]
    push_cast
    ring

/-- Measurability of the selected squared-GSV coordinates at the project
parameters.  This is a field of A3, not a full-vector distributional claim. -/
theorem H6_A3_project_squaredGSV_measurable
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measurable
      (edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1) := by
  have _hSub := H6_A3_literal_parameter_substitution h2NK
  exact (A3_edelmanSutton_proposition_1_2
    N 1 (K - 2 * N) 1 hN (Or.inl rfl)).measurable_squaredGSV

/-- Any measurable symmetric test can be transported after the explicit H6
substitution, still without identifying the project Gaussian source. -/
theorem H6_A3_project_unordered_symmetric_test
    {γ : Type} [MeasurableSpace γ]
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (F : (Fin N → ℝ) → γ)
    (hF : Measurable F) (hSym : IsA2SymmetricTest F) :
    Measure.map
        (F ∘ edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1)
        (edelmanSuttonGaussianPairLaw N 1 (K - 2 * N) 1) =
      Measure.map F
        (betaJacobiProbabilityMeasure N 1
          ((K - 2 * N : ℕ) : ℝ) 1) := by
  simpa using A3_edelmanSutton_unordered_symmetric_test
    (n := N) (a := 1) (b := K - 2 * N) (beta := (1 : ℝ))
    hN (Or.inl rfl) F hF hSym

/-- Beta-prime score followed by the first `r` spectral power sums. -/
def h6A3BetaPrimePowerSumVector (r n : ℕ)
    (lambda_i : Fin n → ℝ) : Fin r → ℝ :=
  a2SpectralPowerSumVector r n (betaPrimeForwardVector n lambda_i)

theorem measurable_h6A3BetaPrimePowerSumVector (r n : ℕ) :
    Measurable (h6A3BetaPrimePowerSumVector r n) := by
  exact (measurable_a2SpectralPowerSumVector r n).comp
    (measurable_betaPrimeForwardVector n)

theorem h6A3BetaPrimePowerSumVector_symmetric (r n : ℕ) :
    IsA2SymmetricTest (h6A3BetaPrimePowerSumVector r n) := by
  intro sigma lambda_i
  unfold h6A3BetaPrimePowerSumVector
  rw [show betaPrimeForwardVector n
      (a2PermuteCoordinates sigma lambda_i) =
        a2PermuteCoordinates sigma
          (betaPrimeForwardVector n lambda_i) by rfl]
  exact a2SpectralPowerSumVector_perm r n sigma
    (betaPrimeForwardVector n lambda_i)

/-- Checked A3 transport to the unordered beta-prime power-sum statistic.
This remains below H6 because neither project Gaussian-source bridge nor the
project symmetric-quotient/GSV bridge is asserted. -/
theorem H6_A3_project_betaPrimePowerSum_test
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map
        (h6A3BetaPrimePowerSumVector r N ∘
          edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1)
        (edelmanSuttonGaussianPairLaw N 1 (K - 2 * N) 1) =
      Measure.map (h6A3BetaPrimePowerSumVector r N)
        (betaJacobiProbabilityMeasure N 1
          ((K - 2 * N : ℕ) : ℝ) 1) := by
  exact H6_A3_project_unordered_symmetric_test hN h2NK
    (h6A3BetaPrimePowerSumVector r N)
    (measurable_h6A3BetaPrimePowerSumVector r N)
    (h6A3BetaPrimePowerSumVector_symmetric r N)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
