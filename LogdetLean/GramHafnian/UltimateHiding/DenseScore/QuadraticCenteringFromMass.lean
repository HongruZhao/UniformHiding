import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.Tactic

/-!
# Quadratic COE centering from total mass

This file isolates the normalization argument that must not be hidden in a
Wishart-moment input.  A pushforward of the probability COE law has total
mass one, so every positive-order derivative of its `univ` event path
vanishes.  Combining the order-two instance with the raw Friedman--Mello
boundary-calculus interface proves that the integral of the literal second
likelihood derivative is zero.

The remaining exact, pointwise projective contraction which identifies the
centered-direction second density with the `(R30)` trace bracket is kept as
an internal algebraic obligation; no centering, score-norm, total-variation,
or hiding statement is introduced as an external atom here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-! ## The actual centered orbital path -/

/-- Event path for the traceless direction `Q_v = vvᴴ-I/N`, acting on the
scaled COE corner by transpose congruence. -/
def concreteCenteredRankOneCOEEventPath {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (t : ℝ) : ℝ :=
  (Measure.map
      (transposeCongruenceFlow (concreteCenteredOrbitalDirection N v) t)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)).real event

/-- The centered orbital pushforward also has unit total mass. -/
theorem concreteCenteredRankOneCOEEventPath_univ_eq_one
    {N K : ℕ} (hNK : N ≤ K) (v : ComplexUnitSphere N) (t : ℝ) :
    concreteCenteredRankOneCOEEventPath K v Set.univ t = 1 := by
  letI : IsProbabilityMeasure
      (scaledHaarTransposeGramLaw
        canonicalUnitaryHaarProbabilityFamily K N K) :=
    scaledHaarTransposeGramLaw_isProbability _ hNK le_rfl
  letI : IsProbabilityMeasure
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) :=
    Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  have hflow : Measurable
      (transposeCongruenceFlow (concreteCenteredOrbitalDirection N v) t) := by
    unfold transposeCongruenceFlow
    exact measurable_transposeCongruence _
  unfold concreteCenteredRankOneCOEEventPath
  rw [map_measureReal_apply hflow MeasurableSet.univ]
  simp

/-- The order-two derivative of the centered total-mass path vanishes. -/
theorem concreteCenteredRankOneCOEEventPath_univ_iteratedDeriv_two_eq_zero
    {N K : ℕ} (hNK : N ≤ K) (v : ComplexUnitSphere N) :
    iteratedDeriv 2
        (concreteCenteredRankOneCOEEventPath K v Set.univ) 0 = 0 := by
  have hfun : concreteCenteredRankOneCOEEventPath K v Set.univ =
      fun _ : ℝ ↦ 1 := by
    funext t
    exact concreteCenteredRankOneCOEEventPath_univ_eq_one hNK v t
  rw [hfun]
  simpa using
    (iteratedDeriv_const (n := 2) (c := (1 : ℝ)) (x := (0 : ℝ)))

/-- Average the centered orbital event path over the same uniform complex
projective direction used in `(R28)--(R30)`. -/
def concreteProjectiveAveragedCenteredCOEEventPath
    (N K : ℕ) (event : Set (ConcreteMatrixState N)) (t : ℝ) : ℝ :=
  ∫ v : ComplexUnitSphere N,
    concreteCenteredRankOneCOEEventPath K v event t
      ∂(complexUnitSphereProbabilityMeasure N)

/-- The projectively averaged centered path still has unit total mass. -/
theorem concreteProjectiveAveragedCenteredCOEEventPath_univ_eq_one
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) (t : ℝ) :
    concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ t = 1 := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold concreteProjectiveAveragedCenteredCOEEventPath
  simp_rw [concreteCenteredRankOneCOEEventPath_univ_eq_one hNK]
  simp

/-- Hence the averaged total-mass path has zero second derivative. -/
theorem
    concreteProjectiveAveragedCenteredCOEEventPath_univ_iteratedDeriv_two_eq_zero
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ) 0 = 0 := by
  have hfun : concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ =
      fun _ : ℝ ↦ 1 := by
    funext t
    exact concreteProjectiveAveragedCenteredCOEEventPath_univ_eq_one hN hNK t
  rw [hfun]
  simpa using
    (iteratedDeriv_const (n := 2) (c := (1 : ℝ)) (x := (0 : ℝ)))

/-- Once the raw determinant-density calculus identifies the second
derivative of the centered `univ` path with the integral of the explicit
`(R30)` density, its integral is zero by probability normalization.

The equality hypothesis is deliberately displayed: it is the remaining
internal centered-flow/projective calculation and cannot be replaced by the
rank-one `P_v` identity above. -/
theorem integral_concreteCenteredQuadraticDensity_eq_zero_of_eventPath
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (hidentify :
      iteratedDeriv 2
          (concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ) 0 =
        ∫ A, concreteCenteredQuadraticDensity N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) :
    (∫ A, concreteCenteredQuadraticDensity N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
  rw [
    concreteProjectiveAveragedCenteredCOEEventPath_univ_iteratedDeriv_two_eq_zero
      hN hNK] at hidentify
  exact hidentify.symm

/-- Removing the nonzero normalization `4/[N(N+1)]` turns zero mean of the
explicit quadratic density into zero mean of the literal `(R30)` bracket. -/
theorem integral_concreteCenteredQuadraticTraceBracket_eq_zero_of_density
    {N K : ℕ} (hN : 1 ≤ N)
    (hdensity :
      (∫ A, concreteCenteredQuadraticDensity N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) = 0) :
    (∫ A, concreteCenteredQuadraticTraceBracket N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNpOne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hfactor : 4 / ((N : ℝ) * ((N : ℝ) + 1)) ≠ 0 := by
    exact div_ne_zero (by norm_num) (mul_ne_zero hNr hNpOne)
  have hmul :
      4 / ((N : ℝ) * ((N : ℝ) + 1)) *
          (∫ A, concreteCenteredQuadraticTraceBracket N K A
            ∂(concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
    rw [← integral_const_mul]
    simpa only [concreteCenteredQuadraticDensity] using hdensity
  exact (mul_eq_zero.mp hmul).resolve_left hfactor

/-- Paper-facing composition of the two preceding normalization steps. -/
theorem integral_concreteCenteredQuadraticTraceBracket_eq_zero_of_eventPath
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (hidentify :
      iteratedDeriv 2
          (concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ) 0 =
        ∫ A, concreteCenteredQuadraticDensity N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) :
    (∫ A, concreteCenteredQuadraticTraceBracket N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
  exact integral_concreteCenteredQuadraticTraceBracket_eq_zero_of_density hN
    (integral_concreteCenteredQuadraticDensity_eq_zero_of_eventPath
      hN hNK hidentify)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
