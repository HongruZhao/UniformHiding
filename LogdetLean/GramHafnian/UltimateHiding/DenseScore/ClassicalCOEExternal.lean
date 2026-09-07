import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCOEStatistics
import LogdetLean.GramHafnian.UltimateHiding.RealWishartGram
import LogdetLean.GramHafnian.GramMomentFubini
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Tactic

/-!
# Shared finite-COE definitions for the source-pruned release

This release copy retains the shared finite-COE definitions and proved
algebraic lemmas used by the active A1--A4 proof.  Historical external
interfaces that do not occur in the public theorem's semantic dependency
closure are omitted physically.

* `friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_external`
  identifies the unscaled principal COE corner with its literal determinant
  density on the independent complex-symmetric coordinates.
* `coeCorner_rankOne_pushforward_external_derived` and
  `coeCorner_rankOne_eventPath_derivative_external_derived` expose
  only the exact rank-one likelihood and its raw derivatives through order
  four, including the moving-support condition.
* `coeTakagiMuirhead_traceVector_betaPrime_external` identifies every fixed
  finite vector of traces of `Z=C(I-CᴴC)⁻¹Cᴴ` with the corresponding
  real matrix beta-prime construction.
* `collinsSniady_complexProjectiveTensorMoment_external` is the general
  balanced tensor moment of one Haar-unitary column.

The rank-one Radon--Nikodym formula below is a finite-dimensional
change-of-variables consequence of the first density.  We expose it as a
separate source atom because the required symmetric-coordinate Jacobian and
boundary calculus are not presently in Mathlib.  Its likelihood is literal;
in particular it does not assume any derivative bound.

Source ledger:

* W. A. Friedman and P. A. Mello, *J. Phys. A* **18** (1985), 425--436,
  DOI 10.1088/0305-4470/18/3/018: determinant density of a square COE
  submatrix.  The exponent is `(K-2N-1)/2`.
* R. J. Muirhead, *Aspects of Multivariate Statistical Theory* (1982),
  Chapter 3, Section 3.3: matrix beta and beta-prime change of variables.
  Together with Takagi coordinates this gives the stated finite trace-vector
  law.  No theorem number is asserted here.
* B. Collins and P. Sniady, *Commun. Math. Phys.* **264** (2006), 773--795,
  DOI 10.1007/s00220-006-1554-3: the unitary Weingarten formula, specialized
  to one Haar column, gives the general balanced complex-projective tensor
  moment stated below.

Every analytic estimate downstream must be proved from these exact laws and
separately stated elementary projective/inverse-Wishart moments.
-/

open scoped ENNReal BigOperators ComplexConjugate ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.LocalAnticoncentration

/-! ## Literal determinant-density model -/

/-- Independent upper-triangular coordinates of a complex symmetric
`N × N` matrix. -/
abbrev ComplexSymmetricCoordinateIndex (N : ℕ) :=
  {ij : Fin N × Fin N // ij.1 ≤ ij.2}

/-- The finite family of independent complex-symmetric coordinates. -/
abbrev ComplexSymmetricCoordinates (N : ℕ) :=
  ComplexSymmetricCoordinateIndex N → ℂ

/-- Reconstruct the full complex symmetric matrix from its upper-triangular
coordinates. -/
def complexSymmetricMatrixOfCoordinates {N : ℕ}
    (x : ComplexSymmetricCoordinates N) : ConcreteMatrixState N :=
  fun i j ↦
    if h : i ≤ j then x ⟨(i, j), h⟩
    else x ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

theorem measurable_complexSymmetricMatrixOfCoordinates (N : ℕ) :
    Measurable (complexSymmetricMatrixOfCoordinates (N := N)) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  by_cases h : i ≤ j
  · simp only [complexSymmetricMatrixOfCoordinates, dif_pos h]
    fun_prop
  · simp only [complexSymmetricMatrixOfCoordinates, dif_neg h]
    fun_prop

theorem complexSymmetricMatrixOfCoordinates_isSymm {N : ℕ}
    (x : ComplexSymmetricCoordinates N) :
    (complexSymmetricMatrixOfCoordinates x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [complexSymmetricMatrixOfCoordinates]
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have hEq : i = j := le_antisymm hij hji
      subst j
      simp
    · simp [hij, hji]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simp [hij, hji]

/-- Flat Lebesgue measure on the independent complex-symmetric
coordinates. -/
def complexSymmetricCoordinateVolume (N : ℕ) :
    Measure (ComplexSymmetricCoordinates N) :=
  Measure.pi fun _ : ComplexSymmetricCoordinateIndex N ↦ (volume : Measure ℂ)

/-- The open matrix-ball support `I-CᴴC > 0`. -/
def coeCornerSupport {N : ℕ} (C : ConcreteMatrixState N) : Prop :=
  (1 - C.conjTranspose * C).PosDef

/-- Friedman--Mello determinant exponent `(K-2N-1)/2`. -/
def coeCornerDensityExponent (N K : ℕ) : ℝ :=
  ((K : ℝ) - 2 * (N : ℝ) - 1) / 2

/-- Literal, unnormalized determinant-density weight on the independent
complex-symmetric coordinates. -/
def coeCornerDeterminantWeight (N K : ℕ)
    (x : ComplexSymmetricCoordinates N) : ℝ≥0∞ :=
  by
    classical
    let C := complexSymmetricMatrixOfCoordinates x
    exact if coeCornerSupport C then
      ENNReal.ofReal <|
        Real.rpow (Matrix.det (1 - C.conjTranspose * C)).re
          (coeCornerDensityExponent N K)
    else 0

/-- The unnormalized determinant-density measure, pushed from the independent
upper-triangular coordinates to the full symmetric matrix space. -/
def coeCornerRawDeterminantDensityMeasure (N K : ℕ) :
    Measure (ConcreteMatrixState N) :=
  Measure.map (complexSymmetricMatrixOfCoordinates (N := N))
    ((complexSymmetricCoordinateVolume N).withDensity
      (coeCornerDeterminantWeight N K))

/-- Canonical normalization of the determinant-density measure.  The source
equality below entails that this normalization is nondegenerate in its stated
range; no integrability estimate is hidden in the definition. -/
def coeCornerDeterminantDensityProbabilityMeasure (N K : ℕ) :
    Measure (ConcreteMatrixState N) :=
  let μ := coeCornerRawDeterminantDensityMeasure N K
  (μ Set.univ)⁻¹ • μ

/-! ## Literal rank-one likelihood associated with E1 -/

/-- The determinant-lemma bracket in the exact rank-one likelihood. -/
def concreteRankOneLikelihoodBracket {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N)
    (t : ℝ) (A : ConcreteMatrixState N) : ℝ :=
  let q := Real.exp (2 * t)
  let x := concreteCOEX v K A
  let w := concreteCOEW v K A
  (1 + (q - 1) * (1 + x)) ^ 2 - (q - 1) ^ 2 * w

/-- Algebraic interior part of the exact forward likelihood ratio for the
pushforward by
`C ↦ exp(t vvᴴ) C exp(t conjugate(v)vᵀ)`.  The first factor is
`q^{-(K-N)}` and the determinant bracket has exponent
`(K-2N-1)/2`.  The support indicator is deliberately kept separate below. -/
def concreteRankOneLikelihoodCore {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N)
    (t : ℝ) (A : ConcreteMatrixState N) : ℝ :=
  let q := Real.exp (2 * t)
  Real.rpow q (-((K : ℝ) - (N : ℝ))) *
    Real.rpow (concreteRankOneLikelihoodBracket K v t A)
      (coeCornerDensityExponent N K)

@[simp]
theorem concreteRankOneLikelihoodBracket_zero {N K : ℕ}
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    concreteRankOneLikelihoodBracket K v 0 A = 1 := by
  simp [concreteRankOneLikelihoodBracket]

@[simp]
theorem concreteRankOneLikelihoodCore_zero {N K : ℕ}
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    concreteRankOneLikelihoodCore K v 0 A = 1 := by
  simp [concreteRankOneLikelihoodCore]

/-- The inverse image of a target matrix under the forward rank-one flow is
still in the unscaled COE matrix ball.  For a shrinking flow this is a proper
subset of the target ball, so the indicator cannot be omitted from the exact
Radon--Nikodym derivative. -/
def concreteRankOneInverseImageInSupport {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N)
    (t : ℝ) (A : ConcreteMatrixState N) : Prop :=
  coeCornerSupport <|
    unscaleCOECorner K <|
      transposeCongruenceFlow (complexRankOneProjection v) (-t) A

/-- Exact likelihood ratio, including the moving-support indicator. -/
def concreteRankOneLikelihoodRatio {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N)
    (t : ℝ) (A : ConcreteMatrixState N) : ℝ := by
  classical
  exact if concreteRankOneInverseImageInSupport K v t A then
    concreteRankOneLikelihoodCore K v t A
  else 0

theorem concreteRankOneLikelihoodRatio_zero_of_support {N K : ℕ}
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hA : coeCornerSupport (unscaleCOECorner K A)) :
    concreteRankOneLikelihoodRatio K v 0 A = 1 := by
  have hs : concreteRankOneInverseImageInSupport K v 0 A := by
    simpa [concreteRankOneInverseImageInSupport] using hA
  simp [concreteRankOneLikelihoodRatio, hs]

/-- Event-probability path for the literal forward rank-one congruence of the
scaled COE corner. -/
def concreteRankOneCOEEventPath {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (t : ℝ) : ℝ :=
  (Measure.map
      (transposeCongruenceFlow (complexRankOneProjection v) t)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)).real event

/-! ## Exact finite trace-vector beta-prime law -/

/-- Product law of a literal iid standard real Gaussian matrix. -/
def standardRealGaussianMatrixMeasure (rows cols : ℕ) :
    Measure (Matrix (Fin rows) (Fin cols) ℝ) :=
  Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure cols

/-- Independent real Gaussian sources producing
`A₀ ~ W_N(N+1,I)` and `B₀ ~ W_N(K-N,I)`. -/
def realBetaPrimeGaussianSourceLaw (N K : ℕ) :
    Measure
      (Matrix (Fin (N + 1)) (Fin N) ℝ ×
        Matrix (Fin (K - N)) (Fin N) ℝ) :=
  (standardRealGaussianMatrixMeasure (N + 1) N).prod
    (standardRealGaussianMatrixMeasure (K - N) N)

/-- Literal real matrix beta-prime ratio `B₀⁻¹ A₀`.  The inverse is the
total matrix inverse; the singular exceptional set has Gaussian measure
zero in the source range. -/
def realMatrixBetaPrimeOfGaussianSource {N K : ℕ}
    (p : Matrix (Fin (N + 1)) (Fin N) ℝ ×
      Matrix (Fin (K - N)) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  (realWishartGram p.2)⁻¹ * realWishartGram p.1

/-- First `r` traces of positive powers of the concrete COE statistic `Z`.
Index `j : Fin r` denotes the power `j+1`. -/
def concreteCOETracePowerVector (r N K : ℕ)
    (A : ConcreteMatrixState N) : Fin r → ℝ :=
  fun j ↦
    (Matrix.trace ((concreteCOEZ K A) ^ (j.1 + 1))).re

/-- First `r` traces of positive powers of the real beta-prime matrix. -/
def realBetaPrimeTracePowerVector (r N K : ℕ)
    (p : Matrix (Fin (N + 1)) (Fin N) ℝ ×
      Matrix (Fin (K - N)) (Fin N) ℝ) : Fin r → ℝ :=
  fun j ↦ Matrix.trace ((realMatrixBetaPrimeOfGaussianSource p) ^ (j.1 + 1))

/-! ## General complex-projective tensor moment -/

/-- Rising factorial `(N)_r = N(N+1)...(N+r-1)` in the normalization of a
uniform complex-projective tensor moment. -/
def complexProjectiveRisingFactorial (N r : ℕ) : ℝ :=
  ∏ a : Fin r, ((N + a.1 : ℕ) : ℝ)

/-- A coordinate of `E[P_v^⊗r]`, written as the balanced monomial
`E[∏_a v_{i_a} conjugate(v_{j_a})]`. -/
def complexProjectiveTensorMomentCoordinate (N r : ℕ)
    (i j : Fin r → Fin N) : ℂ :=
  ∫ v : ComplexUnitSphere N,
    ∏ a : Fin r, complexRankOneProjection v (i a) (j a)
      ∂(complexUnitSphereProbabilityMeasure N)

/-- The corresponding coordinate of the permutation symmetrizer. -/
def complexProjectiveSymmetrizerCoordinate (N r : ℕ)
    (i j : Fin r → Fin N) : ℂ :=
  (((complexProjectiveRisingFactorial N r)⁻¹ : ℝ) : ℂ) *
    ∑ π : Equiv.Perm (Fin r),
      ∏ a : Fin r, if i a = j (π a) then (1 : ℂ) else 0

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
