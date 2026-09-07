import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCOELawNormalization
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredTraceAlgebra
import Mathlib.Tactic

/-!
# Concrete scalar statistics for the scaled COE corner

This file attaches the score algebra to the actual matrix state used by
`Dense.concreteScaledCOECornerLaw`.  It contains definitions only (plus
literal algebraic rewrites): no density, moment, differentiation, or hiding
claim is introduced here.

The state sampled by `concreteScaledCOECornerLaw H N K` is `A = sqrt(K) C`.
We therefore unscale **before** forming any likelihood statistic.  For the
resulting complex symmetric contraction `C`, the definitions agree with

* `Z = C (I-Cᴴ C)^{-1} Cᴴ`;
* `T = (I-C Cᴴ)^{-1} C`;
* `x_v = vᴴ Z v`;
* `B_v = vᴴ T conjugate(v)` and `w_v = |B_v|^2`;
* `Y = c Z`, where `c = K-2N-1`.

They are deliberately total functions on the ambient matrix space.  The COE
support and integrability assertions belong in the external classical-density
and fixed-Wishart-moment layer.
-/

open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open Dense

/-- The real COE density exponent parameter `c = K-2N-1`. -/
def concreteCOEExponent (N K : ℕ) : ℝ :=
  (K : ℝ) - 2 * (N : ℝ) - 1

/-- `Z = C (I-Cᴴ C)^{-1} Cᴴ`, formed from the explicitly unscaled
contraction `C=A/sqrt K`. -/
def concreteCOEZ {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) : ConcreteMatrixState N :=
  let C := unscaleCOECorner K A
  C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose

/-- `T = (I-C Cᴴ)^{-1} C`, formed from `C=A/sqrt K`. -/
def concreteCOET {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) : ConcreteMatrixState N :=
  let C := unscaleCOECorner K A
  (1 - C * C.conjTranspose)⁻¹ * C

/-- `Y = c Z`. -/
def concreteCOEY (N K : ℕ) (C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  ((concreteCOEExponent N K : ℝ) : ℂ) • concreteCOEZ K C

/-- Real trace of a complex matrix.  On the COE support all trace
polynomials used below are real; taking `re` makes the total definition
well-typed without adding a support proof. -/
def concreteRealTrace {N : ℕ} (A : ConcreteMatrixState N) : ℝ :=
  (Matrix.trace A).re

/-- `Tr Y`. -/
def concreteCOETraceOne (N K : ℕ) (C : ConcreteMatrixState N) : ℝ :=
  concreteRealTrace (concreteCOEY N K C)

/-- `Tr Y^2`. -/
def concreteCOETraceTwo (N K : ℕ) (C : ConcreteMatrixState N) : ℝ :=
  concreteRealTrace (concreteCOEY N K C * concreteCOEY N K C)

/-- `Tr Y^3`. -/
def concreteCOETraceThree (N K : ℕ) (C : ConcreteMatrixState N) : ℝ :=
  concreteRealTrace
    (concreteCOEY N K C * concreteCOEY N K C * concreteCOEY N K C)

/-- The quadratic form `x_v = vᴴ Z v`, written as `Tr(P_v Z)`. -/
def concreteCOEX {N : ℕ} (v : ComplexUnitSphere N)
    (K : ℕ) (C : ConcreteMatrixState N) : ℝ :=
  concreteRealTrace (complexRankOneProjection v * concreteCOEZ K C)

/-- The complex bilinear statistic `B_v = vᴴ T conjugate(v)`. -/
def concreteCOEB {N : ℕ} (v : ComplexUnitSphere N)
    (K : ℕ) (C : ConcreteMatrixState N) : ℂ :=
  ∑ i, ∑ j, star (v.1 i) * concreteCOET K C i j * star (v.1 j)

/-- `w_v = |B_v|^2`. -/
def concreteCOEW {N : ℕ} (v : ComplexUnitSphere N)
    (K : ℕ) (C : ConcreteMatrixState N) : ℝ :=
  Complex.normSq (concreteCOEB v K C)

/-- First rank-one logarithmic score attached to the actual COE statistics. -/
def concreteRankOneLogScoreOne (N K : ℕ) (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) : ℝ :=
  coeRankOneLogScoreOne (concreteCOEExponent N K) (N : ℝ)
    (concreteCOEX v K C)

/-- Second rank-one logarithmic score. -/
def concreteRankOneLogScoreTwo (N K : ℕ) (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) : ℝ :=
  coeRankOneLogScoreTwo (concreteCOEExponent N K)
    (concreteCOEX v K C) (concreteCOEW v K C)

/-- Third rank-one logarithmic score. -/
def concreteRankOneLogScoreThree (N K : ℕ) (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) : ℝ :=
  coeRankOneLogScoreThree (concreteCOEExponent N K)
    (concreteCOEX v K C) (concreteCOEW v K C)

/-- Fourth rank-one logarithmic score. -/
def concreteRankOneLogScoreFour (N K : ℕ) (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) : ℝ :=
  coeRankOneLogScoreFour (concreteCOEExponent N K)
    (concreteCOEX v K C) (concreteCOEW v K C)

/-- Third rank-one density score. -/
def concreteRankOneDensityScoreThree (N K : ℕ)
    (v : ComplexUnitSphere N) (C : ConcreteMatrixState N) : ℝ :=
  densityBellThree
    (concreteRankOneLogScoreOne N K v C)
    (concreteRankOneLogScoreTwo N K v C)
    (concreteRankOneLogScoreThree N K v C)

/-- Fourth rank-one density score. -/
def concreteRankOneDensityScoreFour (N K : ℕ)
    (v : ComplexUnitSphere N) (C : ConcreteMatrixState N) : ℝ :=
  densityBellFour
    (concreteRankOneLogScoreOne N K v C)
    (concreteRankOneLogScoreTwo N K v C)
    (concreteRankOneLogScoreThree N K v C)
    (concreteRankOneLogScoreFour N K v C)

/-- The exact (R30) bracket as a function on the concrete matrix state. -/
def concreteCenteredQuadraticTraceBracket (N K : ℕ)
    (C : ConcreteMatrixState N) : ℝ :=
  centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
    (concreteCOETraceOne N K C) (concreteCOETraceTwo N K C)

/-- The normalized (R30) quadratic density, before its identification with
the second derivative of the orbital event path. -/
def concreteCenteredQuadraticDensity (N K : ℕ)
    (C : ConcreteMatrixState N) : ℝ :=
  4 / ((N : ℝ) * ((N : ℝ) + 1)) *
    concreteCenteredQuadraticTraceBracket N K C

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
