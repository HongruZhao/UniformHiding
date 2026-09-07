import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COELikelihoodAlgebra
import Mathlib.Tactic

/-!
# Exact projective contractions in the COE score calculation

This file contains only commutative-algebra identities.  It separates the
novel cancellations in equations (R12)--(R14), (R25), and (R28)--(R30) of
the reverse audit from the classical probabilistic inputs used to estimate
their trace monomials.

In particular, none of the theorems below assumes a total-variation, score,
moment, or hiding estimate.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-! ## The non-`w` part of the averaged cubic score -/

/-- Coefficients obtained after putting `s = c*x-p` in the part of the third
density score that does not contain `w`.

The resulting polynomial is

`8 * (a3*s^3 + a2*s^2 + a1*s + a0)`.
-/
def cubicTraceCoefficientThree (c : ℝ) : ℝ :=
  1 - 3 / c + 2 / c ^ 2

def cubicTraceCoefficientTwo (c p : ℝ) : ℝ :=
  -3 + 3 * (1 - 2 * p) / c + 6 * p / c ^ 2

def cubicTraceCoefficientOne (c p : ℝ) : ℝ :=
  1 - 3 * p + 3 * (2 * p - p ^ 2) / c + 6 * p ^ 2 / c ^ 2

def cubicTraceCoefficientZero (c p : ℝ) : ℝ :=
  p + 3 * p ^ 2 / c + 2 * p ^ 3 / c ^ 2

/-- Exact centered-coordinate expansion of the non-`w` part of the third
rank-one density score.  This makes the four coefficient scales visible
before any projective or Wishart moment estimate is supplied. -/
theorem coeRankOneDensityScoreThree_nonW_centered_expansion
    {c p s x : ℝ} (hc : c ≠ 0) (hx : x = (s + p) / c) :
    8 * s ^ 3 - 24 * c * s * (x + x ^ 2) +
        8 * c * (x + 3 * x ^ 2 + 2 * x ^ 3) =
      8 * (cubicTraceCoefficientThree c * s ^ 3 +
        cubicTraceCoefficientTwo c p * s ^ 2 +
        cubicTraceCoefficientOne c p * s +
        cubicTraceCoefficientZero c p) := by
  subst x
  simp only [cubicTraceCoefficientThree, cubicTraceCoefficientTwo,
    cubicTraceCoefficientOne, cubicTraceCoefficientZero]
  field_simp [hc]
  ring

/-! ## The `w` cancellation and its projective contraction -/

/-- Algebraic form of the fourth- and sixth-projective-moment contraction
in (R13)--(R14).

`traceZW` abbreviates `Tr (Z(I+Z))`, and `traceZ2W` abbreviates
`Tr (Z^2(I+Z))`.  The two hypotheses are exactly the projective moment
identities; the conclusion, including the factor `48`, is derived here. -/
theorem averagedCubicW_exact_contraction
    {N c traceZ traceZW traceZ2W meanW meanXW : ℝ}
    (hN : N ≠ 0) (hNpOne : N + 1 ≠ 0) (hNpTwo : N + 2 ≠ 0)
    (hmeanW : meanW = 2 * traceZW / (N * (N + 1)))
    (hmeanXW : meanXW =
      (2 * traceZ * traceZW + 4 * traceZ2W) /
        (N * (N + 1) * (N + 2))) :
    24 * c * ((N + 2) * meanW - (c - 2) * meanXW) =
      48 * c / (N * (N + 1) * (N + 2)) *
        ((N + 2) ^ 2 * traceZW -
          (c - 2) * (traceZ * traceZW + 2 * traceZ2W)) := by
  rw [hmeanW, hmeanXW]
  field_simp [hN, hNpOne, hNpTwo]
  ring

/-! ## The exact averaged quadratic contraction -/

/-- The three scalar contractions in (R28), with `t1 = Tr Y` and
`t2 = Tr Y^2`, after using `W = I + Y/c`. -/
def quadraticProjectiveA (N t1 t2 : ℝ) : ℝ :=
  (t2 - t1 ^ 2 / N) / (N * (N + 1))

def quadraticProjectiveB (N c t1 t2 : ℝ) : ℝ :=
  ((N + t1 / c) * t1 - (t1 + t2 / c) / N) /
    (N * (N + 1))

def quadraticProjectiveC (N c t1 t2 : ℝ) : ℝ :=
  (N - 1) * (t1 + t2 / c) / (N ^ 2 * (N + 1))

/-- Exact formula (R30) for the averaged centered quadratic density.

This theorem is the cancellation that prevents a crude triangle inequality
from losing a factor of `N`.  All stochastic centering and moment estimates
come strictly after this identity. -/
theorem averagedCenteredQuadratic_exact_contraction
    {N c t1 t2 : ℝ}
    (hN : N ≠ 0) (hNpOne : N + 1 ≠ 0) (hc : c ≠ 0) :
    4 * (quadraticProjectiveA N t1 t2 -
        quadraticProjectiveB N c t1 t2 -
        quadraticProjectiveC N c t1 t2) =
      4 / (N * (N + 1)) *
        (t2 - t1 ^ 2 / N - ((N - 1) * (N + 2) / N) * t1 -
          (1 / c) * (t1 ^ 2 + ((N - 2) / N) * t2)) := by
  simp only [quadraticProjectiveA, quadraticProjectiveB,
    quadraticProjectiveC]
  field_simp [hN, hNpOne, hc]
  ring

/-! ## Centering the cubic generator -/

/-- A denominator-free version of (R25).  It records the exact binomial
cancellation before division by powers of `N` and is convenient when the
analytic layer works with rescaled generators. -/
theorem centeredProjectiveCubic_cleared
    {R : Type*} [CommRing R]
    (N scalar rankOneSecond rankOneThird centeredSecond : R)
    (hcenteredSecond : N ^ 2 * centeredSecond =
      N ^ 2 * rankOneSecond - scalar ^ 2) :
    N ^ 3 * rankOneThird - 3 * N ^ 2 * scalar * rankOneSecond +
          2 * scalar ^ 3 =
      N ^ 3 * rankOneThird - 3 * N ^ 2 * scalar * centeredSecond -
          scalar ^ 3 := by
  calc
    N ^ 3 * rankOneThird - 3 * N ^ 2 * scalar * rankOneSecond +
          2 * scalar ^ 3 =
        N ^ 3 * rankOneThird - 3 * scalar *
          (N ^ 2 * rankOneSecond - scalar ^ 2) - scalar ^ 3 := by ring
    _ = N ^ 3 * rankOneThird - 3 * scalar *
          (N ^ 2 * centeredSecond) - scalar ^ 3 := by rw [hcenteredSecond]
    _ = N ^ 3 * rankOneThird - 3 * N ^ 2 * scalar * centeredSecond -
          scalar ^ 3 := by ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
