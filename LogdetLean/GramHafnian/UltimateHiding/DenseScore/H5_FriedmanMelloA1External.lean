import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.Tactic

/-!
# Approved Friedman--Mello A1 matrix law

This module records the approved literature atom using the paper's dimension
variables: `n` is the ambient dimension and `m` is the principal-block
dimension.  Friedman--Mello Eq. (1.2) uses `S_src = Uᵀ U`.  The Lean
representative below is `S = U Uᵀ`; it has the same Haar law because
`U ↦ Uᵀ` preserves Haar measure.  Thus Eq. (3.7) transfers to the leading
`m × m` block of this representative.  This is a law-equivalent convention
adapter, not a pointwise identification with the source matrix.

No closed gamma/pi normalizing constant occurs here.  The density is
normalized only by its own total mass.  Project substitutions (`m = N`,
`n = K`, and `s = C`) are deliberately absent from the axiom and are proved
in `H5_FriedmanMelloA1Adapter.lean`.
-/

open scoped ENNReal ComplexConjugate ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.CurrentPRL

namespace FriedmanMelloA1

/-- The paper's range `2m ≤ n` implies that the leading `m × m` block
exists. -/
theorem dimensionLe {n m : ℕ} (h2mn : 2 * m ≤ n) : m ≤ n := by
  omega

/-- The project's COE representative `S = U Uᵀ`, law-equivalent under Haar
transpose to Friedman--Mello's source convention `S_src = Uᵀ U`. -/
def S {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (U : Matrix (Fin n) (Fin n) ℂ) *
    (U : Matrix (Fin n) (Fin n) ℂ).transpose

/-- The leading principal block `s` of the project representative `S`; it
corresponds in Haar law to the source's leading block. -/
def s {n m : ℕ} (hmn : m ≤ n) (S : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  S.submatrix (Fin.castLE hmn) (Fin.castLE hmn)

/-- Literal matrix-ball support in the paper variables. -/
def support {m : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (1 - s.conjTranspose * s).PosDef

/-- Literal Friedman--Mello exponent `(n - 2m - 1)/2`. -/
def densityExponent (n m : ℕ) : ℝ :=
  ((n : ℝ) - 2 * (m : ℝ) - 1) / 2

/-- Literal unnormalized density in the independent symmetric coordinates.
The local matrix variable is named `s`, as in the source. -/
def determinantWeight (n m : ℕ)
    (x : ComplexSymmetricCoordinates m) : ℝ≥0∞ :=
  by
    classical
    let s := complexSymmetricMatrixOfCoordinates x
    exact if support s then
      ENNReal.ofReal <|
        Real.rpow (Matrix.det (1 - s.conjTranspose * s)).re
          (densityExponent n m)
    else 0

/-- The paper-variable raw determinant-density measure. -/
def rawDeterminantDensityMeasure (n m : ℕ) :
    Measure (Matrix (Fin m) (Fin m) ℂ) :=
  Measure.map (complexSymmetricMatrixOfCoordinates (N := m))
    ((complexSymmetricCoordinateVolume m).withDensity
      (determinantWeight n m))

/-- The paper-variable determinant density, normalized by its own mass.
No explicit special-function prefactor is imported. -/
def determinantDensityProbabilityMeasure (n m : ℕ) :
    Measure (Matrix (Fin m) (Fin m) ℂ) :=
  let μ := rawDeterminantDensityMeasure n m
  (μ Set.univ)⁻¹ • μ

/-- **Approved literature atom A1 (Friedman--Mello, 1985).**

If `U` is Haar unitary of size `n`, `S = U Uᵀ` is the law-equivalent project
representative described above, and `s` is its leading `m × m` block, then
`s` has the self-normalized determinant density with exponent
`(n - 2m - 1)/2`, for `1 ≤ m` and `2m ≤ n`.

The axiom retains the source dimension variables `n,m` and the local matrix
names `U,S,s`, but its `S = U Uᵀ` convention includes the disclosed Haar-law
adapter from the source's `S_src = Uᵀ U`.  It mentions neither project
variables `N,K,C` nor a closed normalizing prefactor. -/
axiom matrixLaw_external
    {n m : ℕ} (hm : 1 ≤ m) (h2mn : 2 * m ≤ n) :
    Measure.map
        (fun U : Matrix.unitaryGroup (Fin n) ℂ ↦
          let S := FriedmanMelloA1.S U
          let s := FriedmanMelloA1.s (dimensionLe h2mn) S
          s)
        (unitaryHaarProbabilityMeasure n) =
      determinantDensityProbabilityMeasure n m

end FriedmanMelloA1

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
