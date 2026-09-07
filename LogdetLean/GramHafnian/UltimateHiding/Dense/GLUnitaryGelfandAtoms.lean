import LogdetLean.GramHafnian.UltimateHiding.HaarGaussianMatrixLaws
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Definitions for the finite-measure Gelfand theorem on `GL_N(C) / U(N)`

This file defines the measurable complex general linear group and the
`U(N)`-bi-invariance predicate used in the H2 radial--orbital argument.  The
finite-dimensional Gelfand theorem is proved internally in
`GLUnitaryCongruenceAdapter` from polar decomposition and Haar uniqueness.

## Primary source

M. Roesler and M. Voit, *Dunkl theory, convolution algebras, and related
Markov processes*, Section 3.2, PDF pages 37--38:

* equation (3.2) defines the bounded `K`-bi-invariant measures by
  `delta_x * mu * delta_y = mu` for `x,y in K` and states that they form a
  Banach-star convolution algebra;
* Definition 3.1 says that `(G,K)` is a Gelfand pair precisely when this
  measure convolution algebra is commutative;
* Lemma 3.2 gives the standard involution criterion for the Gelfand property.

Source:
https://math.uni-paderborn.de/fileadmin/mathematik/AG_Harmonische_Analysis/
Publications_Roesler/roesler_voit_angers.pdf

For `G = GL_N(C)` and `K = U(N)`, take
`theta(g) = (conjTranspose g)^{-1}`.  This is a continuous involutive group
automorphism.  Singular-value decomposition shows that `g^{-1}` and
`theta(g)` belong to the same `U(N)` double coset, so Lemma 3.2 applies.

The project previously exposed the resulting commutativity statement as an
external axiom.  That assumption has been removed; this module now contains
definitions only.
-/

open MeasureTheory
open scoped MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- The complex general linear group, represented by units of the matrix
ring. -/
abbrev ComplexMatrixGL (N : ℕ) :=
  Matrix.GeneralLinearGroup (Fin N) ℂ

/-- The measurable structure on matrix units induced by the project's
coordinatewise complex-matrix measurable structure.  The slightly higher
priority makes this choice stable in modules that also import generic Pi
measurable-space instances. -/
instance (priority := 1100) complexMatrixGLMeasurableSpace (N : ℕ) :
    MeasurableSpace (ComplexMatrixGL N) :=
  MeasurableSpace.comap
    (fun g : ComplexMatrixGL N ↦
      (g : Matrix (Fin N) (Fin N) ℂ))
    (LogdetLean.GramHafnian.CurrentPRL.hidingReleaseComplexMatrixMeasurableSpace
      (Fin N) (Fin N))

/-- The canonical inclusion `U(N) -> GL_N(C)`.  Mathlib constructs the unit
from the two unitary identities, so no determinant or inverse formula is
postulated here. -/
def unitaryToComplexMatrixGL (N : ℕ) :
    Matrix.unitaryGroup (Fin N) ℂ →* ComplexMatrixGL N :=
  Unitary.toUnits

/-- A finite measure on `GL_N(C)` is `U(N)`-bi-invariant when convolution by
point masses from `U(N)` on the left and right leaves it unchanged.  This is
the literal finite-positive-measure specialization of equation (3.2) in the
source above. -/
def IsUnitaryBiInvariant (N : ℕ)
    (mu : Measure (ComplexMatrixGL N)) : Prop :=
  ∀ U V : Matrix.unitaryGroup (Fin N) ℂ,
    (Measure.dirac (unitaryToComplexMatrixGL N U) ∗ₘ mu) ∗ₘ
        Measure.dirac (unitaryToComplexMatrixGL N V) = mu

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
