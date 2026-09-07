import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete
import Mathlib.Tactic

/-!
# Scaled versus unscaled COE-corner laws

`Dense.concreteScaledCOECornerLaw H N K` is the paper-normalized law of
`sqrt K * C`, whereas the Friedman--Mello determinant density and the
statistics `C (I-CᴴC)⁻¹ Cᴴ` are written for the unscaled contraction `C`.

This file makes that normalization change explicit.  It contains no density,
moment, score, total-variation, or hiding assertion.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense LocalAnticoncentration

/-- Recover the unscaled COE corner `C` from the paper-normalized state
`A = sqrt K * C`. -/
def unscaleCOECorner {N : ℕ} (K : ℕ) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  ((((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ)) • A

theorem measurable_unscaleCOECorner (N K : ℕ) :
    Measurable (unscaleCOECorner (N := N) K) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [unscaleCOECorner, Matrix.smul_apply]
  fun_prop

/-- The literal unscaled COE-corner law obtained from the already-defined
paper-normalized law.  This is the law to which the Friedman--Mello density
must be attached. -/
def concreteUnscaledCOECornerLaw
    (H : UnitaryHaarProbabilityFamily) (N K : ℕ) :
    Measure (ConcreteMatrixState N) :=
  Measure.map (unscaleCOECorner (N := N) K)
    (concreteScaledCOECornerLaw H N K)

/-- Haar uniqueness removes the presentation of normalized Haar probability
also after the explicit unscaling map. -/
theorem concreteUnscaledCOECornerLaw_eq_canonical
    (H : UnitaryHaarProbabilityFamily) (N K : ℕ) :
    concreteUnscaledCOECornerLaw H N K =
      concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K := by
  unfold concreteUnscaledCOECornerLaw
  rw [show concreteScaledCOECornerLaw H N K =
      concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K by
    exact concreteHaarAmbientLaw_eq_canonical H N K K]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
