import LogdetLean.GramHafnian.UltimateHiding.DenseScore.QuadraticCenteringFromMass
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COELikelihoodAlgebra
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Literal centered COE likelihood

This module defines the interior likelihood for the actual traceless
congruence direction `Q_v=P_v-I/N` directly from the determinant density.
It does not combine rank-one and scalar log scores term by term; doing so
would omit cocycle/mixed-state derivatives.

As a mandatory sanity check, the direction, likelihood, and every positive
order density/log derivative vanish when `N=1`, because then `Q_v=0`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- The determinant before applying the inverse centered congruence. -/
def concreteCOEBaseDeterminant {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  let C := unscaleCOECorner K A
  (Matrix.det (1 - C.conjTranspose * C)).re

/-- The determinant at the inverse image of the centered congruence. -/
def concreteCOECenteredInverseDeterminant {N : ℕ} (K : ℕ)
    (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) : ℝ :=
  let C := unscaleCOECorner K A
  let Ct := transposeCongruenceFlow
    (concreteCenteredOrbitalDirection N v) (-t) C
  (Matrix.det (1 - Ct.conjTranspose * Ct)).re

/-- Literal interior likelihood core for the centered direction.  Since
`Tr Q_v=0`, its symmetric-coordinate Jacobian is one.  At the algebraically
degenerate points where the base determinant vanishes we set the total
function to one; the determinant-density law is supported on the open matrix
ball and all analytic uses are on that support. -/
def concreteCenteredLikelihoodCore {N : ℕ} (K : ℕ)
    (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) : ℝ := by
  classical
  exact if concreteCOEBaseDeterminant K A = 0 then 1 else
      Real.rpow
        (concreteCOECenteredInverseDeterminant K v t A /
          concreteCOEBaseDeterminant K A)
        (coeCornerDensityExponent N K)

/-- Literal `r`th centered density score. -/
def concreteCenteredDensityScore (r N K : ℕ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℝ :=
  iteratedDeriv r (fun t ↦ concreteCenteredLikelihoodCore K v t A) 0

/-- Literal `r`th centered logarithmic score. -/
def concreteCenteredLogScore (r N K : ℕ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℝ :=
  iteratedDeriv r
    (fun t ↦ Real.log (concreteCenteredLikelihoodCore K v t A)) 0

/-- In complex dimension one every unit-vector rank-one projection is the
identity matrix. -/
theorem complexRankOneProjection_fin_one_eq_one
    (v : ComplexUnitSphere 1) : complexRankOneProjection v = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  have hvnorm : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 1 ↦ ℂ) v.1
  rw [hvnorm] at hsq
  norm_num at hsq
  have hv0sq : ‖v.1 0‖ ^ 2 = 1 := by simpa using hsq.symm
  have hnormSq : Complex.normSq (v.1 0) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hv0sq]
  calc
    complexRankOneProjection v 0 0 = v.1 0 * star (v.1 0) := rfl
    _ = star (v.1 0) * v.1 0 := mul_comm _ _
    _ = (Complex.normSq (v.1 0) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    _ = 1 := by rw [hnormSq]; norm_num

/-- Hence the centered direction is exactly zero for `N=1`. -/
theorem concreteCenteredOrbitalDirection_fin_one_eq_zero
    (v : ComplexUnitSphere 1) :
    concreteCenteredOrbitalDirection 1 v = 0 := by
  rw [concreteCenteredOrbitalDirection,
    complexRankOneProjection_fin_one_eq_one]
  norm_num

/-- The inverse centered congruence leaves every matrix unchanged when
`N=1`. -/
theorem transposeCongruenceFlow_centered_fin_one
    (v : ComplexUnitSphere 1) (t : ℝ) (A : ConcreteMatrixState 1) :
    transposeCongruenceFlow (concreteCenteredOrbitalDirection 1 v) t A = A := by
  rw [concreteCenteredOrbitalDirection_fin_one_eq_zero]
  simp [transposeCongruenceFlow]

/-- The determinant likelihood core is identically one in dimension one. -/
theorem concreteCenteredLikelihoodCore_fin_one_eq_one
    (K : ℕ) (v : ComplexUnitSphere 1) (t : ℝ)
    (A : ConcreteMatrixState 1) :
    concreteCenteredLikelihoodCore K v t A = 1 := by
  unfold concreteCenteredLikelihoodCore
  split_ifs with hdet
  · rfl
  · have hdetRe : concreteCOEBaseDeterminant K A ≠ 0 := hdet
    have heq : concreteCOECenteredInverseDeterminant K v t A =
        concreteCOEBaseDeterminant K A := by
      simp only [concreteCOECenteredInverseDeterminant,
        concreteCOEBaseDeterminant]
      rw [transposeCongruenceFlow_centered_fin_one]
    rw [heq, div_self hdetRe]
    exact Real.one_rpow _

/-- Mandatory N=1 check: every positive-order centered density score is
zero. -/
theorem concreteCenteredDensityScore_fin_one_eq_zero
    {r K : ℕ} (hr : 1 ≤ r) (v : ComplexUnitSphere 1)
    (A : ConcreteMatrixState 1) :
    concreteCenteredDensityScore r 1 K v A = 0 := by
  have hfun : (fun t ↦ concreteCenteredLikelihoodCore K v t A) =
      fun _ : ℝ ↦ 1 := by
    funext t
    exact concreteCenteredLikelihoodCore_fin_one_eq_one K v t A
  rw [concreteCenteredDensityScore, hfun]
  rw [iteratedDeriv_const, if_neg (Nat.ne_of_gt hr)]

/-- Mandatory N=1 check: every positive-order centered logarithmic score is
zero. -/
theorem concreteCenteredLogScore_fin_one_eq_zero
    {r K : ℕ} (hr : 1 ≤ r) (v : ComplexUnitSphere 1)
    (A : ConcreteMatrixState 1) :
    concreteCenteredLogScore r 1 K v A = 0 := by
  have hfun : (fun t ↦ Real.log (concreteCenteredLikelihoodCore K v t A)) =
      fun _ : ℝ ↦ 0 := by
    funext t
    rw [concreteCenteredLikelihoodCore_fin_one_eq_one]
    simp
  rw [concreteCenteredLogScore, hfun]
  rw [iteratedDeriv_const, if_neg (Nat.ne_of_gt hr)]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
