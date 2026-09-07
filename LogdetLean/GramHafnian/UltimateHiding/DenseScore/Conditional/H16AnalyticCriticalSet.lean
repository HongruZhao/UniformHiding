import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantAnalyticCurve
import Mathlib.Topology.DiscreteSubset

/-!
# Finite critical sets for the H16 determinant curve

The existing supported-real-power FTC works on intervals where the determinant
gap is monotone.  Real analyticity supplies the missing compact decomposition:
unless the derivative vanishes identically, its zero set on a compact interval
is finite.  This file proves that exact dichotomy, first abstractly and then
for the literal centered H16 determinant gap.
-/

open Filter Set
open scoped Interval

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- An everywhere real-analytic scalar function either has identically zero
derivative or only finitely many critical points on a compact interval. -/
theorem finite_critical_set_or_deriv_eq_zero_of_analytic
    {f : ℝ → ℝ} (hf : ∀ t, AnalyticAt ℝ f t) (a b : ℝ) :
    ({t : ℝ | t ∈ [[a, b]] ∧ deriv f t = 0}).Finite ∨ deriv f = 0 := by
  by_cases hzero : ∀ t, deriv f t = 0
  · right
    funext t
    exact hzero t
  · left
    push Not at hzero
    obtain ⟨t₀, ht₀⟩ := hzero
    have hderiv : AnalyticOnNhd ℝ (deriv f) Set.univ := by
      intro t _
      exact (hf t).deriv
    have hcodGlobal : (deriv f) ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
      hderiv.preimage_zero_mem_codiscrete ht₀
    have hcod : (deriv f) ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin [[a, b]] :=
      (Filter.codiscreteWithin_mono (Set.subset_univ [[a, b]])) hcodGlobal
    have hfinite := isCompact_uIcc.finite_sdiff_of_mem_codiscreteWithin hcod
    have heq : {t : ℝ | t ∈ [[a, b]] ∧ deriv f t = 0} =
        [[a, b]] \ (deriv f) ⁻¹' {0}ᶜ := by
      ext t
      simp
    rw [heq]
    exact hfinite

/-- The literal H16 determinant gap has finitely many critical points on
every compact interval unless it is constant there (indeed, globally). -/
theorem finite_h16CenteredTransportGap_critical_set_or_deriv_eq_zero
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (a b : ℝ) :
    ({t : ℝ | t ∈ [[a, b]] ∧
      deriv (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) t = 0}).Finite ∨
      deriv (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) = 0 := by
  apply finite_critical_set_or_deriv_eq_zero_of_analytic
  exact analyticAt_h16CenteredTransportGapDeterminant hN v x

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
