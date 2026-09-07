import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16AnalyticFiniteMonotonicityFTC
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalLowerJetContinuity

/-!
# Finite time-support frontier for the H16 centered flow

The positive-definite support along a fixed centered orbit need not be
identified with the positive set of its determinant.  For the one-dimensional
FTC this converse is unnecessary: every point where the time support changes
lies on the joint positive-definite frontier, and the determinant vanishes on
that frontier.  Since the determinant curve is real analytic, its zeros on a
compact interval are finite unless it vanishes identically.  In the latter
case the positive-definite time support is empty.

Thus the exact time support has only finitely many frontier points on every
compact interval.  This gives a foundations-only component decomposition and
avoids importing a separate matrix log-convexity theorem.
-/

open Filter Set
open scoped Interval Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The set of times at which one fixed coordinate point lies in the moving
positive-definite support. -/
def h16CenteredTimeSupport {N : ℕ}
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N) : Set ℝ :=
  {t | x ∈ h16CenteredTransportSupport v t}

theorem h16CenteredTimeSupport_eq_preimage_jointSupport
    {N : ℕ} (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTimeSupport v x =
      (fun t : ℝ ↦ (((v, t), x) : H16CenteredJointParameter N)) ⁻¹'
        h16CenteredJointSupport N := by
  ext t
  rfl

/-- The time support is open. -/
theorem isOpen_h16CenteredTimeSupport
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    IsOpen (h16CenteredTimeSupport v x) := by
  rw [h16CenteredTimeSupport_eq_preimage_jointSupport]
  exact (isOpen_h16CenteredJointSupport hN).preimage (by fun_prop)

/-- A frontier point of the one-dimensional time support maps to the frontier
of the full joint support. -/
theorem h16Centered_timeSupport_frontier_mapsTo_jointFrontier
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) {t : ℝ}
    (ht : t ∈ frontier (h16CenteredTimeSupport v x)) :
    (((v, t), x) : H16CenteredJointParameter N) ∈
      frontier (h16CenteredJointSupport N) := by
  let line : ℝ → H16CenteredJointParameter N :=
    fun u ↦ ((v, u), x)
  let T : Set ℝ := h16CenteredTimeSupport v x
  let J : Set (H16CenteredJointParameter N) := h16CenteredJointSupport N
  have hline : Continuous line := by
    fun_prop
  have hpre : T = line ⁻¹' J := by
    simpa only [T, J, line] using
      h16CenteredTimeSupport_eq_preimage_jointSupport v x
  have hopenT : IsOpen T := by
    simpa only [T] using isOpen_h16CenteredTimeSupport hN v x
  have htNot : t ∉ T := by
    intro htT
    exact Set.disjoint_left.1
      (disjoint_frontier_iff_isOpen.mpr hopenT) ht htT
  have hmaps : MapsTo line T J := by
    intro u hu
    rw [hpre] at hu
    exact hu
  have hclosure : line t ∈ closure J :=
    map_mem_closure hline ht.1 hmaps
  have hnotJ : line t ∉ J := by
    intro hJ
    apply htNot
    rw [hpre]
    exact hJ
  exact ⟨hclosure, fun hinterior ↦ hnotJ (interior_subset hinterior)⟩

/-- The determinant gap vanishes at every time-support frontier point. -/
theorem h16CenteredTransportGap_zero_on_timeSupport_frontier
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) {t : ℝ}
    (ht : t ∈ frontier (h16CenteredTimeSupport v x)) :
    h16CenteredTransportGapDeterminant v t x = 0 := by
  let p : H16CenteredJointParameter N := ((v, t), x)
  have hp : p ∈ frontier (h16CenteredJointSupport N) := by
    exact h16Centered_timeSupport_frontier_mapsTo_jointFrontier hN v x ht
  have hgap := h16CenteredTransportGap_zero_on_joint_frontier hN hp
  simpa only [p] using hgap

/-- An everywhere real-analytic scalar function either vanishes identically
or has only finitely many zeros on a compact interval. -/
theorem finite_zero_set_or_eq_zero_of_analytic
    {f : ℝ → ℝ} (hf : ∀ t, AnalyticAt ℝ f t) (a b : ℝ) :
    ({t : ℝ | t ∈ [[a, b]] ∧ f t = 0}).Finite ∨ f = 0 := by
  by_cases hzero : ∀ t, f t = 0
  · right
    funext t
    exact hzero t
  · left
    push Not at hzero
    obtain ⟨t₀, ht₀⟩ := hzero
    have hanalytic : AnalyticOnNhd ℝ f Set.univ := by
      intro t _
      exact hf t
    have hcodGlobal : f ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
      hanalytic.preimage_zero_mem_codiscrete ht₀
    have hcod : f ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin [[a, b]] :=
      (Filter.codiscreteWithin_mono (Set.subset_univ [[a, b]])) hcodGlobal
    have hfinite := isCompact_uIcc.finite_sdiff_of_mem_codiscreteWithin hcod
    have heq : {t : ℝ | t ∈ [[a, b]] ∧ f t = 0} =
        [[a, b]] \ f ⁻¹' {0}ᶜ := by
      ext t
      simp
    rw [heq]
    exact hfinite

/-- On every compact interval the exact positive-definite time support has a
finite frontier.  No converse from determinant positivity to support is used. -/
theorem finite_h16CenteredTimeSupport_frontier_on_uIcc
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (a b : ℝ) :
    ({t : ℝ | t ∈ [[a, b]] ∧
      t ∈ frontier (h16CenteredTimeSupport v x)}).Finite := by
  let q : ℝ → ℝ := fun t ↦
    h16CenteredTransportGapDeterminant v t x
  rcases finite_zero_set_or_eq_zero_of_analytic
      (analyticAt_h16CenteredTransportGapDeterminant hN v x) a b with
      hfinite | hzero
  · apply hfinite.subset
    intro t ht
    exact ⟨ht.1,
      h16CenteredTransportGap_zero_on_timeSupport_frontier hN v x ht.2⟩
  · have hempty : h16CenteredTimeSupport v x = ∅ := by
      ext t
      simp only [mem_empty_iff_false, iff_false]
      intro hsupport
      have hpos : 0 < h16CenteredTransportGapDeterminant v t x := by
        apply h16COECoordinateGapDeterminant_pos
        simpa [h16CenteredTimeSupport, h16CenteredTransportSupport] using hsupport
      have hqt : q t = 0 := congrFun hzero t
      exact (ne_of_gt hpos) hqt
    rw [hempty]
    simp

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
