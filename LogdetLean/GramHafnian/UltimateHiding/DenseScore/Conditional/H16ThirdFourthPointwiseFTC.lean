import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ThirdJetAbsoluteContinuity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectFourthPointwiseDerivative

/-!
# Pointwise `J3 -> J4` FTC for H16

The literal third jet is now known to be absolutely continuous in time.  Away
from the finite time-support frontier, it has the literal fourth jet as its
ordinary derivative: inside the support this is the smooth interior chain,
and outside the support both jets vanish locally.  Removing the finite
frontier therefore identifies the a.e. derivative of `J3` with `J4` and gives
the exact scalar interval FTC at every fixed coordinate point.
-/

open Filter MeasureTheory Set
open scoped Interval Topology ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem h16CenteredTransportInteriorJet_three_hasDerivAt_time
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (t : ℝ)
    (hgap : 0 < h16CenteredTransportGapDeterminant v t x) :
    HasDerivAt
      (fun u : ℝ ↦ iteratedDeriv 3
        (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) u)
      (iteratedDeriv 4
        (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t) t := by
  let q : ℝ → ℝ := fun u ↦
    h16CenteredTransportGapDeterminant v u x
  let f : ℝ → ℝ := fun u ↦
    h16CenteredTransportInteriorDensity N K v u x
  have hq : ContDiffAt ℝ 4 q t :=
    (contDiff_h16CenteredTransportGapDeterminant_time hN v x).contDiffAt.of_le
      (WithTop.coe_le_coe.2 (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hpow : ContDiffAt ℝ 4
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K) (q t) :=
    Real.contDiffAt_rpow_const_of_ne hgap.ne'
  have hf : ContDiffAt ℝ 4 f t := by
    unfold f h16CenteredTransportInteriorDensity
    exact contDiffAt_const.mul (hpow.comp t hq)
  have hdiff : DifferentiableAt ℝ (iteratedDeriv 3 f) t := by
    rw [← differentiableWithinAt_univ]
    rw [← iteratedDerivWithin_univ]
    exact hf.differentiableWithinAt_iteratedDerivWithin
      (by norm_num) (by simpa using
        (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)))
  have hd : HasDerivAt (iteratedDeriv 3 f)
      (deriv (iteratedDeriv 3 f) t) t := hdiff.hasDerivAt
  simpa only [f, iteratedDeriv_succ] using hd

/-- At every time outside the exact support frontier, the literal third jet
has the literal fourth jet as derivative. -/
theorem h16CenteredTransportJet_three_hasDerivAt_of_not_timeSupport_frontier
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (t : ℝ)
    (htfrontier : t ∉ frontier (h16CenteredTimeSupport v x)) :
    HasDerivAt
      (fun u : ℝ ↦ h16CenteredTransportJet N K 3 v u x)
      (h16CenteredTransportJet N K 4 v t x) t := by
  let U : Set ℝ := h16CenteredTimeSupport v x
  have hopen : IsOpen U := by
    simpa only [U] using isOpen_h16CenteredTimeSupport hN v x
  by_cases htU : t ∈ U
  · have hevent : ∀ᶠ u in 𝓝 t, u ∈ U := hopen.mem_nhds htU
    have hsupport : x ∈ h16CenteredTransportSupport v t := by
      simpa only [U, h16CenteredTimeSupport, mem_setOf_eq] using htU
    have hgap : 0 < h16CenteredTransportGapDeterminant v t x := by
      apply h16COECoordinateGapDeterminant_pos
      simpa [h16CenteredTransportSupport] using hsupport
    let raw : ℝ → ℝ := fun u ↦ iteratedDeriv 3
      (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) u
    have hraw : HasDerivAt raw
        (iteratedDeriv 4
          (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t) t := by
      simpa only [raw] using
        h16CenteredTransportInteriorJet_three_hasDerivAt_time hN v x t hgap
    have heq : (fun u : ℝ ↦ h16CenteredTransportJet N K 3 v u x)
        =ᶠ[𝓝 t] raw := by
      filter_upwards [hevent] with u hu
      have husupport : x ∈ h16CenteredTransportSupport v u := by
        simpa only [U, h16CenteredTimeSupport, mem_setOf_eq] using hu
      simp [h16CenteredTransportJet, husupport, raw]
    have hnext : h16CenteredTransportJet N K 4 v t x =
        iteratedDeriv 4
          (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t := by
      simp [h16CenteredTransportJet, hsupport]
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv hnext.symm
  · have htclosure : t ∉ closure U := by
      have htfrontierU : t ∉ frontier U := by
        simpa only [U] using htfrontier
      have htNotInterior : t ∉ interior U := by
        rw [hopen.interior_eq]
        exact htU
      intro htcl
      exact htfrontierU ⟨htcl, htNotInterior⟩
    have houtOpen : IsOpen ((closure U)ᶜ) := isClosed_closure.isOpen_compl
    have htout : t ∈ (closure U)ᶜ := by simpa using htclosure
    have hevent : ∀ᶠ u in 𝓝 t, u ∉ U := by
      filter_upwards [houtOpen.mem_nhds htout] with u hu
      exact fun huU ↦ hu (subset_closure huU)
    have heq : (fun u : ℝ ↦ h16CenteredTransportJet N K 3 v u x)
        =ᶠ[𝓝 t] (fun _u ↦ 0) := by
      filter_upwards [hevent] with u hu
      apply h16CenteredTransportJet_zero_off_support
      simpa only [U, h16CenteredTimeSupport, mem_setOf_eq] using hu
    have hnext : h16CenteredTransportJet N K 4 v t x = 0 := by
      apply h16CenteredTransportJet_zero_off_support
      simpa only [U, h16CenteredTimeSupport, mem_setOf_eq] using htU
    exact ((hasDerivAt_const (x := t) (c := (0 : ℝ))).congr_of_eventuallyEq heq).congr_deriv
      hnext.symm

/-- On a compact time interval, the a.e. derivative of the literal third jet
is the literal fourth jet. -/
theorem h16CenteredTransportJet_three_deriv_eq_four_ae_on_uIoc
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (a b : ℝ) :
    ∀ᵐ t : ℝ ∂volume,
      t ∈ Ι a b →
        deriv (fun u : ℝ ↦ h16CenteredTransportJet N K 3 v u x) t =
          h16CenteredTransportJet N K 4 v t x := by
  let B : Set ℝ := {t : ℝ | t ∈ [[a, b]] ∧
    t ∈ frontier (h16CenteredTimeSupport v x)}
  have hBfinite : B.Finite := by
    simpa only [B] using
      finite_h16CenteredTimeSupport_frontier_on_uIcc hN v x a b
  have hBzero : volume B = 0 := hBfinite.measure_zero volume
  have hae : ∀ᵐ t : ℝ ∂volume, t ∉ B := by
    rw [ae_iff]
    simpa only [not_not, setOf_mem_eq] using hBzero
  filter_upwards [hae] with t htB ht
  have htIcc : t ∈ [[a, b]] := uIoc_subset_uIcc ht
  have htfrontier : t ∉ frontier (h16CenteredTimeSupport v x) := by
    intro htfr
    exact htB ⟨htIcc, htfr⟩
  exact
    (h16CenteredTransportJet_three_hasDerivAt_of_not_timeSupport_frontier
      (N := N) (K := K) hN v x t htfrontier).deriv

/-- Exact pointwise scalar FTC: the fourth literal jet is time-integrable at
every fixed coordinate point and integrates to the third-jet increment. -/
theorem intervalIntegrable_and_integral_h16CenteredTransportJet_four_eq_three_sub
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    (a b : ℝ) :
    IntervalIntegrable
        (fun t : ℝ ↦ h16CenteredTransportJet N K 4 v t x)
        volume a b ∧
      (∫ t in a..b, h16CenteredTransportJet N K 4 v t x) =
        h16CenteredTransportJet N K 3 v b x -
          h16CenteredTransportJet N K 3 v a x := by
  let f : ℝ → ℝ := fun t ↦ h16CenteredTransportJet N K 3 v t x
  let g : ℝ → ℝ := fun t ↦ h16CenteredTransportJet N K 4 v t x
  have hAC : AbsolutelyContinuousOnInterval f a b := by
    simpa only [f] using
      absolutelyContinuousOnInterval_h16CenteredTransportJet_three
        hN hboundary v x a b
  have hae : ∀ᵐ t : ℝ ∂volume, t ∈ Ι a b → deriv f t = g t := by
    simpa only [f, g] using
      h16CenteredTransportJet_three_deriv_eq_four_ae_on_uIoc
        (N := N) (K := K) hN v x a b
  have haeRestrict : deriv f =ᵐ[volume.restrict (Ι a b)] g :=
    (ae_restrict_iff' measurableSet_uIoc).2 hae
  have hgint : IntervalIntegrable g volume a b :=
    hAC.intervalIntegrable_deriv.congr_ae haeRestrict
  refine ⟨by simpa only [g] using hgint, ?_⟩
  calc
    (∫ t in a..b, h16CenteredTransportJet N K 4 v t x) =
        ∫ t in a..b, deriv f t := by
          symm
          exact intervalIntegral.integral_congr_ae hae
    _ = f b - f a := hAC.integral_deriv_eq_sub
    _ = h16CenteredTransportJet N K 3 v b x -
          h16CenteredTransportJet N K 3 v a x := rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
