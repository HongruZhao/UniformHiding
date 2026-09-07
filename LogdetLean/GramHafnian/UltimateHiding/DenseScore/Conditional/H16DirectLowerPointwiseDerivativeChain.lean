import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectLowerPointwiseDerivative
import Mathlib.Tactic

/-!
# The complete lower pointwise H16 derivative chain

The determinant exponent is at least `7 / 2`, so the ambient real-power
density is globally `C^3`.  Its jets through order three vanish when the
determinant gap is zero.  Consequently the literal zero extensions have the
expected time derivative at moving-support frontier points, as well as in the
support interior and outside its closure.

This closes the pointwise portions of the direct `0 -> 1`, `1 -> 2`, and
`2 -> 3` slots without a boundary-nullity or Gauss--Green hypothesis.
-/

open Filter Set Asymptotics
open scoped ContDiff Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem h16CenteredGap_time_contDiff_lower_chain
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    ContDiff ℝ ∞ (fun u : ℝ ↦
      h16CenteredTransportGapDeterminant v u x) := by
  have heq : (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) =
      fun u : ℝ ↦ h16AmbientTransportGap N ((v.1, x), u) := by
    funext u
    exact h16CenteredTransportGap_eq_ambient hN v u x
  rw [heq]
  exact (contDiff_h16AmbientTransportGap N).comp
    (contDiff_const.prodMk contDiff_id)

/-- The Faà di Bruno formula for an ambient lower jet remains valid at every
gap value, including zero, because the real power is globally `C^r` for
`r ≤ 3`. -/
theorem h16CenteredTransportInteriorJet_eq_formula_through_three
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 3)
    (p : H16CenteredJointParameter N) :
    iteratedDeriv r
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity
          N K p.1.1 u p.2) p.1.2 =
      h16CenteredInteriorJetFormula N K r p := by
  have hrR : (r : ℝ) ≤ coeCornerDensityExponent N K := by
    have : (r : ℝ) ≤ 3 := by exact_mod_cast hr
    linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  have houter : ContDiffAt ℝ r
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K)
      (h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2) :=
    Real.contDiffAt_rpow_const_of_le hrR
  have hinner : ContDiffAt ℝ r
      (fun u : ℝ ↦ h16CenteredTransportGapDeterminant p.1.1 u p.2)
      p.1.2 :=
    (h16CenteredGap_time_contDiff_lower_chain hN p.1.1 p.2).contDiffAt.of_le
      (mod_cast le_top)
  unfold h16CenteredTransportInteriorDensity
    h16CenteredInteriorJetFormula
  rw [iteratedDeriv_const_mul_field]
  change (h16COECoordinateRawMass N K)⁻¹.toReal *
      iteratedDeriv r
        ((fun z : ℝ ↦ z ^ coeCornerDensityExponent N K) ∘
          fun u : ℝ ↦ h16CenteredTransportGapDeterminant p.1.1 u p.2)
        p.1.2 = _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition houter hinner le_rfl]
  congr 1

private theorem h16CenteredTransportInteriorJet_hasDerivAt_lower
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r < 3) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ iteratedDeriv r
        (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) u)
      (iteratedDeriv (r + 1)
        (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t) t := by
  have hrR : ((r + 1 : ℕ) : ℝ) ≤
      coeCornerDensityExponent N K := by
    have : (r + 1 : ℕ) ≤ 3 := by omega
    have : ((r + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast this
    linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  have houter : ContDiff ℝ (r + 1)
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K) :=
    Real.contDiff_rpow_const_of_le hrR
  have hinner : ContDiff ℝ (r + 1)
      (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) :=
    (h16CenteredGap_time_contDiff_lower_chain hN v x).of_le
      (mod_cast le_top)
  have hdensity : ContDiff ℝ (r + 1)
      (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x) := by
    unfold h16CenteredTransportInteriorDensity
    exact contDiff_const.mul (houter.comp hinner)
  have hd : HasDerivAt
      (iteratedDeriv r
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x))
      (deriv (iteratedDeriv r
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x)) t) t :=
    (hdensity.differentiable_iteratedDeriv' r).differentiableAt.hasDerivAt
  simpa only [iteratedDeriv_succ] using hd

/-- At a moving-support frontier point, every lower literal jet has its
successor literal jet as time derivative. -/
theorem h16CenteredTransportJet_lower_hasDerivAt_on_jointFrontier
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 3) {p : H16CenteredJointParameter N}
    (hp : p ∈ frontier (h16CenteredJointSupport N)) :
    HasDerivAt
      (fun u : ℝ ↦ h16CenteredTransportJet N K
        r.castSucc.castSucc p.1.1 u p.2)
      (h16CenteredTransportJet N K r.succ.castSucc
        p.1.1 p.1.2 p.2) p.1.2 := by
  let raw : ℝ → ℝ := fun u ↦ iteratedDeriv (r : ℕ)
    (fun s : ℝ ↦ h16CenteredTransportInteriorDensity
      N K p.1.1 s p.2) u
  let rawNext : ℝ := iteratedDeriv ((r : ℕ) + 1)
    (fun s : ℝ ↦ h16CenteredTransportInteriorDensity
      N K p.1.1 s p.2) p.1.2
  let F : ℝ → ℝ := fun u ↦ h16CenteredTransportJet N K
    r.castSucc.castSucc p.1.1 u p.2
  have hpnot : p ∉ h16CenteredJointSupport N := by
    intro hpmem
    exact Set.disjoint_left.1
      (disjoint_frontier_iff_isOpen.mpr (isOpen_h16CenteredJointSupport hN))
      hp hpmem
  have hsupportNot :
      p.2 ∉ h16CenteredTransportSupport p.1.1 p.1.2 := by
    simpa [h16CenteredJointSupport] using hpnot
  have hgapzero :
      h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2 = 0 :=
    h16CenteredTransportGap_zero_on_joint_frontier hN hp
  have hrawzero : raw p.1.2 = 0 := by
    rw [show raw p.1.2 = h16CenteredInteriorJetFormula
        N K (r : ℕ) p by
      exact h16CenteredTransportInteriorJet_eq_formula_through_three
        hN hboundary (by omega) p]
    exact h16CenteredInteriorJetFormula_zero_of_gap_zero
      hboundary (by omega) hgapzero
  have hrawNextzero : rawNext = 0 := by
    rw [show rawNext = h16CenteredInteriorJetFormula
        N K ((r : ℕ) + 1) p by
      exact h16CenteredTransportInteriorJet_eq_formula_through_three
        hN hboundary (by omega) p]
    exact h16CenteredInteriorJetFormula_zero_of_gap_zero
      hboundary (by omega) hgapzero
  have hFzero : F p.1.2 = 0 := by
    exact h16CenteredTransportJet_zero_off_support
      (K := K) r.castSucc.castSucc p.1.1 p.1.2 p.2 hsupportNot
  have hnextzero : h16CenteredTransportJet N K r.succ.castSucc
      p.1.1 p.1.2 p.2 = 0 := by
    exact h16CenteredTransportJet_zero_off_support
      (K := K) r.succ.castSucc p.1.1 p.1.2 p.2 hsupportNot
  have hraw : HasDerivAt raw rawNext p.1.2 := by
    simpa [raw, rawNext] using
      (h16CenteredTransportInteriorJet_hasDerivAt_lower
        (N := N) (K := K) hN hboundary (by omega)
        p.1.1 p.2 p.1.2)
  have hraw0 : HasDerivAt raw 0 p.1.2 :=
    hraw.congr_deriv hrawNextzero
  have hFRaw : F =O[𝓝 p.1.2] raw := by
    apply IsBigO.of_bound 1
    filter_upwards [] with u
    by_cases hu : p.2 ∈ h16CenteredTransportSupport p.1.1 u
    · simp [F, raw, h16CenteredTransportJet, hu]
    · have hzero := h16CenteredTransportJet_zero_off_support
        (N := N) (K := K) (r := r.castSucc.castSucc)
        p.1.1 u p.2 hu
      simp [F, hzero]
  have hrawLittle : raw =o[𝓝 p.1.2]
      (fun u : ℝ ↦ u - p.1.2) := by
    simpa [hrawzero] using hraw0.isLittleO
  have hFLittle : F =o[𝓝 p.1.2]
      (fun u : ℝ ↦ u - p.1.2) :=
    hFRaw.trans_isLittleO hrawLittle
  have hderivZero : HasDerivAt F 0 p.1.2 := by
    apply HasDerivAt.of_isLittleO
    simpa [hFzero] using hFLittle
  change HasDerivAt F
    (h16CenteredTransportJet N K r.succ.castSucc
      p.1.1 p.1.2 p.2) p.1.2
  exact hderivZero.congr_deriv hnextzero.symm

/-- For each of the three lower orders, the literal zero-extended jet has its
successor as time derivative at every coordinate and every time. -/
theorem h16CenteredTransportJet_lower_hasDerivAt
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 3) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ h16CenteredTransportJet N K
        r.castSucc.castSucc v u x)
      (h16CenteredTransportJet N K r.succ.castSucc v t x) t := by
  let p : H16CenteredJointParameter N := ((v, t), x)
  let S := h16CenteredJointSupport N
  have hopen : IsOpen S := isOpen_h16CenteredJointSupport hN
  have hline : Continuous (fun u : ℝ ↦
      (((v, u), x) : H16CenteredJointParameter N)) := by
    fun_prop
  by_cases hin : p ∈ S
  · have hsupport : x ∈ h16CenteredTransportSupport v t := by
      simpa [p, S, h16CenteredJointSupport] using hin
    have hev : ∀ᶠ u in 𝓝 t,
        x ∈ h16CenteredTransportSupport v u := by
      have hevent := hline.continuousAt.eventually (hopen.mem_nhds hin)
      filter_upwards [hevent] with u hu
      simpa [p, S, h16CenteredJointSupport] using hu
    let raw : ℝ → ℝ := fun u ↦ iteratedDeriv (r : ℕ)
      (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) u
    have hraw : HasDerivAt raw
        (iteratedDeriv ((r : ℕ) + 1)
          (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t) t := by
      simpa [raw] using
        (h16CenteredTransportInteriorJet_hasDerivAt_lower
          (N := N) (K := K) hN hboundary (by omega) v x t)
    have heq : (fun u : ℝ ↦ h16CenteredTransportJet N K
        r.castSucc.castSucc v u x) =ᶠ[𝓝 t] raw := by
      filter_upwards [hev] with u hu
      simp [h16CenteredTransportJet, hu, raw]
    have hnext : h16CenteredTransportJet N K r.succ.castSucc v t x =
        iteratedDeriv ((r : ℕ) + 1)
          (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t := by
      simp [h16CenteredTransportJet, hsupport]
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv hnext.symm
  · by_cases hclosure : p ∈ closure S
    · have hpfrontier : p ∈ frontier S := by
        refine ⟨hclosure, ?_⟩
        simpa [hopen.interior_eq] using hin
      simpa [p, S] using
        (h16CenteredTransportJet_lower_hasDerivAt_on_jointFrontier
          (N := N) (K := K) hN hboundary r hpfrontier)
    · have houtOpen : IsOpen ((closure S)ᶜ) := isClosed_closure.isOpen_compl
      have hpout : p ∈ (closure S)ᶜ := by simpa using hclosure
      have hevent := hline.continuousAt.eventually (houtOpen.mem_nhds hpout)
      have hev : ∀ᶠ u in 𝓝 t,
          x ∉ h16CenteredTransportSupport v u := by
        filter_upwards [hevent] with u hu
        intro hsupport
        have hmem : (((v, u), x) : H16CenteredJointParameter N) ∈ S := by
          simpa [S, h16CenteredJointSupport] using hsupport
        exact hu (subset_closure hmem)
      have heq : (fun u : ℝ ↦ h16CenteredTransportJet N K
          r.castSucc.castSucc v u x) =ᶠ[𝓝 t] (fun _ ↦ 0) := by
        filter_upwards [hev] with u hu
        exact h16CenteredTransportJet_zero_off_support
          (K := K) r.castSucc.castSucc v u x hu
      have hsupportNot : x ∉ h16CenteredTransportSupport v t := by
        simpa [p, S, h16CenteredJointSupport] using hin
      have hnext : h16CenteredTransportJet N K r.succ.castSucc v t x = 0 :=
        h16CenteredTransportJet_zero_off_support
          (K := K) r.succ.castSucc v t x hsupportNot
      exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq).congr_deriv
        hnext.symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
