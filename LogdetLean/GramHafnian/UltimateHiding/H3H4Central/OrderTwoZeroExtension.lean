import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.OrderTwoApiScratch

/-!
# Determinant-specific order-two zero extension

This module promotes the checked raw determinant calculus from
`OrderTwoApiScratch` to the public H3/H4 analytic contract.  The only
matrix-boundary input is the elementary fact that
`det (1 - Cᴴ C) = 0` when the L2 operator norm of `C` is one.  Mathlib's
global `ContDiff` theorem for positive real powers then supplies the two
vanishing boundary jets directly; no unrestricted Sobolev extension theorem
or order-four certificate is used.
-/

open MeasureTheory Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Public globally zero-extended transported determinant-density jet. -/
def coeCentralTransportJet (N K : ℕ) (j : Fin 3)
    (t : ℝ) (x : ComplexSymmetricCoordinates N) : ℝ :=
  coeCentralTransportJetScratch N K j t x

/-- Public order-zero transported coordinate density. -/
def coeCentralTransportedCoordinateDensity (N K : ℕ)
    (t : ℝ) (x : ComplexSymmetricCoordinates N) : ℝ :=
  coeCentralTransportJet N K 0 t x

/-- Exact analytic input consumed by the twice-dominated integral theorem. -/
structure COEOrderTwoZeroExtensionFacts
    (N K : ℕ) (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Prop where
  joint_continuous : ∀ j : Fin 3,
    Continuous (fun p : ℝ × ComplexSymmetricCoordinates N =>
      coeCentralTransportJet N K j p.1 p.2)
  derivative_chain : ∀ j : Fin 2, ∀ x t,
    HasDerivAt
      (fun u => coeCentralTransportJet N K j.castSucc u x)
      (coeCentralTransportJet N K j.succ t x) t
  local_L1_envelope : ∀ t0 : ℝ, ∃ delta : ℝ, 0 < delta ∧
    ∃ g : Fin 3 → ComplexSymmetricCoordinates N → ℝ,
      (∀ j, Integrable (g j) (complexSymmetricCoordinateVolume N)) ∧
      ∀ x j t, |t - t0| ≤ delta →
        ‖coeCentralTransportJet N K j t x‖ ≤ g j x

theorem continuous_coeCentralTransportCornerScratch (N : ℕ) :
    Continuous (coeCentralTransportCornerScratch N) := by
  unfold coeCentralTransportCornerScratch
  fun_prop

theorem continuous_coeCentralTransportCornerNormScratch (N : ℕ) :
    Continuous (fun p : ℝ × ComplexSymmetricCoordinates N =>
      ‖coeCentralTransportCornerScratch N p‖) :=
  continuous_norm.comp (continuous_coeCentralTransportCornerScratch N)

/-- The gap determinant vanishes on the L2-operator-norm boundary. -/
theorem coeCentralTransportDet_eq_zero_of_corner_norm_eq_one
    {N : ℕ} (hN : 1 ≤ N)
    (p : ℝ × ComplexSymmetricCoordinates N)
    (hnorm : ‖coeCentralTransportCornerScratch N p‖ = 1) :
    coeCentralTransportDetScratch N p = 0 := by
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
  let C : ConcreteMatrixState N := coeCentralTransportCornerScratch N p
  let a : ConcreteMatrixState N := star C * C
  have ha : 0 ≤ a := star_mul_self_nonneg C
  have hnorma : ‖a‖ = 1 := by
    have hmul : ‖a‖ = ‖C‖ * ‖C‖ := by
      simpa only [a] using CStarRing.norm_star_mul_self (x := C)
    rw [hmul]
    simpa only [C, hnorm, mul_one]
  have hspectrum : (1 : ℝ) ∈ spectrum ℝ a := by
    rw [← hnorma]
    exact CStarAlgebra.norm_mem_spectrum_of_nonneg ha
  have hnotunit : ¬IsUnit ((1 : ConcreteMatrixState N) - a) := by
    simpa using (spectrum.mem_iff.mp hspectrum)
  have hdet : Matrix.det ((1 : ConcreteMatrixState N) - a) = 0 := by
    by_contra hne
    apply hnotunit
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hne
  unfold coeCentralTransportDetScratch coeCentralTransportGapScratch
  have hdet' : Matrix.det
      ((1 : ConcreteMatrixState N) - C.conjTranspose * C) = 0 := by
    simpa only [a, Matrix.star_eq_conjTranspose] using hdet
  simpa only [C, hdet', Complex.zero_re]

/-- Every raw determinant jet through order two vanishes at the norm-one
moving boundary. -/
theorem coeCentralTransportRawJet_eq_zero_of_corner_norm_eq_one
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (j : Fin 3) (p : ℝ × ComplexSymmetricCoordinates N)
    (hnorm : ‖coeCentralTransportCornerScratch N p‖ = 1) :
    coeCentralTransportRawJetScratch N K j p = 0 := by
  have hdet :=
    coeCentralTransportDet_eq_zero_of_corner_norm_eq_one hN p hnorm
  have hthree : 3 < coeCornerDensityExponent N K := by
    simpa only [coeCornerDensityExponent] using
      coe_boundary_exponent_gt_three hboundary
  have halpha : coeCornerDensityExponent N K ≠ 0 := by
    linarith
  have halpha1 : coeCornerDensityExponent N K - 1 ≠ 0 := by
    linarith
  have halpha2 : coeCornerDensityExponent N K - 2 ≠ 0 := by
    linarith
  fin_cases j <;>
    simp [coeCentralTransportRawJetScratch,
      coeCentralTransportRawJetZeroScratch,
      coeCentralTransportRawJetOneScratch,
      coeCentralTransportRawJetTwoScratch, hdet,
      Real.zero_rpow halpha, Real.zero_rpow halpha1,
      Real.zero_rpow halpha2]

/-- Topology-aligned wrappers around the checked raw `ContDiff` facts. -/
theorem continuous_coeCentralTransportRawJetZeroScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    Continuous (coeCentralTransportRawJetZeroScratch N K) := by
  exact (contDiff_two_coeCentralTransportRawJetZeroScratch
    (N := N) (K := K) hboundary).continuous

theorem continuous_coeCentralTransportRawJetOneScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    Continuous (coeCentralTransportRawJetOneScratch N K) := by
  exact (contDiff_one_coeCentralTransportRawJetOneScratch
    (N := N) (K := K) hboundary).continuous

theorem continuous_coeCentralTransportRawJetScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) (j : Fin 3) :
    Continuous (coeCentralTransportRawJetScratch N K j) := by
  fin_cases j
  · change Continuous (coeCentralTransportRawJetZeroScratch N K)
    exact continuous_coeCentralTransportRawJetZeroScratch hboundary
  · change Continuous (coeCentralTransportRawJetOneScratch N K)
    exact continuous_coeCentralTransportRawJetOneScratch hboundary
  · change Continuous (coeCentralTransportRawJetTwoScratch N K)
    exact continuous_coeCentralTransportRawJetTwoScratch hboundary

theorem hasDerivAt_coeCentralTransportRawJetScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (j : Fin 2) (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt
      (fun u => coeCentralTransportRawJetScratch N K j.castSucc (u, x))
      (coeCentralTransportRawJetScratch N K j.succ (t, x)) t := by
  fin_cases j
  · simpa [coeCentralTransportRawJetScratch] using
      hasDerivAt_coeCentralTransportRawJetZeroScratch
        (N := N) (K := K) hboundary x t
  · simpa [coeCentralTransportRawJetScratch] using
      hasDerivAt_coeCentralTransportRawJetOneScratch
        (N := N) (K := K) hboundary x t

theorem continuousAt_ite_of_eq_orderTwo
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Prop} [DecidablePred p]
    {f g : X → Y} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hfg : f x = g x) :
    ContinuousAt (fun y => if p y then f y else g y) x := by
  rw [ContinuousAt] at hf hg ⊢
  have hg' : Tendsto g (𝓝 x) (𝓝 (f x)) := by
    simpa only [hfg] using hg
  have h := Filter.Tendsto.if' (p := p) hf hg'
  simpa only [hfg, ite_self] using h

/-- Joint continuity of all three globally zero-extended jets. -/
theorem continuous_coeCentralTransportJet_uncurry
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (j : Fin 3) :
    Continuous (fun p : ℝ × ComplexSymmetricCoordinates N =>
      coeCentralTransportJet N K j p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let raw : ℝ × ComplexSymmetricCoordinates N → ℝ :=
    coeCentralTransportRawJetScratch N K j
  let support : ℝ × ComplexSymmetricCoordinates N → Prop :=
    fun q => ‖coeCentralTransportCornerScratch N q‖ < 1
  have hraw : Continuous raw :=
    continuous_coeCentralTransportRawJetScratch hboundary j
  have hnormCont : ContinuousAt
      (fun q : ℝ × ComplexSymmetricCoordinates N =>
        ‖coeCentralTransportCornerScratch N q‖) p :=
    (continuous_coeCentralTransportCornerNormScratch N).continuousAt
  by_cases hin : support p
  · have hev : ∀ᶠ q in 𝓝 p, support q :=
      hnormCont.eventually (eventually_lt_nhds hin)
    have heq : (fun q : ℝ × ComplexSymmetricCoordinates N =>
        coeCentralTransportJet N K j q.1 q.2) =ᶠ[𝓝 p] raw := by
      filter_upwards [hev] with q hq
      simp only [coeCentralTransportJet, coeCentralTransportJetScratch,
        coeCentralTransportOpenSupportScratch, Set.mem_setOf_eq,
        support] at hq ⊢
      rw [if_pos hq]
    rw [ContinuousAt]
    rw [show coeCentralTransportJet N K j p.1 p.2 = raw p by
      simp [coeCentralTransportJet, coeCentralTransportJetScratch,
        coeCentralTransportOpenSupportScratch, raw, support, hin]]
    exact hraw.continuousAt.congr' heq.symm
  · by_cases hout : 1 < ‖coeCentralTransportCornerScratch N p‖
    · have hev : ∀ᶠ q in 𝓝 p,
          1 < ‖coeCentralTransportCornerScratch N q‖ :=
        hnormCont.eventually (eventually_gt_nhds hout)
      have heq : (fun q : ℝ × ComplexSymmetricCoordinates N =>
          coeCentralTransportJet N K j q.1 q.2) =ᶠ[𝓝 p]
          (fun _ => 0) := by
        filter_upwards [hev] with q hq
        have hnot : ¬ ‖coeCentralTransportCornerScratch N q‖ < 1 := by
          linarith
        simp [coeCentralTransportJet, coeCentralTransportJetScratch,
          coeCentralTransportOpenSupportScratch, hnot]
      rw [ContinuousAt]
      rw [show coeCentralTransportJet N K j p.1 p.2 = 0 by
        have hnot : ¬ ‖coeCentralTransportCornerScratch N p‖ < 1 := by
          linarith
        simp [coeCentralTransportJet, coeCentralTransportJetScratch,
          coeCentralTransportOpenSupportScratch, hnot]]
      exact continuousAt_const.congr' heq.symm
    · have hboundaryNorm :
          ‖coeCentralTransportCornerScratch N p‖ = 1 := by
        dsimp only [support] at hin
        linarith
      have hzero : raw p = 0 := by
        exact coeCentralTransportRawJet_eq_zero_of_corner_norm_eq_one
          hN hboundary j p hboundaryNorm
      have hpaste := continuousAt_ite_of_eq_orderTwo
        (p := support) hraw.continuousAt continuousAt_const hzero
      simpa [coeCentralTransportJet, coeCentralTransportJetScratch,
        coeCentralTransportOpenSupportScratch, raw, support] using hpaste

theorem continuous_coeCentralTransportCornerNorm_time
    (N : ℕ) (x : ComplexSymmetricCoordinates N) :
    Continuous (fun t : ℝ => ‖coeCentralTransportCornerScratch N (t, x)‖) := by
  exact (continuous_coeCentralTransportCornerNormScratch N).comp
    (continuous_id.prodMk continuous_const)

/-- The two global derivative links, including the moving boundary. -/
theorem hasDerivAt_coeCentralTransportJet
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (j : Fin 2) (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt
      (fun u => coeCentralTransportJet N K j.castSucc u x)
      (coeCentralTransportJet N K j.succ t x) t := by
  let raw : ℝ → ℝ := fun u =>
    coeCentralTransportRawJetScratch N K j.castSucc (u, x)
  let rawNext : ℝ → ℝ := fun u =>
    coeCentralTransportRawJetScratch N K j.succ (u, x)
  let support : ℝ → Prop := fun u =>
    ‖coeCentralTransportCornerScratch N (u, x)‖ < 1
  have hraw : HasDerivAt raw (rawNext t) t := by
    simpa only [raw, rawNext] using
      hasDerivAt_coeCentralTransportRawJetScratch hboundary j x t
  have hnormCont : ContinuousAt
      (fun u : ℝ => ‖coeCentralTransportCornerScratch N (u, x)‖) t :=
    (continuous_coeCentralTransportCornerNorm_time N x).continuousAt
  by_cases hin : support t
  · have hev : ∀ᶠ u in 𝓝 t, support u :=
      hnormCont.eventually (eventually_lt_nhds hin)
    have heq : (fun u => coeCentralTransportJet N K j.castSucc u x)
        =ᶠ[𝓝 t] raw := by
      filter_upwards [hev] with u hu
      simp only [coeCentralTransportJet, coeCentralTransportJetScratch,
        coeCentralTransportOpenSupportScratch, Set.mem_setOf_eq,
        support] at hu ⊢
      rw [if_pos hu]
    have hnext : coeCentralTransportJet N K j.succ t x = rawNext t := by
      simp [coeCentralTransportJet, coeCentralTransportJetScratch,
        coeCentralTransportOpenSupportScratch, rawNext, support, hin]
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv hnext.symm
  · by_cases hout : 1 < ‖coeCentralTransportCornerScratch N (t, x)‖
    · have hev : ∀ᶠ u in 𝓝 t,
          1 < ‖coeCentralTransportCornerScratch N (u, x)‖ :=
        hnormCont.eventually (eventually_gt_nhds hout)
      have heq : (fun u => coeCentralTransportJet N K j.castSucc u x)
          =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [hev] with u hu
        have hnot : ¬ support u := by
          dsimp only [support]
          linarith
        simp [coeCentralTransportJet, coeCentralTransportJetScratch,
          coeCentralTransportOpenSupportScratch, support, hnot]
      have hnext : coeCentralTransportJet N K j.succ t x = 0 := by
        have hnot : ¬ support t := by
          dsimp only [support]
          linarith
        simp [coeCentralTransportJet, coeCentralTransportJetScratch,
          coeCentralTransportOpenSupportScratch, support, hnot]
      exact ((hasDerivAt_const t 0).congr_of_eventuallyEq heq).congr_deriv
        hnext.symm
    · have hboundaryNorm :
          ‖coeCentralTransportCornerScratch N (t, x)‖ = 1 := by
        dsimp only [support] at hin
        linarith
      have hzero : raw t = 0 := by
        exact coeCentralTransportRawJet_eq_zero_of_corner_norm_eq_one
          hN hboundary j.castSucc (t, x) hboundaryNorm
      have hnextzero : rawNext t = 0 := by
        exact coeCentralTransportRawJet_eq_zero_of_corner_norm_eq_one
          hN hboundary j.succ (t, x) hboundaryNorm
      have hpaste := hasDerivAt_ite_of_eq_scratch
        (p := support) (hraw.congr_deriv hnextzero)
          (hasDerivAt_const t 0) hzero
      have hnot : ¬ support t := by
        dsimp only [support]
        linarith
      have htarget : coeCentralTransportJet N K j.succ t x = 0 := by
        simp [coeCentralTransportJet, coeCentralTransportJetScratch,
          coeCentralTransportOpenSupportScratch, support, hnot]
      rw [htarget]
      change HasDerivAt (fun u => if support u then raw u else 0) 0 t
      exact hpaste

/-- A transported support point lies in the fixed coordinate ball dictated
by its time. -/
theorem coeCentralTransport_support_coordinateNorm_lt
    {N : ℕ} {t : ℝ} {x : ComplexSymmetricCoordinates N}
    (hx : x ∈ coeCentralTransportOpenSupportScratch N t) :
    ‖x‖ < Real.exp (2 * t) := by
  letI : NormedAddCommGroup (ConcreteMatrixState N) :=
    Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℂ (ConcreteMatrixState N) :=
    Matrix.instL2OpNormedSpace
  have hsupport : ‖coeCentralTransportCornerScratch N (t, x)‖ < 1 := hx
  let M := complexSymmetricMatrixOfCoordinates x
  have hnormMap : ‖CStarMatrix.ofMatrix M‖ = ‖M‖ := by
    exact StarAlgEquiv.norm_map
      (CStarMatrix.ofMatrixStarAlgEquiv
        (n := Fin N) (A := ℂ)) M
  have hxM : ‖x‖ ≤ ‖M‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    rintro ⟨⟨i, j⟩, hij⟩
    calc
      ‖x ⟨(i, j), hij⟩‖ ≤ ‖CStarMatrix.ofMatrix M‖ := by
        simpa only [M, CStarMatrix.ofMatrix_apply,
          complexSymmetricMatrixOfCoordinates, dif_pos hij] using
          (CStarMatrix.norm_entry_le_norm
            (M := CStarMatrix.ofMatrix M) (i := i) (j := j))
      _ = ‖M‖ := hnormMap
  have hnormscalar :
      ‖(((Real.exp (-2 * t) : ℝ) : ℂ))‖ = Real.exp (-2 * t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hscale : ‖coeCentralTransportCornerScratch N (t, x)‖ =
      Real.exp (-2 * t) * ‖M‖ := by
    unfold coeCentralTransportCornerScratch
    rw [norm_smul, hnormscalar]
  have hexp : 0 < Real.exp (-2 * t) := Real.exp_pos _
  have hM : ‖M‖ < 1 / Real.exp (-2 * t) := by
    rw [lt_div_iff₀ hexp]
    rw [mul_comm, ← hscale]
    exact hsupport
  have hrecip : 1 / Real.exp (-2 * t) = Real.exp (2 * t) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hrecip] at hM
  exact hxM.trans_lt hM

/-- Compact-time fixed-ball `L¹` envelopes for all three jets. -/
theorem coeCentralTransportJet_local_L1_envelope
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (t0 : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ g : Fin 3 → ComplexSymmetricCoordinates N → ℝ,
        (∀ j, Integrable (g j) (complexSymmetricCoordinateVolume N)) ∧
        ∀ x j t, |t - t0| ≤ delta →
          ‖coeCentralTransportJet N K j t x‖ ≤ g j x := by
  letI : (complexSymmetricCoordinateVolume N).IsAddHaarMeasure :=
    complexSymmetricCoordinateVolume_isAddHaarMeasure N
  let delta : ℝ := 1
  let R : ℝ := Real.exp (2 * (t0 + delta))
  let B : Set (ComplexSymmetricCoordinates N) := Metric.closedBall 0 R
  let T : Set ℝ := Set.Icc (t0 - delta) (t0 + delta)
  let S : Set (ℝ × ComplexSymmetricCoordinates N) := T ×ˢ B
  have hS : IsCompact S := by
    exact isCompact_Icc.prod (ProperSpace.isCompact_closedBall 0 R)
  have hbound : ∀ j : Fin 3, ∃ M : ℝ, ∀ p ∈ S,
      ‖coeCentralTransportJet N K j p.1 p.2‖ ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := hS.bddAbove_image
      (continuous_coeCentralTransportJet_uncurry hN hboundary j).norm.continuousOn
    exact ⟨M, fun p hp => hM (Set.mem_image_of_mem _ hp)⟩
  choose M hM using hbound
  let g : Fin 3 → ComplexSymmetricCoordinates N → ℝ := fun j =>
    B.indicator (fun _ => max (M j) 0)
  have hgint : ∀ j, Integrable (g j)
      (complexSymmetricCoordinateVolume N) := by
    intro j
    exact (MeasureTheory.integrableOn_const
      (MeasureTheory.measure_closedBall_lt_top.ne)).integrable_indicator
        measurableSet_closedBall
  refine ⟨delta, by norm_num [delta], g, hgint, ?_⟩
  intro x j t ht
  have htT : t ∈ T := by
    rw [show T = Set.Icc (t0 - delta) (t0 + delta) by rfl]
    rw [abs_le] at ht
    constructor <;> linarith
  by_cases hxB : x ∈ B
  · have hcompactBound := hM j (t, x) ⟨htT, hxB⟩
    calc
      ‖coeCentralTransportJet N K j t x‖ ≤ M j := hcompactBound
      _ ≤ max (M j) 0 := le_max_left _ _
      _ = g j x := by simp [g, Set.indicator_of_mem hxB]
  · have hnotSupport : x ∉ coeCentralTransportOpenSupportScratch N t := by
      intro hsupp
      apply hxB
      have hxnorm := coeCentralTransport_support_coordinateNorm_lt hsupp
      have htupper : t ≤ t0 + delta := htT.2
      have hexp : Real.exp (2 * t) ≤ R := by
        dsimp only [R]
        exact Real.exp_le_exp.mpr (by linarith)
      change dist x 0 ≤ R
      simpa [dist_eq_norm] using (le_trans hxnorm.le hexp)
    have hjet : coeCentralTransportJet N K j t x = 0 := by
      simp [coeCentralTransportJet, coeCentralTransportJetScratch,
        hnotSupport]
    simp [hjet, g, hxB]

/-- The determinant-specific order-two zero-extension theorem required by
H3/H4.  It has no H5 or event hypothesis. -/
theorem coeCentralTransport_orderTwo_zeroExtension
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    COEOrderTwoZeroExtensionFacts N K hN hboundary where
  joint_continuous :=
    continuous_coeCentralTransportJet_uncurry hN hboundary
  derivative_chain :=
    hasDerivAt_coeCentralTransportJet hN hboundary
  local_L1_envelope :=
    coeCentralTransportJet_local_L1_envelope hN hboundary

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
