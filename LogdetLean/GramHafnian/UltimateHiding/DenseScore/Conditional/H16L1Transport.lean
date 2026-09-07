import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# H16: generic determinant-one transport in `L1`

This module contains the event-free functional-analytic layer needed for the
common-ambient H16 route.  It deliberately does not mention an event or a set
integral.

The pinned Mathlib supplies:

* the change-of-variables formula for an invertible linear map on finite
  products of `ℝ`;
* isometric pullback along a measure-preserving map on `L1`; and
* continuity of that pullback when the map varies continuously.

It does not supply an integer `W^{4,1}` pullback theorem.  The exact remaining
analytic input is therefore recorded below as locally uniform `L1` remainder
convergence for four successive jets.  This is the Banach-space formulation
that is valid for a zero-extended moving-boundary density; it does not assume a
single pointwise fourth-derivative dominator.
-/

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional

noncomputable section

variable {ι : Type*} [Fintype ι]

abbrev H16Euclidean (ι : Type*) := ι → ℝ

/-- Determinant-one continuous linear equivalences preserve Lebesgue measure
on every finite-dimensional real normed space. -/
theorem h16_measurePreserving_of_abs_det_one_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (e : E ≃L[ℝ] E)
    (hdet : |LinearMap.det e.toLinearMap| = 1) :
    MeasurePreserving e μ μ := by
  have hdet_ne : LinearMap.det e.toLinearMap ≠ 0 := by
    intro hzero
    simp [hzero] at hdet
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e.toLinearMap μ = μ
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet_ne]
  rw [abs_inv, hdet]
  simp

/-- A real linear equivalence with determinant of absolute value one preserves
Lebesgue measure. -/
theorem h16_measurePreserving_of_abs_det_one
    (e : H16Euclidean ι ≃L[ℝ] H16Euclidean ι)
    (hdet : |LinearMap.det e.toLinearMap| = 1) :
    MeasurePreserving e volume volume := by
  have hdet_ne : LinearMap.det e.toLinearMap ≠ 0 := by
    intro hzero
    simp [hzero] at hdet
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e.toLinearMap volume = volume
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet_ne]
  rw [abs_inv, hdet]
  simp

/-- Pull an `L1` function back by a determinant-one linear equivalence. -/
noncomputable def h16L1Pullback
    (e : H16Euclidean ι ≃L[ℝ] H16Euclidean ι)
    (hdet : |LinearMap.det e.toLinearMap| = 1)
    (f : H16Euclidean ι →₁[volume] ℝ) :
    H16Euclidean ι →₁[volume] ℝ :=
  Lp.compMeasurePreserving e (h16_measurePreserving_of_abs_det_one e hdet) f

/-- The bundled pullback has the expected representative almost everywhere. -/
theorem h16L1Pullback_coeFn_ae
    (e : H16Euclidean ι ≃L[ℝ] H16Euclidean ι)
    (hdet : |LinearMap.det e.toLinearMap| = 1)
    (f : H16Euclidean ι →₁[volume] ℝ) :
    (fun x ↦ h16L1Pullback e hdet f x) =ᵐ[volume]
      fun x ↦ f (e x) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Determinant-one pullback is an `L1` isometry. -/
theorem norm_h16L1Pullback
    (e : H16Euclidean ι ≃L[ℝ] H16Euclidean ι)
    (hdet : |LinearMap.det e.toLinearMap| = 1)
    (f : H16Euclidean ι →₁[volume] ℝ) :
    ‖h16L1Pullback e hdet f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- The common-ambient `L1` path obtained by pulling one base density back
along a determinant-one linear-equivalence path. -/
noncomputable def h16L1PullbackPath
    (e : ℝ → H16Euclidean ι ≃L[ℝ] H16Euclidean ι)
    (hdet : ∀ t, |LinearMap.det (e t).toLinearMap| = 1)
    (f : H16Euclidean ι →₁[volume] ℝ) :
    ℝ → (H16Euclidean ι →₁[volume] ℝ) :=
  fun t ↦ h16L1Pullback (e t) (hdet t) f

/-- The zero-order statement available directly in the pinned library:
continuous variation of determinant-one linear maps gives continuous
variation of their pullbacks in `L1`. -/
theorem continuousAt_h16L1PullbackPath
    (e : ℝ → H16Euclidean ι ≃L[ℝ] H16Euclidean ι)
    (hdet : ∀ t, |LinearMap.det (e t).toLinearMap| = 1)
    (f : H16Euclidean ι →₁[volume] ℝ) {t₀ : ℝ}
    (he : ContinuousAt
      (fun t ↦ (e t : C(H16Euclidean ι, H16Euclidean ι))) t₀) :
    ContinuousAt (h16L1PullbackPath e hdet f) t₀ := by
  unfold h16L1PullbackPath h16L1Pullback
  apply continuousAt_const.compMeasurePreservingLp he
  simp

/-! ## A locally uniform `L1` derivative tower

The sharp COE boundary does not admit a common pointwise fourth-derivative
dominator.  The correct replacement is a derivative tower in the Banach
space itself.  The following structure and theorem contain no probability,
event, density, or matrix-specific premise. -/

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Four successive Banach-valued derivatives, with continuity required only
for the fourth jet.  In the H16 application `B` is an ambient `L1` space, so
each derivative assertion is exactly convergence of difference quotients in
`L1`, rather than pointwise domination. -/
structure H16L1FourJetTower
    (f₀ f₁ f₂ f₃ f₄ : ℝ → B) : Prop where
  d01 : ∀ t, HasDerivAt f₀ (f₁ t) t
  d12 : ∀ t, HasDerivAt f₁ (f₂ t) t
  d23 : ∀ t, HasDerivAt f₂ (f₃ t) t
  d34 : ∀ t, HasDerivAt f₃ (f₄ t) t
  continuous_four : Continuous f₄

namespace H16L1FourJetTower

theorem contDiff_four
    {f₀ f₁ f₂ f₃ f₄ : ℝ → B}
    (T : H16L1FourJetTower f₀ f₁ f₂ f₃ f₄) :
    ContDiff ℝ 4 f₀ := by
  have hd₀ : Differentiable ℝ f₀ := fun t ↦ (T.d01 t).differentiableAt
  have hd₁ : Differentiable ℝ f₁ := fun t ↦ (T.d12 t).differentiableAt
  have hd₂ : Differentiable ℝ f₂ := fun t ↦ (T.d23 t).differentiableAt
  have hd₃ : Differentiable ℝ f₃ := fun t ↦ (T.d34 t).differentiableAt
  have heq₀ : deriv f₀ = f₁ := funext fun t ↦ (T.d01 t).deriv
  have heq₁ : deriv f₁ = f₂ := funext fun t ↦ (T.d12 t).deriv
  have heq₂ : deriv f₂ = f₃ := funext fun t ↦ (T.d23 t).deriv
  have heq₃ : deriv f₃ = f₄ := funext fun t ↦ (T.d34 t).deriv
  have hc₃ : ContDiff ℝ 1 f₃ := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hd₃, by simpa only [heq₃] using T.continuous_four⟩
  have hc₂ : ContDiff ℝ 2 f₂ := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    exact ⟨hd₂, by simp, by simpa only [heq₂] using hc₃⟩
  have hc₁ : ContDiff ℝ 3 f₁ := by
    rw [show (3 : ℕ∞ω) = 2 + 1 from rfl, contDiff_succ_iff_deriv]
    exact ⟨hd₁, by simp, by simpa only [heq₁] using hc₂⟩
  rw [show (4 : ℕ∞ω) = 3 + 1 from rfl, contDiff_succ_iff_deriv]
  exact ⟨hd₀, by simp, by simpa only [heq₀] using hc₁⟩

end H16L1FourJetTower

/-! ## Strongly continuous one-parameter groups

For determinant-one congruence, the pullbacks form an `L1`-isometric group.
It is enough to prove the four generator identities at time zero: the group
law propagates each identity to every time. -/

/-- The exact bridge supplied by the direct integration-by-parts route.  A
Bochner fundamental identity for one orbit implies its derivative at the
identity; no pointwise difference-quotient dominator is required. -/
theorem h16_hasDerivAt_orbit_of_integral_identity
    [CompleteSpace B]
    (U : ℝ → B → B) (x dx : B)
    (hzero : U 0 dx = dx)
    (hcont : Continuous (fun s ↦ U s dx))
    (hfund : ∀ h : ℝ,
      U h x - x = ∫ s in (0 : ℝ)..h, U s dx) :
    HasDerivAt (fun h ↦ U h x) dx 0 := by
  have hint : HasDerivAt
      (fun h ↦ ∫ s in (0 : ℝ)..h, U s dx) (U 0 dx) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 0)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt
  have heq : (fun h ↦ U h x) =
      fun h ↦ x + ∫ s in (0 : ℝ)..h, U s dx := by
    funext h
    calc
      U h x = (U h x - x) + x := (sub_add_cancel _ _).symm
      _ = (∫ s in (0 : ℝ)..h, U s dx) + x := by rw [hfund h]
      _ = x + ∫ s in (0 : ℝ)..h, U s dx := add_comm _ _
  rw [heq]
  simpa only [hzero] using hint.const_add x

/-- A derivative of one orbit at the identity propagates to the whole orbit
under a one-parameter group of continuous linear equivalences. -/
theorem h16_hasDerivAt_orbit_of_at_zero
    (U : ℝ → B ≃L[ℝ] B)
    (hgroup : ∀ s t x, U (s + t) x = U s (U t x))
    {x dx : B}
    (hzero : HasDerivAt (fun h ↦ U h x) dx 0) (t : ℝ) :
    HasDerivAt (fun s ↦ U s x) (U t dx) t := by
  have hsub : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hshift : HasDerivAt (fun s ↦ U (s - t) x) dx t := by
    have hzero' : HasDerivAt (fun h ↦ U h x) dx (t - t) := by
      simpa using hzero
    simpa using hzero'.comp_sub_const t t
  have hcomp : HasDerivAt (fun s ↦ U t (U (s - t) x)) (U t dx) t :=
    (U t).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hshift
  have heq : (fun s ↦ U s x) = fun s ↦ U t (U (s - t) x) := by
    funext s
    calc
      U s x = U (t + (s - t)) x := by
        congr 2
        ring
      _ = U t (U (s - t) x) := hgroup t (s - t) x
  rwa [heq]

/-- Four generator identities at the identity, plus strong continuity of the
fourth orbit, imply a globally `C^4` Banach-valued orbit. -/
theorem h16_contDiff_four_orbit
    (U : ℝ → B ≃L[ℝ] B)
    (hgroup : ∀ s t x, U (s + t) x = U s (U t x))
    (f₀ f₁ f₂ f₃ f₄ : B)
    (h01 : HasDerivAt (fun t ↦ U t f₀) f₁ 0)
    (h12 : HasDerivAt (fun t ↦ U t f₁) f₂ 0)
    (h23 : HasDerivAt (fun t ↦ U t f₂) f₃ 0)
    (h34 : HasDerivAt (fun t ↦ U t f₃) f₄ 0)
    (h4 : Continuous (fun t ↦ U t f₄)) :
    ContDiff ℝ 4 (fun t ↦ U t f₀) := by
  exact H16L1FourJetTower.contDiff_four
    { d01 := h16_hasDerivAt_orbit_of_at_zero U hgroup h01
      d12 := h16_hasDerivAt_orbit_of_at_zero U hgroup h12
      d23 := h16_hasDerivAt_orbit_of_at_zero U hgroup h23
      d34 := h16_hasDerivAt_orbit_of_at_zero U hgroup h34
      continuous_four := h4 }

/-- Direct-integration-by-parts form of the preceding theorem.  Four Bochner
fundamental identities and strong continuity of the four successor orbits
are sufficient; this is the narrow endpoint targeted on the determinant
interior exhaustion. -/
theorem h16_contDiff_four_orbit_of_integral_identities
    [CompleteSpace B]
    (U : ℝ → B ≃L[ℝ] B)
    (hgroup : ∀ s t x, U (s + t) x = U s (U t x))
    (hzero : ∀ x, U 0 x = x)
    (f₀ f₁ f₂ f₃ f₄ : B)
    (hc₁ : Continuous (fun t ↦ U t f₁))
    (hc₂ : Continuous (fun t ↦ U t f₂))
    (hc₃ : Continuous (fun t ↦ U t f₃))
    (hc₄ : Continuous (fun t ↦ U t f₄))
    (hfund₀₁ : ∀ h : ℝ,
      U h f₀ - f₀ = ∫ s in (0 : ℝ)..h, U s f₁)
    (hfund₁₂ : ∀ h : ℝ,
      U h f₁ - f₁ = ∫ s in (0 : ℝ)..h, U s f₂)
    (hfund₂₃ : ∀ h : ℝ,
      U h f₂ - f₂ = ∫ s in (0 : ℝ)..h, U s f₃)
    (hfund₃₄ : ∀ h : ℝ,
      U h f₃ - f₃ = ∫ s in (0 : ℝ)..h, U s f₄) :
    ContDiff ℝ 4 (fun t ↦ U t f₀) := by
  apply h16_contDiff_four_orbit U hgroup f₀ f₁ f₂ f₃ f₄
  · exact h16_hasDerivAt_orbit_of_integral_identity
      (fun t x ↦ U t x) f₀ f₁ (hzero f₁) hc₁ hfund₀₁
  · exact h16_hasDerivAt_orbit_of_integral_identity
      (fun t x ↦ U t x) f₁ f₂ (hzero f₂) hc₂ hfund₁₂
  · exact h16_hasDerivAt_orbit_of_integral_identity
      (fun t x ↦ U t x) f₂ f₃ (hzero f₃) hc₃ hfund₂₃
  · exact h16_hasDerivAt_orbit_of_integral_identity
      (fun t x ↦ U t x) f₃ f₄ (hzero f₄) hc₄ hfund₃₄
  · exact hc₄

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional
