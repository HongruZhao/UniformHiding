import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantVitaliReduction
import Mathlib.Tactic

/-!
# H16 fourth secants: the exact local `L1` remainder

The existing determinant estimate and volume-preserving transport already
make the complete orbit of the fourth literal jet uniformly integrable.  This
module proves that fact and isolates the remaining endpoint as one scalar,
event-free local `L1` limit for the normalized `3 -> 4` remainder.

This local limit is strictly narrower than uniform integrability of the full
real-parameter family: it asks only that the integral of the nonnegative
remainder tend to zero at the single time `0`.  It is nevertheless exactly
what is needed for the Banach derivative and hence for the already proved
lower derivative chain.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Volume-preserving transport upgrades time-zero fourth-jet integrability
to uniform integrability of its whole orbit.  Thus the outstanding H16 issue
is not concentration of the transported fourth jet itself. -/
theorem unifIntegrable_h16CenteredTransportJet_four_orbit_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) :
    UnifIntegrable
      (fun t : ℝ ↦ h16CenteredTransportJet N K 4 v t)
      1 (complexSymmetricCoordinateVolume N) := by
  let μ := complexSymmetricCoordinateVolume N
  let f₀ : ComplexSymmetricCoordinates N → ℝ :=
    h16CenteredTransportJet N K 4 v 0
  have hf₀int : Integrable f₀ μ := by
    simpa only [f₀, μ] using
      (integrable_h16CenteredTransportJet_direct_exactH5
        hH5 hN hboundary (4 : Fin 5) v 0)
  have hf₀mem : MemLp f₀ 1 μ :=
    memLp_one_iff_integrable.mpr hf₀int
  have hui₀ : UnifIntegrable (fun _ : ℝ ↦ f₀) 1 μ :=
    unifIntegrable_const le_rfl ENNReal.one_ne_top hf₀mem
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hui₀ hε
  refine ⟨δ, hδ, ?_⟩
  intro t s hs hμs
  let u : Set (ComplexSymmetricCoordinates N) :=
    h16CenteredCoordinateFlow v t ⁻¹' s
  have hu : MeasurableSet u := by
    exact hs.preimage
      (h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
        v t ((h16CenteredCoordinateComplexJacobianFamily hN) v t)).measurable
  have hμu : μ u = μ s := by
    exact
      (h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
        v t ((h16CenteredCoordinateComplexJacobianFamily hN) v t)).measure_preimage
          hs.nullMeasurableSet
  have hfun :
      s.indicator (h16CenteredTransportJet N K 4 v t) =
        (u.indicator f₀) ∘ h16CenteredCoordinateFlow v (-t) := by
    funext x
    dsimp only [Function.comp_apply]
    by_cases hx : x ∈ s
    · have hxu : h16CenteredCoordinateFlow v (-t) x ∈ u := by
        change h16CenteredCoordinateFlow v t
            (h16CenteredCoordinateFlow v (-t) x) ∈ s
        simpa using hx
      rw [indicator_of_mem hx, indicator_of_mem hxu]
      simpa only [f₀] using
        h16CenteredTransportJet_eq_zero_pullback
          (N := N) (K := K) (4 : Fin 5) v t x
    · have hxu : h16CenteredCoordinateFlow v (-t) x ∉ u := by
        intro hmem
        apply hx
        change h16CenteredCoordinateFlow v t
            (h16CenteredCoordinateFlow v (-t) x) ∈ s at hmem
        simpa using hmem
      rw [indicator_of_notMem hx]
      change 0 = u.indicator f₀ (h16CenteredCoordinateFlow v (-t) x)
      rw [indicator_of_notMem hxu]
  rw [hfun]
  rw [eLpNorm_comp_measurePreserving
    (hf₀int.aestronglyMeasurable.indicator hu)
    (h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
      v (-t) ((h16CenteredCoordinateComplexJacobianFamily hN) v (-t)))]
  exact hsmall t u hu (by simpa only [hμu] using hμs)

/-- The exact scalar local `L1` statement left by the fourth secant: only the
integral of the nonnegative normalized remainder must vanish at time zero. -/
def H16CenteredFourthLocalSecantIntegralVanishing (N K : ℕ) : Prop :=
  ∀ v : ComplexUnitSphere N,
    Tendsto
      (fun t : ℝ ↦ ∫ x,
        h16CenteredFourthLocalSecantRemainder N K v t x
          ∂(complexSymmetricCoordinateVolume N))
      (𝓝 0) (𝓝 0)

/-- The scalar local remainder limit is sufficient for the sharp canonical
`L1` derivative. -/
theorem h16CenteredDirectFourthL1DerivativeAtZero_of_secantIntegralVanishing_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishing N K) :
    H16CenteredDirectFourthL1DerivativeAtZero hH5 hN hboundary := by
  intro v
  let μ := complexSymmetricCoordinateVolume N
  let R : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t ↦
    h16CenteredFourthLocalSecantRemainder N K v t
  let L : ℝ → H16CenteredCoordinateL1 N := fun t ↦
    h16CenteredDirectJetLp hH5 hN hboundary (3 : Fin 5) v t
  let L' : H16CenteredCoordinateL1 N :=
    h16CenteredDirectJetLp hH5 hN hboundary (4 : Fin 5) v 0
  have hIntegral : Tendsto (fun t : ℝ ↦ ∫ x, R t x ∂μ)
      (𝓝 0) (𝓝 0) := by
    simpa only [R, μ] using hvanish v
  rw [hasDerivAt_iff_tendsto]
  apply hIntegral.congr'
  filter_upwards
      [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1)] with t ht
  symm
  change ‖t - 0‖⁻¹ * ‖L t - L 0 - (t - 0) • L'‖ =
    ∫ x, R t x ∂μ
  rw [sub_zero]
  rw [L1.norm_eq_integral_norm]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards
      [Lp.coeFn_sub (L t) (L 0),
        Lp.coeFn_smul t L',
        Lp.coeFn_sub (L t - L 0) (t • L'),
        h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
          (3 : Fin 5) v t,
        h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
          (3 : Fin 5) v 0,
        h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
          (4 : Fin 5) v 0] with
      x hsub hsmul hsub' hJt hJzero hJfour
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hsub'
  rw [hsub', hsub, hsmul, hJt, hJzero, hJfour]
  simp [R, h16CenteredFourthLocalSecantRemainder, ht, smul_eq_mul]

/-- Conversely, the sharp Banach derivative forces the scalar remainder
integral to vanish.  Hence the new condition is an exact scalar encoding of
the only missing top derivative, rather than an additional regularity demand. -/
theorem h16CenteredFourthLocalSecantIntegralVanishing_of_directFourthL1DerivativeAtZero_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hfourth : H16CenteredDirectFourthL1DerivativeAtZero
      hH5 hN hboundary) :
    H16CenteredFourthLocalSecantIntegralVanishing N K := by
  intro v
  let μ := complexSymmetricCoordinateVolume N
  let R : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t ↦
    h16CenteredFourthLocalSecantRemainder N K v t
  let L : ℝ → H16CenteredCoordinateL1 N := fun t ↦
    h16CenteredDirectJetLp hH5 hN hboundary (3 : Fin 5) v t
  let L' : H16CenteredCoordinateL1 N :=
    h16CenteredDirectJetLp hH5 hN hboundary (4 : Fin 5) v 0
  have hquot : Tendsto
      (fun t : ℝ ↦ ‖t - 0‖⁻¹ * ‖L t - L 0 - (t - 0) • L'‖)
      (𝓝 0) (𝓝 0) := by
    simpa only [L, L'] using hasDerivAt_iff_tendsto.mp (hfourth v)
  have hIntegral : Tendsto (fun t : ℝ ↦ ∫ x, R t x ∂μ)
      (𝓝 0) (𝓝 0) := by
    apply hquot.congr'
    filter_upwards
        [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
          (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [sub_zero]
    rw [L1.norm_eq_integral_norm]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards
        [Lp.coeFn_sub (L t) (L 0),
          Lp.coeFn_smul t L',
          Lp.coeFn_sub (L t - L 0) (t • L'),
          h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
            (3 : Fin 5) v t,
          h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
            (3 : Fin 5) v 0,
          h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
            (4 : Fin 5) v 0] with
        x hsub hsmul hsub' hJt hJzero hJfour
    simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hsub'
    rw [hsub', hsub, hsmul, hJt, hJzero, hJfour]
    simp [R, h16CenteredFourthLocalSecantRemainder, ht, smul_eq_mul]
  simpa only [R, μ] using hIntegral

/-- Under exact H5, the scalar local integral limit is equivalent to the
sharp top-slot `L1` derivative. -/
theorem h16CenteredFourthLocalSecantIntegralVanishing_iff_directFourthL1DerivativeAtZero_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    H16CenteredFourthLocalSecantIntegralVanishing N K ↔
      H16CenteredDirectFourthL1DerivativeAtZero hH5 hN hboundary :=
  ⟨h16CenteredDirectFourthL1DerivativeAtZero_of_secantIntegralVanishing_exactH5
      hH5 hN hboundary,
    h16CenteredFourthLocalSecantIntegralVanishing_of_directFourthL1DerivativeAtZero_exactH5
      hH5 hN hboundary⟩

/-- The formerly isolated uniform-integrability condition implies the scalar
local limit, confirming that the latter is the narrower remaining target. -/
theorem h16CenteredFourthLocalSecantIntegralVanishing_of_unifIntegrable_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hui : H16CenteredFourthLocalSecantsUnifIntegrable N K) :
    H16CenteredFourthLocalSecantIntegralVanishing N K :=
  h16CenteredFourthLocalSecantIntegralVanishing_of_directFourthL1DerivativeAtZero_exactH5
    hH5 hN hboundary
    (h16CenteredDirectFourthL1DerivativeAtZero_of_unifIntegrable_exactH5
      hH5 hN hboundary hui)

/-- The proved lower chain and the scalar top-slot limit give the complete
direct derivative chain. -/
theorem h16CenteredDirectL1DerivativeAtZeroChain_of_secantIntegralVanishing_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishing N K) :
    H16CenteredDirectL1DerivativeAtZeroChain hH5 hN hboundary :=
  h16CenteredDirectL1DerivativeAtZeroChain_of_lower_of_fourth
    hH5 hN hboundary
    (h16CenteredDirectLowerL1DerivativeAtZeroChain_proved_exactH5
      hH5 hN hboundary)
    (h16CenteredDirectFourthL1DerivativeAtZero_of_secantIntegralVanishing_exactH5
      hH5 hN hboundary hvanish)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
