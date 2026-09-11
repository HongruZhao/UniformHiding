import GBSHiding.OptimizedCertificates
import LogdetLean.GramHafnian.ThreePaper.CoefficientAsymptoticComparison
import LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison
import HidingStatement

/-! Corollary 3.3, Route 1: the infimum of the actual capped budgets
tends to zero. Thresholds need not minimize the budget. -/
open Filter MeasureTheory Set
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.ThreePaper
open LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
open LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 1600000

/-- The paper's `E₁(τ)`, with the capped hiding error. -/
def routeOneCertificate (gamma : ℝ → ℝ) (M K n : ℕ)
    (rho p₁ tau : ℝ) : ℝ :=
  min 1 (gamma tau + paperBkn K n * (tau / (rho * p₁)) +
    hidingRemainder M (2 * n))

theorem routeOneCertificate_nonneg
    (gamma : ℝ → ℝ) (M K n : ℕ) (rho p₁ tau : ℝ)
    (hg : 0 ≤ gamma tau) (hB : 0 ≤ paperBkn K n)
    (hr : 0 < rho) (hp : 0 < p₁) (ht : 0 ≤ tau) :
    0 ≤ routeOneCertificate gamma M K n rho p₁ tau := by
  unfold routeOneCertificate hidingRemainder ultimateSquaredHidingRate
  exact le_min zero_le_one (add_nonneg (add_nonneg hg
    (mul_nonneg hB (div_nonneg ht (mul_pos hr hp).le)))
    (le_min zero_le_one (by positivity)))

theorem optimizedCertificate_le_at
    (E : ℝ → ℝ) (hE : ∀ t, 0 ≤ t → 0 ≤ E t)
    (tau : ℝ) (htau : 0 ≤ tau) : optimizedCertificate E ≤ E tau := by
  apply csInf_le
  · exact ⟨0, by rintro y ⟨t, ht, rfl⟩; exact hE t ht⟩
  · exact ⟨tau, htau, rfl⟩

/-- The Route 1 conclusion of Corollary 3.3. The functions `gamma n`
are nonnegative additive-failure curves and `tau n` are the stated
polynomially scaled physical thresholds. No infimum-attainment premise
and no Route 2 comparison are used. -/
theorem corollary3_3_route1_optimized
    (gamma : ℕ → ℝ → ℝ) (K M : ℕ → ℕ) (rho p₁ tau : ℕ → ℝ)
    {c a : ℝ} (hc : 0 < c) (ha : 1 / 2 + 3 / (4 * c) < a)
    (hgamma : ∀ n t, 0 ≤ t → 0 ≤ gamma n t)
    (hrho : ∀ n, 0 < rho n) (hp : ∀ n, 0 < p₁ n)
    (htau : ∀ n, 0 ≤ tau n)
    (hratio : ∀ᶠ n in atTop,
      tau n / (rho n * p₁ n) = ((2 * n : ℕ) : ℝ) ^ (-a))
    (hsmall : Tendsto (fun n ↦ gamma n (tau n)) atTop (nhds 0))
    (hK4 : ∀ᶠ n in atTop, 4 * n ≤ K n)
    (hlower : ∀ᶠ n in atTop,
      c * (((2 * n : ℕ) : ℝ) ^ 2) / Real.log ((2 * n : ℕ) : ℝ) ≤ K n)
    (hMsquared : Tendsto
      (fun n ↦ ((2 * n : ℕ) : ℝ) ^ 2 / (M n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n ↦ optimizedCertificate
      (routeOneCertificate (gamma n) (M n) (K n) n (rho n) (p₁ n)))
      atTop (nhds 0) := by
  have hscale := decisiveWindow_lowerBound_implies_ambientLogScale K hc hlower
  have ha' : 1 / 2 + 3 * (1 / c) / 4 < a := by
    have heq : 3 / (4 * c) = 3 * (1 / c) / 4 := by ring
    rwa [← heq]
  have hanti := paperBkn_mul_polynomialThreshold_tendsto_zero_of_ambientLogScale
    K (one_div_pos.mpr hc) ha' hK4 hscale
  have hhide := hidingRemainder_tendsto_zero_of_squaredRate
    M (fun n ↦ 2 * n) hMsquared
  have hbudget : Tendsto
      (fun n ↦ routeOneCertificate (gamma n) (M n) (K n) n
        (rho n) (p₁ n) (tau n)) atTop (nhds 0) := by
    have hb := capped_three_term_budget_tendsto_zero
      (fun n ↦ gamma n (tau n))
      (fun n ↦ paperBkn (K n) n * ((2 * n : ℕ) : ℝ) ^ (-a))
      (fun n ↦ hidingRemainder (M n) (2 * n)) hsmall hanti hhide
    apply hb.congr'
    filter_upwards [hratio] with n hn
    simp only [routeOneCertificate, hn]
  have hnonneg : ∀ᶠ n in atTop, ∀ t, 0 ≤ t →
      0 ≤ routeOneCertificate (gamma n) (M n) (K n) n (rho n) (p₁ n) t := by
    filter_upwards [hK4, eventually_ge_atTop 1] with n hKn hn t ht
    have hB : 0 ≤ paperBkn (K n) n := by
      change 0 ≤ shiftedAnticoncentrationConstant (K n) n
      rw [shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hKn]
      exact mul_nonneg (paperBn_pos n hn).le (Real.exp_nonneg _)
    exact routeOneCertificate_nonneg _ _ _ _ _ _ _
      (hgamma n t ht) hB (hrho n) (hp n) ht
  refine squeeze_zero' ?_ ?_ hbudget
  · filter_upwards [hnonneg] with n hn
    exact lowerBound_optimizedCertificate 0 _ hn
  · filter_upwards [hnonneg] with n hn
    exact optimizedCertificate_le_at _ hn (tau n) (htau n)

theorem optimizedCertificate_eq_iInf (E : ℝ → ℝ) :
    optimizedCertificate E = ⨅ t : {t : ℝ // 0 ≤ t}, E t := by
  have hr : E '' Set.Ici 0 = Set.range (fun t : {t : ℝ // 0 ≤ t} ↦ E t) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
  change sInf (E '' Set.Ici 0) = sInf (Set.range _)
  rw [hr]

/-- The scalar certificate is literally the public, physical-threshold
budget when gamma is the actual additive-failure probability. -/
theorem routeOneCertificate_eq_publicBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (deltaP : Ω → ℝ) (r : ℝ) (M K n : ℕ) (rho tau : ℝ) :
    routeOneCertificate
      (fun t ↦ μ.real (FairAbsoluteThresholdComparison.absoluteAdditiveFailureEvent deltaP t))
      M K n rho (gbsGaussianReferenceProbability r M K n) tau =
        UniformHiding.routeOneBound μ deltaP r M K n rho tau := rfl

theorem optimizedCertificate_eq_publicBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (deltaP : Ω → ℝ) (r : ℝ) (M K n : ℕ) (rho : ℝ) :
    optimizedCertificate (routeOneCertificate
      (fun t ↦ μ.real (FairAbsoluteThresholdComparison.absoluteAdditiveFailureEvent deltaP t))
      M K n rho (gbsGaussianReferenceProbability r M K n)) =
        UniformHiding.optimizedRouteOneBound μ deltaP r M K n rho := by
  rw [optimizedCertificate_eq_iInf]
  rfl

/-- Corollary 3.3 for the public optimized probability bound itself.
No attainment, independence of the estimator, or Route 2 premise is used. -/
theorem corollary3_3_route1_public
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) (deltaP : (n : ℕ) → Ω n → ℝ)
    (K M : ℕ → ℕ) (r rho tau : ℕ → ℝ)
    {c a : ℝ} (hc : 0 < c) (ha : 1/2+3/(4*c) < a)
    (hrho : ∀ n, 0 < rho n)
    (hp : ∀ n, 0 < gbsGaussianReferenceProbability (r n) (M n) (K n) n)
    (htau : ∀ n, 0 ≤ tau n)
    (hratio : ∀ᶠ n in atTop,
      tau n / (rho n * gbsGaussianReferenceProbability (r n) (M n) (K n) n) =
        ((2*n:ℕ):ℝ)^(-a))
    (hsmall : Tendsto (fun n ↦ (μ n).real
      (FairAbsoluteThresholdComparison.absoluteAdditiveFailureEvent (deltaP n) (tau n)))
      atTop (nhds 0))
    (hK4 : ∀ᶠ n in atTop, 4*n ≤ K n)
    (hlower : ∀ᶠ n in atTop, c * (((2*n:ℕ):ℝ)^2) / Real.log ((2*n:ℕ):ℝ) ≤ K n)
    (hMsquared : Tendsto (fun n ↦ ((2*n:ℕ):ℝ)^2/(M n:ℝ)) atTop (nhds 0)) :
    Tendsto (fun n ↦ UniformHiding.optimizedRouteOneBound
      (μ n) (deltaP n) (r n) (M n) (K n) n (rho n)) atTop (nhds 0) := by
  have h := corollary3_3_route1_optimized
    (fun n t ↦ (μ n).real (FairAbsoluteThresholdComparison.absoluteAdditiveFailureEvent (deltaP n) t))
    K M rho (fun n ↦ gbsGaussianReferenceProbability (r n) (M n) (K n) n) tau
    hc ha (fun _ _ _ ↦ measureReal_nonneg) hrho hp htau hratio hsmall hK4 hlower hMsquared
  simpa only [optimizedCertificate_eq_publicBound] using h

end
end GBSHiding
