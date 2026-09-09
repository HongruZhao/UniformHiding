import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
import LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

open MeasureTheory
open LogdetLean.GramHafnian LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

namespace UniformHiding
noncomputable section

/-- The normalized matrix-law assertion of manuscript Theorem 2.1, for
every positive row and input count fitting in the ambient matrix. -/
def Theorem21 : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
    1 ≤ N → N ≤ M → 1 ≤ K → K ≤ M →
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N))

/-- Corollary 2.2: the immediate quantitative specialization of Theorem 2.1
to `N = 2*n` and `M ≥ n² / delta`, in the unnormalized product convention. -/
def Corollary22 : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (M n K : ℕ),
    1 ≤ n → 2 * n ≤ M → 1 ≤ K → K ≤ M →
    ∀ delta : ℝ, 0 < delta → (n : ℝ)^2 / delta ≤ (M : ℝ) →
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M (2 * n) K)
      (gaussianTransposeGramLaw (2 * n) K)
      (4 * 615172 * delta)

/-- Divide a product matrix by the ambient dimension. This changes the
stored laws of `m U Uᵀ` and `G Gᵀ` to the source scale in Eq. (S62). -/
def s62ScaleDown (m N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ :=
  fun A ↦ (m : ℂ)⁻¹ • A

/-- Source-scale Haar product law. Under `2*n ≤ m` and `k ≤ m`, this is
the literal law of `U_(2n,k) U_(2n,k)ᵀ`; the equality is proved below. -/
def s62HaarProductLaw (H : UnitaryHaarProbabilityFamily) (m n k : ℕ) :
    Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :=
  (scaledHaarTransposeGramLaw H m (2 * n) k).map (s62ScaleDown m (2 * n))

/-- Source-scale Gaussian product law: the law of `(1/m) G Gᵀ` for a
standard `(2n) × k` Gaussian factor. In the source notation this is
`XᵀX`, where `X = Gᵀ / sqrt(m)` has entry variance `1/m`. -/
def s62GaussianProductLaw (m n k : ℕ) :
    Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :=
  (gaussianTransposeGramLaw (2 * n) k).map (s62ScaleDown m (2 * n))

/-- Explicit quantitative form of manuscript reference [10], Ehrenberg
et al., Conjecture 1 (Formal), Supplemental Eq. (S62): all `1 ≤ k ≤ m`,
with `m ≥ n² / delta`, have probability-TV at most `4 * 615172 * delta`.
The source uses the transpose orientation for its Haar block. The
notation dictionary and the common source-scale products are documented
in `docs/COROLLARY_2_2.md`. -/
def Corollary22S62 : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (m n k : ℕ),
    1 ≤ n → 2 * n ≤ m → 1 ≤ k → k ≤ m →
    ∀ delta : ℝ, 0 < delta → (n : ℝ)^2 / delta ≤ (m : ℝ) →
    probabilityTotalVariationLE
      (s62HaarProductLaw H m n k)
      (s62GaussianProductLaw m n k)
      (4 * 615172 * delta)

/-- Exact capped hiding remainder, in the probability-TV convention. -/
def deltaOne (M n : ℕ) : ℝ :=
  min 1 (615172 * ultimateSquaredHidingRate M (2 * n))

/-- E1(tau) from Theorem 3.2, with gamma(tau) the actual additive failure. -/
def routeOneBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (deltaP : Ω → ℝ) (r : ℝ) (M K n : ℕ)
    (rho tau : ℝ) : ℝ :=
  min 1 (μ.real (absoluteAdditiveFailureEvent deltaP tau) +
    paperBkn K n * (tau / (rho * gbsGaussianReferenceProbability r M K n)) +
    deltaOne M n)

/-- The infimum is over all nonnegative physical additive thresholds. -/
def optimizedRouteOneBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (deltaP : Ω → ℝ) (r : ℝ) (M K n : ℕ) (rho : ℝ) : ℝ :=
  ⨅ tau : {t : ℝ // 0 ≤ t}, routeOneBound μ deltaP r M K n rho tau

end
end UniformHiding
