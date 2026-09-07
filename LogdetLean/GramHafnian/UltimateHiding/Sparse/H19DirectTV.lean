import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19DensityLimit
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangDensityProved
import LogdetLean.GramHafnian.UltimateHiding.Sparse.Scheffe
import LogdetLean.GaussianColumnProduct

/-!
# Direct Scheffe total-variation limit for H19

For fixed positive `N ≤ K`, the scaled Jiang density converges pointwise to
the standard complex-Gaussian density.  Since all shifted ambient laws have
mass one, Scheffe's lemma upgrades this to total-variation convergence.  No
likelihood, KL, moment, or Bartlett/Rouault input occurs here.
-/

open Filter MeasureTheory ProbabilityTheory Complex
open scoped ComplexConjugate ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

/-- A nonnegative measurable real density of a probability measure is
integrable with total integral one. -/
theorem integrable_and_integral_eq_one_of_probability_withDensity_ofReal
    {alpha : Type*} [MeasurableSpace alpha]
    (mu nu : Measure alpha) [IsProbabilityMeasure nu]
    (f : alpha → ℝ) (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hnu : nu = mu.withDensity (fun x ↦ ENNReal.ofReal (f x))) :
    Integrable f mu ∧ ∫ x, f x ∂mu = 1 := by
  have hu := congrArg (fun m : Measure alpha ↦ m Set.univ) hnu
  have hlin : ∫⁻ x, ENNReal.ofReal (f x) ∂mu = 1 := by
    symm
    simpa [withDensity_apply, measure_univ] using hu
  have hint : Integrable f mu := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hf.aestronglyMeasurable (ae_of_all mu hf_nonneg)).mp
    rw [hlin]
    exact ENNReal.one_ne_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all mu hf_nonneg) hf.aestronglyMeasurable, hlin]
  simp

/-- The harmless ambient shift used to put every term in the internally
proved strict Jiang range `K+N < M`. -/
def h19ShiftedAmbient (K N n : ℕ) : ℕ := n + (K + N + 1)

theorem integrable_h19ShiftedJiangRealPDF
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K) (n : ℕ) :
    Integrable
      (jiangSqrtScaledTallHaarCornerRealPDF
        (h19ShiftedAmbient K N n) K N)
      (complexRectangularLebesgueVolume K N) := by
  let M := h19ShiftedAmbient K N n
  have hs : K + N < M := by
    simp only [M, h19ShiftedAmbient]
    omega
  have hM : 0 < M := by omega
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  letI : IsProbabilityMeasure (jiangSqrtScaledTallHaarCornerLaw M K N) :=
    jiangSqrtScaledTallHaarCornerLaw_isProbability hM hKM hNM
  exact (integrable_and_integral_eq_one_of_probability_withDensity_ofReal
    (complexRectangularLebesgueVolume K N)
    (jiangSqrtScaledTallHaarCornerLaw M K N)
    (jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (jiangSqrtScaledTallHaarCornerRealPDF_nonneg M K N)
    (jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs)).1

theorem integral_h19ShiftedJiangRealPDF_eq_one
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K) (n : ℕ) :
    ∫ Z, jiangSqrtScaledTallHaarCornerRealPDF
        (h19ShiftedAmbient K N n) K N Z
      ∂(complexRectangularLebesgueVolume K N) = 1 := by
  let M := h19ShiftedAmbient K N n
  have hs : K + N < M := by
    simp only [M, h19ShiftedAmbient]
    omega
  have hM : 0 < M := by omega
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := by omega
  letI : IsProbabilityMeasure (jiangSqrtScaledTallHaarCornerLaw M K N) :=
    jiangSqrtScaledTallHaarCornerLaw_isProbability hM hKM hNM
  exact (integrable_and_integral_eq_one_of_probability_withDensity_ofReal
    (complexRectangularLebesgueVolume K N)
    (jiangSqrtScaledTallHaarCornerLaw M K N)
    (jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (measurable_jiangSqrtScaledTallHaarCornerRealPDF M K N)
    (jiangSqrtScaledTallHaarCornerRealPDF_nonneg M K N)
    (jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs)).2

theorem integrable_standardComplexGaussianTallRealPDF (K N : ℕ) :
    Integrable (standardComplexGaussianTallRealPDF K N)
      (complexRectangularLebesgueVolume K N) := by
  letI : IsProbabilityMeasure (standardGaussianBlockLaw K N) :=
    standardComplexGaussianRectangularMeasure_isProbability K N
  exact (integrable_and_integral_eq_one_of_probability_withDensity_ofReal
    (complexRectangularLebesgueVolume K N)
    (standardGaussianBlockLaw K N)
    (standardComplexGaussianTallRealPDF K N)
    (measurable_standardComplexGaussianTallRealPDF K N)
    (standardComplexGaussianTallRealPDF_nonneg K N)
    (standardGaussianBlockLaw_eq_withDensity_ofReal_H19 K N)).1

theorem integral_standardComplexGaussianTallRealPDF_eq_one (K N : ℕ) :
    ∫ Z, standardComplexGaussianTallRealPDF K N Z
      ∂(complexRectangularLebesgueVolume K N) = 1 := by
  letI : IsProbabilityMeasure (standardGaussianBlockLaw K N) :=
    standardComplexGaussianRectangularMeasure_isProbability K N
  exact (integrable_and_integral_eq_one_of_probability_withDensity_ofReal
    (complexRectangularLebesgueVolume K N)
    (standardGaussianBlockLaw K N)
    (standardComplexGaussianTallRealPDF K N)
    (measurable_standardComplexGaussianTallRealPDF K N)
    (standardComplexGaussianTallRealPDF_nonneg K N)
    (standardGaussianBlockLaw_eq_withDensity_ofReal_H19 K N)).2

/-- Pointwise density convergence remains true after the fixed shift which
puts every ambient dimension in Jiang's source range. -/
theorem tendsto_h19ShiftedJiangRealPDF
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (Z : Matrix (Fin K) (Fin N) ℂ) :
    Tendsto
      (fun n : ℕ ↦ jiangSqrtScaledTallHaarCornerRealPDF
        (h19ShiftedAmbient K N n) K N Z)
      atTop (nhds (standardComplexGaussianTallRealPDF K N Z)) := by
  exact (tendsto_jiangSqrtScaledTallHaarCornerRealPDF hN hK hNK Z).comp
    (tendsto_add_atTop_nat (K + N + 1))

/-- Direct Scheffe convergence for the tall orientation of Jiang's scaled
Haar corner.  This theorem uses densities only: no KL divergence or moment
factorization is involved. -/
theorem eventually_h19ShiftedTall_probabilityTotalVariationLE
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      probabilityTotalVariationLE
        (jiangSqrtScaledTallHaarCornerLaw
          (h19ShiftedAmbient K N n) K N)
        (standardGaussianBlockLaw K N) epsilon := by
  have hscheffe :=
    eventually_probabilityTotalVariationLE_withDensity_ofReal
      (mu := complexRectangularLebesgueVolume K N)
      (f := fun n ↦ jiangSqrtScaledTallHaarCornerRealPDF
        (h19ShiftedAmbient K N n) K N)
      (g := standardComplexGaussianTallRealPDF K N)
      (integrable_h19ShiftedJiangRealPDF hN hK hNK)
      (integrable_standardComplexGaussianTallRealPDF K N)
      (fun n ↦ jiangSqrtScaledTallHaarCornerRealPDF_nonneg
        (h19ShiftedAmbient K N n) K N)
      (standardComplexGaussianTallRealPDF_nonneg K N)
      (fun n ↦ by
        rw [integral_h19ShiftedJiangRealPDF_eq_one hN hK hNK n,
          integral_standardComplexGaussianTallRealPDF_eq_one])
      (tendsto_h19ShiftedJiangRealPDF hN hK hNK)
      hepsilon
  filter_upwards [hscheffe] with n hn
  have hs : K + N < h19ShiftedAmbient K N n := by
    simp only [h19ShiftedAmbient]
    omega
  rw [← jiangSqrtScaledTallHaarCornerLaw_eq_withDensity_ofReal_proved_strict
      hN hK hNK hs,
    ← standardGaussianBlockLaw_eq_withDensity_ofReal_H19 K N] at hn
  exact hn

/-- The same tall-corner convergence indexed by the actual ambient
dimension, rather than by the shifted auxiliary index. -/
theorem eventually_jiangSqrtScaledTallHaarCornerLaw_probabilityTotalVariationLE
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ M : ℕ in atTop,
      probabilityTotalVariationLE
        (jiangSqrtScaledTallHaarCornerLaw M K N)
        (standardGaussianBlockLaw K N) epsilon := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (eventually_h19ShiftedTall_probabilityTotalVariationLE
      hN hK hNK hepsilon)
  refine eventually_atTop.2 ⟨n₀ + (K + N + 1), ?_⟩
  intro M hM
  have hsub : n₀ ≤ M - (K + N + 1) := by omega
  have heq : h19ShiftedAmbient K N (M - (K + N + 1)) = M := by
    simp [h19ShiftedAmbient]
    omega
  simpa only [heq] using hn₀ (M - (K + N + 1)) hsub

/-! ## Elementary orientation and data processing -/

/-- A standard circular complex Gaussian is invariant under complex
conjugation.  This follows directly from the symmetry of its second real
Gaussian coordinate. -/
theorem map_conj_circularGaussian_H19 :
    Measure.map (fun z : ℂ ↦ conj z) circularGaussian =
      circularGaussian := by
  let pairLaw : Measure (ℝ × ℝ) :=
    (gaussianReal 0 1).prod (gaussianReal 0 1)
  let reflectSecond : ℝ × ℝ → ℝ × ℝ :=
    Prod.map id (fun y : ℝ ↦ -y)
  have hneg : Measure.map (fun y : ℝ ↦ -y) (gaussianReal 0 1) =
      gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hreflect : Measure.map reflectSecond pairLaw = pairLaw := by
    dsimp only [reflectSecond, pairLaw]
    rw [← Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
      measurable_id (by fun_prop), Measure.map_id, hneg]
  have hcoord :
      (fun q : ℝ × ℝ ↦ conj (circularGaussianCoordinate q)) =
        circularGaussianCoordinate ∘ reflectSecond := by
    funext q
    apply Complex.ext <;>
      simp [circularGaussianCoordinate, reflectSecond, div_eq_mul_inv]
  have hcoord' :
      (fun z : ℂ ↦ conj z) ∘ circularGaussianCoordinate =
        circularGaussianCoordinate ∘ reflectSecond := by
    funext q
    exact congrFun hcoord q
  rw [circularGaussian,
    Measure.map_map Complex.continuous_conj.measurable
      measurable_circularGaussianCoordinate,
    hcoord', ← Measure.map_map measurable_circularGaussianCoordinate
      (by fun_prop), hreflect]

/-- Coordinatewise conjugation preserves every finite iid circular-Gaussian
vector law. -/
theorem map_entrywiseConj_circularGaussianVector_H19 (N : ℕ) :
    Measure.map (fun z : Fin N → ℂ ↦ fun j ↦ conj (z j))
        (circularGaussianVector N) =
      circularGaussianVector N := by
  unfold circularGaussianVector
  rw [Measure.pi_map_pi (fun _ ↦
    Complex.continuous_conj.measurable.aemeasurable)]
  congr 1
  funext j
  exact map_conj_circularGaussian_H19

/-- Conjugate transposition preserves the iid standard complex-Gaussian
rectangular law, while exchanging its two dimensions. -/
theorem map_rectangularConjTranspose_standardGaussianBlockLaw_H19
    (K N : ℕ) :
    Measure.map (rectangularConjTransposeMeasurableEquiv K N)
        (standardGaussianBlockLaw K N) =
      standardGaussianBlockLaw N K := by
  let entrywiseConj : (Fin K → Fin N → ℂ) → (Fin K → Fin N → ℂ) :=
    fun Z i j ↦ conj (Z i j)
  have hentry : Measurable entrywiseConj := by
    dsimp only [entrywiseConj]
    fun_prop
  have hconj :
      Measure.map entrywiseConj
          (Measure.pi fun _ : Fin K ↦ circularGaussianVector N) =
        Measure.pi fun _ : Fin K ↦ circularGaussianVector N := by
    change Measure.map
      (fun Z : Fin K → Fin N → ℂ ↦
        fun i ↦ (fun z : Fin N → ℂ ↦ fun j ↦ conj (z j)) (Z i))
      (Measure.pi fun _ : Fin K ↦ circularGaussianVector N) = _
    rw [Measure.pi_map_pi (fun _ ↦
      (by fun_prop : Measurable
        (fun z : Fin N → ℂ ↦ fun j ↦ conj (z j))).aemeasurable)]
    congr 1
    funext i
    exact map_entrywiseConj_circularGaussianVector_H19 N
  have hfun :
      (rectangularConjTransposeMeasurableEquiv K N :
        Matrix (Fin K) (Fin N) ℂ → Matrix (Fin N) (Fin K) ℂ) =
      LogdetLean.piTransposeMeasurableEquiv (Fin K) (Fin N) ℂ ∘
        entrywiseConj := by
    funext Z
    ext j i
    rfl
  let toMatrixKN := functionToComplexMatrix K N
  let toMatrixNK := functionToComplexMatrix N K
  let transpose :=
    LogdetLean.piTransposeMeasurableEquiv (Fin K) (Fin N) ℂ
  have htoKN : Measurable toMatrixKN :=
    measurable_functionToComplexMatrix K N
  have htoNK : Measurable toMatrixNK :=
    measurable_functionToComplexMatrix N K
  have htranspose : Measurable transpose :=
    (LogdetLean.piTransposeMeasurableEquiv
      (Fin K) (Fin N) ℂ).measurable
  have hcompose :
      (rectangularConjTransposeMeasurableEquiv K N) ∘ toMatrixKN =
        toMatrixNK ∘ transpose ∘ entrywiseConj := by
    funext Z
    ext j i
    rfl
  unfold standardGaussianBlockLaw
  unfold standardComplexGaussianRectangularMeasure
  change Measure.map (rectangularConjTransposeMeasurableEquiv K N)
      (Measure.map toMatrixKN
        (Measure.pi fun _ : Fin K ↦ circularGaussianVector N)) =
    Measure.map toMatrixNK
      (Measure.pi fun _ : Fin N ↦ circularGaussianVector K)
  calc
    Measure.map (rectangularConjTransposeMeasurableEquiv K N)
        (Measure.map toMatrixKN
          (Measure.pi fun _ : Fin K ↦ circularGaussianVector N)) =
      Measure.map
        ((rectangularConjTransposeMeasurableEquiv K N) ∘ toMatrixKN)
        (Measure.pi fun _ : Fin K ↦ circularGaussianVector N) := by
          rw [Measure.map_map
            (rectangularConjTransposeMeasurableEquiv K N).measurable htoKN]
    _ = Measure.map (toMatrixNK ∘ transpose ∘ entrywiseConj)
        (Measure.pi fun _ : Fin K ↦ circularGaussianVector N) := by
          rw [hcompose]
    _ = Measure.map toMatrixNK
        (Measure.map transpose
          (Measure.map entrywiseConj
            (Measure.pi fun _ : Fin K ↦ circularGaussianVector N))) := by
          rw [Measure.map_map htoNK htranspose,
            Measure.map_map (htoNK.comp htranspose) hentry]
          congr 1
    _ = Measure.map toMatrixNK
        (Measure.map transpose
          (Measure.pi fun _ : Fin K ↦ circularGaussianVector N)) := by
          rw [hconj]
    _ = Measure.map toMatrixNK
        (Measure.pi fun _ : Fin N ↦ circularGaussianVector K) := by
          change Measure.map toMatrixNK
              (Measure.map transpose
                (Measure.pi fun _ : Fin K ↦
                  Measure.pi fun _ : Fin N ↦ circularGaussian)) =
            Measure.map toMatrixNK
              (Measure.pi fun _ : Fin N ↦
                Measure.pi fun _ : Fin K ↦ circularGaussian)
          rw [show transpose =
              LogdetLean.piTransposeMeasurableEquiv
                (Fin K) (Fin N) ℂ by rfl,
            LogdetLean.map_pi_pi_piTranspose circularGaussian]

/-- Direct block-law convergence in the project's `N × K` orientation for
the canonical Haar probability family. -/
theorem eventually_canonicalSqrtScaledHaarBlockLaw_probabilityTotalVariationLE_H19
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ M : ℕ in atTop,
      probabilityTotalVariationLE
        (sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily M N K)
        (standardGaussianBlockLaw N K) epsilon := by
  have htall :=
    eventually_jiangSqrtScaledTallHaarCornerLaw_probabilityTotalVariationLE
      hN hK hNK hepsilon
  filter_upwards [htall, eventually_ge_atTop (K + N)] with M htv hs
  have hmap := htv.map
    (rectangularConjTransposeMeasurableEquiv K N).measurable
  rw [map_rectangularConjTranspose_jiangSqrtScaledTallHaarCornerLaw hNK hs,
    map_rectangularConjTranspose_standardGaussianBlockLaw_H19 K N] at hmap
  exact hmap

/-- The block convergence is independent of the chosen normalized Haar
family. -/
theorem eventually_sqrtScaledHaarBlockLaw_probabilityTotalVariationLE_H19
    (H : UnitaryHaarProbabilityFamily)
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ M : ℕ in atTop,
      probabilityTotalVariationLE
        (sqrtScaledHaarBlockLaw H M N K)
        (standardGaussianBlockLaw N K) epsilon := by
  filter_upwards
    [eventually_canonicalSqrtScaledHaarBlockLaw_probabilityTotalVariationLE_H19
      hN hK hNK hepsilon] with M hM
  rw [sqrtScaledHaarBlockLaw_eq_canonical H M N K]
  exact hM

/-- Deterministic transpose-Gram data processing gives the exact H19 target
law convergence. -/
theorem eventually_scaledHaarTransposeGramLaw_probabilityTotalVariationLE_H19
    (H : UnitaryHaarProbabilityFamily)
    {K N : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ M : ℕ in atTop,
      probabilityTotalVariationLE
        (scaledHaarTransposeGramLaw H M N K)
        (gaussianTransposeGramLaw N K) epsilon := by
  have hblock :=
    eventually_sqrtScaledHaarBlockLaw_probabilityTotalVariationLE_H19
      H hN hK hNK hepsilon
  filter_upwards [hblock, eventually_ge_atTop (K + N)] with M htv hs
  have hNM : N ≤ M := by omega
  have hKM : K ≤ M := by omega
  have hmap := htv.map (measurable_rectangularTransposeGram N K)
  rw [map_rectangularTransposeGram_sqrtScaledHaarBlockLaw H hNM hKM,
    map_rectangularTransposeGram_standardGaussianBlockLaw N K] at hmap
  exact hmap

/-- Sequence form needed by the dense telescope: starting at any ambient
dimension, some later term lies within every positive tolerance. -/
theorem exists_add_scaledHaarTransposeGramLaw_probabilityTotalVariationLE_H19
    (H : UnitaryHaarProbabilityFamily)
    {K N start : ℕ} (hN : 0 < N) (hK : 0 < K) (hNK : N ≤ K)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ,
      probabilityTotalVariationLE
        (scaledHaarTransposeGramLaw H (start + n) N K)
        (gaussianTransposeGramLaw N K) epsilon := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1
    (eventually_scaledHaarTransposeGramLaw_probabilityTotalVariationLE_H19
      H hN hK hNK hepsilon)
  refine ⟨M₀, hM₀ (start + M₀) ?_⟩
  omega

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
