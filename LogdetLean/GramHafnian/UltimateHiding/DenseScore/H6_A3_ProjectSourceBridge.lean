import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A3_EdelmanSuttonProp12Conditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_BetaJacobiNormalizationA2Free

/-!
# A3 project real-Gaussian source bridge

This module identifies the project's literal pair of real Gaussian matrices
with the beta-one Edelman--Sutton source after only coordinatewise complex
embedding and the proved row-count equality.  It then transports measurable
permutation-invariant tests of the A3 squared-GSV coordinates back to the
project real source.  No ordered-coordinate law, spectral quotient, or H6
trace identity is asserted here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

local instance h6A3RealMatrixMeasurableSpace
    (rows n : Type*) : MeasurableSpace (Matrix rows n ℝ) := by
  unfold Matrix
  infer_instance

/-- Reindex the rows of a real matrix along a proved equality of row counts. -/
def h6A3RealMatrixRowCast
    {sourceRows targetRows n : ℕ} (hrows : targetRows = sourceRows) :
    Matrix (Fin sourceRows) (Fin n) ℝ →
      Matrix (Fin targetRows) (Fin n) ℝ :=
  fun X i j ↦ X (Fin.cast hrows i) j

theorem measurable_h6A3RealMatrixRowCast
    {sourceRows targetRows n : ℕ} (hrows : targetRows = sourceRows) :
    Measurable (h6A3RealMatrixRowCast (n := n) hrows) := by
  unfold h6A3RealMatrixRowCast
  fun_prop

theorem map_standardRealGaussianMatrixMeasure_rowCast
    {sourceRows targetRows n : ℕ} (hrows : targetRows = sourceRows) :
    Measure.map (h6A3RealMatrixRowCast (n := n) hrows)
        (standardRealGaussianMatrixMeasure sourceRows n) =
      standardRealGaussianMatrixMeasure targetRows n := by
  cases hrows
  have hid : h6A3RealMatrixRowCast
      (n := n) (rfl : sourceRows = sourceRows) = id := by
    funext X i j
    rfl
  rw [hid, Measure.map_id]

theorem measurable_edelmanSuttonRealMatrixEmbedding
    (rows n : ℕ) :
    Measurable (edelmanSuttonRealMatrixEmbedding rows n) := by
  unfold edelmanSuttonRealMatrixEmbedding
  fun_prop

/-- Row cast followed by the paper's coordinatewise real-to-complex map. -/
def h6A3RealMatrixCastEmbedding
    {sourceRows targetRows n : ℕ} (hrows : targetRows = sourceRows) :
    Matrix (Fin sourceRows) (Fin n) ℝ →
      Matrix (Fin targetRows) (Fin n) ℂ :=
  fun X i j ↦ (X (Fin.cast hrows i) j : ℂ)

theorem measurable_h6A3RealMatrixCastEmbedding
    {sourceRows targetRows n : ℕ} (hrows : targetRows = sourceRows) :
    Measurable (h6A3RealMatrixCastEmbedding (n := n) hrows) := by
  unfold h6A3RealMatrixCastEmbedding
  fun_prop

theorem map_standardRealGaussianMatrixMeasure_castEmbedding
    {sourceRows targetRows n : ℕ} (hrows : targetRows = sourceRows) :
    Measure.map (h6A3RealMatrixCastEmbedding (n := n) hrows)
        (standardRealGaussianMatrixMeasure sourceRows n) =
      edelmanSuttonRealGaussianMatrixLaw targetRows n := by
  unfold edelmanSuttonRealGaussianMatrixLaw
  calc
    Measure.map (h6A3RealMatrixCastEmbedding (n := n) hrows)
        (standardRealGaussianMatrixMeasure sourceRows n) =
      Measure.map (edelmanSuttonRealMatrixEmbedding targetRows n)
        (Measure.map (h6A3RealMatrixRowCast (n := n) hrows)
          (standardRealGaussianMatrixMeasure sourceRows n)) := by
            rw [Measure.map_map
              (measurable_edelmanSuttonRealMatrixEmbedding targetRows n)
              (measurable_h6A3RealMatrixRowCast hrows)]
            rfl
    _ = Measure.map (edelmanSuttonRealMatrixEmbedding targetRows n)
        (standardRealGaussianMatrixMeasure targetRows n) := by
          rw [map_standardRealGaussianMatrixMeasure_rowCast hrows]

/-- Concrete project pair embedded in the literal beta-one A3 carrier. -/
def h6A3ProjectPairEmbedding
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    RealBetaPrimeGaussianSource N K →
      EdelmanSuttonGaussianPair N 1 (K - 2 * N) :=
  fun p ↦
    (edelmanSuttonRealMatrixEmbedding (N + 1) N p.1,
      h6A3RealMatrixCastEmbedding
        (H6_A3_literal_parameter_substitution h2NK).1 p.2)

theorem measurable_h6A3ProjectPairEmbedding
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    Measurable (h6A3ProjectPairEmbedding h2NK) := by
  unfold h6A3ProjectPairEmbedding
  exact ((measurable_edelmanSuttonRealMatrixEmbedding (N + 1) N).comp
      measurable_fst).prodMk
    ((measurable_h6A3RealMatrixCastEmbedding
      (H6_A3_literal_parameter_substitution h2NK).1).comp measurable_snd)

/-- The A3 beta-one source is exactly the pushforward of the project's real
Gaussian pair; the `N,K` row arithmetic is outside the A3 atom. -/
theorem H6_A3_projectGaussianSource_embeddingLaw
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    Measure.map (h6A3ProjectPairEmbedding h2NK)
        (realBetaPrimeGaussianSourceLaw N K) =
      edelmanSuttonGaussianPairLaw N 1 (K - 2 * N) 1 := by
  let μA := standardRealGaussianMatrixMeasure (N + 1) N
  let μB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure μA := by
    dsimp [μA]
    unfold standardRealGaussianMatrixMeasure
    apply Measure.pi.instIsProbabilityMeasure
  letI : IsProbabilityMeasure μB := by
    dsimp [μB]
    unfold standardRealGaussianMatrixMeasure
    apply Measure.pi.instIsProbabilityMeasure
  rw [edelmanSuttonGaussianPairLaw_beta_one]
  change Measure.map (h6A3ProjectPairEmbedding h2NK) (μA.prod μB) = _
  calc
    Measure.map (h6A3ProjectPairEmbedding h2NK) (μA.prod μB) =
      (Measure.map (edelmanSuttonRealMatrixEmbedding (N + 1) N) μA).prod
        (Measure.map (h6A3RealMatrixCastEmbedding
          (H6_A3_literal_parameter_substitution h2NK).1) μB) := by
            rw [Measure.map_prod_map μA μB
              (measurable_edelmanSuttonRealMatrixEmbedding (N + 1) N)
              (measurable_h6A3RealMatrixCastEmbedding
                (H6_A3_literal_parameter_substitution h2NK).1)]
            rfl
    _ = (edelmanSuttonRealGaussianMatrixLaw (N + 1) N).prod
        (edelmanSuttonRealGaussianMatrixLaw
          (N + (K - 2 * N)) N) := by
      rw [map_standardRealGaussianMatrixMeasure_castEmbedding
        (H6_A3_literal_parameter_substitution h2NK).1]
      rfl

/-- AE-measurability of the squared-GSV coordinates in the exact project
range.  The corrected A3 contract supplies the stronger measurable statement
directly; no ordered-vector distributional equality is used. -/
theorem H6_A3_project_squaredGSV_aemeasurable
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    AEMeasurable
      (edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1)
      (edelmanSuttonGaussianPairLaw N 1 (K - 2 * N) 1) := by
  exact (H6_A3_project_squaredGSV_measurable hN h2NK).aemeasurable

/-- A3 transported back to the project's literal real Gaussian source after
an arbitrary measurable permutation-invariant test.  This is the strongest
source-faithful law needed downstream; it deliberately does not identify the
law of Mathlib's canonically ordered eigenvalue vector with the symmetric
beta-Jacobi measure. -/
theorem H6_A3_projectRealSource_unordered_symmetric_test
    {γ : Type} [MeasurableSpace γ]
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ∀ (F : (Fin N → ℝ) → γ),
      Measurable F →
      IsA2SymmetricTest F →
    Measure.map
        (fun p ↦ F
          (edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1
            (h6A3ProjectPairEmbedding h2NK p)))
        (realBetaPrimeGaussianSourceLaw N K) =
      Measure.map F
        (betaJacobiProbabilityMeasure N 1
          ((K - 2 * N : ℕ) : ℝ) 1) := by
  intro F hF hSym
  let coordinates :=
    edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1
  have hbridge := H6_A3_projectGaussianSource_embeddingLaw h2NK
  have hcoordinates : Measurable coordinates := by
    simpa [coordinates] using
      H6_A3_project_squaredGSV_measurable hN h2NK
  calc
    Measure.map
        (fun p ↦ F
          (edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1
            (h6A3ProjectPairEmbedding h2NK p)))
        (realBetaPrimeGaussianSourceLaw N K) =
      Measure.map (F ∘ coordinates)
        (Measure.map (h6A3ProjectPairEmbedding h2NK)
          (realBetaPrimeGaussianSourceLaw N K)) := by
      rw [Measure.map_map (hF.comp hcoordinates)
        (measurable_h6A3ProjectPairEmbedding h2NK)]
      rfl
    _ = Measure.map (F ∘ coordinates)
        (edelmanSuttonGaussianPairLaw N 1 (K - 2 * N) 1) := by
          rw [hbridge]
    _ = Measure.map F
        (betaJacobiProbabilityMeasure N 1
          ((K - 2 * N : ℕ) : ℝ) 1) := by
      simpa [coordinates] using
        H6_A3_project_unordered_symmetric_test hN h2NK F hF hSym

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
