import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A3_GSVDQuotientSpectrum

/-!
# H6 A3 concrete project-source trace transport

This module proves the row-reindexing and real-to-complex Gram identities that
specialize the full-rank Edelman--Sutton quotient theorem to the frozen
project Gaussian source.  It introduces no axiom.
-/

open scoped BigOperators MatrixOrder ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra
open H6RadialMeasureAdapters
open H6VectorChangeOfVariables
open LogdetLean.GramHafnian.Wishart

theorem h6A3_castEmbedding_gram
    {sourceRows targetRows n : ℕ}
    (hrows : targetRows = sourceRows)
    (X : Matrix (Fin sourceRows) (Fin n) ℝ) :
    Matrix.conjTranspose (h6A3RealMatrixCastEmbedding hrows X) *
        h6A3RealMatrixCastEmbedding hrows X =
      (realWishartGram X).map Complex.ofRealHom := by
  subst targetRows
  ext i j
  simp [h6A3RealMatrixCastEmbedding, realWishartGram,
    Matrix.mul_apply]

theorem h6A3_realEmbedding_gram
    {rows n : ℕ} (X : Matrix (Fin rows) (Fin n) ℝ) :
    Matrix.conjTranspose (edelmanSuttonRealMatrixEmbedding rows n X) *
        edelmanSuttonRealMatrixEmbedding rows n X =
      (realWishartGram X).map Complex.ofRealHom := by
  ext i j
  simp [edelmanSuttonRealMatrixEmbedding, realWishartGram,
    Matrix.mul_apply]

theorem h6A3_projectEmbedding_firstGram
    {N K : ℕ} (h2NK : 2 * N ≤ K)
    (p : RealBetaPrimeGaussianSource N K) :
    edelmanSuttonFirstGram (h6A3ProjectPairEmbedding h2NK p) =
      (realWishartGram p.1).map Complex.ofRealHom := by
  unfold edelmanSuttonFirstGram h6A3ProjectPairEmbedding
  exact h6A3_realEmbedding_gram p.1

theorem h6A3_projectEmbedding_secondGram
    {N K : ℕ} (h2NK : 2 * N ≤ K)
    (p : RealBetaPrimeGaussianSource N K) :
    edelmanSuttonSecondGram (h6A3ProjectPairEmbedding h2NK p) =
      (realWishartGram p.2).map Complex.ofRealHom := by
  unfold edelmanSuttonSecondGram h6A3ProjectPairEmbedding
  exact h6A3_castEmbedding_gram
    (H6_A3_literal_parameter_substitution h2NK).1 p.2

theorem isUnit_det_map_complex_ofReal
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hdet : IsUnit M.det) :
    IsUnit (M.map Complex.ofRealHom).det := by
  change IsUnit (Complex.ofRealHom.mapMatrix M).det
  rw [← RingHom.map_det]
  exact hdet.map Complex.ofRealHom

theorem map_nonsing_inv_complex_ofReal
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hdet : IsUnit M.det) :
    (M⁻¹).map Complex.ofRealHom =
      (M.map Complex.ofRealHom)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M hdet]
  simp

theorem h6A3_projectEmbedding_ratio
    {N K : ℕ} (h2NK : 2 * N ≤ K)
    (p : RealBetaPrimeGaussianSource N K)
    (hBdet : IsUnit (realWishartGram p.2).det) :
    (realMatrixBetaPrimeOfGaussianSource p).map Complex.ofRealHom =
      (edelmanSuttonSecondGram
          (h6A3ProjectPairEmbedding h2NK p))⁻¹ *
        edelmanSuttonFirstGram
          (h6A3ProjectPairEmbedding h2NK p) := by
  rw [h6A3_projectEmbedding_firstGram,
    h6A3_projectEmbedding_secondGram]
  unfold realMatrixBetaPrimeOfGaussianSource
  rw [Matrix.map_mul, map_nonsing_inv_complex_ofReal hBdet]

theorem complex_ofReal_trace_pow
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    Complex.ofReal (Matrix.trace (M ^ m)) =
      Matrix.trace ((M.map Complex.ofRealHom) ^ m) := by
  have hmapPow :
      (M ^ m).map Complex.ofRealHom =
        (M.map Complex.ofRealHom) ^ m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.map_mul, ih, pow_succ]
  calc
    Complex.ofReal (Matrix.trace (M ^ m)) =
        Matrix.trace ((M ^ m).map Complex.ofRealHom) := by
      exact AddMonoidHom.map_trace Complex.ofRealHom (M ^ m)
    _ = Matrix.trace ((M.map Complex.ofRealHom) ^ m) := by rw [hmapPow]

/-- Exact first theorem requested by the H6 integration handoff: on the
full-rank project source, the concrete quotient trace vector is the unordered
power-sum vector of the Edelman--Sutton odds coordinates. -/
theorem ae_realBetaPrimeTracePowerVector_eq_h6A3BetaPrimePowerSumVector
    {r N K : ℕ} (h2NK : 2 * N ≤ K) :
    ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
      realBetaPrimeTracePowerVector r N K p =
        h6A3BetaPrimePowerSumVector r N
          (fun i ↦
            (edelmanSutton_c_i N 1 (K - 2 * N) 1
              (h6A3ProjectPairEmbedding h2NK p) i) ^ 2) := by
  filter_upwards [ae_betaPrimeSource_wishart_det_units_internal h2NK]
    with p hp
  funext j
  apply Complex.ofReal_injective
  let omega := h6A3ProjectPairEmbedding h2NK p
  let m := j.1 + 1
  have hBdetComplex : IsUnit (edelmanSuttonSecondGram omega).det := by
    rw [show edelmanSuttonSecondGram omega =
        (realWishartGram p.2).map Complex.ofRealHom by
      exact h6A3_projectEmbedding_secondGram h2NK p]
    exact isUnit_det_map_complex_ofReal hp.2
  calc
    (realBetaPrimeTracePowerVector r N K p j : ℂ) =
        Matrix.trace
          (((realMatrixBetaPrimeOfGaussianSource p).map
            Complex.ofRealHom) ^ m) := by
      unfold realBetaPrimeTracePowerVector
      exact complex_ofReal_trace_pow
        (realMatrixBetaPrimeOfGaussianSource p) m
    _ = Matrix.trace
        (((edelmanSuttonSecondGram omega)⁻¹ *
          edelmanSuttonFirstGram omega) ^ m) := by
      rw [h6A3_projectEmbedding_ratio h2NK p hp.2]
    _ = ∑ i : Fin N,
        ((betaPrimeForward
          ((edelmanSutton_c_i N 1 (K - 2 * N) 1 omega i) ^ 2) : ℂ) ^ m) :=
      edelmanSutton_fullRank_quotient_trace_pow_eq_odds
        1 omega hBdetComplex m
    _ = (h6A3BetaPrimePowerSumVector r N
          (fun i ↦
            (edelmanSutton_c_i N 1 (K - 2 * N) 1 omega i) ^ 2) j : ℂ) := by
      simp [h6A3BetaPrimePowerSumVector, a2SpectralPowerSumVector,
        betaPrimeForwardVector, m]

theorem H6_A3_projectRealSource_traceVector_betaPrime_unordered
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (realBetaPrimeTracePowerVector r N K)
        (realBetaPrimeGaussianSourceLaw N K) =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  let μ := realBetaPrimeGaussianSourceLaw N K
  let coordinates : RealBetaPrimeGaussianSource N K → (Fin N → ℝ) :=
    fun p ↦
      edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1
        (h6A3ProjectPairEmbedding h2NK p)
  have hpoint :=
    ae_realBetaPrimeTracePowerVector_eq_h6A3BetaPrimePowerSumVector
      (r := r) h2NK
  calc
    Measure.map (realBetaPrimeTracePowerVector r N K) μ =
        Measure.map
          (fun p ↦ h6A3BetaPrimePowerSumVector r N (coordinates p)) μ := by
      apply Measure.map_congr
      filter_upwards [hpoint] with p hp
      change realBetaPrimeTracePowerVector r N K p =
        h6A3BetaPrimePowerSumVector r N
          (fun i ↦
            (edelmanSutton_c_i N 1 (K - 2 * N) 1
              (h6A3ProjectPairEmbedding h2NK p) i) ^ 2)
      exact hp
    _ = Measure.map (h6A3BetaPrimePowerSumVector r N)
        (betaJacobiProbabilityMeasure N 1
          ((K - 2 * N : ℕ) : ℝ) 1) := by
      simpa [μ, coordinates] using
        H6_A3_projectRealSource_unordered_symmetric_test hN h2NK
          (h6A3BetaPrimePowerSumVector r N)
          (measurable_h6A3BetaPrimePowerSumVector r N)
          (h6A3BetaPrimePowerSumVector_symmetric r N)
    _ = Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
      change Measure.map
          (a2SpectralPowerSumVector r N ∘ betaPrimeForwardVector N)
          (betaJacobiProbabilityMeasure N 1
            ((K - 2 * N : ℕ) : ℝ) 1) = _
      rw [← Measure.map_map (measurable_a2SpectralPowerSumVector r N)
        (measurable_betaPrimeForwardVector N)]
      exact H6_betaJacobi_to_betaPrime_unordered_traceVector hN h2NK

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
