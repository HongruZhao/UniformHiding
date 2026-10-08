import A3.BetaMatrixSpectralLaw
import A3.WishartGramDensity

open MeasureTheory MeasureTheory.Measure Set
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace A3Research

/-- Exact real Gram-pair matrix-beta law, with the genuine Gaussian normalizers. -/
theorem realGaussianGramPair_jacobiLaw (n a b : ℕ) (hn : 1 ≤ n) :
    Measure.map betaMatrixJacobiCoordinates
      ((realGaussianGramCoordinateLaw (n + a) n).prod
        (realGaussianGramCoordinateLaw (n + b) n)) =
      betaMatrixProbabilityMeasure n ℝ (((n + a : ℕ) : ℝ) / 2) (((n + b : ℕ) : ℝ) / 2) := by
  letI : IsAddHaarMeasure (hermitianCoordinateVolume n ℝ) := by
    unfold hermitianCoordinateVolume
    exact prod.instIsAddHaarMeasure _ _
  have hA := realGaussianGramCoordinateLaw_eq_ambientDensity (rows := n + a) (n := n) (by omega)
  have hB := realGaussianGramCoordinateLaw_eq_ambientDensity (rows := n + b) (n := n) (by omega)
  letI : IsProbabilityMeasure
      (ENNReal.ofReal (wishartBartlettNormalization n ℝ (((n + a : ℕ) : ℝ) / 2)
        (Real.sqrt Real.pi)⁻¹) • wishartAmbientMeasure n ℝ (((n + a : ℕ) : ℝ) / 2)) := by
    rw [← hA]
    exact realGaussianGramCoordinateLaw_probability _ _
  letI : IsProbabilityMeasure
      (ENNReal.ofReal (wishartBartlettNormalization n ℝ (((n + b : ℕ) : ℝ) / 2)
        (Real.sqrt Real.pi)⁻¹) • wishartAmbientMeasure n ℝ (((n + b : ℕ) : ℝ) / 2)) := by
    rw [← hB]
    exact realGaussianGramCoordinateLaw_probability _ _
  rw [hA, hB]
  exact map_normalizedWishartPair_jacobi hn _ _ (measurable_betaMatrixJacobiCoordinates_real n) _ _

/-- Exact complex Gram-pair matrix-beta law, with the genuine Gaussian normalizers. -/
theorem complexGaussianGramPair_jacobiLaw (n a b : ℕ) (hn : 1 ≤ n) :
    Measure.map betaMatrixJacobiCoordinates
      ((complexGaussianGramCoordinateLaw (n + a) n).prod
        (complexGaussianGramCoordinateLaw (n + b) n)) =
      betaMatrixProbabilityMeasure n ℂ ((n + a : ℕ) : ℝ) ((n + b : ℕ) : ℝ) := by
  letI : IsAddHaarMeasure (hermitianCoordinateVolume n ℂ) := by
    unfold hermitianCoordinateVolume
    exact prod.instIsAddHaarMeasure _ _
  have hA := complexGaussianGramCoordinateLaw_eq_ambientDensity (rows := n + a) (n := n) (by omega)
  have hB := complexGaussianGramCoordinateLaw_eq_ambientDensity (rows := n + b) (n := n) (by omega)
  letI : IsProbabilityMeasure
      (ENNReal.ofReal (wishartBartlettNormalization n ℂ ((n + a : ℕ) : ℝ) Real.pi⁻¹) •
        wishartAmbientMeasure n ℂ ((n + a : ℕ) : ℝ)) := by
    rw [← hA]
    exact complexGaussianGramCoordinateLaw_probability _ _
  letI : IsProbabilityMeasure
      (ENNReal.ofReal (wishartBartlettNormalization n ℂ ((n + b : ℕ) : ℝ) Real.pi⁻¹) •
        wishartAmbientMeasure n ℂ ((n + b : ℕ) : ℝ)) := by
    rw [← hB]
    exact complexGaussianGramCoordinateLaw_probability _ _
  rw [hA, hB]
  exact map_normalizedWishartPair_jacobi hn _ _ (measurable_betaMatrixJacobiCoordinates_complex n) _ _

theorem realGaussianGramPair_symmetric_betaJacobiLaw
    (n a b : ℕ) (hn : 1 ≤ n) {Y : Type} [MeasurableSpace Y]
    (F : (Fin n → ℝ) → Y) (hF : Measurable F) (hperm : IsA2SymmetricTest F) :
    Measure.map (F ∘ canonicalHermitianSpectrum ∘ betaMatrixJacobiCoordinates)
      ((realGaussianGramCoordinateLaw (n + a) n).prod
        (realGaussianGramCoordinateLaw (n + b) n)) =
      Measure.map F (betaJacobiProbabilityMeasure n (a : ℝ) (b : ℝ) 1) := by
  change Measure.map ((F ∘ (canonicalHermitianSpectrum : HermitianCoordinates n ℝ → _)) ∘
    (betaMatrixJacobiCoordinates : HermitianCoordinates n ℝ × HermitianCoordinates n ℝ → _))
      ((realGaussianGramCoordinateLaw (n + a) n).prod (realGaussianGramCoordinateLaw (n + b) n)) = _
  have hf : Measurable (F ∘ (canonicalHermitianSpectrum : HermitianCoordinates n ℝ → _)) :=
    hF.comp measurable_canonicalHermitianSpectrum
  rw [← Measure.map_map hf
    (measurable_betaMatrixJacobiCoordinates_real n), realGaussianGramPair_jacobiLaw n a b hn]
  simpa only [Module.finrank_self, Nat.cast_one, one_mul, Nat.cast_add] using
    betaMatrixProbabilityMeasure_symmetric_test_law (n := n) (K := ℝ) (a : ℝ) (b : ℝ) F hF hperm

theorem complexGaussianGramPair_symmetric_betaJacobiLaw
    (n a b : ℕ) (hn : 1 ≤ n) {Y : Type} [MeasurableSpace Y]
    (F : (Fin n → ℝ) → Y) (hF : Measurable F) (hperm : IsA2SymmetricTest F) :
    Measure.map (F ∘ canonicalHermitianSpectrum ∘ betaMatrixJacobiCoordinates)
      ((complexGaussianGramCoordinateLaw (n + a) n).prod
        (complexGaussianGramCoordinateLaw (n + b) n)) =
      Measure.map F (betaJacobiProbabilityMeasure n (a : ℝ) (b : ℝ) 2) := by
  change Measure.map ((F ∘ (canonicalHermitianSpectrum : HermitianCoordinates n ℂ → _)) ∘
    (betaMatrixJacobiCoordinates : HermitianCoordinates n ℂ × HermitianCoordinates n ℂ → _))
      ((complexGaussianGramCoordinateLaw (n + a) n).prod (complexGaussianGramCoordinateLaw (n + b) n)) = _
  have hf : Measurable (F ∘ (canonicalHermitianSpectrum : HermitianCoordinates n ℂ → _)) :=
    hF.comp measurable_canonicalHermitianSpectrum
  rw [← Measure.map_map hf
    (measurable_betaMatrixJacobiCoordinates_complex n), complexGaussianGramPair_jacobiLaw n a b hn]
  simpa only [Complex.finrank_real_complex, Nat.cast_ofNat, Nat.cast_add, mul_div_cancel_left₀
    _ (by norm_num : (2 : ℝ) ≠ 0)] using
    betaMatrixProbabilityMeasure_symmetric_test_law (n := n) (K := ℂ) (a : ℝ) (b : ℝ) F hF hperm

end A3Research
