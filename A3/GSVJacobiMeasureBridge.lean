import A3.LiteralJacobiBridge

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace A3Research

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev RealGaussianPairSource (n a b : ℕ) :=
  (Fin (n + a) → Fin n → ℝ) × (Fin (n + b) → Fin n → ℝ)

def realGaussianPairEmbedding {n a b : ℕ}
    (p : RealGaussianPairSource n a b) : EdelmanSuttonGaussianPair n a b :=
  (edelmanSuttonRealMatrixEmbedding (n + a) n (Matrix.of p.1),
    edelmanSuttonRealMatrixEmbedding (n + b) n (Matrix.of p.2))

theorem measurable_realGaussianPairEmbedding (n a b : ℕ) :
    Measurable (realGaussianPairEmbedding : RealGaussianPairSource n a b → _) := by
  unfold realGaussianPairEmbedding edelmanSuttonRealMatrixEmbedding
  change Measurable (fun p : RealGaussianPairSource n a b ↦
    (fun i j ↦ (p.1 i j : ℂ), fun i j ↦ (p.2 i j : ℂ)))
  fun_prop

theorem edelmanSuttonGaussianPairLaw_one_eq_map_realSource (n a b : ℕ) :
    edelmanSuttonGaussianPairLaw n a b 1 =
      ((A4Research.standardGaussianRows (n + a) n).prod
        (A4Research.standardGaussianRows (n + b) n)).map realGaussianPairEmbedding := by
  rw [edelmanSuttonGaussianPairLaw_beta_one]
  unfold edelmanSuttonRealGaussianMatrixLaw
  change ((A4Research.standardGaussianRows (n + a) n).map
      (fun X : Fin (n + a) → Fin n → ℝ ↦
        edelmanSuttonRealMatrixEmbedding (n + a) n (Matrix.of X))).prod
    ((A4Research.standardGaussianRows (n + b) n).map
      (fun Y : Fin (n + b) → Fin n → ℝ ↦
        edelmanSuttonRealMatrixEmbedding (n + b) n (Matrix.of Y))) = _
  exact Measure.map_prod_map _ _
    (a3_measurable_edelmanSuttonRealMatrixEmbedding (n + a) n)
    (a3_measurable_edelmanSuttonRealMatrixEmbedding (n + b) n)

theorem ae_posDef_realGaussianRows_gram (rows n : ℕ) (h : n ≤ rows) :
    ∀ᵐ X ∂(A4Research.standardGaussianRows rows n),
      ((Matrix.of X).conjTranspose * Matrix.of X).PosDef := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [ae_det_leadingMinor_ne_zero rows n h (gaussianReal 0 1)] with X hX
  exact Matrix.PosDef.conjTranspose_mul_self (Matrix.of X)
    (injective_mulVec_of_det_leadingMinor_ne_zero h (Matrix.of X) hX)

theorem realGaussianPairGramCoordinates_embedding {n a b : ℕ}
    (p : RealGaussianPairSource n a b) :
    realGaussianPairGramCoordinates (realGaussianPairEmbedding p) =
      (hermitianCoordinateProjection (A4Research.standardGaussianGram p.1),
        hermitianCoordinateProjection (A4Research.standardGaussianGram p.2)) := by
  apply Prod.ext
  · exact embeddedRealHalfGramCoordinates_embedding (Matrix.of p.1)
  · exact embeddedRealHalfGramCoordinates_embedding (Matrix.of p.2)

theorem map_complex_squaredGSV_symmetric_statistic
    {n a b : ℕ} {gamma : Type} [MeasurableSpace gamma]
    (F : (Fin n → ℝ) → gamma) (hF : Measurable F) :
    (edelmanSuttonGaussianPairLaw n a b 2).map
      (F ∘ edelmanSuttonSquaredGSVCoordinates n a b 2) =
      ((complexGaussianGramCoordinateLaw (n + a) n).prod
        (complexGaussianGramCoordinateLaw (n + b) n)).map
        (F ∘ canonicalHermitianSpectrum ∘ betaMatrixJacobiCoordinates) := by
  have hobs : Measurable (F ∘ canonicalHermitianSpectrum ∘
      (betaMatrixJacobiCoordinates :
        HermitianCoordinates n ℂ × HermitianCoordinates n ℂ → _)) :=
    (hF.comp measurable_canonicalHermitianSpectrum).comp
      (measurable_betaMatrixJacobiCoordinates_complex n)
  rw [← map_complexGaussianPairGramCoordinates,
    Measure.map_map hobs
      (measurable_complexGaussianPairGramCoordinates n a b)]
  apply congrArg (fun f ↦ (edelmanSuttonGaussianPairLaw n a b 2).map f)
  funext omega
  exact congrArg F (canonicalHermitianSpectrum_complexGaussianPair 2 omega).symm

theorem map_real_squaredGSV_symmetric_statistic
    {n a b : ℕ} {gamma : Type} [MeasurableSpace gamma]
    (F : (Fin n → ℝ) → gamma) (hF : Measurable F) (hsym : IsA2SymmetricTest F) :
    (edelmanSuttonGaussianPairLaw n a b 1).map
      (F ∘ edelmanSuttonSquaredGSVCoordinates n a b 1) =
      ((realGaussianGramCoordinateLaw (n + a) n).prod
        (realGaussianGramCoordinateLaw (n + b) n)).map
        (F ∘ canonicalHermitianSpectrum ∘ betaMatrixJacobiCoordinates) := by
  have hobs : Measurable (F ∘ canonicalHermitianSpectrum ∘
      (betaMatrixJacobiCoordinates :
        HermitianCoordinates n ℝ × HermitianCoordinates n ℝ → _)) :=
    (hF.comp measurable_canonicalHermitianSpectrum).comp
      (measurable_betaMatrixJacobiCoordinates_real n)
  rw [← map_realGaussianPairGramCoordinates,
    Measure.map_map hobs (measurable_realGaussianPairGramCoordinates n a b),
    edelmanSuttonGaussianPairLaw_one_eq_map_realSource,
    Measure.map_map (hF.comp (measurable_edelmanSuttonSquaredGSVCoordinates n a b 1))
      (measurable_realGaussianPairEmbedding n a b),
    Measure.map_map (hobs.comp (measurable_realGaussianPairGramCoordinates n a b))
      (measurable_realGaussianPairEmbedding n a b)]
  apply Measure.map_congr
  filter_upwards
    [Measure.quasiMeasurePreserving_fst.ae
      (ae_posDef_realGaussianRows_gram (n + a) n (Nat.le_add_right n a)),
      Measure.quasiMeasurePreserving_snd.ae
      (ae_posDef_realGaussianRows_gram (n + b) n (Nat.le_add_right n b))] with p hX hY
  change F (edelmanSuttonSquaredGSVCoordinates n a b 1 (realGaussianPairEmbedding p)) =
    F (canonicalHermitianSpectrum (betaMatrixJacobiCoordinates
      (realGaussianPairGramCoordinates (realGaussianPairEmbedding p))))
  rw [realGaussianPairGramCoordinates_embedding]
  exact canonicalHermitianSpectrum_realGaussianPair_symmetric_test F hsym
    (Matrix.of p.1) (Matrix.of p.2) hX hY

end A3Research
