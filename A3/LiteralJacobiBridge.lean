import A3.GaussianPairGramCoordinates
import A3.RealComplexSpectrumBridge

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace A3Research

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem betaMatrixJacobiCoordinates_complexGaussianPair {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    betaMatrixJacobiCoordinates (complexGaussianPairGramCoordinates omega) =
      hermitianCoordinateProjection (edelmanSuttonJacobiMatrix omega) := by
  unfold betaMatrixJacobiCoordinates complexGaussianPairGramCoordinates
  change hermitianCoordinateProjection
    ((CFC.sqrt (hermitianMatrixOfCoordinates
        (hermitianCoordinateProjection (edelmanSuttonFirstGram omega)) +
      hermitianMatrixOfCoordinates
        (hermitianCoordinateProjection (edelmanSuttonSecondGram omega))))⁻¹ *
      hermitianMatrixOfCoordinates (hermitianCoordinateProjection
        (edelmanSuttonFirstGram omega)) *
      ((CFC.sqrt (hermitianMatrixOfCoordinates
        (hermitianCoordinateProjection (edelmanSuttonFirstGram omega)) +
        hermitianMatrixOfCoordinates
          (hermitianCoordinateProjection (edelmanSuttonSecondGram omega))))⁻¹).conjTranspose) = _
  rw [hermitianMatrixOfCoordinates_projection _
    (a3_edelmanSuttonFirstGram_posSemidef omega).isHermitian,
    hermitianMatrixOfCoordinates_projection _
    (a3_edelmanSuttonSecondGram_posSemidef omega).isHermitian]
  rfl

theorem canonicalHermitianSpectrum_complexGaussianPair {n a b : ℕ}
    (beta : ℝ) (omega : EdelmanSuttonGaussianPair n a b) :
    canonicalHermitianSpectrum
      (betaMatrixJacobiCoordinates (complexGaussianPairGramCoordinates omega)) =
      edelmanSuttonSquaredGSVCoordinates n a b beta omega := by
  rw [betaMatrixJacobiCoordinates_complexGaussianPair,
    canonicalHermitianSpectrum_projection _ (edelmanSuttonJacobiMatrix_isHermitian omega),
    edelmanSuttonSquaredGSVCoordinates_eq_eigenvalues]

theorem standardGaussianGram_eq_half_realGram {rows n : ℕ}
    (X : Matrix (Fin rows) (Fin n) ℝ) :
    A4Research.standardGaussianGram X = (1 / 2 : ℝ) • (X.conjTranspose * X) := by
  ext i j
  simp [A4Research.standardGaussianGram, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, div_eq_mul_inv, mul_comm]

theorem realEmbedding_gram {rows n : ℕ} (X : Matrix (Fin rows) (Fin n) ℝ) :
    (edelmanSuttonRealMatrixEmbedding rows n X).conjTranspose *
      edelmanSuttonRealMatrixEmbedding rows n X =
      realMatrixComplexEmbedding (X.conjTranspose * X) := by
  change (realMatrixComplexEmbedding X).conjTranspose * realMatrixComplexEmbedding X = _
  rw [← realMatrixComplexEmbedding_conjTranspose, ← realMatrixComplexEmbedding_mul]

theorem realCoordinatesEmbedding_projection {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    realHermitianCoordinatesEmbedding (hermitianCoordinateProjection A) =
      hermitianCoordinateProjection (realMatrixComplexEmbedding A) := by
  apply Prod.ext <;> funext i <;>
    simp [realHermitianCoordinatesEmbedding, hermitianCoordinateProjection,
      realMatrixComplexEmbedding]

theorem realEmbedding_gram_coordinates {rows n : ℕ}
    (X : Matrix (Fin rows) (Fin n) ℝ) :
    hermitianCoordinateProjection
      ((edelmanSuttonRealMatrixEmbedding rows n X).conjTranspose *
        edelmanSuttonRealMatrixEmbedding rows n X) =
      (2 : ℝ) • realHermitianCoordinatesEmbedding
        (hermitianCoordinateProjection (A4Research.standardGaussianGram X)) := by
  rw [realCoordinatesEmbedding_projection, realEmbedding_gram,
    standardGaussianGram_eq_half_realGram, realMatrixComplexEmbedding_smul]
  change hermitianCoordinateProjection (realMatrixComplexEmbedding (X.conjTranspose * X)) =
    (2 : ℝ) • hermitianCoordinateProjection
      ((1 / 2 : ℝ) • realMatrixComplexEmbedding (X.conjTranspose * X))
  have hproj (r : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
      hermitianCoordinateProjection (r • H) = r • hermitianCoordinateProjection H :=
    (hermitianCoordinateProjectionLinearMap n ℂ).map_smul r H
  rw [hproj, smul_smul]
  norm_num

theorem canonicalHermitianSpectrum_realGaussianPair_symmetric_test
    {n a b : ℕ} {gamma : Type} (F : (Fin n → ℝ) → gamma) (hF : IsA2SymmetricTest F)
    (X : Matrix (Fin (n + a)) (Fin n) ℝ) (Y : Matrix (Fin (n + b)) (Fin n) ℝ)
    (hX : (X.conjTranspose * X).PosDef) (hY : (Y.conjTranspose * Y).PosDef) :
    F (edelmanSuttonSquaredGSVCoordinates n a b 1
      (edelmanSuttonRealMatrixEmbedding (n + a) n X,
        edelmanSuttonRealMatrixEmbedding (n + b) n Y)) =
      F (canonicalHermitianSpectrum (betaMatrixJacobiCoordinates
        (hermitianCoordinateProjection (A4Research.standardGaussianGram X),
          hermitianCoordinateProjection (A4Research.standardGaussianGram Y)))) := by
  let p : HermitianCoordinates n ℝ × HermitianCoordinates n ℝ :=
    (hermitianCoordinateProjection (A4Research.standardGaussianGram X),
      hermitianCoordinateProjection (A4Research.standardGaussianGram Y))
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hpX : (A4Research.standardGaussianGram X).PosDef := by
    rw [standardGaussianGram_eq_half_realGram]
    exact hX.smul hhalf
  have hpY : (A4Research.standardGaussianGram Y).PosDef := by
    rw [standardGaussianGram_eq_half_realGram]
    exact hY.smul hhalf
  have hsum : (hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2).PosDef := by
    change (hermitianMatrixOfCoordinates
      (hermitianCoordinateProjection (A4Research.standardGaussianGram X)) +
      hermitianMatrixOfCoordinates
      (hermitianCoordinateProjection (A4Research.standardGaussianGram Y))).PosDef
    rw [hermitianMatrixOfCoordinates_projection _ hpX.isHermitian,
      hermitianMatrixOfCoordinates_projection _ hpY.isHermitian]
    exact hpX.add hpY
  let pc : HermitianCoordinates n ℂ × HermitianCoordinates n ℂ :=
    (realHermitianCoordinatesEmbedding p.1, realHermitianCoordinatesEmbedding p.2)
  have hsumc : (hermitianMatrixOfCoordinates pc.1 + hermitianMatrixOfCoordinates pc.2).PosDef := by
    rw [hermitianMatrixOfCoordinates_realEmbedding,
      hermitianMatrixOfCoordinates_realEmbedding, ← realMatrixComplexEmbedding_add]
    exact realMatrixComplexEmbedding_posDef hsum
  have hpair : complexGaussianPairGramCoordinates
      (edelmanSuttonRealMatrixEmbedding (n + a) n X,
        edelmanSuttonRealMatrixEmbedding (n + b) n Y) =
        ((2 : ℝ) • pc.1, (2 : ℝ) • pc.2) := by
    apply Prod.ext
    · exact realEmbedding_gram_coordinates X
    · exact realEmbedding_gram_coordinates Y
  change F (edelmanSuttonSquaredGSVCoordinates n a b 1
    (edelmanSuttonRealMatrixEmbedding (n + a) n X,
      edelmanSuttonRealMatrixEmbedding (n + b) n Y)) =
    F (canonicalHermitianSpectrum (betaMatrixJacobiCoordinates p))
  rw [← canonicalHermitianSpectrum_complexGaussianPair, hpair,
    betaMatrixJacobiCoordinates_commonScale_complex pc hsumc (c := 2) (by norm_num)]
  change F (canonicalHermitianSpectrum (betaMatrixJacobiCoordinates
    (realHermitianCoordinatesEmbedding p.1, realHermitianCoordinatesEmbedding p.2))) = _
  rw [betaMatrixJacobiCoordinates_realEmbedding p hsum]
  exact symmetric_test_canonicalHermitianSpectrum_realEmbedding F hF _

end A3Research
