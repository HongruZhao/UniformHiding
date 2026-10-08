import A3.RealGaussianBartlettLaw
import A3.ComplexBartlettLaplace
import A3.GSVAESupport

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable section
namespace A3Research

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def complexGaussianPairGramCoordinates {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    HermitianCoordinates n ℂ × HermitianCoordinates n ℂ :=
  (hermitianCoordinateProjection (edelmanSuttonFirstGram omega),
    hermitianCoordinateProjection (edelmanSuttonSecondGram omega))

theorem measurable_complexGaussianPairGramCoordinates (n a b : ℕ) :
    Measurable (complexGaussianPairGramCoordinates : EdelmanSuttonGaussianPair n a b → _) :=
  ((measurable_complexGaussianGramCoordinates (n + a) n).comp measurable_fst).prodMk
    ((measurable_complexGaussianGramCoordinates (n + b) n).comp measurable_snd)

theorem map_complexGaussianPairGramCoordinates (n a b : ℕ) :
    (edelmanSuttonGaussianPairLaw n a b 2).map complexGaussianPairGramCoordinates =
      (complexGaussianGramCoordinateLaw (n + a) n).prod
        (complexGaussianGramCoordinateLaw (n + b) n) := by
  have htwo : (2 : ℝ) ≠ 1 := by norm_num
  simp only [edelmanSuttonGaussianPairLaw, edelmanSuttonGaussianMatrixLaw, if_neg htwo,
    complexGaussianGramCoordinateLaw]
  exact (Measure.map_prod_map _ _
    (measurable_complexGaussianGramCoordinates (n + a) n)
    (measurable_complexGaussianGramCoordinates (n + b) n)).symm

def embeddedRealHalfGramCoordinates {rows n : ℕ} (X : Matrix (Fin rows) (Fin n) ℂ) :
    HermitianCoordinates n ℝ :=
  hermitianCoordinateProjection ((1 / 2 : ℝ) • (X.conjTranspose * X).map Complex.re)

theorem measurable_embeddedRealHalfGramCoordinates (rows n : ℕ) :
    Measurable (embeddedRealHalfGramCoordinates : Matrix (Fin rows) (Fin n) ℂ → _) := by
  unfold embeddedRealHalfGramCoordinates hermitianCoordinateProjection
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, dotProduct]
    fun_prop
  · apply measurable_pi_lambda
    intro ij
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, dotProduct]
    fun_prop

theorem embeddedRealHalfGramCoordinates_embedding {rows n : ℕ}
    (X : Matrix (Fin rows) (Fin n) ℝ) :
    embeddedRealHalfGramCoordinates (edelmanSuttonRealMatrixEmbedding rows n X) =
      hermitianCoordinateProjection (A4Research.standardGaussianGram X) := by
  have hg : (1 / 2 : ℝ) •
      ((edelmanSuttonRealMatrixEmbedding rows n X).conjTranspose *
        edelmanSuttonRealMatrixEmbedding rows n X).map Complex.re =
        A4Research.standardGaussianGram X := by
    ext i j
    simp [edelmanSuttonRealMatrixEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Matrix.map_apply, A4Research.standardGaussianGram,
      Complex.re_sum, mul_comm, div_eq_mul_inv]
  exact congrArg hermitianCoordinateProjection hg

theorem map_embeddedRealHalfGramCoordinates (rows n : ℕ) :
    (edelmanSuttonRealGaussianMatrixLaw rows n).map embeddedRealHalfGramCoordinates =
      realGaussianGramCoordinateLaw rows n := by
  unfold edelmanSuttonRealGaussianMatrixLaw realGaussianGramCoordinateLaw
  rw [Measure.map_map (measurable_embeddedRealHalfGramCoordinates rows n)
    (a3_measurable_edelmanSuttonRealMatrixEmbedding rows n)]
  have heq : embeddedRealHalfGramCoordinates ∘ edelmanSuttonRealMatrixEmbedding rows n =
      fun X : Fin rows → Fin n → ℝ ↦
        hermitianCoordinateProjection (A4Research.standardGaussianGram X) := by
    funext X
    exact embeddedRealHalfGramCoordinates_embedding X
  rw [heq]
  rfl

def realGaussianPairGramCoordinates {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    HermitianCoordinates n ℝ × HermitianCoordinates n ℝ :=
  (embeddedRealHalfGramCoordinates omega.1, embeddedRealHalfGramCoordinates omega.2)

theorem measurable_realGaussianPairGramCoordinates (n a b : ℕ) :
    Measurable (realGaussianPairGramCoordinates : EdelmanSuttonGaussianPair n a b → _) :=
  ((measurable_embeddedRealHalfGramCoordinates (n + a) n).comp measurable_fst).prodMk
    ((measurable_embeddedRealHalfGramCoordinates (n + b) n).comp measurable_snd)

theorem map_realGaussianPairGramCoordinates (n a b : ℕ) :
    (edelmanSuttonGaussianPairLaw n a b 1).map realGaussianPairGramCoordinates =
      (realGaussianGramCoordinateLaw (n + a) n).prod
        (realGaussianGramCoordinateLaw (n + b) n) := by
  simp only [edelmanSuttonGaussianPairLaw, edelmanSuttonGaussianMatrixLaw, ite_true]
  change ((edelmanSuttonRealGaussianMatrixLaw (n + a) n).prod
    (edelmanSuttonRealGaussianMatrixLaw (n + b) n)).map
      (Prod.map (@embeddedRealHalfGramCoordinates (n + a) n)
        (@embeddedRealHalfGramCoordinates (n + b) n)) = _
  rw [← Measure.map_prod_map _ _
    (measurable_embeddedRealHalfGramCoordinates (n + a) n)
    (measurable_embeddedRealHalfGramCoordinates (n + b) n),
    map_embeddedRealHalfGramCoordinates, map_embeddedRealHalfGramCoordinates]

end A3Research
