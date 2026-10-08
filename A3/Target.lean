import A3.Definitions
open scoped BigOperators MatrixOrder
open MeasureTheory
noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense

open LogdetLean.GramHafnian.LocalAnticoncentration
local instance edelmanSuttonRealMatrixMeasurableSpace
    (rows n : Type*) : MeasurableSpace (Matrix rows n ℝ) := by
  unfold Matrix
  infer_instance

/-! ## Literal Gaussian pair and generalized singular values -/

/-- The paper sample space: matrices with `(n+a) x n` and `(n+b) x n`
entries.  A common complex carrier lets the literal real (`beta=1`) and
complex (`beta=2`) cases inhabit the same measurable space. -/
abbrev EdelmanSuttonGaussianPair (n a b : ℕ) :=
  Matrix (Fin (n + a)) (Fin n) ℂ ×
    Matrix (Fin (n + b)) (Fin n) ℂ

/-- Coordinatewise embedding of a real matrix in the common complex carrier. -/
def edelmanSuttonRealMatrixEmbedding (rows n : ℕ) :
    Matrix (Fin rows) (Fin n) ℝ → Matrix (Fin rows) (Fin n) ℂ :=
  fun X i j ↦ (X i j : ℂ)

/-- Iid standard real Gaussian matrix, embedded coordinatewise in `ℂ`. -/
def edelmanSuttonRealGaussianMatrixLaw (rows n : ℕ) :
    Measure (Matrix (Fin rows) (Fin n) ℂ) :=
  Measure.map (edelmanSuttonRealMatrixEmbedding rows n)
    (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure n)

/-- Literal one-matrix source law.  On the only values admitted by A3 it is
real iid Gaussian for `beta=1` and standard circular complex iid Gaussian for
`beta=2`. -/
def edelmanSuttonGaussianMatrixLaw (rows n : ℕ) (beta : ℝ) :
    Measure (Matrix (Fin rows) (Fin n) ℂ) :=
  if beta = 1 then
    edelmanSuttonRealGaussianMatrixLaw rows n
  else
    standardComplexGaussianRectangularMeasure rows n

/-- Independent literal Gaussian matrices of paper dimensions
`(n+a) x n` and `(n+b) x n`. -/
def edelmanSuttonGaussianPairLaw (n a b : ℕ) (beta : ℝ) :
    Measure (EdelmanSuttonGaussianPair n a b) :=
  (edelmanSuttonGaussianMatrixLaw (n + a) n beta).prod
    (edelmanSuttonGaussianMatrixLaw (n + b) n beta)

theorem edelmanSuttonGaussianPairLaw_beta_one (n a b : ℕ) :
    edelmanSuttonGaussianPairLaw n a b 1 =
      (edelmanSuttonRealGaussianMatrixLaw (n + a) n).prod
        (edelmanSuttonRealGaussianMatrixLaw (n + b) n) := by
  simp [edelmanSuttonGaussianPairLaw, edelmanSuttonGaussianMatrixLaw]

theorem edelmanSuttonGaussianPairLaw_beta_two (n a b : ℕ) :
    edelmanSuttonGaussianPairLaw n a b 2 =
      (standardComplexGaussianRectangularMeasure (n + a) n).prod
        (standardComplexGaussianRectangularMeasure (n + b) n) := by
  norm_num [edelmanSuttonGaussianPairLaw,
    edelmanSuttonGaussianMatrixLaw]

/-- Gram matrix of the first Gaussian matrix. -/
def edelmanSuttonFirstGram {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.conjTranspose omega.1 * omega.1

/-- Gram matrix of the second Gaussian matrix. -/
def edelmanSuttonSecondGram {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.conjTranspose omega.2 * omega.2

/-- Positive square root of the sum of the two Gram matrices. -/
def edelmanSuttonTotalGramSqrt {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.sqrt (edelmanSuttonFirstGram omega + edelmanSuttonSecondGram omega)

/-- Hermitian representative of the squared generalized singular-value
problem: `S⁻¹ (N₁ᴴN₁) (S⁻¹)ᴴ`, where
`S=(N₁ᴴN₁+N₂ᴴN₂)^(1/2)`. -/
def edelmanSuttonJacobiMatrix {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    Matrix (Fin n) (Fin n) ℂ :=
  (edelmanSuttonTotalGramSqrt omega)⁻¹ *
    edelmanSuttonFirstGram omega *
      Matrix.conjTranspose ((edelmanSuttonTotalGramSqrt omega)⁻¹)

theorem edelmanSuttonJacobiMatrix_isHermitian
    {n a b : ℕ} (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonJacobiMatrix omega).IsHermitian := by
  change (((edelmanSuttonTotalGramSqrt omega)⁻¹ *
    (Matrix.conjTranspose omega.1 * omega.1) *
      Matrix.conjTranspose ((edelmanSuttonTotalGramSqrt omega)⁻¹)).IsHermitian)
  exact Matrix.isHermitian_mul_mul_conjTranspose _
    (Matrix.isHermitian_conjTranspose_mul_self omega.1)

/-- The paper's literal generalized singular value `c_i`.  Its square is the
Jacobi coordinate appearing in Proposition 1.2. -/
def edelmanSutton_c_i (n a b : ℕ) (beta : ℝ)
    (omega : EdelmanSuttonGaussianPair n a b) (i : Fin n) : ℝ :=
  Real.sqrt ((edelmanSuttonJacobiMatrix_isHermitian omega).eigenvalues i)

/-- A concrete measurable-coordinate candidate for the squared generalized
singular values.  Mathlib's Hermitian eigenvalue API chooses a canonical
ordering, so this vector is used only through permutation-invariant tests. -/
def edelmanSuttonSquaredGSVCoordinates (n a b : ℕ) (beta : ℝ) :
    EdelmanSuttonGaussianPair n a b → (Fin n → ℝ) :=
  fun omega i ↦ (edelmanSutton_c_i n a b beta omega i) ^ 2

/-! ## The sole approved A3 atom -/

/-- Source-faithful interface for Edelman--Sutton Proposition 1.2.

The source theorem gives an unordered collection of squared generalized
singular values.  Consequently this contract does **not** equate Mathlib's
canonically ordered eigenvalue vector with the beta-Jacobi measure on the full
unordered cube.  It records measurability of the chosen coordinates and the
law only after arbitrary measurable permutation-invariant tests.

The `measurable_squaredGSV` field is an explicit elementary interface
extension: the literature proposition gives the distributional statement,
whereas this Lean development also needs measurability of Mathlib's selected
Hermitian-eigenvalue coordinates in order to compose maps.  No suitable
measurability theorem for this selector is currently available in Mathlib.
Collision nullity is *not* a field: it is derived below from this symmetric
test law and the internally proved nullity of the beta-Jacobi collision set. -/
structure EdelmanSuttonProposition12SymmetricContract
    (n a b : ℕ) (beta : ℝ) : Prop where
  measurable_squaredGSV :
    Measurable (edelmanSuttonSquaredGSVCoordinates n a b beta)
  symmetric_test_law :
    ∀ {γ : Type} [MeasurableSpace γ]
      (F : (Fin n → ℝ) → γ),
      Measurable F →
      IsA2SymmetricTest F →
      Measure.map (F ∘ edelmanSuttonSquaredGSVCoordinates n a b beta)
          (edelmanSuttonGaussianPairLaw n a b beta) =
        Measure.map F
          (betaJacobiProbabilityMeasure n (a : ℝ) (b : ℝ) beta)

abbrev A3OriginalTarget :=
  ∀
    (n a b : ℕ) (beta : ℝ)
    (hn : 1 ≤ n)
    (hbeta : beta = 1 ∨ beta = 2),
    EdelmanSuttonProposition12SymmetricContract n a b beta

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
