import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.BoundedPreservedSScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.GenericHalfGaussianFullRank
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.IntegratedCoupledScore
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.PastCofactorBridge
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedCofactorWeights
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.RegularizedInverseMomentLimit

/-!
# A generic preserved-coordinate inverse-variance endpoint

This file formalizes the reusable theorem in the successor matrix-law article before
the hafnian cofactor specialization.  A measurable vector `c(S)` may be any
function of the preserved complex transpose-Gram coordinate.  The probability
space is the literal split-real realization of a standard circular complex
Gaussian matrix.

The proof uses the already kernel-checked bounded preserved-coordinate score,
finite Hermitian rank-one coordinate assembly, Schur order, matrix
Cauchy--Schwarz, and the monotone/Fatou regularization-removal theorem.  It
introduces no new probabilistic or aggregate theorem axiom.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder ENNReal

namespace LogdetLean.GramHafnian.MatrixLawEndpoints

noncomputable section

open Wishart

/-- The vector selected by a measurable rule from the preserved transpose
Gram coordinate. -/
def preservedCoordinateVector {k m : ℕ}
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : Fin m → ℂ :=
  c (preservedSCoordinate R)

/-- The coordinate called `S=AᵀA` in the article is literally the
preserved score coordinate used below. -/
theorem preservedSCoordinate_eq_transposeGramMatrix_complexOfRealMatrix
    {k m : ℕ} (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedSCoordinate R =
      transposeGramMatrix (complexOfRealMatrix R) := by
  unfold preservedSCoordinate
  exact sCoordinateOfRealGram_realWishartGram R

/-- `W=c(S)^*c(S)` in the real scalar convention used by the article. -/
def preservedCoordinateW {k m : ℕ}
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  vectorNormSq (preservedCoordinateVector c R)

/-- `V=c(S)^*Q c(S)`, where `Q=A^*A` and `A` is the complex matrix encoded
by the split-real matrix `R`. -/
def preservedCoordinateV {k m : ℕ}
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  quadraticFormReal
    (hermitianGram (complexOfRealMatrix R))
    (preservedCoordinateVector c R)

/-- The coupled inverse-Schur quadratic `Xi` produced by the real Wishart
score. -/
def preservedCoordinateXi {k m : ℕ}
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  quadraticFormReal
    (Matrix.toBlocks₁₁
      (coupledGramKernel (complexOfRealMatrix R))⁻¹)
    (preservedCoordinateVector c R)

/-- The regularized inverse-square weight `(W+δ)^(-2)`. -/
def preservedCoordinateRegularizedWeight {k m : ℕ}
    (δ : ℝ) (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  (preservedCoordinateW c R + δ)⁻¹ ^ 2

/-- The same regularized weight, before composition with the preserved
coordinate. -/
def preservedCoordinateRegularizedWeightOnS {m : ℕ}
    (δ : ℝ) (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (S : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  (vectorNormSq (c S) + δ)⁻¹ ^ 2

@[simp] theorem preservedCoordinateRegularizedWeightOnS_comp
    {k m : ℕ} (δ : ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateRegularizedWeightOnS δ c
        (preservedSCoordinate R) =
      preservedCoordinateRegularizedWeight δ c R := by
  rfl

theorem vectorNormSq_eq_sum_normSq {m : ℕ} (v : Fin m → ℂ) :
    vectorNormSq v = ∑ i, Complex.normSq (v i) := by
  unfold vectorNormSq dotProduct
  simp [Complex.normSq_apply, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_sum]

theorem vectorNormSq_nonneg {m : ℕ} (v : Fin m → ℂ) :
    0 ≤ vectorNormSq v := by
  rw [vectorNormSq_eq_sum_normSq]
  exact Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg (v i)

theorem normSq_le_vectorNormSq {m : ℕ} (v : Fin m → ℂ)
    (i : Fin m) :
    Complex.normSq (v i) ≤ vectorNormSq v := by
  rw [vectorNormSq_eq_sum_normSq]
  exact Finset.single_le_sum
    (fun j _ ↦ Complex.normSq_nonneg (v j)) (Finset.mem_univ i)

theorem abs_re_rankOneCoordinate_div_two_le_vectorNormSq {m : ℕ}
    (v : Fin m → ℂ) (i j : Fin m) :
    |((v i * star (v j)).re / 2)| ≤ vectorNormSq v := by
  let W := vectorNormSq v
  have hWi : Complex.normSq (v i) ≤ W := normSq_le_vectorNormSq v i
  have hWj : Complex.normSq (v j) ≤ W := normSq_le_vectorNormSq v j
  have hW : 0 ≤ W := vectorNormSq_nonneg v
  have ham : 2 * (‖v i‖ * ‖v j‖) ≤
      Complex.normSq (v i) + Complex.normSq (v j) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖v i‖ - ‖v j‖)]
  have hprod : ‖v i‖ * ‖v j‖ ≤ W := by nlinarith
  calc
    |((v i * star (v j)).re / 2)| = |(v i * star (v j)).re| / 2 := by
      rw [abs_div]
      norm_num
    _ ≤ ‖v i * star (v j)‖ / 2 := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ = (‖v i‖ * ‖v j‖) / 2 := by
      rw [Complex.norm_mul, norm_star]
    _ ≤ W := by nlinarith [norm_nonneg (v i), norm_nonneg (v j)]

theorem abs_im_rankOneCoordinate_div_two_le_vectorNormSq {m : ℕ}
    (v : Fin m → ℂ) (i j : Fin m) :
    |((v i * star (v j)).im / 2)| ≤ vectorNormSq v := by
  let W := vectorNormSq v
  have hWi : Complex.normSq (v i) ≤ W := normSq_le_vectorNormSq v i
  have hWj : Complex.normSq (v j) ≤ W := normSq_le_vectorNormSq v j
  have hW : 0 ≤ W := vectorNormSq_nonneg v
  have ham : 2 * (‖v i‖ * ‖v j‖) ≤
      Complex.normSq (v i) + Complex.normSq (v j) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖v i‖ - ‖v j‖)]
  have hprod : ‖v i‖ * ‖v j‖ ≤ W := by nlinarith
  calc
    |((v i * star (v j)).im / 2)| = |(v i * star (v j)).im| / 2 := by
      rw [abs_div]
      norm_num
    _ ≤ ‖v i * star (v j)‖ / 2 := by
      gcongr
      exact Complex.abs_im_le_norm _
    _ = (‖v i‖ * ‖v j‖) / 2 := by
      rw [Complex.norm_mul, norm_star]
    _ ≤ W := by nlinarith [norm_nonneg (v i), norm_nonneg (v j)]

theorem vectorEnergy_div_add_sq_le_inv {W δ : ℝ}
    (hW : 0 ≤ W) (hδ : 0 < δ) :
    W / (W + δ) ^ 2 ≤ δ⁻¹ := by
  have hden : 0 < W + δ := add_pos_of_nonneg_of_pos hW hδ
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) hδ).2
  nlinarith [sq_nonneg W, sq_nonneg δ]

/-- Real coordinate of the regularized rank-one direction, as a function of
the preserved coordinate alone. -/
def preservedCoordinateRealWeight {m : ℕ} (δ : ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (i j : Fin m) (S : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  preservedCoordinateRegularizedWeightOnS δ c S *
    ((c S i * star (c S j)).re / 2)

/-- Imaginary coordinate of the regularized rank-one direction. -/
def preservedCoordinateImagWeight {m : ℕ} (δ : ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (i j : Fin m) (S : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  preservedCoordinateRegularizedWeightOnS δ c S *
    ((c S i * star (c S j)).im / 2)

theorem measurable_preservedCoordinateRegularizedWeightOnS {m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) (δ : ℝ) :
    Measurable (preservedCoordinateRegularizedWeightOnS δ c) := by
  unfold preservedCoordinateRegularizedWeightOnS vectorNormSq dotProduct
  fun_prop

theorem measurable_preservedCoordinateRealWeight {m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) (δ : ℝ) (i j : Fin m) :
    Measurable (preservedCoordinateRealWeight δ c i j) := by
  unfold preservedCoordinateRealWeight
  have hi : Measurable (fun S ↦ c S i) :=
    (measurable_pi_apply i).comp hc
  have hj : Measurable (fun S ↦ c S j) :=
    (measurable_pi_apply j).comp hc
  exact (measurable_preservedCoordinateRegularizedWeightOnS hc δ).mul
    ((Complex.measurable_re.comp
      (hi.mul (continuous_star.measurable.comp hj))).div_const 2)

theorem measurable_preservedCoordinateImagWeight {m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) (δ : ℝ) (i j : Fin m) :
    Measurable (preservedCoordinateImagWeight δ c i j) := by
  unfold preservedCoordinateImagWeight
  have hi : Measurable (fun S ↦ c S i) :=
    (measurable_pi_apply i).comp hc
  have hj : Measurable (fun S ↦ c S j) :=
    (measurable_pi_apply j).comp hc
  exact (measurable_preservedCoordinateRegularizedWeightOnS hc δ).mul
    ((Complex.measurable_im.comp
      (hi.mul (continuous_star.measurable.comp hj))).div_const 2)

theorem abs_preservedCoordinateRealWeight_le {m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    {δ : ℝ} (hδ : 0 < δ) (i j : Fin m)
    (S : Matrix (Fin m) (Fin m) ℂ) :
    |preservedCoordinateRealWeight δ c i j S| ≤ δ⁻¹ := by
  let W := vectorNormSq (c S)
  have hW : 0 ≤ W := vectorNormSq_nonneg (c S)
  have hcoord := abs_re_rankOneCoordinate_div_two_le_vectorNormSq (c S) i j
  have hweight : 0 ≤ preservedCoordinateRegularizedWeightOnS δ c S := by
    unfold preservedCoordinateRegularizedWeightOnS
    positivity
  unfold preservedCoordinateRealWeight
  rw [abs_mul, abs_of_nonneg hweight]
  calc
    preservedCoordinateRegularizedWeightOnS δ c S *
        |((c S i * star (c S j)).re / 2)| ≤
        preservedCoordinateRegularizedWeightOnS δ c S * W :=
      mul_le_mul_of_nonneg_left hcoord hweight
    _ = W / (W + δ) ^ 2 := by
      unfold preservedCoordinateRegularizedWeightOnS
      rw [inv_pow, div_eq_mul_inv]
      ring
    _ ≤ δ⁻¹ := vectorEnergy_div_add_sq_le_inv hW hδ

theorem abs_preservedCoordinateImagWeight_le {m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    {δ : ℝ} (hδ : 0 < δ) (i j : Fin m)
    (S : Matrix (Fin m) (Fin m) ℂ) :
    |preservedCoordinateImagWeight δ c i j S| ≤ δ⁻¹ := by
  let W := vectorNormSq (c S)
  have hW : 0 ≤ W := vectorNormSq_nonneg (c S)
  have hcoord := abs_im_rankOneCoordinate_div_two_le_vectorNormSq (c S) i j
  have hweight : 0 ≤ preservedCoordinateRegularizedWeightOnS δ c S := by
    unfold preservedCoordinateRegularizedWeightOnS
    positivity
  unfold preservedCoordinateImagWeight
  rw [abs_mul, abs_of_nonneg hweight]
  calc
    preservedCoordinateRegularizedWeightOnS δ c S *
        |((c S i * star (c S j)).im / 2)| ≤
        preservedCoordinateRegularizedWeightOnS δ c S * W :=
      mul_le_mul_of_nonneg_left hcoord hweight
    _ = W / (W + δ) ^ 2 := by
      unfold preservedCoordinateRegularizedWeightOnS
      rw [inv_pow, div_eq_mul_inv]
      ring
    _ ≤ δ⁻¹ := vectorEnergy_div_add_sq_le_inv hW hδ

@[simp] theorem rankOneRealCoordinateWeight_preservedCoordinate
    {k m : ℕ} (δ : ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (i j : Fin m) (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    rankOneRealCoordinateWeight
        (preservedCoordinateRegularizedWeight δ c)
        (preservedCoordinateVector c) i j R =
      preservedSWeight (preservedCoordinateRealWeight δ c i j) R := by
  rfl

@[simp] theorem rankOneImagCoordinateWeight_preservedCoordinate
    {k m : ℕ} (δ : ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (i j : Fin m) (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    rankOneImagCoordinateWeight
        (preservedCoordinateRegularizedWeight δ c)
        (preservedCoordinateVector c) i j R =
      preservedSWeight (preservedCoordinateImagWeight δ c i j) R := by
  rfl

theorem preservedCoordinateRegularizedWeight_mul_W
    {k m : ℕ} (δ : ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateRegularizedWeight δ c R *
        preservedCoordinateW c R =
      preservedCoordinateW c R /
        (preservedCoordinateW c R + δ) ^ 2 := by
  unfold preservedCoordinateRegularizedWeight
  rw [inv_pow, div_eq_mul_inv]
  ring

theorem preservedCoordinateRegularizedWeight_mul_Xi
    {k m : ℕ} (δ : ℝ)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateRegularizedWeight δ c R *
        preservedCoordinateXi c R =
      preservedCoordinateXi c R /
        (preservedCoordinateW c R + δ) ^ 2 := by
  unfold preservedCoordinateRegularizedWeight
  rw [inv_pow, div_eq_mul_inv]
  ring

theorem two_mul_inverseGramScoreCoefficient_preserved (k m : ℕ) :
    2 * inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) =
      (k : ℝ) - 2 * m - 1 := by
  simp only [inverseGramScoreCoefficient, Fintype.card_fin,
    Fintype.card_sum]
  push_cast
  ring

/-- Fixed real-coordinate score data for a measurable generic `c(S)`. -/
theorem preservedCoordinate_realCoordinate_score_pair
    {k m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : 2 * m + 1 < k)
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) (i j : Fin m) :
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneRealCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianRealCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m)) ∧
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneRealCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m)) ∧
    ((∫ R, rankOneRealCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianRealCoordinateDirection i j)))
        ∂halfGaussianMatrixSum k (Fin m)) =
      ∫ R, rankOneRealCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j))
        ∂halfGaussianMatrixSum k (Fin m)) := by
  simpa only [rankOneRealCoordinateWeight_preservedCoordinate] using
    (bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
      (preservedCoordinateRealWeight δ c i j)
      (measurable_preservedCoordinateRealWeight hc δ i j)
      δ⁻¹ (abs_preservedCoordinateRealWeight_le hδ i j)
      (H := hermitianRealCoordinateDirection i j)
      (hermitianRealCoordinateDirection_isHermitian i j)
      (by simpa [two_mul] using hgap))

/-- Fixed imaginary-coordinate score data for a measurable generic `c(S)`. -/
theorem preservedCoordinate_imagCoordinate_score_pair
    {k m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : 2 * m + 1 < k)
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) (i j : Fin m) :
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneImagCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianImagCoordinateDirection i j))))
      (halfGaussianMatrixSum k (Fin m)) ∧
    Integrable (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
      rankOneImagCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
      (halfGaussianMatrixSum k (Fin m)) ∧
    ((∫ R, rankOneImagCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        (inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m) *
          Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM (hermitianImagCoordinateDirection i j)))
        ∂halfGaussianMatrixSum k (Fin m)) =
      ∫ R, rankOneImagCoordinateWeight
          (preservedCoordinateRegularizedWeight δ c)
          (preservedCoordinateVector c) i j R *
        Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j))
        ∂halfGaussianMatrixSum k (Fin m)) := by
  simpa only [rankOneImagCoordinateWeight_preservedCoordinate] using
    (bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
      (preservedCoordinateImagWeight δ c i j)
      (measurable_preservedCoordinateImagWeight hc δ i j)
      δ⁻¹ (abs_preservedCoordinateImagWeight_le hδ i j)
      (H := hermitianImagCoordinateDirection i j)
      (hermitianImagCoordinateDirection_isHermitian i j)
      (by simpa [two_mul] using hgap))

/-- Exact regularized score identity and both integrability statements for
an arbitrary measurable preserved-coordinate vector. -/
theorem preservedCoordinate_regularized_integral_data
    {k m : ℕ} (hgap : 2 * m + 1 < k)
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) (δ : ℝ) (hδ : 0 < δ) :
    Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          preservedCoordinateXi c R /
            (preservedCoordinateW c R + δ) ^ 2)
        (halfGaussianMatrixSum k (Fin m)) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          preservedCoordinateW c R /
            (preservedCoordinateW c R + δ) ^ 2)
        (halfGaussianMatrixSum k (Fin m)) ∧
      ((∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
          preservedCoordinateXi c R /
            (preservedCoordinateW c R + δ) ^ 2
          ∂halfGaussianMatrixSum k (Fin m)) =
        (((k : ℝ) - 2 * m - 1)⁻¹) *
          ∫ R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ,
            preservedCoordinateW c R /
              (preservedCoordinateW c R + δ) ^ 2
            ∂halfGaussianMatrixSum k (Fin m)) := by
  let μ := halfGaussianMatrixSum k (Fin m)
  let a := inverseGramScoreCoefficient (Fin k) (Fin m ⊕ Fin m)
  let b : ℝ := (k : ℝ) - 2 * m - 1
  have hre (i j : Fin m) :=
    preservedCoordinate_realCoordinate_score_pair hδ hgap hc i j
  have him (i j : Fin m) :=
    preservedCoordinate_imagCoordinate_score_pair hδ hgap hc i j
  have hLRe := fun i j ↦ (hre i j).1
  have hLIm := fun i j ↦ (him i j).1
  have hRRe := fun i j ↦ (hre i j).2.1
  have hRIm := fun i j ↦ (him i j).2.1
  have hscoreRe := fun i j ↦ (hre i j).2.2
  have hscoreIm := fun i j ↦ (him i j).2.2
  have hvariable :
      (∫ R, preservedCoordinateRegularizedWeight δ c R *
          (a * Matrix.trace ((realWishartGram R)⁻¹ *
            scoreDeltaM
              (hermitianRankOne (preservedCoordinateVector c R)))) ∂μ) =
        ∫ R, preservedCoordinateRegularizedWeight δ c R *
          Matrix.trace
            (scoreDeltaM
              (hermitianRankOne (preservedCoordinateVector c R))) ∂μ := by
    exact integral_variable_rankOne_score_eq_of_coordinate_scores
      μ (fun R ↦ (realWishartGram R)⁻¹)
      (preservedCoordinateRegularizedWeight δ c)
      (preservedCoordinateVector c) a
      hLRe hLIm hRRe hRIm hscoreRe hscoreIm
  have hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det := by
    exact ae_isUnit_det_realWishartGram_halfGaussianMatrixSum_generic
      k (Fin m) (by simp; omega)
  have hcoupled := integral_coupledQuadratic_eq_of_variable_rankOne_score
    μ (preservedCoordinateRegularizedWeight δ c)
      (preservedCoordinateVector c) a hfull hvariable
  have hscore :
      (∫ R, preservedCoordinateRegularizedWeight δ c R *
          (b * preservedCoordinateXi c R) ∂μ) =
        ∫ R, preservedCoordinateRegularizedWeight δ c R *
          preservedCoordinateW c R ∂μ := by
    simpa [μ, a, b, preservedCoordinateXi, preservedCoordinateW,
      two_mul_inverseGramScoreCoefficient_preserved] using hcoupled
  have hleftScore := integrable_variable_rankOne_score_left_of_coordinates
    μ (fun R ↦ (realWishartGram R)⁻¹)
      (preservedCoordinateRegularizedWeight δ c)
      (preservedCoordinateVector c) a hLRe hLIm
  have hscaled : Integrable (fun R ↦
      preservedCoordinateRegularizedWeight δ c R *
        (b * preservedCoordinateXi c R)) μ := by
    apply hleftScore.congr
    filter_upwards [hfull] with R hR
    rw [realWishartGram_inverse_rankOne_score_trace_eq_coupled
      R (preservedCoordinateVector c R) hR]
    have hab : 2 * a = b := by
      simpa [a, b] using
        two_mul_inverseGramScoreCoefficient_preserved k m
    rw [← hab]
    unfold preservedCoordinateXi
    ring
  have hb : b ≠ 0 := by
    have hkR : ((2 * m + 1 : ℕ) : ℝ) < (k : ℝ) := by
      exact_mod_cast hgap
    dsimp [b]
    push_cast at hkR
    linarith
  have hXi : Integrable
      (fun R ↦ preservedCoordinateXi c R /
        (preservedCoordinateW c R + δ) ^ 2) μ := by
    have hunscaled := hscaled.const_mul b⁻¹
    apply hunscaled.congr
    filter_upwards [] with R
    calc
      b⁻¹ * (preservedCoordinateRegularizedWeight δ c R *
          (b * preservedCoordinateXi c R)) =
          preservedCoordinateRegularizedWeight δ c R *
            preservedCoordinateXi c R := by field_simp [hb]
      _ = preservedCoordinateXi c R /
          (preservedCoordinateW c R + δ) ^ 2 :=
        preservedCoordinateRegularizedWeight_mul_Xi δ c R
  have hrightScore := integrable_variable_rankOne_score_right_of_coordinates
    μ (preservedCoordinateRegularizedWeight δ c)
      (preservedCoordinateVector c) hRRe hRIm
  have hW : Integrable
      (fun R ↦ preservedCoordinateW c R /
        (preservedCoordinateW c R + δ) ^ 2) μ := by
    apply hrightScore.congr
    filter_upwards [] with R
    rw [trace_scoreDeltaM_hermitianRankOne_eq_vectorNormSq]
    exact preservedCoordinateRegularizedWeight_mul_W δ c R
  refine ⟨?_, ?_, ?_⟩
  · simpa [μ] using hXi
  · simpa [μ] using hW
  · have hleftIntegral :
        (∫ R, preservedCoordinateRegularizedWeight δ c R *
            (b * preservedCoordinateXi c R) ∂μ) =
          b * ∫ R, preservedCoordinateXi c R /
            (preservedCoordinateW c R + δ) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with R
      rw [← preservedCoordinateRegularizedWeight_mul_Xi δ c R]
      ring
    have hrightIntegral :
        (∫ R, preservedCoordinateRegularizedWeight δ c R *
            preservedCoordinateW c R ∂μ) =
          ∫ R, preservedCoordinateW c R /
            (preservedCoordinateW c R + δ) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with R
      exact preservedCoordinateRegularizedWeight_mul_W δ c R
    rw [hleftIntegral, hrightIntegral] at hscore
    have hsolve := congrArg (fun x : ℝ ↦ b⁻¹ * x) hscore
    have hbinv : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
    change
      (∫ R, preservedCoordinateXi c R /
          (preservedCoordinateW c R + δ) ^ 2 ∂μ) =
        b⁻¹ * ∫ R, preservedCoordinateW c R /
          (preservedCoordinateW c R + δ) ^ 2 ∂μ
    calc
      (∫ R, preservedCoordinateXi c R /
          (preservedCoordinateW c R + δ) ^ 2 ∂μ) =
          (b⁻¹ * b) * ∫ R, preservedCoordinateXi c R /
            (preservedCoordinateW c R + δ) ^ 2 ∂μ := by
        rw [hbinv, one_mul]
      _ = b⁻¹ * (b * ∫ R, preservedCoordinateXi c R /
            (preservedCoordinateW c R + δ) ^ 2 ∂μ) := by ring
      _ = b⁻¹ * ∫ R, preservedCoordinateW c R /
          (preservedCoordinateW c R + δ) ^ 2 ∂μ := hsolve

/-! ## Measurability and deterministic Schur geometry -/

private theorem measurable_complex_matrix_det_comp
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {F : Ω → Matrix ι ι ℂ} (hF : Measurable F) :
    Measurable (fun ω ↦ (F ω).det) := by
  simp_rw [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ ↦
    measurable_const.mul (Finset.measurable_prod _ fun i _ ↦
      (measurable_pi_apply i).comp
        ((measurable_pi_apply (σ i)).comp hF))

private theorem measurable_complex_matrix_inv_comp
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {F : Ω → Matrix ι ι ℂ} (hF : Measurable F) :
    Measurable (fun ω ↦ (F ω)⁻¹) := by
  have hentry (i j : ι) : Measurable (fun ω ↦ F ω i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)
  have hdet : Measurable (fun ω ↦ (F ω).det) :=
    measurable_complex_matrix_det_comp hF
  have hadj : Measurable (fun ω ↦ (F ω).adjugate) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.adjugate_apply]
    apply measurable_complex_matrix_det_comp
    refine measurable_pi_lambda _ fun a ↦ measurable_pi_lambda _ fun b ↦ ?_
    by_cases ha : a = j
    · simp [ha]
    · simpa [Matrix.updateRow_apply, ha] using hentry a b
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul]
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  have hadjEntry : Measurable (fun ω ↦ (F ω).adjugate i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hadj)
  exact hdet.fun_inv.mul hadjEntry

theorem measurable_preservedCoordinateVector
    {k m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) :
    Measurable (preservedCoordinateVector (k := k) c) := by
  exact hc.comp measurable_preservedSCoordinate

theorem measurable_preservedCoordinateW
    {k m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) :
    Measurable (preservedCoordinateW (k := k) c) := by
  have hcR : Measurable (preservedCoordinateVector (k := k) c) :=
    measurable_preservedCoordinateVector hc
  unfold preservedCoordinateW vectorNormSq dotProduct
  apply Complex.measurable_re.comp
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have hci : Measurable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        preservedCoordinateVector c R i) :=
    (measurable_pi_apply i).comp hcR
  exact (continuous_star.measurable.comp hci).mul hci

theorem measurable_preservedCoordinateV
    {k m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) :
    Measurable (preservedCoordinateV (k := k) c) := by
  have hcR : Measurable (preservedCoordinateVector (k := k) c) :=
    measurable_preservedCoordinateVector hc
  have hA : Measurable
      (complexOfRealMatrix :
        Matrix (Fin k) (Fin m ⊕ Fin m) ℝ →
          Matrix (Fin k) (Fin m) ℂ) := by
    unfold complexOfRealMatrix complexOfRealPair realMatrixLeft realMatrixRight
    fun_prop
  unfold preservedCoordinateV quadraticFormReal dotProduct Matrix.mulVec
  apply Complex.measurable_re.comp
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have hci : Measurable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        preservedCoordinateVector c R i) :=
    (measurable_pi_apply i).comp hcR
  apply (continuous_star.measurable.comp hci).mul
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  have hQij : Measurable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        hermitianGram (complexOfRealMatrix R) i j) := by
    simp only [hermitianGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.measurable_sum _ fun a _ ↦ ?_
    have hai : Measurable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          complexOfRealMatrix R a i) :=
      (measurable_pi_apply i).comp ((measurable_pi_apply a).comp hA)
    have haj : Measurable
        (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
          complexOfRealMatrix R a j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply a).comp hA)
    exact (continuous_star.measurable.comp hai).mul haj
  exact hQij.mul ((measurable_pi_apply j).comp hcR)

theorem measurable_preservedCoordinateXi
    {k m : ℕ}
    {c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ}
    (hc : Measurable c) :
    Measurable (preservedCoordinateXi (k := k) c) := by
  have hA : Measurable
      (complexOfRealMatrix :
        Matrix (Fin k) (Fin m ⊕ Fin m) ℝ →
          Matrix (Fin k) (Fin m) ℂ) := by
    unfold complexOfRealMatrix complexOfRealPair realMatrixLeft realMatrixRight
    fun_prop
  have hK : Measurable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        coupledGramKernel (complexOfRealMatrix R)) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    cases i <;> cases j <;>
      simp [coupledGramKernel, hermitianGram, transposeGramMatrix,
        Matrix.mul_apply, complexOfRealMatrix, complexOfRealPair,
        realMatrixLeft, realMatrixRight] <;> fun_prop
  have hKinv : Measurable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        (coupledGramKernel (complexOfRealMatrix R))⁻¹) :=
    measurable_complex_matrix_inv_comp hK
  have hcR : Measurable
      (preservedCoordinateVector (k := k) c) :=
    measurable_preservedCoordinateVector hc
  unfold preservedCoordinateXi quadraticFormReal dotProduct Matrix.mulVec
    Matrix.toBlocks₁₁
  apply Complex.measurable_re.comp
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have hci : Measurable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        preservedCoordinateVector c R i) :=
    (measurable_pi_apply i).comp hcR
  apply (continuous_star.measurable.comp hci).mul
  refine Finset.measurable_sum _ fun j _ ↦ ?_
  have hblock : Measurable
      (fun R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ ↦
        (coupledGramKernel (complexOfRealMatrix R))⁻¹
          (Sum.inl i) (Sum.inl j)) :=
    (measurable_pi_apply (Sum.inl j)).comp
      ((measurable_pi_apply (Sum.inl i)).comp hKinv)
  exact hblock.mul ((measurable_pi_apply j).comp hcR)

/-- At every nonsingular split-real Gram matrix, Schur order and matrix
Cauchy--Schwarz give all pointwise hypotheses needed by the limiting theorem. -/
theorem preservedCoordinate_geometry_of_isUnit
    {k m : ℕ}
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ)
    (hM : IsUnit (realWishartGram R).det)
    (hc : preservedCoordinateVector c R ≠ 0) :
    0 < preservedCoordinateV c R ∧
      0 < preservedCoordinateW c R ∧
      0 ≤ preservedCoordinateXi c R ∧
      preservedCoordinateW c R ^ 2 ≤
        preservedCoordinateV c R * preservedCoordinateXi c R := by
  let A := complexOfRealMatrix R
  let v := preservedCoordinateVector c R
  have hMpair : IsUnit
      (realPairGram (realMatrixLeft R) (realMatrixRight R)).det := by
    simpa [realPairGram_left_right] using hM
  have hKdet : IsUnit (coupledGramKernel A).det := by
    simpa [A, complexOfRealMatrix] using
      (coupledGramKernel_det_isUnit_of_realPairGram
        (realMatrixLeft R) (realMatrixRight R) hMpair)
  have hKunit : IsUnit (coupledGramKernel A) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hKdet
  have hK : (coupledGramKernel A).PosDef :=
    (coupledGramKernel_posSemidef A).posDef_iff_isUnit.mpr hKunit
  have hQ : (hermitianGram A).PosDef := by
    convert hK.submatrix (e := Sum.inl) Sum.inl_injective using 1 <;>
      ext i j <;> rfl
  have hVpos : 0 < preservedCoordinateV c R := by
    simpa [preservedCoordinateV, A, v] using
      (quadraticFormReal_pos hQ hc)
  have hWpos : 0 < preservedCoordinateW c R := by
    simpa [preservedCoordinateW, v] using vectorNormSq_pos hc
  have hKinvPSD : ((coupledGramKernel A)⁻¹).PosSemidef :=
    hK.inv.posSemidef
  have hblockPSD :
      (Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹).PosSemidef := by
    convert hKinvPSD.submatrix Sum.inl using 1 <;>
      ext i j <;> rfl
  have hXinonneg : 0 ≤ preservedCoordinateXi c R := by
    simpa [preservedCoordinateXi, quadraticFormReal, A, v] using
      hblockPSD.re_dotProduct_nonneg v
  have hKblock :
      (Matrix.fromBlocks (hermitianGram A)
        ((transposeGramMatrix A).map star)
        ((transposeGramMatrix A).map star).conjTranspose
        ((hermitianGram A).map star)).PosDef := by
    rw [← coupledGramKernel_eq_fromBlocks_adjoint]
    exact hK
  have hQinvle :
      (hermitianGram A)⁻¹ ≤
        Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹ := by
    rw [coupledGramKernel_eq_fromBlocks_adjoint,
      inverse_fromBlocks_toBlocks11 hKblock]
    exact inverse_le_schurComplement22_inverse hKblock
  have hquadraticMono :
      quadraticFormReal (hermitianGram A)⁻¹ v ≤
        quadraticFormReal
          (Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹) v :=
    quadraticFormReal_mono hQinvle v
  have hcs := matrix_cauchy_schwarz hQ v
  have hquadratic : preservedCoordinateW c R ^ 2 ≤
      preservedCoordinateV c R * preservedCoordinateXi c R := by
    calc
      preservedCoordinateW c R ^ 2 = vectorNormSq v ^ 2 := by rfl
      _ ≤ quadraticFormReal (hermitianGram A) v *
          quadraticFormReal (hermitianGram A)⁻¹ v := hcs
      _ ≤ quadraticFormReal (hermitianGram A) v *
          quadraticFormReal
            (Matrix.toBlocks₁₁ (coupledGramKernel A)⁻¹) v :=
        mul_le_mul_of_nonneg_left hquadraticMono (le_of_lt hVpos)
      _ = preservedCoordinateV c R * preservedCoordinateXi c R := by rfl
  exact ⟨hVpos, hWpos, hXinonneg, hquadratic⟩

/-! ## Paper-facing theorem and equation wrappers -/

/-- **Preserved-coordinate inverse variance.**  This is the article theorem
on the literal split-real model of an iid standard circular complex Gaussian
`k × m` matrix.  The conclusion is an inequality of extended nonnegative
expectations, so no finiteness assumption is hidden. -/
theorem preserved_coordinate_inverse_variance
    {k m : ℕ} (_hm : 1 ≤ m) (hgap : 2 * m + 1 < k)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (hc : Measurable c)
    (hcne : ∀ᵐ R ∂halfGaussianMatrixSum k (Fin m),
      preservedCoordinateVector c R ≠ 0) :
    ennInverseMoment (halfGaussianMatrixSum k (Fin m))
        (preservedCoordinateV c) ≤
      ENNReal.ofReal (((k : ℝ) - 2 * m - 1)⁻¹) *
        ennInverseMoment (halfGaussianMatrixSum k (Fin m))
          (preservedCoordinateW c) := by
  let μ := halfGaussianMatrixSum k (Fin m)
  have hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det := by
    exact ae_isUnit_det_realWishartGram_halfGaussianMatrixSum_generic
      k (Fin m) (by simp; omega)
  have hgeometry : ∀ᵐ R ∂μ,
      0 < preservedCoordinateV c R ∧
        0 < preservedCoordinateW c R ∧
        0 ≤ preservedCoordinateXi c R ∧
        preservedCoordinateW c R ^ 2 ≤
          preservedCoordinateV c R * preservedCoordinateXi c R := by
    filter_upwards [hfull, hcne] with R hR hcR
    exact preservedCoordinate_geometry_of_isUnit c R hR hcR
  have hcden : 0 < (k : ℝ) - 2 * m - 1 := by
    have hkR : ((2 * m + 1 : ℕ) : ℝ) < (k : ℝ) := by
      exact_mod_cast hgap
    push_cast at hkR
    linarith
  apply ennInverseMoment_le_of_regularized_integral_identity
    μ (preservedCoordinateV c) (preservedCoordinateW c)
      (preservedCoordinateXi c)
  · exact measurable_preservedCoordinateV hc
  · exact measurable_preservedCoordinateW hc
  · exact measurable_preservedCoordinateXi hc
  · exact hgeometry.mono fun _ h ↦ h.1
  · exact hgeometry.mono fun _ h ↦ h.2.1
  · exact hgeometry.mono fun _ h ↦ h.2.2.1
  · exact hgeometry.mono fun _ h ↦ h.2.2.2
  · exact inv_nonneg.mpr (le_of_lt hcden)
  · intro δ hδ
    simpa [μ] using preservedCoordinate_regularized_integral_data
      hgap hc δ hδ

/-- Literal endpoint for `thm:preserved-coordinate-inverse-variance` and
`eq:preserved-coordinate-inverse-variance`, with the article's null-event
hypothesis `P{c(S)=0}=0`. -/
theorem eq_preserved_coordinate_inverse_variance
    {k m : ℕ} (hm : 1 ≤ m) (hgap : 2 * m + 1 < k)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (hc : Measurable c)
    (hnull : (halfGaussianMatrixSum k (Fin m))
      {R | preservedCoordinateVector c R = 0} = 0) :
    ennInverseMoment (halfGaussianMatrixSum k (Fin m))
        (preservedCoordinateV c) ≤
      ENNReal.ofReal (((k : ℝ) - 2 * m - 1)⁻¹) *
        ennInverseMoment (halfGaussianMatrixSum k (Fin m))
          (preservedCoordinateW c) := by
  apply preserved_coordinate_inverse_variance hm hgap c hc
  rw [ae_iff]
  simpa only [Classical.not_not] using hnull

/-- Literal endpoint for the introductory display
`eq:general-wishart-overview`. -/
theorem eq_general_wishart_overview
    {k m : ℕ} (hm : 1 ≤ m) (hgap : 2 * m + 1 < k)
    (c : Matrix (Fin m) (Fin m) ℂ → Fin m → ℂ)
    (hc : Measurable c)
    (hnull : (halfGaussianMatrixSum k (Fin m))
      {R | preservedCoordinateVector c R = 0} = 0) :
    ennInverseMoment (halfGaussianMatrixSum k (Fin m))
        (preservedCoordinateV c) ≤
      ENNReal.ofReal (((k : ℝ) - 2 * m - 1)⁻¹) *
        ennInverseMoment (halfGaussianMatrixSum k (Fin m))
          (preservedCoordinateW c) :=
  eq_preserved_coordinate_inverse_variance hm hgap c hc hnull

/-! ## Exact symmetric-domain formulation -/

/-- The literal domain `{S : Sᵀ = S}` appearing in the article. -/
abbrev SymmetricComplexMatrix (m : ℕ) :=
  {S : Matrix (Fin m) (Fin m) ℂ // S.IsSymm}

/-- A measurable retraction from the ambient matrix space to the symmetric
subspace. -/
def symmetricComplexMatrixProjection {m : ℕ}
    (S : Matrix (Fin m) (Fin m) ℂ) : SymmetricComplexMatrix m :=
  ⟨(1 / 2 : ℂ) • (S + S.transpose), by
    unfold Matrix.IsSymm
    ext i j
    simp [Matrix.transpose_apply, add_comm]
    ring⟩

theorem measurable_symmetricComplexMatrixProjection {m : ℕ} :
    Measurable (symmetricComplexMatrixProjection (m := m)) := by
  apply Measurable.subtype_mk
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp [symmetricComplexMatrixProjection, Matrix.transpose_apply]
  fun_prop

@[simp] theorem symmetricComplexMatrixProjection_of_isSymm
    {m : ℕ} {S : Matrix (Fin m) (Fin m) ℂ} (hS : S.IsSymm) :
    (symmetricComplexMatrixProjection S : Matrix (Fin m) (Fin m) ℂ) = S := by
  change (1 / 2 : ℂ) • (S + S.transpose) = S
  rw [hS.eq]
  ext i j
  simp
  ring

/-- Extend a Borel rule from the symmetric subspace to the ambient matrix
space through the preceding measurable retraction. -/
def extendSymmetricPreservedRule {m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (S : Matrix (Fin m) (Fin m) ℂ) : Fin m → ℂ :=
  c (symmetricComplexMatrixProjection S)

theorem measurable_extendSymmetricPreservedRule {m : ℕ}
    {c : SymmetricComplexMatrix m → Fin m → ℂ}
    (hc : Measurable c) :
    Measurable (extendSymmetricPreservedRule c) :=
  hc.comp measurable_symmetricComplexMatrixProjection

/-- The literal random symmetric coordinate `S=AᵀA`, valued in its
subspace rather than in the ambient matrix type. -/
def preservedSymmetricCoordinate {k m : ℕ}
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    SymmetricComplexMatrix m :=
  ⟨preservedSCoordinate R, by
    rw [preservedSCoordinate_eq_transposeGramMatrix_complexOfRealMatrix]
    exact transposeGramMatrix_isSymm (complexOfRealMatrix R)⟩

theorem measurable_preservedSymmetricCoordinate {k m : ℕ} :
    Measurable (preservedSymmetricCoordinate (k := k) (m := m)) := by
  apply Measurable.subtype_mk
  exact measurable_preservedSCoordinate

/-- The article's literal `c(S)` for a rule whose domain is the symmetric
matrix subspace. -/
def preservedSymmetricCoordinateVector {k m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : Fin m → ℂ :=
  c (preservedSymmetricCoordinate R)

@[simp] theorem preservedCoordinateVector_extendSymmetricRule
    {k m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateVector (extendSymmetricPreservedRule c) R =
      preservedSymmetricCoordinateVector c R := by
  unfold preservedCoordinateVector extendSymmetricPreservedRule
    preservedSymmetricCoordinateVector
  congr 1
  apply Subtype.ext
  exact symmetricComplexMatrixProjection_of_isSymm
    (preservedSymmetricCoordinate R).property

/-- Literal `W=c(S)^*c(S)` for a rule on the symmetric matrix subspace. -/
def preservedSymmetricCoordinateW {k m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  vectorNormSq (preservedSymmetricCoordinateVector c R)

/-- Literal `V=c(S)^*Q c(S)` for the same rule. -/
def preservedSymmetricCoordinateV {k m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) : ℝ :=
  quadraticFormReal (hermitianGram (complexOfRealMatrix R))
    (preservedSymmetricCoordinateVector c R)

@[simp] theorem preservedCoordinateW_extendSymmetricRule
    {k m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateW (extendSymmetricPreservedRule c) R =
      preservedSymmetricCoordinateW c R := by
  rw [preservedCoordinateW, preservedSymmetricCoordinateW,
    preservedCoordinateVector_extendSymmetricRule]

@[simp] theorem preservedCoordinateV_extendSymmetricRule
    {k m : ℕ}
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (R : Matrix (Fin k) (Fin m ⊕ Fin m) ℝ) :
    preservedCoordinateV (extendSymmetricPreservedRule c) R =
      preservedSymmetricCoordinateV c R := by
  rw [preservedCoordinateV, preservedSymmetricCoordinateV,
    preservedCoordinateVector_extendSymmetricRule]

/-- Exact paper-domain endpoint for
`thm:preserved-coordinate-inverse-variance` and
`eq:preserved-coordinate-inverse-variance`. -/
theorem eq_preserved_coordinate_inverse_variance_symmetricDomain
    {k m : ℕ} (hm : 1 ≤ m) (hgap : 2 * m + 1 < k)
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (hc : Measurable c)
    (hnull : (halfGaussianMatrixSum k (Fin m))
      {R | preservedSymmetricCoordinateVector c R = 0} = 0) :
    ennInverseMoment (halfGaussianMatrixSum k (Fin m))
        (preservedSymmetricCoordinateV c) ≤
      ENNReal.ofReal (((k : ℝ) - 2 * m - 1)⁻¹) *
        ennInverseMoment (halfGaussianMatrixSum k (Fin m))
          (preservedSymmetricCoordinateW c) := by
  let cext := extendSymmetricPreservedRule c
  have hnull' : (halfGaussianMatrixSum k (Fin m))
      {R | preservedCoordinateVector cext R = 0} = 0 := by
    simpa [cext] using hnull
  have h := eq_preserved_coordinate_inverse_variance hm hgap cext
    (measurable_extendSymmetricPreservedRule hc) hnull'
  have hVeq : preservedCoordinateV (k := k) cext =
      preservedSymmetricCoordinateV c := by
    funext R
    simp [cext]
  have hWeq : preservedCoordinateW (k := k) cext =
      preservedSymmetricCoordinateW c := by
    funext R
    simp [cext]
  rwa [hVeq, hWeq] at h

/-- Exact symmetric-domain endpoint for `eq:general-wishart-overview`. -/
theorem eq_general_wishart_overview_symmetricDomain
    {k m : ℕ} (hm : 1 ≤ m) (hgap : 2 * m + 1 < k)
    (c : SymmetricComplexMatrix m → Fin m → ℂ)
    (hc : Measurable c)
    (hnull : (halfGaussianMatrixSum k (Fin m))
      {R | preservedSymmetricCoordinateVector c R = 0} = 0) :
    ennInverseMoment (halfGaussianMatrixSum k (Fin m))
        (preservedSymmetricCoordinateV c) ≤
      ENNReal.ofReal (((k : ℝ) - 2 * m - 1)⁻¹) *
        ennInverseMoment (halfGaussianMatrixSum k (Fin m))
          (preservedSymmetricCoordinateW c) :=
  eq_preserved_coordinate_inverse_variance_symmetricDomain
    hm hgap c hc hnull

end

end LogdetLean.GramHafnian.MatrixLawEndpoints
