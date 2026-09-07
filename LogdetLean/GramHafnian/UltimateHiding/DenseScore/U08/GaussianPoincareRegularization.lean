import LogdetLean.GramHafnian.UltimateHiding.DenseScore.BetaPrimeMeanInternal
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# Gaussian-Poincare regularization and singular-limit closure

For a denominator matrix `H`, set
`B_ε = HᵀH + εI`.  Poincare/log-Sobolev is applied only at `ε>0`,
where inverse trace functions are smooth.  The generic Fatou closure below
passes any uniform `L^p` estimate to the almost-everywhere `ε ↓0` limit.
The inverse-entry moments in the companion U08 module provide the required
domination on the full-rank event.
-/

open MeasureTheory Filter
open scoped ENNReal Matrix MatrixOrder Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Ridge-regularized real Wishart Gram matrix. -/
def regularizedWishartGram (epsilon : ℝ)
    {k p : ℕ} (H : Matrix (Fin k) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  realWishartGram H + epsilon • 1

@[simp]
theorem regularizedWishartGram_zero
    {k p : ℕ} (H : Matrix (Fin k) (Fin p) ℝ) :
    regularizedWishartGram 0 H = realWishartGram H := by
  simp [regularizedWishartGram]

/-- Every positive ridge makes the Gram matrix positive definite, including
when the unregularized Gram matrix is singular. -/
theorem regularizedWishartGram_posDef
    {k p : ℕ} (H : Matrix (Fin k) (Fin p) ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (regularizedWishartGram epsilon H).PosDef := by
  unfold regularizedWishartGram
  exact Matrix.PosDef.posSemidef_add
    (realWishartGram_posSemidef H)
    ((Matrix.PosDef.one (n := Fin p)).smul hepsilon)

theorem regularizedWishartGram_det_ne_zero
    {k p : ℕ} (H : Matrix (Fin k) (Fin p) ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (regularizedWishartGram epsilon H).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (regularizedWishartGram_posDef H hepsilon).isUnit)

/-- The regularized Gram matrix depends continuously on the ridge. -/
theorem continuous_regularizedWishartGram
    {k p : ℕ} (H : Matrix (Fin k) (Fin p) ℝ) :
    Continuous (fun epsilon : ℝ ↦ regularizedWishartGram epsilon H) := by
  unfold regularizedWishartGram
  fun_prop

/-- At fixed ridge, the regularized Gram matrix is continuous in the entire
rectangular Gaussian matrix. -/
theorem continuous_regularizedWishartGram_matrix
    (epsilon : ℝ) {k p : ℕ} :
    Continuous (fun H : Matrix (Fin k) (Fin p) ℝ ↦
      regularizedWishartGram epsilon H) := by
  unfold regularizedWishartGram
  exact continuous_realWishartGram_genericSteinHaff.add continuous_const

/-- The positive-ridge inverse is globally continuous in the Gaussian
matrix; there is no singular exceptional locus at fixed `epsilon > 0`. -/
theorem continuous_regularizedWishartGram_inv_matrix
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {k p : ℕ} :
    Continuous (fun H : Matrix (Fin k) (Fin p) ℝ ↦
      (regularizedWishartGram epsilon H)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro H
  exact (continuousAt_matrix_inv (regularizedWishartGram epsilon H)
    (by simpa only [Ring.inverse_eq_inv'] using
      continuousAt_inv₀ (regularizedWishartGram_det_ne_zero H hepsilon))).tendsto.comp
      (continuous_regularizedWishartGram_matrix epsilon).continuousAt.tendsto

/-- On the full-rank event, the regularized inverse converges to the ordinary
inverse along every ridge sequence tending to zero. -/
theorem tendsto_regularizedWishartGram_inv
    {k p : ℕ} (H : Matrix (Fin k) (Fin p) ℝ)
    (hdet : (realWishartGram H).det ≠ 0)
    {iota : Type*} {l : Filter iota} {epsilon : iota → ℝ}
    (hepsilon : Tendsto epsilon l (𝓝 0)) :
    Tendsto
      (fun i ↦ (regularizedWishartGram (epsilon i) H)⁻¹) l
      (𝓝 (realWishartGram H)⁻¹) := by
  have hGram : Tendsto
      (fun i ↦ regularizedWishartGram (epsilon i) H) l
      (𝓝 (realWishartGram H)) := by
    simpa only [Function.comp_def, regularizedWishartGram_zero] using
      (continuous_regularizedWishartGram H).continuousAt.tendsto.comp hepsilon
  exact (continuousAt_matrix_inv (realWishartGram H)
    (by simpa only [Ring.inverse_eq_inv'] using
      continuousAt_inv₀ hdet)).tendsto.comp hGram

/-- Loewner domination used for inverse-moment control in the ridge limit:
on the full-rank event and for `epsilon ≥ 0`,
`(HᵀH+epsilon I)⁻¹ ≤ (HᵀH)⁻¹`. -/
theorem regularizedWishartGram_inv_le
    {k p : ℕ} (H : Matrix (Fin k) (Fin p) ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hdet : (realWishartGram H).det ≠ 0) :
    (regularizedWishartGram epsilon H)⁻¹ ≤
      (realWishartGram H)⁻¹ := by
  let A := realWishartGram H
  let B := regularizedWishartGram epsilon H
  have hA : A.PosDef :=
    (realWishartGram_posSemidef H).posDef_iff_det_ne_zero.mpr hdet
  have hB : B.PosDef := by
    dsimp only [A, B, regularizedWishartGram]
    exact hA.add_posSemidef
      ((Matrix.PosSemidef.one (n := Fin p)).smul hepsilon)
  have hle : A ≤ B := by
    rw [Matrix.le_iff]
    dsimp only [A, B]
    simpa [regularizedWishartGram] using
      (Matrix.PosSemidef.one (n := Fin p)).smul hepsilon
  have hdiff : (B - A).PosSemidef := Matrix.le_iff.mp hle
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  have hAinv : A⁻¹.PosDef := hA.inv
  letI : Invertible A⁻¹ := hAinv.isUnit.invertible
  let I : Matrix (Fin p) (Fin p) ℝ := 1
  have hblock :
      (Matrix.fromBlocks B I Iᴴ A⁻¹).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ B I hAinv).mpr
    simpa only [I, Matrix.inv_inv_of_invertible, Matrix.one_mul,
      Matrix.mul_one, Matrix.conjTranspose_one] using hdiff
  have htarget := (Matrix.PosDef.fromBlocks₁₁
    I A⁻¹ hB).mp hblock
  rw [Matrix.le_iff]
  simpa only [I, Matrix.one_mul, Matrix.mul_one,
    Matrix.conjTranspose_one] using htarget

/-- The denominator Gram matrix is nonsingular almost surely under the
literal beta-prime Gaussian source law.  This is the product-measure lift of
the already internal standard-Gaussian full-rank theorem; no moment or H8/H10
input is used. -/
theorem ae_isUnit_det_betaPrimeDenominatorWishartGram
    {N K : ℕ} (hNK : N ≤ K - N) :
    ∀ᵐ source :
        Matrix (Fin (N + 1)) (Fin N) ℝ ×
          Matrix (Fin (K - N)) (Fin N) ℝ
      ∂(realBetaPrimeGaussianSourceLaw N K),
      IsUnit (realWishartGram source.2).det := by
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (N + 1) N) :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (K - N) N) :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hfull :
      ∀ᵐ B ∂(standardRealGaussianMatrixMeasure (K - N) N),
        IsUnit (realWishartGram B).det :=
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure hNK
  unfold realBetaPrimeGaussianSourceLaw
  exact (Measure.quasiMeasurePreserving_snd
    (μ := standardRealGaussianMatrixMeasure (N + 1) N)
    (ν := standardRealGaussianMatrixMeasure (K - N) N)).ae hfull

/-- Fatou closure for regularized Gaussian-Poincare estimates.  Uniform real
`lpNorm` control of measurable approximants passes to an almost-everywhere
pointwise limit, including `MemLp` of that limit. -/
theorem memLp_and_lpNorm_le_of_ae_tendsto_uniform
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {p : ENNReal}
    {f : ℕ → Omega → ℝ} {g : Omega → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ n, MemLp (f n) p mu)
    (hbound : ∀ n, lpNorm (f n) p mu ≤ C)
    (htendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun n ↦ f n omega) atTop (𝓝 (g omega))) :
    MemLp g p mu ∧ lpNorm g p mu ≤ C := by
  have hboundENN : ∀ n, eLpNorm (f n) p mu ≤ ENNReal.ofReal C := by
    intro n
    rw [← ofReal_lpNorm (hf n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hlimENN : eLpNorm g p mu ≤ ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto
      (u := atTop) (f := f)
    · exact Filter.Eventually.of_forall hboundENN
    · exact fun n ↦ (hf n).aestronglyMeasurable
    · exact htendsto
  have hgMeas : AEStronglyMeasurable g mu :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hf n).aestronglyMeasurable) htendsto
  have hg : MemLp g p mu :=
    ⟨hgMeas, lt_of_le_of_lt hlimENN (by simp)⟩
  refine ⟨hg, ?_⟩
  rw [← toReal_eLpNorm hgMeas]
  exact (ENNReal.toReal_mono (by simp) hlimENN).trans_eq
    (ENNReal.toReal_ofReal hC)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
