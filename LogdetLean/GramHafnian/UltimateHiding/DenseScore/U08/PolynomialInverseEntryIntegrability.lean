import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartEntryProductIntegrability
import Mathlib.Tactic

/-!
# Gaussian-polynomial weights times inverse-Wishart entry products

This module strengthens the qualitative entry-product engine by allowing a
fixed polynomial in the rectangular Gaussian mass.  The proof stays at the
same inverse-moment threshold: the polynomial is absorbed by a small extra
Gaussian exponential tilt, while the Bartlett exponent remains `-q`.

The result is the integrability input needed to apply scalar Gaussian
integration by parts directly to one unbounded inverse-Gram entry.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

/-- A positive constant used to absorb a degree-`d` polynomial into an
additional Gaussian exponential tilt. -/
def inverseWishartPolynomialTiltConstant (d : ℕ) : ℝ :=
  (4 * ((2 * d : ℕ) : ℝ)) ^ (2 * d) *
    (((2 * d).factorial : ℕ) : ℝ) *
      Real.exp (1 / (4 * ((2 * d : ℕ) : ℝ)))

/-- Multiplying an order-`q` inverse-entry product by any fixed power of
`1 + ‖R‖_F²` does not change the inverse-Wishart existence threshold. -/
theorem integrable_one_add_rectangularSqMass_pow_mul_inverseWishartEntryProduct_halfGaussianMatrix
    {k p q d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hgap : p + 2 * q ≤ k)
    (indices : Fin q → Fin p × Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (1 + rectangularSqMass R) ^ d *
          inverseWishartEntryProduct indices R)
      (halfGaussianMatrix k p) := by
  by_cases hpzero : p = 0
  · subst p
    exact Fin.elim0 (indices ⟨0, hq⟩).1
  have hp : 0 < p := Nat.pos_of_ne_zero hpzero
  let mu := nestedProductMeasure
    (stdGaussian (EuclideanSpace ℝ (Fin k))) p
  let c₀ : ℝ := -(1 / (4 * ((p * q : ℕ) : ℝ)))
  let c₁ : ℝ := c₀ - 1 / (8 * (d : ℝ))
  let P : ℝ := inverseWishartPolynomialTiltConstant d
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hpqR : 0 < ((p * q : ℕ) : ℝ) := by exact_mod_cast hpq
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hpqOne : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
    exact_mod_cast hpq
  have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hquarter : 1 / (4 * ((p * q : ℕ) : ℝ)) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ((p * q : ℕ) : ℝ))).2
    nlinarith
  have heighth : 1 / (8 * (d : ℝ)) ≤ (1 / 8 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (d : ℝ))).2
    nlinarith
  have hrate : 0 < (1 / 2 : ℝ) + c₁ := by
    dsimp only [c₁, c₀]
    linarith
  have hkernel : Integrable
      (nestedGaussianWishartKernel
        (E := EuclideanSpace ℝ (Fin k)) (-(q : ℝ)) (fun _ ↦ c₁) p)
      mu := by
    dsimp only [mu]
    exact integrable_nestedGaussianWishartKernel_neg_nat_const
      (by omega) (by omega) hgap hrate
  have hmajor : Integrable
      (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
        (inverseWishartEntryProductMajorantConstant p q * P) *
          nestedGaussianWishartKernel (-(q : ℝ)) (fun _ ↦ c₁) p z)
      mu := by
    simpa only [smul_eq_mul] using
      hkernel.const_mul (inverseWishartEntryProductMajorantConstant p q * P)
  have hli :
      ∀ᵐ z ∂mu, LinearIndependent ℝ (nestedTupleToFin p z) := by
    dsimp only [mu]
    exact ae_linearIndependent_nested_stdGaussian p (by
      simp
      omega)
  have hsource : Integrable
      (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
        (1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d *
          inverseWishartEntryProduct indices
            (nestedStandardToHalfMatrix k p z)) mu := by
    apply Integrable.mono' hmajor
      ((((measurable_const.add measurable_rectangularSqMass).pow_const d).mul
        (measurable_inverseWishartEntryProduct k p q indices)).comp
          (measurable_nestedStandardToHalfMatrix k p)).aestronglyMeasurable
    filter_upwards [hli] with z hz
    let energy : ℝ := ∑ i : Fin p, ‖nestedTupleToFin p z i‖ ^ 2
    have henergy : 0 ≤ energy := by
      dsimp only [energy]
      positivity
    have hmass :
        rectangularSqMass (nestedStandardToHalfMatrix k p z) ≤ energy := by
      rw [rectangularSqMass_nestedStandardToHalfMatrix]
      dsimp only [energy]
      nlinarith
    have hbase :
        1 + rectangularSqMass (nestedStandardToHalfMatrix k p z) ≤
          1 + energy := by linarith
    have hpolyDegree :
        (1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d ≤
          (1 + energy) ^ (2 * d) := by
      calc
        (1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d ≤
            (1 + energy) ^ d :=
          pow_le_pow_left₀ (by
            have := rectangularSqMass_nonneg
              (nestedStandardToHalfMatrix k p z)
            linarith) hbase d
        _ ≤ (1 + energy) ^ (2 * d) :=
          pow_le_pow_right₀ (by linarith) (by omega)
    have hpoly0 := one_add_pow_le_exp_div
      (p := 2 * d) (Nat.mul_pos (by norm_num) hd) henergy
    have hpoly :
        (1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d ≤
          P * Real.exp (energy / (8 * (d : ℝ))) := by
      refine hpolyDegree.trans ?_
      dsimp only [P, inverseWishartPolynomialTiltConstant]
      have hden :
          (4 : ℝ) * ((2 * d : ℕ) : ℝ) = 8 * (d : ℝ) := by
        push_cast
        ring
      rw [hden] at hpoly0 ⊢
      exact hpoly0
    have hentry := abs_inverseWishartEntryProduct_half_le_tiltedKernel
      hp hq indices z hz
    have hkernelMul :
        nestedGaussianWishartKernel (-(q : ℝ)) (fun _ ↦ c₀) p z *
            Real.exp (energy / (8 * (d : ℝ))) =
          nestedGaussianWishartKernel (-(q : ℝ)) (fun _ ↦ c₁) p z := by
      unfold nestedGaussianWishartKernel
      have hsum₀ :
          (∑ i : Fin p, c₀ * ‖nestedTupleToFin p z i‖ ^ 2) =
            c₀ * energy := by
        dsimp only [energy]
        rw [Finset.mul_sum]
      have hsum₁ :
          (∑ i : Fin p, c₁ * ‖nestedTupleToFin p z i‖ ^ 2) =
            c₁ * energy := by
        dsimp only [energy]
        rw [Finset.mul_sum]
      rw [hsum₀, hsum₁, mul_assoc, ← Real.exp_add]
      congr 2
      dsimp only [c₁]
      ring
    change
      |(1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d *
        inverseWishartEntryProduct indices
          (nestedStandardToHalfMatrix k p z)| ≤ _
    rw [abs_mul]
    have hbaseNonneg :
        0 ≤ (1 + rectangularSqMass
          (nestedStandardToHalfMatrix k p z)) ^ d := by
      apply pow_nonneg
      have := rectangularSqMass_nonneg
        (nestedStandardToHalfMatrix k p z)
      linarith
    have hPnonneg : 0 ≤ P := by
      dsimp only [P, inverseWishartPolynomialTiltConstant]
      positivity
    calc
      |(1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d| *
          |inverseWishartEntryProduct indices
            (nestedStandardToHalfMatrix k p z)| =
          (1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d *
            |inverseWishartEntryProduct indices
              (nestedStandardToHalfMatrix k p z)| := by
        rw [abs_of_nonneg hbaseNonneg]
      _ ≤ (P * Real.exp (energy / (8 * (d : ℝ)))) *
          (inverseWishartEntryProductMajorantConstant p q *
            nestedGaussianWishartKernel (-(q : ℝ)) (fun _ ↦ c₀) p z) := by
        exact mul_le_mul hpoly hentry (abs_nonneg _)
          (mul_nonneg hPnonneg (Real.exp_pos _).le)
      _ = (inverseWishartEntryProductMajorantConstant p q * P) *
          nestedGaussianWishartKernel (-(q : ℝ)) (fun _ ↦ c₁) p z := by
        rw [← hkernelMul]
        ring
  rw [← map_nestedStandardToHalfMatrix k p]
  apply (integrable_map_measure
    (((measurable_const.add measurable_rectangularSqMass).pow_const d).mul
      (measurable_inverseWishartEntryProduct k p q indices)).aestronglyMeasurable
    (measurable_nestedStandardToHalfMatrix k p).aemeasurable).2
  change Integrable
    (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
      (1 + rectangularSqMass (nestedStandardToHalfMatrix k p z)) ^ d *
        inverseWishartEntryProduct indices
          (nestedStandardToHalfMatrix k p z))
    (nestedProductMeasure (stdGaussian (EuclideanSpace ℝ (Fin k))) p)
  simpa only [mu] using hsource

/-- The degree-one specialization used by inverse-entry Stein fields. -/
theorem integrable_one_add_rectangularSqMass_mul_inverseWishartEntryProduct_halfGaussianMatrix
    {k p q : ℕ} (hq : 0 < q) (hgap : p + 2 * q ≤ k)
    (indices : Fin q → Fin p × Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (1 + rectangularSqMass R) * inverseWishartEntryProduct indices R)
      (halfGaussianMatrix k p) := by
  simpa using
    integrable_one_add_rectangularSqMass_pow_mul_inverseWishartEntryProduct_halfGaussianMatrix
      (d := 1) hq (by norm_num) hgap indices

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
