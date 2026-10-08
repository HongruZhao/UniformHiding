import A3.WishartCholeskyTrace
import A3.WishartCholeskyJacobian
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open ProbabilityTheory MeasureTheory
open scoped BigOperators ENNReal ComplexOrder

noncomputable section
namespace A3Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K]

def wishartBartlettNormalization (n : ℕ) (K : Type*) [RCLike K]
    (alpha c : ℝ) : ℝ :=
  (∏ i : Fin n, (Real.Gamma (wishartBartlettShape alpha K i))⁻¹) *
    c ^ Fintype.card (HermitianCoordinateIndex n)

theorem wishartBartlettNormalization_pos (alpha c : ℝ) (hc : 0 < c)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha K i) :
    0 < wishartBartlettNormalization n K alpha c := by
  apply mul_pos
  · exact Finset.prod_pos (fun i _ ↦ inv_pos.mpr (Real.Gamma_pos_of_pos (ha i)))
  · exact pow_pos hc _

theorem wishart_sqrt_nat_pow (q : ℝ) (hq : 0 ≤ q) (k : ℕ) :
    (Real.sqrt q) ^ k = q ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq]
  congr 1
  ring

theorem wishartJacobian_exponent (alpha : ℝ) (i : Fin n) :
    alpha - wishartHermitianKappa n K +
      (Module.finrank ℝ K : ℝ) * ((n - 1 - i.val : ℕ) : ℝ) / 2 =
        wishartBartlettShape alpha K i - 1 := by
  have hi : i.val + 1 ≤ n := i.isLt
  have hs : n - 1 - i.val = n - (i.val + 1) := by omega
  have hcast : ((n - 1 - i.val : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℝ) := by
    rw [hs, Nat.cast_sub hi]
    push_cast
    ring
  rw [hcast]
  unfold wishartHermitianKappa wishartBartlettShape
  ring

theorem wishartJacobian_rpow (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    (fderiv ℝ wishartGramCoordinates x).toLinearMap.det =
      ∏ i : Fin n, (x.1 i) ^
        ((Module.finrank ℝ K : ℝ) * ((n - 1 - i.val : ℕ) : ℝ) / 2) := by
  rw [det_fderiv_wishartGramCoordinates x hx]
  apply Finset.prod_congr rfl
  intro i _
  rw [wishart_sqrt_nat_pow _ (hx i).le]
  congr 1
  push_cast
  ring

theorem wishartDetReal_gram (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    wishartDetReal (wishartGramCoordinates x) = ∏ i, x.1 i := by
  unfold wishartDetReal
  rw [det_wishartGramCoordinates x hx, RCLike.ofReal_re]

theorem wishartKernel_mul_jacobian (alpha : ℝ) (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    wishartAmbientKernel n K alpha (wishartGramCoordinates x) *
      (fderiv ℝ wishartGramCoordinates x).toLinearMap.det =
      Real.exp (-((∑ i, x.1 i) + ∑ ij, RCLike.normSq (x.2 ij))) *
        ∏ i, (x.1 i) ^ (wishartBartlettShape alpha K i - 1) := by
  unfold wishartAmbientKernel
  rw [wishartTraceReal_gram x hx, wishartDetReal_gram x hx, wishartJacobian_rpow x hx,
    ← Real.finsetProd_rpow Finset.univ (fun i ↦ x.1 i) (fun i _ ↦ (hx i).le),
    mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_add (hx i), wishartJacobian_exponent]

/-- Exact real source-density identity before converting to `ENNReal`. -/
theorem wishartBartlettDensity_real_identity (alpha c : ℝ) (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    ((∏ i, gammaPDFReal (wishartBartlettShape alpha K i) 1 (x.1 i)) *
      ∏ ij, c * Real.exp (-RCLike.normSq (x.2 ij))) =
      wishartBartlettNormalization n K alpha c *
        (wishartAmbientKernel n K alpha (wishartGramCoordinates x) *
          (fderiv ℝ wishartGramCoordinates x).toLinearMap.det) := by
  rw [wishartKernel_mul_jacobian alpha x hx]
  have hg (i : Fin n) : gammaPDFReal (wishartBartlettShape alpha K i) 1 (x.1 i) =
      (Real.Gamma (wishartBartlettShape alpha K i))⁻¹ *
        (x.1 i) ^ (wishartBartlettShape alpha K i - 1) * Real.exp (-(x.1 i)) := by
    simp [gammaPDFReal, (hx i).le]
  simp_rw [hg]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_sum, Finset.sum_neg_distrib,
    wishartBartlettNormalization]
  rw [neg_add, Real.exp_add]
  ring

/-- Literal Gamma/Gaussian density is the pullback of the ambient density times its Jacobian. -/
theorem wishartBartlettDensity_identity (alpha c : ℝ) (hc : 0 < c)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha K i)
    (x : HermitianCoordinates n K) (hx : x ∈ wishartCholeskyDomain n K) :
    wishartBartlettDensity n alpha (fun z ↦ ENNReal.ofReal (c * Real.exp (-RCLike.normSq z))) x =
      ENNReal.ofReal (wishartBartlettNormalization n K alpha c) *
        (wishartAmbientDensity n K alpha (wishartGramCoordinates x) *
          ENNReal.ofReal |(fderiv ℝ wishartGramCoordinates x).det|) := by
  have hg (i : Fin n) : 0 ≤ gammaPDFReal (wishartBartlettShape alpha K i) 1 (x.1 i) :=
    (gammaPDFReal_pos (ha i) (by norm_num) (hx i)).le
  have hz (ij : HermitianCoordinateIndex n) : 0 ≤ c * Real.exp (-RCLike.normSq (x.2 ij)) :=
    (mul_pos hc (Real.exp_pos _)).le
  unfold wishartBartlettDensity
  simp only [gammaPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hg i),
    ← ENNReal.ofReal_prod_of_nonneg (fun ij _ ↦ hz ij),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ ↦ hg i)),
    wishartBartlettDensity_real_identity alpha c x hx]
  have hcone := wishartGramCoordinates_posDef x hx
  change (hermitianMatrixOfCoordinates (wishartGramCoordinates x)).PosDef at hcone
  simp only [wishartAmbientDensity, if_pos hcone]
  rw [abs_of_pos (det_fderiv_wishartGramCoordinates_pos x hx),
    ENNReal.ofReal_mul (wishartBartlettNormalization_pos alpha c hc ha).le,
    ENNReal.ofReal_mul (wishartAmbientKernel_pos alpha hcone).le]

end A3Research
