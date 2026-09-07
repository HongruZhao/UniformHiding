import LogdetLean.GramHafnian.UltimateHiding.WishartCore.Wishart.InverseTraceIntegrability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.BetaPrimeMeanInternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatrixInverseMeasurability
import Mathlib.Tactic

/-!
# Products of inverse real-Wishart entries through order four

This file proves the denominator/integrability layer needed by U08.  The
argument is entirely internal: the Bartlett--Mellin transform at exponent
`-q` controls the reciprocal determinant, while a small Gaussian exponential
tilt absorbs the finite adjugate numerator.  The resulting theorem is valid
for every finite order `q`; the final wrapper records the requested `q <= 4`
contract.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Positivity of a diagonal Bartlett factor at the negative integer Mellin
exponent `-q`. -/
theorem wishartDiagonalStageTransform_neg_nat_pos
    {k n q : ℕ} (hk : 0 < k) (hnk : n < k)
    (hshape : 0 < (((k - n : ℕ) : ℝ) / 2) - (q : ℝ))
    {c : ℝ} (hrate : 0 < (1 / 2 : ℝ) + c) :
    0 < wishartDiagonalStageTransform k n (-(q : ℝ)) c := by
  unfold wishartDiagonalStageTransform
  have hbase : 0 < (((k - n : ℕ) : ℝ) / 2) := by
    have : 0 < k - n := Nat.sub_pos_of_lt hnk
    positivity
  have hkreal : 0 < (k : ℝ) / 2 := by positivity
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hGshape :
      0 < Real.Gamma ((((k - n : ℕ) : ℝ) / 2) + (-(q : ℝ))) := by
    apply Real.Gamma_pos_of_pos
    linarith
  have hGbase : 0 < Real.Gamma (((k - n : ℕ) : ℝ) / 2) :=
    Real.Gamma_pos_of_pos hbase
  have hp1 : 0 < (1 / 2 : ℝ) ^ ((k : ℝ) / 2) :=
    Real.rpow_pos_of_pos hhalf _
  have hp2 : 0 < ((1 / 2 : ℝ) + c) ^ ((k : ℝ) / 2 + (-(q : ℝ))) :=
    Real.rpow_pos_of_pos hrate _
  positivity

/-- The exact Bartlett kernel is integrable at negative integer exponent
`-q` under the sharp integer threshold `p + 2*q <= k`. -/
theorem integrable_nestedGaussianWishartKernel_neg_nat_const
    {k p q : ℕ} (hk : 0 < k) (hp : p ≤ k)
    (hgap : p + 2 * q ≤ k)
    {c : ℝ} (hrate : 0 < (1 / 2 : ℝ) + c) :
    Integrable
      (nestedGaussianWishartKernel
        (E := EuclideanSpace ℝ (Fin k)) (-(q : ℝ)) (fun _ ↦ c) p)
      (nestedProductMeasure
        (stdGaussian (EuclideanSpace ℝ (Fin k))) p) := by
  have ht : ∀ n < p,
      0 < (((k - n : ℕ) : ℝ) / 2) + (-(q : ℝ)) := by
    intro n hn
    have hnat : 2 * q + 1 ≤ k - n := by omega
    have hcast : ((2 * q + 1 : ℕ) : ℝ) ≤ ((k - n : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hrate' : ∀ n < p, 0 < (1 / 2 : ℝ) + c := by
    intro _ _
    exact hrate
  have heval := integral_nestedGaussianWishartKernel_eq_diagonal
    hk hp (fun _ ↦ c) ht hrate'
  have hprodPos : 0 <
      ∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform k n (-(q : ℝ)) c := by
    apply Finset.prod_pos
    intro n hn
    have hnp : n < p := Finset.mem_range.mp hn
    have hnk : n < k := lt_of_lt_of_le hnp hp
    exact wishartDiagonalStageTransform_neg_nat_pos hk hnk (by
      linarith [ht n hnp]) hrate
  apply Integrable.of_integral_ne_zero
  rw [heval]
  exact hprodPos.ne'

/-- Product of a prescribed finite list of entries of the nonsingular
inverse of a real Gram matrix. -/
def inverseWishartEntryProduct {k p q : ℕ}
    (indices : Fin q → Fin p × Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) : ℝ :=
  ∏ a : Fin q,
    (realWishartGram R)⁻¹ (indices a).1 (indices a).2

/-- The prescribed inverse-entry product is measurable. -/
theorem measurable_inverseWishartEntryProduct
    (k p q : ℕ) (indices : Fin q → Fin p × Fin p) :
    Measurable (inverseWishartEntryProduct (k := k) indices) := by
  have hGram : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ realWishartGram R) := by
    unfold realWishartGram
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hinv : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R)⁻¹) :=
    (measurable_realMatrix_inv p).comp hGram
  unfold inverseWishartEntryProduct
  exact Finset.measurable_prod _ fun a _ ↦
    (measurable_pi_apply (indices a).2).comp
      ((measurable_pi_apply (indices a).1).comp hinv)

/-- One inverse entry is bounded by one reciprocal determinant and the
elementary adjugate polynomial. -/
theorem abs_nonsingInv_apply_le
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdet : 0 < A.det) (i j : Fin p) :
    |A⁻¹ i j| ≤ A.det⁻¹ *
      ((p.factorial : ℝ) * matrixEntryUnitBound A ^ p) := by
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
  rw [abs_mul, abs_inv, abs_of_pos hdet]
  exact mul_le_mul_of_nonneg_left
    (by simpa using abs_adjugate_apply_le A i j)
    (by positivity)

/-- Under the half-Gaussian scaling, each inverse Gram entry acquires the
factor two. -/
theorem inv_realWishartGram_nestedStandardToHalfMatrix_apply
    {k p : ℕ} (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p)
    (hz : LinearIndependent ℝ (nestedTupleToFin p z)) (i j : Fin p) :
    (realWishartGram (nestedStandardToHalfMatrix k p z))⁻¹ i j =
      2 * (Matrix.gram ℝ (nestedTupleToFin p z))⁻¹ i j := by
  rw [realWishartGram_nestedStandardToHalfMatrix]
  let G := Matrix.gram ℝ (nestedTupleToFin p z)
  have hdet : G.det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hz
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible (1 / 2 : ℝ) :=
    invertibleOfNonzero (by norm_num)
  change ((1 / 2 : ℝ) • G)⁻¹ i j = 2 * G⁻¹ i j
  rw [Matrix.inv_smul (A := G) (1 / 2 : ℝ) hunit]
  change (⅟ (1 / 2 : ℝ)) * G⁻¹ i j = 2 * G⁻¹ i j
  norm_num

/-- Explicit constant in the exponentially tilted majorant for an order-`q`
product of inverse entries. -/
def inverseWishartEntryProductMajorantConstant (p q : ℕ) : ℝ :=
  (2 * (p.factorial : ℝ)) ^ q *
    (2 * (p : ℝ) ^ 2) ^ (p * q) *
      ((4 * ((p * q : ℕ) : ℝ)) ^ (p * q) *
        ((p * q).factorial : ℝ) *
          Real.exp (1 / (4 * ((p * q : ℕ) : ℝ))))

/-- Pointwise on the full-rank event, an order-`q` inverse-entry product is
dominated by the exponent-`-q` Bartlett kernel with a small admissible
Gaussian tilt. -/
theorem abs_inverseWishartEntryProduct_half_le_tiltedKernel
    {k p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (indices : Fin q → Fin p × Fin p)
    (z : NestedTuple (EuclideanSpace ℝ (Fin k)) p)
    (hz : LinearIndependent ℝ (nestedTupleToFin p z)) :
    |inverseWishartEntryProduct indices
        (nestedStandardToHalfMatrix k p z)| ≤
      inverseWishartEntryProductMajorantConstant p q *
        nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin k)) (-(q : ℝ))
          (fun _ ↦ -(1 / (4 * ((p * q : ℕ) : ℝ)))) p z := by
  let G := Matrix.gram ℝ (nestedTupleToFin p z)
  let energy : ℝ := ∑ i : Fin p, ‖nestedTupleToFin p z i‖ ^ 2
  let r : ℕ := p * q
  let C : ℝ := 2 * (p : ℝ) ^ 2
  let D : ℝ :=
    (4 * (r : ℝ)) ^ r * (r.factorial : ℝ) *
      Real.exp (1 / (4 * (r : ℝ)))
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hr : 0 < r := by
    dsimp only [r]
    exact Nat.mul_pos hp hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have henergy : 0 ≤ energy := by
    dsimp only [energy]
    positivity
  have hdet : 0 < G.det :=
    ((Matrix.posSemidef_gram ℝ
        (nestedTupleToFin p z)).posDef_iff_det_ne_zero.mpr
      (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hz)).det_pos
  have hunit : matrixEntryUnitBound G ≤ C * (1 + energy) := by
    have h := matrixEntryUnitBound_realWishartGram_le hp
      (nestedStandardMatrix k p z)
    rw [realWishartGram_nestedStandardMatrix,
      rectangularSqMass_nestedStandardMatrix] at h
    simpa only [C, energy] using h
  have hunitnonneg : 0 ≤ matrixEntryUnitBound G :=
    (one_le_matrixEntryUnitBound G).trans' (by norm_num)
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hbaseNonneg : 0 ≤ C * (1 + energy) := by positivity
  have hpow :
      matrixEntryUnitBound G ^ r ≤
        C ^ r * (1 + energy) ^ r := by
    have h := pow_le_pow_left₀ hunitnonneg hunit r
    simpa only [mul_pow] using h
  have hpoly :
      (1 + energy) ^ r ≤ D * Real.exp (energy / (4 * (r : ℝ))) := by
    simpa only [D] using one_add_pow_le_exp_div hr henergy
  have hentry : ∀ a : Fin q,
      |(realWishartGram
          (nestedStandardToHalfMatrix k p z))⁻¹
            (indices a).1 (indices a).2| ≤
        2 * G.det⁻¹ *
          ((p.factorial : ℝ) * matrixEntryUnitBound G ^ p) := by
    intro a
    rw [inv_realWishartGram_nestedStandardToHalfMatrix_apply z hz]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := abs_nonsingInv_apply_le G hdet (indices a).1 (indices a).2
    nlinarith
  have hproduct :
      |inverseWishartEntryProduct indices
          (nestedStandardToHalfMatrix k p z)| ≤
        (2 * G.det⁻¹ *
          ((p.factorial : ℝ) * matrixEntryUnitBound G ^ p)) ^ q := by
    unfold inverseWishartEntryProduct
    calc
      |∏ a : Fin q,
          (realWishartGram
            (nestedStandardToHalfMatrix k p z))⁻¹
              (indices a).1 (indices a).2| =
          ∏ a : Fin q,
            |(realWishartGram
              (nestedStandardToHalfMatrix k p z))⁻¹
                (indices a).1 (indices a).2| := by
        simpa using Finset.abs_prod (Finset.univ : Finset (Fin q))
          (fun a ↦ (realWishartGram
            (nestedStandardToHalfMatrix k p z))⁻¹
              (indices a).1 (indices a).2)
      _ ≤ ∏ _a : Fin q,
          (2 * G.det⁻¹ *
            ((p.factorial : ℝ) * matrixEntryUnitBound G ^ p)) := by
        exact Finset.prod_le_prod
          (fun _ _ ↦ abs_nonneg _)
          (fun a _ ↦ hentry a)
      _ = (2 * G.det⁻¹ *
          ((p.factorial : ℝ) * matrixEntryUnitBound G ^ p)) ^ q := by
        simp
  have hproductRewrite :
      (2 * G.det⁻¹ *
          ((p.factorial : ℝ) * matrixEntryUnitBound G ^ p)) ^ q =
        (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q * matrixEntryUnitBound G ^ r := by
    dsimp only [r]
    rw [mul_pow, mul_pow, mul_pow, pow_mul]
    ring
  have hafterUnit :
      (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q * matrixEntryUnitBound G ^ r ≤
        (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q * (C ^ r * (1 + energy) ^ r) := by
    gcongr
  have hafterPoly :
      (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q * (C ^ r * (1 + energy) ^ r) ≤
        (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q *
            (C ^ r * (D * Real.exp (energy / (4 * (r : ℝ))))) := by
    gcongr
  have hkernel :
      nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin k)) (-(q : ℝ))
          (fun _ ↦ -(1 / (4 * ((p * q : ℕ) : ℝ)))) p z =
        G.det⁻¹ ^ q * Real.exp (energy / (4 * (r : ℝ))) := by
    unfold nestedGaussianWishartKernel
    have hpowneg : G.det ^ (-(q : ℝ)) = G.det⁻¹ ^ q := by
      rw [Real.rpow_neg hdet.le, Real.rpow_natCast, inv_pow]
    rw [hpowneg]
    congr 1
    dsimp only [energy, r]
    rw [← Finset.mul_sum]
    field_simp
  calc
    |inverseWishartEntryProduct indices
        (nestedStandardToHalfMatrix k p z)| ≤
        (2 * G.det⁻¹ *
          ((p.factorial : ℝ) * matrixEntryUnitBound G ^ p)) ^ q := hproduct
    _ = (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q * matrixEntryUnitBound G ^ r := hproductRewrite
    _ ≤ (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q * (C ^ r * (1 + energy) ^ r) := hafterUnit
    _ ≤ (2 * (p.factorial : ℝ)) ^ q *
          G.det⁻¹ ^ q *
            (C ^ r * (D * Real.exp (energy / (4 * (r : ℝ))))) := hafterPoly
    _ = inverseWishartEntryProductMajorantConstant p q *
        (G.det⁻¹ ^ q * Real.exp (energy / (4 * (r : ℝ)))) := by
      dsimp only [inverseWishartEntryProductMajorantConstant, C, D, r]
      ring
    _ = inverseWishartEntryProductMajorantConstant p q *
        nestedGaussianWishartKernel
          (E := EuclideanSpace ℝ (Fin k)) (-(q : ℝ))
          (fun _ ↦ -(1 / (4 * ((p * q : ℕ) : ℝ)))) p z := by
      rw [hkernel]

/-- Products of `q` prescribed inverse-Wishart entries are integrable under
the sharp integer condition `p + 2*q ≤ k`.  This is the qualitative
fourth-order inverse-moment engine required by H8 and H10. -/
theorem integrable_inverseWishartEntryProduct_halfGaussianMatrix
    {k p q : ℕ} (hgap : p + 2 * q ≤ k)
    (indices : Fin q → Fin p × Fin p) :
    Integrable (inverseWishartEntryProduct (k := k) indices)
      (halfGaussianMatrix k p) := by
  by_cases hqzero : q = 0
  · subst q
    refine (integrable_const (1 : ℝ) : Integrable
      (fun _R : Matrix (Fin k) (Fin p) ℝ ↦ (1 : ℝ))
      (halfGaussianMatrix k p)).congr ?_
    filter_upwards [] with R
    simp [inverseWishartEntryProduct]
  have hq : 0 < q := Nat.pos_of_ne_zero hqzero
  by_cases hpzero : p = 0
  · subst p
    exact Fin.elim0 (indices ⟨0, hq⟩).1
  have hp : 0 < p := Nat.pos_of_ne_zero hpzero
  let mu := nestedProductMeasure
    (stdGaussian (EuclideanSpace ℝ (Fin k))) p
  let c : ℝ := -(1 / (4 * ((p * q : ℕ) : ℝ)))
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hpqR : 0 < ((p * q : ℕ) : ℝ) := by exact_mod_cast hpq
  have hpqOne : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
    exact_mod_cast hpq
  have hrate : 0 < (1 / 2 : ℝ) + c := by
    have heq : (1 / 2 : ℝ) + c =
        (2 * ((p * q : ℕ) : ℝ) - 1) /
          (4 * ((p * q : ℕ) : ℝ)) := by
      dsimp only [c]
      field_simp [hpqR.ne']
      ring
    rw [heq]
    exact div_pos (by linarith [hpqOne]) (by positivity)
  have hkernel : Integrable
      (nestedGaussianWishartKernel
        (E := EuclideanSpace ℝ (Fin k)) (-(q : ℝ)) (fun _ ↦ c) p)
      mu := by
    dsimp only [mu]
    exact integrable_nestedGaussianWishartKernel_neg_nat_const
      (by omega) (by omega) hgap hrate
  have hmajor : Integrable
      (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
        inverseWishartEntryProductMajorantConstant p q *
          nestedGaussianWishartKernel (-(q : ℝ)) (fun _ ↦ c) p z)
      mu := by
    simpa only [smul_eq_mul] using
      hkernel.const_mul (inverseWishartEntryProductMajorantConstant p q)
  have hli :
      ∀ᵐ z ∂mu, LinearIndependent ℝ (nestedTupleToFin p z) := by
    dsimp only [mu]
    exact ae_linearIndependent_nested_stdGaussian p (by
      simp
      omega)
  have hsource : Integrable
      (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
        inverseWishartEntryProduct indices
          (nestedStandardToHalfMatrix k p z)) mu := by
    apply Integrable.mono' hmajor
      ((measurable_inverseWishartEntryProduct k p q indices).comp
        (measurable_nestedStandardToHalfMatrix k p)).aestronglyMeasurable
    filter_upwards [hli] with z hz
    rw [Real.norm_eq_abs]
    dsimp only [c]
    exact abs_inverseWishartEntryProduct_half_le_tiltedKernel hp hq indices z hz
  rw [← map_nestedStandardToHalfMatrix k p]
  apply (integrable_map_measure
    (measurable_inverseWishartEntryProduct k p q indices).aestronglyMeasurable
    (measurable_nestedStandardToHalfMatrix k p).aemeasurable).2
  change Integrable
    (fun z : NestedTuple (EuclideanSpace ℝ (Fin k)) p ↦
      inverseWishartEntryProduct indices
        (nestedStandardToHalfMatrix k p z))
    (nestedProductMeasure
      (stdGaussian (EuclideanSpace ℝ (Fin k))) p)
  simpa only [mu] using hsource

/-- Scaling a full-rank variance-one Gaussian matrix by `1/sqrt 2`
multiplies an order-`q` inverse-entry product by `2^q`. -/
theorem inverseWishartEntryProduct_invSqrtTwoScaleMatrix
    {k p q : ℕ} (indices : Fin q → Fin p × Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (hunit : IsUnit (realWishartGram R).det) :
    inverseWishartEntryProduct indices
        (invSqrtTwoScaleMatrix k p R) =
      2 ^ q * inverseWishartEntryProduct indices R := by
  have hinv :
      (realWishartGram (invSqrtTwoScaleMatrix k p R))⁻¹ =
        (2 : ℝ) • (realWishartGram R)⁻¹ := by
    rw [realWishartGram_invSqrtTwoScaleMatrix]
    letI : Invertible (1 / 2 : ℝ) :=
      invertibleOfNonzero (by norm_num)
    rw [Matrix.inv_smul (A := realWishartGram R) (1 / 2 : ℝ) hunit]
    change (⅟ (1 / 2 : ℝ)) • (realWishartGram R)⁻¹ =
      (2 : ℝ) • (realWishartGram R)⁻¹
    norm_num
  unfold inverseWishartEntryProduct
  simp_rw [hinv, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

/-- Literal variance-one formulation used by the beta-prime source law. -/
theorem integrable_inverseWishartEntryProduct_standardGaussian
    {k p q : ℕ} (hgap : p + 2 * q ≤ k)
    (indices : Fin q → Fin p × Fin p) :
    Integrable (inverseWishartEntryProduct (k := k) indices)
      (standardRealGaussianMatrixMeasure k p) := by
  let f : Matrix (Fin k) (Fin p) ℝ → ℝ :=
    inverseWishartEntryProduct (k := k) indices
  have hhalf : Integrable f (halfGaussianMatrix k p) :=
    integrable_inverseWishartEntryProduct_halfGaussianMatrix hgap indices
  rw [← map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure] at hhalf
  have hcomp : Integrable (f ∘ invSqrtTwoScaleMatrix k p)
      (standardRealGaussianMatrixMeasure k p) :=
    (integrable_map_measure
      (measurable_inverseWishartEntryProduct k p q indices).aestronglyMeasurable
      (measurable_invSqrtTwoScaleMatrix k p).aemeasurable).mp hhalf
  have hp_le_k : p ≤ k := by omega
  have hunit :=
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure hp_le_k
  have heq : f ∘ invSqrtTwoScaleMatrix k p =ᵐ[
      standardRealGaussianMatrixMeasure k p]
      fun R ↦ 2 ^ q * f R := by
    filter_upwards [hunit] with R hR
    exact inverseWishartEntryProduct_invSqrtTwoScaleMatrix indices R hR
  have hscaled : Integrable (fun R ↦ 2 ^ q * f R)
      (standardRealGaussianMatrixMeasure k p) := hcomp.congr heq
  have hrescaled := hscaled.const_mul ((2 : ℝ) ^ q)⁻¹
  simpa [f, mul_assoc] using hrescaled

/-- Uniform order-at-most-four wrapper with eight degrees of freedom of
margin. -/
theorem integrable_inverseWishartEntryProduct_order_le_four_standardGaussian
    {k p q : ℕ} (hq : q ≤ 4) (hgap : p + 8 ≤ k)
    (indices : Fin q → Fin p × Fin p) :
    Integrable (inverseWishartEntryProduct (k := k) indices)
      (standardRealGaussianMatrixMeasure k p) := by
  exact integrable_inverseWishartEntryProduct_standardGaussian
    (by omega) indices

/-- Exact H8/H10 denominator specialization: if `K ≥ 2N+8`, every
product of at most four entries of the inverse denominator Gram matrix is
integrable under its literal variance-one Gaussian law. -/
theorem integrable_betaPrimeDenominator_inverseEntryProduct_order_le_four
    {N K q : ℕ} (hgap : 2 * N + 8 ≤ K) (hq : q ≤ 4)
    (indices : Fin q → Fin N × Fin N) :
    Integrable
      (inverseWishartEntryProduct (k := K - N) indices)
      (standardRealGaussianMatrixMeasure (K - N) N) := by
  apply integrable_inverseWishartEntryProduct_order_le_four_standardGaussian
    hq (indices := indices)
  omega

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
