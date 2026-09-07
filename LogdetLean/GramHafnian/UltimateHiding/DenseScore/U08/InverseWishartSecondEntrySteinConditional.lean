import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.FiniteGaussianWishartSecondMoment
import Mathlib.Tactic

/-!
# CONDITIONAL inverse-Wishart second-entry formula from one Stein recursion

This module isolates the smallest remaining analytic step in the exact
second-entry calculation.  The entrywise first inverse-Wishart moment is
proved from the already internal bounded-test Stein--Haff theorem.  A pure
three-pair algebra lemma then solves the second-entry tensor from the single
unbounded-test Stein recursion below.  Finally the result is transported
from the half-Gaussian normalization to the literal variance-one Gaussian
law and packaged as `ScaledInverseWishartSecondEntryMomentFormula`.

No axiom is declared.  The Stein recursion is an explicit theorem parameter;
consequently every theorem consuming it is CONDITIONAL until its singular
inverse-entry cutoff/limit proof is supplied.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

local instance inverseWishartSteinFunctionalNorm
    {p : Type*} [Fintype p] :
    Norm (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

local instance inverseWishartSteinFunctionalSeminormedAddCommGroup
    {p : Type*} [Fintype p] :
    SeminormedAddCommGroup (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

/-- The real degrees-of-freedom gap `k-p-1`. -/
def inverseWishartEntryGap (k p : ℕ) : ℝ :=
  (k : ℝ) - (p : ℝ) - 1

/-- A first inverse-Wishart entry integral in the half-Gaussian
normalization. -/
def halfGaussianInverseWishartEntryMeanIntegral
    (k p : ℕ) (i j : Fin p) : ℝ :=
  ∫ R : Matrix (Fin k) (Fin p) ℝ,
    (realWishartGram R)⁻¹ i j ∂halfGaussianMatrix k p

/-- A product of two inverse-Wishart entries in the half-Gaussian
normalization. -/
def halfGaussianInverseWishartSecondEntryIntegral
    (k p : ℕ) (i j l m : Fin p) : ℝ :=
  ∫ R : Matrix (Fin k) (Fin p) ℝ,
    (realWishartGram R)⁻¹ i j * (realWishartGram R)⁻¹ l m
      ∂halfGaussianMatrix k p

/-- Exact bounded-test Stein--Haff consequence for an arbitrary fixed
symmetric direction. -/
theorem halfGaussian_inverseWishart_trace_mul_const_mean
    {k p : ℕ} (hgap : p + 1 < k)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ * D)
        ∂halfGaussianMatrix k p) =
      2 * Matrix.trace D / inverseWishartEntryGap k p := by
  have h := steinHaff_halfGaussianMatrix_of_bounded_fderiv
    hgap (fun _ : Matrix (Fin p) (Fin p) ℝ ↦ (1 : ℝ))
    (contDiff_const : ContDiff ℝ 1
      (fun _ : Matrix (Fin p) (Fin p) ℝ ↦ (1 : ℝ)))
    1 (by intro M; norm_num) 0 (by intro M; norm_num) D hD
  have heq := h.2.2
  simp only [one_mul] at heq
  simp at heq
  have hcoeff : inverseGramScoreCoefficient (Fin k) (Fin p) =
      inverseWishartEntryGap k p / 2 := by
    simp [inverseGramScoreCoefficient, inverseWishartEntryGap]
  rw [hcoeff, integral_const_mul] at heq
  have hden : 0 < inverseWishartEntryGap k p := by
    have hgapR : ((p + 1 : ℕ) : ℝ) < (k : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    unfold inverseWishartEntryGap
    linarith
  apply (eq_div_iff hden.ne').2
  nlinarith [heq]

/-- Exact first entry mean under the half-Gaussian normalization. -/
theorem halfGaussian_inverseWishart_entry_mean
    {k p : ℕ} (hgap : p + 1 < k) (i j : Fin p) :
    halfGaussianInverseWishartEntryMeanIntegral k p i j =
      2 * realKroneckerDelta i j / inverseWishartEntryGap k p := by
  let D : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.single j i 1 + Matrix.single i j 1
  have hD : D.IsSymm := by
    dsimp only [D]
    simpa [Matrix.transpose_single] using
      Matrix.isSymm_add_transpose_self (Matrix.single j i (1 : ℝ))
  have h := halfGaussian_inverseWishart_trace_mul_const_mean hgap D hD
  have htraceD : Matrix.trace D = 2 * realKroneckerDelta i j := by
    by_cases hij : i = j
    · subst j
      dsimp only [D]
      rw [Matrix.trace_add, Matrix.trace_single_eq_same]
      norm_num [realKroneckerDelta]
    · have hji : j ≠ i := fun hji ↦ hij hji.symm
      dsimp only [D]
      rw [Matrix.trace_add,
        Matrix.trace_single_eq_of_ne j i (1 : ℝ) hji,
        Matrix.trace_single_eq_of_ne i j (1 : ℝ) hij]
      simp [realKroneckerDelta, hij]
  have htraceInv :
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((realWishartGram R)⁻¹ * D)) =
      (fun R ↦ 2 * (realWishartGram R)⁻¹ i j) := by
    funext R
    rw [Matrix.mul_add, Matrix.trace_add,
      trace_mul_single_eq_entry, trace_mul_single_eq_entry,
      (realWishartGram_inv_isSymm R).apply i j]
    ring
  rw [htraceInv, integral_const_mul, htraceD] at h
  unfold halfGaussianInverseWishartEntryMeanIntegral
  apply mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
  calc
    2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ i j ∂halfGaussianMatrix k p) =
        2 * (2 * realKroneckerDelta i j) /
          inverseWishartEntryGap k p := h
    _ = 2 * (2 * realKroneckerDelta i j /
          inverseWishartEntryGap k p) := by ring

/-- **CONDITIONAL analytic input.**  This is the direct entrywise identity
obtained by applying Stein--Haff to one inverse entry and using
`D = E_ji + E_ij`.  It is strictly below the closed tensor formula: it is a
three-pair linear recursion whose right side still contains unknown second
entry integrals. -/
structure HalfGaussianInverseWishartSecondEntrySteinRecursion
    (k p : ℕ) : Prop where
  entry_product_recursion : ∀ i j l m : Fin p,
    inverseWishartEntryGap k p *
        halfGaussianInverseWishartSecondEntryIntegral k p i j l m =
      2 * halfGaussianInverseWishartEntryMeanIntegral k p l m *
          realKroneckerDelta i j +
        halfGaussianInverseWishartSecondEntryIntegral k p i l j m +
        halfGaussianInverseWishartSecondEntryIntegral k p i m j l

/-- Symmetry of the inverse Gram matrix swaps the two indices in the second
entry under the integral. -/
theorem halfGaussianInverseWishartSecondEntryIntegral_swap_second
    (k p : ℕ) (i j l m : Fin p) :
    halfGaussianInverseWishartSecondEntryIntegral k p i j l m =
      halfGaussianInverseWishartSecondEntryIntegral k p i j m l := by
  unfold halfGaussianInverseWishartSecondEntryIntegral
  apply integral_congr_ae
  filter_upwards [] with R
  rw [(realWishartGram_inv_isSymm R).apply l m]

/-- Pure algebra: the three permuted Stein recursions have the unique first
pairing value displayed by the inverse-Wishart tensor. -/
theorem solve_inverseWishart_threePairSteinSystem
    {c a b d x y z : ℝ} (hc : 2 < c)
    (hx : c * x = 4 / c * a + y + z)
    (hy : c * y = 4 / c * b + x + z)
    (hz : c * z = 4 / c * d + x + y) :
    x = 4 * ((c - 1) * a + b + d) /
      (c * (c - 2) * (c + 1)) := by
  have hc0 : c ≠ 0 := by linarith
  have hc2 : c - 2 ≠ 0 := by linarith
  have hcp1 : c + 1 ≠ 0 := by linarith
  have hcomb :
      (c - 2) * (c + 1) * x =
        4 / c * ((c - 1) * a + b + d) := by
    linear_combination (c - 1) * hx + hy + hz
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hc0 hc2) hcp1)).2
  calc
    x * (c * (c - 2) * (c + 1)) =
        c * ((c - 2) * (c + 1) * x) := by ring
    _ = c * (4 / c * ((c - 1) * a + b + d)) := by rw [hcomb]
    _ = 4 * ((c - 1) * a + b + d) := by field_simp

/-- The exact half-Gaussian second-entry tensor, conditional only on the
single Stein recursion. -/
theorem halfGaussian_inverseWishart_secondEntry_formula_conditional
    {k p : ℕ} (hgap : p + 4 ≤ k)
    (Hstein : HalfGaussianInverseWishartSecondEntrySteinRecursion k p)
    (i j l m : Fin p) :
    halfGaussianInverseWishartSecondEntryIntegral k p i j l m =
      4 *
        ((inverseWishartEntryGap k p - 1) *
              realKroneckerDelta i j * realKroneckerDelta l m +
            realKroneckerDelta i l * realKroneckerDelta j m +
            realKroneckerDelta i m * realKroneckerDelta j l) /
        (inverseWishartEntryGap k p *
          (inverseWishartEntryGap k p - 2) *
          (inverseWishartEntryGap k p + 1)) := by
  let c := inverseWishartEntryGap k p
  let X := halfGaussianInverseWishartSecondEntryIntegral k p i j l m
  let Y := halfGaussianInverseWishartSecondEntryIntegral k p i l j m
  let Z := halfGaussianInverseWishartSecondEntryIntegral k p i m j l
  let A := realKroneckerDelta i j * realKroneckerDelta l m
  let B := realKroneckerDelta i l * realKroneckerDelta j m
  let D := realKroneckerDelta i m * realKroneckerDelta j l
  have hc : 2 < c := by
    have hgapR : ((p + 4 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    dsimp only [c, inverseWishartEntryGap]
    linarith
  have hmean (a b : Fin p) :
      halfGaussianInverseWishartEntryMeanIntegral k p a b =
        2 * realKroneckerDelta a b / c := by
    simpa only [c] using
      halfGaussian_inverseWishart_entry_mean (k := k) (p := p) (by omega) a b
  have hx0 := Hstein.entry_product_recursion i j l m
  have hy0 := Hstein.entry_product_recursion i l j m
  have hz0 := Hstein.entry_product_recursion i m j l
  rw [hmean] at hx0 hy0 hz0
  have hx : c * X = 4 / c * A + Y + Z := by
    dsimp only [c, X, Y, Z, A]
    calc
      inverseWishartEntryGap k p *
          halfGaussianInverseWishartSecondEntryIntegral k p i j l m =
          2 * (2 * realKroneckerDelta l m / inverseWishartEntryGap k p) *
              realKroneckerDelta i j +
            halfGaussianInverseWishartSecondEntryIntegral k p i l j m +
            halfGaussianInverseWishartSecondEntryIntegral k p i m j l := hx0
      _ = _ := by ring
  have hy : c * Y = 4 / c * B + X + Z := by
    dsimp only [c, X, Y, Z, B]
    calc
      inverseWishartEntryGap k p *
          halfGaussianInverseWishartSecondEntryIntegral k p i l j m =
          2 * (2 * realKroneckerDelta j m / inverseWishartEntryGap k p) *
              realKroneckerDelta i l +
            halfGaussianInverseWishartSecondEntryIntegral k p i j l m +
            halfGaussianInverseWishartSecondEntryIntegral k p i m l j := hy0
      _ = 4 / inverseWishartEntryGap k p *
              (realKroneckerDelta i l * realKroneckerDelta j m) +
            halfGaussianInverseWishartSecondEntryIntegral k p i j l m +
            halfGaussianInverseWishartSecondEntryIntegral k p i m l j := by
        ring
      _ = _ := by
        rw [halfGaussianInverseWishartSecondEntryIntegral_swap_second
          k p i m l j]
  have hz : c * Z = 4 / c * D + X + Y := by
    dsimp only [c, X, Y, Z, D]
    calc
      inverseWishartEntryGap k p *
          halfGaussianInverseWishartSecondEntryIntegral k p i m j l =
          2 * (2 * realKroneckerDelta j l / inverseWishartEntryGap k p) *
              realKroneckerDelta i m +
            halfGaussianInverseWishartSecondEntryIntegral k p i j m l +
            halfGaussianInverseWishartSecondEntryIntegral k p i l m j := hz0
      _ = 4 / inverseWishartEntryGap k p *
              (realKroneckerDelta i m * realKroneckerDelta j l) +
            halfGaussianInverseWishartSecondEntryIntegral k p i j m l +
            halfGaussianInverseWishartSecondEntryIntegral k p i l m j := by
        ring
      _ = _ := by
        rw [halfGaussianInverseWishartSecondEntryIntegral_swap_second
            k p i j m l,
          halfGaussianInverseWishartSecondEntryIntegral_swap_second
            k p i l m j]
  simpa only [c, X, A, B, D, mul_assoc] using
    solve_inverseWishart_threePairSteinSystem hc hx hy hz

/-- Scaling a variance-one Gaussian matrix by `1/sqrt 2` multiplies a
second inverse-entry integral by four. -/
theorem halfGaussian_inverseWishart_secondEntry_integral_eq_four_mul_standard
    {k p : ℕ} (hpk : p ≤ k) (i j l m : Fin p) :
    halfGaussianInverseWishartSecondEntryIntegral k p i j l m =
      4 *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ i j * (realWishartGram R)⁻¹ l m
            ∂standardRealGaussianMatrixMeasure k p) := by
  let indices : Fin 2 → Fin p × Fin p := ![(i, j), (l, m)]
  let f : Matrix (Fin k) (Fin p) ℝ → ℝ :=
    inverseWishartEntryProduct indices
  have hf : Measurable f :=
    measurable_inverseWishartEntryProduct k p 2 indices
  have hunit := ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
    (k := k) (p := p) hpk
  have hscale :
      f ∘ invSqrtTwoScaleMatrix k p =ᵐ[
        standardRealGaussianMatrixMeasure k p]
        fun R ↦ 4 * f R := by
    filter_upwards [hunit] with R hR
    have hs := inverseWishartEntryProduct_invSqrtTwoScaleMatrix indices R hR
    norm_num at hs
    simpa [f] using hs
  have hf_apply (R : Matrix (Fin k) (Fin p) ℝ) :
      f R = (realWishartGram R)⁻¹ i j * (realWishartGram R)⁻¹ l m := by
    simp [f, indices, inverseWishartEntryProduct, Fin.prod_univ_two]
  calc
    halfGaussianInverseWishartSecondEntryIntegral k p i j l m =
        ∫ R, f R ∂halfGaussianMatrix k p := by
      apply integral_congr_ae
      filter_upwards [] with R
      exact (hf_apply R).symm
    _ = ∫ R, f R
        ∂Measure.map (invSqrtTwoScaleMatrix k p)
          (standardRealGaussianMatrixMeasure k p) := by
      rw [map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure]
    _ = ∫ R, f (invSqrtTwoScaleMatrix k p R)
        ∂standardRealGaussianMatrixMeasure k p := by
      rw [integral_map (measurable_invSqrtTwoScaleMatrix k p).aemeasurable
        hf.aestronglyMeasurable]
    _ = ∫ R, 4 * f R
        ∂standardRealGaussianMatrixMeasure k p := by
      apply integral_congr_ae
      filter_upwards [hscale] with R hR
      simpa only [Function.comp_apply] using hR
    _ = 4 * ∫ R, f R
        ∂standardRealGaussianMatrixMeasure k p := by
      rw [integral_const_mul]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with R
      exact hf_apply R

/-- Exact variance-one inverse-Wishart second-entry formula, conditional on
the half-Gaussian Stein recursion. -/
theorem integral_inverseWishart_entry_mul_entry_standardGaussian_eq_conditional
    {k p : ℕ} (hgap : p + 4 ≤ k)
    (Hstein : HalfGaussianInverseWishartSecondEntrySteinRecursion k p)
    (i j l m : Fin p) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ i j * (realWishartGram R)⁻¹ l m
        ∂standardRealGaussianMatrixMeasure k p) =
      ((inverseWishartEntryGap k p - 1) *
            realKroneckerDelta i j * realKroneckerDelta l m +
          realKroneckerDelta i l * realKroneckerDelta j m +
          realKroneckerDelta i m * realKroneckerDelta j l) /
        (inverseWishartEntryGap k p *
          (inverseWishartEntryGap k p - 2) *
          (inverseWishartEntryGap k p + 1)) := by
  have hhalf := halfGaussian_inverseWishart_secondEntry_formula_conditional
    hgap Hstein i j l m
  have hscale :=
    halfGaussian_inverseWishart_secondEntry_integral_eq_four_mul_standard
      (k := k) (p := p) (by omega) i j l m
  apply mul_left_cancel₀ (by norm_num : (4 : ℝ) ≠ 0)
  calc
    4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ i j * (realWishartGram R)⁻¹ l m
          ∂standardRealGaussianMatrixMeasure k p) =
        halfGaussianInverseWishartSecondEntryIntegral k p i j l m :=
      hscale.symm
    _ = 4 *
        ((inverseWishartEntryGap k p - 1) *
              realKroneckerDelta i j * realKroneckerDelta l m +
            realKroneckerDelta i l * realKroneckerDelta j m +
            realKroneckerDelta i m * realKroneckerDelta j l) /
          (inverseWishartEntryGap k p *
            (inverseWishartEntryGap k p - 2) *
            (inverseWishartEntryGap k p + 1)) := hhalf
    _ = 4 *
        (((inverseWishartEntryGap k p - 1) *
              realKroneckerDelta i j * realKroneckerDelta l m +
            realKroneckerDelta i l * realKroneckerDelta j m +
            realKroneckerDelta i m * realKroneckerDelta j l) /
          (inverseWishartEntryGap k p *
            (inverseWishartEntryGap k p - 2) *
            (inverseWishartEntryGap k p + 1))) := by ring

/-- The exact scaled denominator tensor package, with every normalization
and parameter cast discharged, conditional only on the entrywise Stein
recursion. -/
theorem scaledInverseWishartSecondEntryMomentFormula_of_stein_conditional
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (Hstein : HalfGaussianInverseWishartSecondEntrySteinRecursion (K - N) N) :
    ScaledInverseWishartSecondEntryMomentFormula N K := by
  have hNK : N ≤ K := by omega
  have hentryGap : inverseWishartEntryGap (K - N) N =
      concreteCOEExponent N K := by
    unfold inverseWishartEntryGap concreteCOEExponent
    rw [Nat.cast_sub hNK]
    ring
  refine ⟨fun i j l m ↦ ?_⟩
  have hraw :=
    integral_inverseWishart_entry_mul_entry_standardGaussian_eq_conditional
      (k := K - N) (p := N) (by omega) Hstein i j l m
  rw [hentryGap] at hraw
  rw [show
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        scaledInverseWishartMatrix N K H i j *
          scaledInverseWishartMatrix N K H l m) =
      (fun H ↦ concreteCOEExponent N K ^ 2 *
        ((realWishartGram H)⁻¹ i j * (realWishartGram H)⁻¹ l m)) by
    funext H
    simp only [scaledInverseWishartMatrix, Matrix.smul_apply, smul_eq_mul]
    ring]
  rw [integral_const_mul, hraw]
  have hden : inverseWishartSecondMomentDenominator
      (concreteCOEExponent N K) =
      (concreteCOEExponent N K - 2) *
        (concreteCOEExponent N K + 1) := by
    unfold inverseWishartSecondMomentDenominator
    ring
  rw [hden]
  have hc2pos : 2 < concreteCOEExponent N K := by
    have hgapR : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    unfold concreteCOEExponent
    linarith
  have hc : 0 < concreteCOEExponent N K := by linarith
  have hc2 : concreteCOEExponent N K - 2 ≠ 0 := by linarith
  have hcp1 : concreteCOEExponent N K + 1 ≠ 0 := by linarith
  field_simp [hc.ne', hc2, hcp1]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
