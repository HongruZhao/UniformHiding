import A4.DirectMomentsGaussianWick
import A4.MatchingGramColoring
import A4.MatchingGramColoringSum
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- All finite products of complex linear forms of an actual iid standard
Gaussian field are integrable. -/
theorem integrable_complexAuxiliaryFieldProduct_standardGaussian
    {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
    (X : K → I → ℂ) :
    Integrable (A4Standalone.GramHafnian.complexAuxiliaryFieldProduct X)
      (Measure.pi fun _ : K ↦ gaussianReal 0 1) := by
  classical
  rw [show A4Standalone.GramHafnian.complexAuxiliaryFieldProduct X =
      fun z ↦ ∑ c : I → K,
        A4Standalone.GramHafnian.complexColoringCoefficient X c *
          A4Standalone.GramHafnian.complexCoordinatePowerProduct
            (A4Standalone.GramHafnian.colorMultiplicity c) z by
    funext z
    exact A4Standalone.GramHafnian.complexAuxiliaryFieldProduct_eq_coloringSum X z]
  apply integrable_finsetSum
  intro c _
  apply Integrable.const_mul
  unfold A4Standalone.GramHafnian.complexCoordinatePowerProduct
  exact Integrable.fintype_prod
    (E := ℝ) (μ := fun _ : K ↦ gaussianReal 0 1)
    (f := fun a x ↦ (x : ℂ) ^ A4Standalone.GramHafnian.colorMultiplicity c a)
    (fun a ↦ by
      have hc : Integrable
          (fun x : ℝ ↦ ((x ^ A4Standalone.GramHafnian.colorMultiplicity c a : ℝ) : ℂ))
          (gaussianReal 0 1) :=
        (A4Standalone.GramHafnian.integrable_pow_gaussianReal
          (A4Standalone.GramHafnian.colorMultiplicity c a)).ofReal
      simpa only [Complex.ofReal_pow] using
        hc)

/-- The exact Wick formula with involution pairings, before canonical slot
notation is applied. -/
theorem integral_gaussian_linear_product_eq_pairPartitions {n r : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) :
    (∫ z, A4Standalone.GramHafnian.complexAuxiliaryFieldProduct X z
      ∂(Measure.pi fun _ : Fin r ↦ gaussianReal 0 1)) =
      ∑ N : PM n, ∏ i : N.pairReps, ∑ a : Fin r, X a i.1 * X a (N i.1) := by
  calc
    _ = A4Standalone.GramHafnian.gaussianWickColoringSum X :=
      A4Standalone.GramHafnian.integral_complexAuxiliaryFieldProduct_standardGaussian X
    _ = A4Standalone.GramHafnian.gramMatchingColoringSum X :=
      A4Standalone.GramHafnian.gaussianWickColoringSum_eq_gramMatchingColoringSum X
    _ = _ := ?_
  unfold A4Standalone.GramHafnian.gramMatchingColoringSum
  apply Finset.sum_congr rfl
  intro N _
  simpa only [A4Standalone.GramHafnian.coloredMatchingMonomial] using
    (Fintype.prod_sum (fun (i : N.pairReps) (a : Fin r) ↦ X a i.1 * X a (N i.1))).symm

/-- One linear form in one independent Gaussian row. -/
def gaussianRowLinear {n r k : ℕ} (X : Matrix (Fin r) (Fin (2 * n)) ℂ)
    (z : Fin (k * r) → ℝ) (c : Fin k) (i : Fin (2 * n)) : ℂ :=
  ∑ a : Fin r, (z (finProdFinEquiv (c, a)) : ℂ) * X a i

/-- A slotwise entry of the transpose Gram of `k` independent Gaussian rows. -/
def gaussianGramSlot {n r k : ℕ} (X : Matrix (Fin r) (Fin (2 * n)) ℂ)
    (z : Fin (k * r) → ℝ) (i j : Fin (2 * n)) : ℂ :=
  ∑ c : Fin k, gaussianRowLinear X z c i * gaussianRowLinear X z c j

/-- Sparse linear coefficients select the row assigned to each slot. -/
def maskedGaussianCoefficients {n r k : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) (c : Fin (2 * n) → Fin k) :
    Matrix (Fin (k * r)) (Fin (2 * n)) ℂ :=
  fun a i ↦ if (finProdFinEquiv.symm a).1 = c i
    then X (finProdFinEquiv.symm a).2 i else 0

theorem sum_maskedGaussianCoefficients_mul {n r k : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) (c : Fin (2 * n) → Fin k)
    (i j : Fin (2 * n)) :
    (∑ a : Fin (k * r),
      maskedGaussianCoefficients X c a i * maskedGaussianCoefficients X c a j) =
      if c i = c j then ∑ a : Fin r, X a i * X a j else 0 := by
  classical
  rw [← (finProdFinEquiv : Fin k × Fin r ≃ Fin (k * r)).sum_comp
    (fun a ↦ maskedGaussianCoefficients X c a i * maskedGaussianCoefficients X c a j),
    Fintype.sum_prod_type]
  simp only [maskedGaussianCoefficients, Equiv.symm_apply_apply]
  by_cases h : c i = c j
  · simp [h]
  · simp [h, Ne.symm h, ite_mul, mul_ite]

theorem complexAuxiliaryFieldProduct_masked {n r k : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) (c : Fin (2 * n) → Fin k)
    (z : Fin (k * r) → ℝ) :
    A4Standalone.GramHafnian.complexAuxiliaryFieldProduct
      (maskedGaussianCoefficients X c) z =
      ∏ i : Fin (2 * n), gaussianRowLinear X z (c i) i := by
  classical
  unfold A4Standalone.GramHafnian.complexAuxiliaryFieldProduct gaussianRowLinear
  apply Finset.prod_congr rfl
  intro i _
  rw [← (finProdFinEquiv : Fin k × Fin r ≃ Fin (k * r)).sum_comp
    (fun a ↦ (z a : ℂ) * maskedGaussianCoefficients X c a i), Fintype.sum_prod_type]
  simp [maskedGaussianCoefficients, mul_ite]

theorem product_gaussianGramSlot_eq_pairColoringSum {n r k : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) (M : PM n)
    (z : Fin (k * r) → ℝ) :
    (∏ i : M.pairReps, gaussianGramSlot X z i.1 (M i.1)) =
      ∑ c : A4Standalone.GramHafnian.PairColoring M k,
        A4Standalone.GramHafnian.complexAuxiliaryFieldProduct
          (maskedGaussianCoefficients X
            (A4Standalone.GramHafnian.vertexColoringOfPairColoring M c)) z := by
  classical
  unfold gaussianGramSlot
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [complexAuxiliaryFieldProduct_masked]
  exact (A4Standalone.GramHafnian.complexColoringCoefficient_vertexColoringOfPairColoring
    (fun a i ↦ gaussianRowLinear X z a i) M c).symm

theorem integrable_product_gaussianGramSlot {n r k : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) (M : PM n) :
    Integrable (fun z : Fin (k * r) → ℝ ↦
      ∏ i : M.pairReps, gaussianGramSlot X z i.1 (M i.1))
      (Measure.pi fun _ : Fin (k * r) ↦ gaussianReal 0 1) := by
  classical
  rw [show (fun z : Fin (k * r) → ℝ ↦
      ∏ i : M.pairReps, gaussianGramSlot X z i.1 (M i.1)) =
      fun z ↦ ∑ c : A4Standalone.GramHafnian.PairColoring M k,
        A4Standalone.GramHafnian.complexAuxiliaryFieldProduct
          (maskedGaussianCoefficients X
            (A4Standalone.GramHafnian.vertexColoringOfPairColoring M c)) z by
    funext z
    exact product_gaussianGramSlot_eq_pairColoringSum X M z]
  exact integrable_finsetSum _ fun c _ ↦
    integrable_complexAuxiliaryFieldProduct_standardGaussian _

/-- Actual Gaussian Gram moments, expanded into both-matchings compatible
row assignments. The next finite regrouping replaces this count by `k^κ`. -/
theorem integral_product_gaussianGramSlot_eq_coloredPairPartitions {n r k : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) (M : PM n) :
    (∫ z : Fin (k * r) → ℝ,
      (∏ i : M.pairReps, gaussianGramSlot X z i.1 (M i.1))
      ∂(Measure.pi fun _ : Fin (k * r) ↦ gaussianReal 0 1)) =
      ∑ N : PM n, ∑ c : A4Standalone.GramHafnian.PairColoring M k,
        ∏ i : N.pairReps,
          if A4Standalone.GramHafnian.vertexColoringOfPairColoring M c i.1 =
              A4Standalone.GramHafnian.vertexColoringOfPairColoring M c (N i.1)
          then ∑ a : Fin r, X a i.1 * X a (N i.1) else 0 := by
  classical
  simp_rw [product_gaussianGramSlot_eq_pairColoringSum X M]
  rw [integral_finsetSum]
  · simp_rw [integral_gaussian_linear_product_eq_pairPartitions,
      sum_maskedGaussianCoefficients_mul]
    exact Finset.sum_comm
  · intro c _
    exact integrable_complexAuxiliaryFieldProduct_standardGaussian _

/-- The complete all-degree iid real-Gaussian Gram tensor moment formula.
Each connected component of the two matchings contributes one independent
row color, hence the literal loop coefficient `k^κ`. -/
theorem integral_product_gaussianGramSlot_eq_loop_moments {n r k : ℕ}
    (X : Matrix (Fin r) (Fin (2 * n)) ℂ) (M : PM n) :
    (∫ z : Fin (k * r) → ℝ,
      (∏ i : M.pairReps, gaussianGramSlot X z i.1 (M i.1))
      ∂(Measure.pi fun _ : Fin (k * r) ↦ gaussianReal 0 1)) =
      ∑ N : PM n, (k : ℂ) ^ matchingKappa M N *
        ∏ i : N.pairReps, ∑ a : Fin r, X a i.1 * X a (N i.1) := by
  classical
  rw [integral_product_gaussianGramSlot_eq_coloredPairPartitions]
  apply Finset.sum_congr rfl
  intro N _
  simp_rw [Fintype.prod_ite_zero]
  calc
    _ = (∑ c : A4Standalone.GramHafnian.PairColoring M k,
        if ∀ i : N.pairReps,
          A4Standalone.GramHafnian.vertexColoringOfPairColoring M c i.1 =
            A4Standalone.GramHafnian.vertexColoringOfPairColoring M c (N i.1)
        then (1 : ℂ) else 0) *
        ∏ i : N.pairReps, ∑ a : Fin r, X a i.1 * X a (N i.1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    _ = _ := by rw [sum_pairColoring_compatible_eq_loop_power]

end MatsumotoPaper
