import A4.DirectMomentsWickRegrouping
import A4.MatchingGramCanonical
import A4.DirectMomentsGaussianScalar

/-!
The required iid-Gaussian integration proofs are isolated from the preserved
original `AuxiliaryFieldExpansion.lean` and `AuxiliaryGaussian.lean`.
All imports are within A4 or mathlib. The generic hypotheses below are
instantiated with mathlib's actual standard Gaussian measure.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace A4Standalone.GramHafnian

variable {I K : Type*} [Fintype I] [Fintype K]
  [DecidableEq I] [DecidableEq K]

theorem prod_comp_eq_coordinatePowerProduct
    {R : Type*} [CommMonoid R] (c : I → K) (g : K → R) :
    (∏ i, g (c i)) = ∏ a, (g a) ^ colorMultiplicity c a := by
  rw [← Finset.prod_fiberwise' Finset.univ c g]
  apply Finset.prod_congr rfl
  intro a _
  rw [Finset.prod_const]
  rfl

/-- Coordinate powers of a real field, embedded into `ℂ`. -/
def complexCoordinatePowerProduct (e : K → ℕ) (g : K → ℝ) : ℂ :=
  ∏ a, (g a : ℂ) ^ (e a)

/-- Product of complex linear forms driven by a real auxiliary field. -/
def complexAuxiliaryFieldProduct (X : K → I → ℂ) (g : K → ℝ) : ℂ :=
  ∏ i, ∑ a, (g a : ℂ) * X a i

theorem complexAuxiliaryFieldProduct_eq_coloringSum
    (X : K → I → ℂ) (g : K → ℝ) :
    complexAuxiliaryFieldProduct X g =
      ∑ c : I → K,
        complexColoringCoefficient X c *
          complexCoordinatePowerProduct (colorMultiplicity c) g := by
  classical
  unfold complexAuxiliaryFieldProduct
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold complexColoringCoefficient complexCoordinatePowerProduct
  have hp : (∏ i, (g (c i) : ℂ)) =
      ∏ a, (g a : ℂ) ^ colorMultiplicity c a :=
    prod_comp_eq_coordinatePowerProduct c (fun a ↦ (g a : ℂ))
  rw [← hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem integral_complexCoordinatePowerProduct_pi
    (mu : Measure ℝ) [SigmaFinite mu] (e : K → ℕ) :
    ∫ g, complexCoordinatePowerProduct e g
        ∂(Measure.pi fun _ : K ↦ mu) =
      ∏ a, ∫ x, (x : ℂ) ^ (e a) ∂mu := by
  unfold complexCoordinatePowerProduct
  exact integral_fintype_prod_eq_prod
    (E := fun _ : K ↦ ℝ) (μ := fun _ : K ↦ mu)
    (fun a x ↦ (x : ℂ) ^ (e a))

/-- Exact iid real-field expansion with complex deterministic coefficients. -/
theorem integral_complexAuxiliaryFieldProduct_eq_weightedColoringSum
    (mu : Measure ℝ) [SigmaFinite mu]
    (hInt : ∀ r : ℕ, Integrable (fun x : ℝ ↦ x ^ r) mu)
    (scalarMoment : ℕ → ℝ)
    (hMoment : ∀ r : ℕ, ∫ x, x ^ r ∂mu = scalarMoment r)
    (X : K → I → ℂ) :
    ∫ g, complexAuxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : K ↦ mu) =
      ∑ c : I → K,
        complexColoringCoefficient X c *
          ∏ a, (scalarMoment (colorMultiplicity c a) : ℂ) := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (complexAuxiliaryFieldProduct_eq_coloringSum X))]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul, integral_complexCoordinatePowerProduct_pi]
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    simp_rw [← Complex.ofReal_pow]
    rw [integral_complex_ofReal, hMoment (colorMultiplicity c a)]
  · intro c _
    apply Integrable.const_mul
    unfold complexCoordinatePowerProduct
    exact Integrable.fintype_prod
      (E := ℝ)
      (μ := fun _ : K ↦ mu)
      (f := fun a x ↦ (x : ℂ) ^ colorMultiplicity c a)
      (fun a ↦ by
        have hr := hInt (colorMultiplicity c a)
        have hc : Integrable
            (fun x : ℝ ↦ ((x ^ colorMultiplicity c a : ℝ) : ℂ)) mu :=
          hr.ofReal
        simpa only [Complex.ofReal_pow] using hc)

theorem integral_pow_gaussianReal_eq_standardRealGaussianMoment (r : ℕ) :
    (∫ x : ℝ, x ^ r ∂gaussianReal 0 1) = standardRealGaussianMoment r := by
  rcases Nat.even_or_odd r with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · simpa [two_mul, standardRealGaussianMoment] using
      integral_pow_two_gaussianReal n
  · have hne : ¬ Even (n + n + 1) :=
      Nat.not_even_iff_odd.mpr ⟨n, by omega⟩
    simpa [two_mul, standardRealGaussianMoment, hne] using
      integral_pow_odd_gaussianReal n

/-- Exact row-colouring formula for a real iid standard-Gaussian auxiliary
field and arbitrary complex deterministic coefficients. -/
theorem integral_complexAuxiliaryFieldProduct_standardGaussian
    (X : K → I → ℂ) :
    ∫ g, complexAuxiliaryFieldProduct X g
        ∂(Measure.pi fun _ : K ↦ gaussianReal 0 1) =
      ∑ c : I → K,
        complexColoringCoefficient X c *
          ∏ a, (standardRealGaussianMoment (colorMultiplicity c a) : ℂ) := by
  exact integral_complexAuxiliaryFieldProduct_eq_weightedColoringSum
    (mu := gaussianReal 0 1)
    integrable_pow_gaussianReal
    standardRealGaussianMoment
    integral_pow_gaussianReal_eq_standardRealGaussianMoment
    X


end A4Standalone.GramHafnian

noncomputable section

namespace MatsumotoPaper

/-- Pair representatives indexed in their canonical increasing order. -/
def wickMatchingPairRepsEquiv {n : ℕ}
    (M : A4Standalone.GramHafnian.PerfectMatching n) : Fin n ≃ M.pairReps :=
  Equiv.ofBijective (fun i ↦ ⟨matchingPairOrder M i, matchingPairOrder_mem M i⟩)
    ⟨by
      intro i j hij
      apply (matchingPairOrder M).injective
      exact congrArg Subtype.val hij,
    by
      intro j
      obtain ⟨i, hi⟩ := matchingPairOrder_surjective M j.2
      exact ⟨i, Subtype.ext hi⟩⟩

/-- A Gram covariance pairing may be evaluated either on pair representatives
or on the literal canonical permutation slots. -/
theorem wick_pairProduct_eq_canonicalSlots {n k : ℕ}
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ)
    (M : A4Standalone.GramHafnian.PerfectMatching n) :
    (∏ i : M.pairReps, ∑ a : Fin k, X a i.1 * X a (M i.1)) =
      ∏ i : Fin n, ∑ a : Fin k,
        X a (canonicalMatchingPermutation M (leftSlot i)) *
          X a (canonicalMatchingPermutation M (rightSlot i)) := by
  rw [← (wickMatchingPairRepsEquiv M).prod_comp
    (fun i : M.pairReps ↦ ∑ a : Fin k, X a i.1 * X a (M i.1))]
  simp only [canonicalMatchingPermutation_left, canonicalMatchingPermutation_right]
  rfl

/-- The all-degree real-Gaussian Wick identity in A4's literal canonical
matching notation. Its covariance is the transpose Gram `X^T X`, with no
conjugation of the arbitrary complex linear coefficients. -/
theorem integral_gaussian_linear_product_eq_canonicalMatchings {n k : ℕ}
    (X : Matrix (Fin k) (Fin (2 * n)) ℂ) :
    (∫ z, A4Standalone.GramHafnian.complexAuxiliaryFieldProduct X z
      ∂(Measure.pi fun _ : Fin k ↦ gaussianReal 0 1)) =
      ∑ M : PerfectMatching n, ∏ i : Fin n,
        ∑ a : Fin k, X a (M.toPerm (leftSlot i)) *
          X a (M.toPerm (rightSlot i)) := by
  let f := fun M : A4Standalone.GramHafnian.PerfectMatching n ↦
    ∏ i : M.pairReps, ∑ a : Fin k, X a i.1 * X a (M i.1)
  have hpair : A4Standalone.GramHafnian.gramMatchingColoringSum X = ∑ M, f M := by
    unfold A4Standalone.GramHafnian.gramMatchingColoringSum
    apply Finset.sum_congr rfl
    intro M _
    simpa only [f, A4Standalone.GramHafnian.coloredMatchingMonomial] using
      (Fintype.prod_sum (fun (i : M.pairReps) (a : Fin k) ↦
        X a i.1 * X a (M i.1))).symm
  calc
    _ = A4Standalone.GramHafnian.gaussianWickColoringSum X :=
      A4Standalone.GramHafnian.integral_complexAuxiliaryFieldProduct_standardGaussian X
    _ = A4Standalone.GramHafnian.gramMatchingColoringSum X :=
      A4Standalone.GramHafnian.gaussianWickColoringSum_eq_gramMatchingColoringSum X
    _ = ∑ M, f M := hpair
    _ = ∑ M : PerfectMatching n, f (canonicalToPairPartition M) :=
      (sum_canonical_eq_sum_pairPartition f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro M _
      have hperm : canonicalMatchingPermutation (canonicalToPairPartition M) = M.toPerm := by
        have h := congrArg PerfectMatching.toPerm
          (pairPartitionToCanonical_canonicalToPairPartition M)
        exact h
      have hprod := wick_pairProduct_eq_canonicalSlots X (canonicalToPairPartition M)
      rw [hperm] at hprod
      exact hprod

end MatsumotoPaper
