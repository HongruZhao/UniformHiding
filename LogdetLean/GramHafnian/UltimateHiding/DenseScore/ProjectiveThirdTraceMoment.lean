import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveSecondMoment
import Mathlib.Tactic

/-!
# Exact third complex-projective trace moment

This file derives the cubic trace contraction from the internally proved
order-three complex-projective tensor identity.  No cubic score, moment
bound, total variation, or hiding statement is assumed here.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- A product of three entries of a rank-one projective matrix is integrable. -/
theorem integrable_complexRankOneProjection_entry_mul_three
    {N : ℕ} (hN : 1 ≤ N)
    (i j k l p q : Fin N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexRankOneProjection v i j *
        complexRankOneProjection v k l *
        complexRankOneProjection v p q)
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  apply (integrable_const (1 : ℝ)).mono
  · exact (((((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp
          (measurable_complexRankOneProjection N))).mul
      ((measurable_pi_apply l).comp
        ((measurable_pi_apply k).comp
          (measurable_complexRankOneProjection N)))).mul
      ((measurable_pi_apply q).comp
        ((measurable_pi_apply p).comp
          (measurable_complexRankOneProjection N))))).aestronglyMeasurable
  · filter_upwards [] with v
    rw [norm_one, norm_mul, norm_mul]
    have h₁ := norm_complexRankOneProjection_entry_le_one v i j
    have h₂ := norm_complexRankOneProjection_entry_le_one v k l
    have h₃ := norm_complexRankOneProjection_entry_le_one v p q
    have hn₁ := norm_nonneg (complexRankOneProjection v i j)
    have hn₂ := norm_nonneg (complexRankOneProjection v k l)
    have hn₃ := norm_nonneg (complexRankOneProjection v p q)
    calc
      ‖complexRankOneProjection v i j‖ *
            ‖complexRankOneProjection v k l‖ *
            ‖complexRankOneProjection v p q‖ ≤
          (1 : ℝ) * 1 * ‖complexRankOneProjection v p q‖ := by
            gcongr
      _ ≤ 1 := by simpa using h₃

private def permThree01 : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1

private def permThree02 : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 2

private def permThree12 : Equiv.Perm (Fin 3) :=
  Equiv.swap (1 : Fin 3) 2

private def permThree012 : Equiv.Perm (Fin 3) :=
  permThree12.trans permThree01

private def permThree021 : Equiv.Perm (Fin 3) :=
  permThree01.trans permThree12

private theorem sum_perm_fin_three (F : Equiv.Perm (Fin 3) → ℂ) :
    (∑ π, F π) =
      F (Equiv.refl _) + F permThree01 + F permThree02 + F permThree12 +
        F permThree012 + F permThree021 := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {Equiv.refl _, permThree01, permThree02, permThree12,
        permThree012, permThree021} := by
    decide
  have h0 : Equiv.refl (Fin 3) ∉
      ({permThree01, permThree02, permThree12,
        permThree012, permThree021} : Finset (Equiv.Perm (Fin 3))) := by
    decide
  have h1 : permThree01 ∉
      ({permThree02, permThree12, permThree012, permThree021} :
        Finset (Equiv.Perm (Fin 3))) := by
    decide
  have h2 : permThree02 ∉
      ({permThree12, permThree012, permThree021} :
        Finset (Equiv.Perm (Fin 3))) := by
    decide
  have h3 : permThree12 ∉
      ({permThree012, permThree021} : Finset (Equiv.Perm (Fin 3))) := by
    decide
  have h4 : permThree012 ≠ permThree021 := by decide
  rw [huniv, Finset.sum_insert h0, Finset.sum_insert h1,
    Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_insert (by simpa using h4), Finset.sum_singleton]
  ring

/-- The six Kronecker-delta contractions associated with `S₃`. -/
private def projectiveThirdPermutationDelta {N : ℕ}
    (i j k l p q : Fin N) : ℂ :=
  (if i = j then 1 else 0) * (if k = l then 1 else 0) *
      (if p = q then 1 else 0) +
    (if i = l then 1 else 0) * (if k = j then 1 else 0) *
      (if p = q then 1 else 0) +
    (if i = q then 1 else 0) * (if k = l then 1 else 0) *
      (if p = j then 1 else 0) +
    (if i = j then 1 else 0) * (if k = q then 1 else 0) *
      (if p = l then 1 else 0) +
    (if i = l then 1 else 0) * (if k = q then 1 else 0) *
      (if p = j then 1 else 0) +
    (if i = q then 1 else 0) * (if k = j then 1 else 0) *
      (if p = l then 1 else 0)

/-- A triple finite sum is invariant under swapping its first and third
indices.  This tiny reindexing lemma keeps the cubic trace contraction
transparent to the simplifier. -/
private theorem sum_three_swap_first_third
    {α R : Type*} [Fintype α] [AddCommMonoid R]
    (f : α → α → α → R) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      ∑ i, ∑ j, ∑ k, f k j i := by
  calc
    (∑ i, ∑ j, ∑ k, f i j k) =
        ∑ i, ∑ k, ∑ j, f i j k := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, f i j k := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ j, ∑ i, f i j k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ k, f k j i := rfl

private theorem sum_three_congr
    {α R : Type*} [Fintype α] [AddCommMonoid R]
    {f g : α → α → α → R}
    (h : ∀ i j k, f i j k = g i j k) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, g i j k := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact h i j k

/-- Third entry moment, written as the six permutation contractions. -/
theorem integral_complexRankOneProjection_entry_mul_three
    {N : ℕ} (hN : 1 ≤ N)
    (i j k l p q : Fin N) :
    (∫ v : ComplexUnitSphere N,
      complexRankOneProjection v i j *
        complexRankOneProjection v k l *
        complexRankOneProjection v p q
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹ : ℝ) : ℂ) *
        projectiveThirdPermutationDelta i j k l p q := by
  have h := complexProjectiveTensorMoment_le_four_internal
    (N := N) (r := 3) hN (by norm_num)
      (fun a ↦ if a = 0 then i else if a = 1 then k else p)
      (fun a ↦ if a = 0 then j else if a = 1 then l else q)
  unfold complexProjectiveSymmetrizerCoordinate at h
  rw [sum_perm_fin_three] at h
  have h010 : permThree01 (0 : Fin 3) = 1 := by decide
  have h011 : permThree01 (1 : Fin 3) = 0 := by decide
  have h012 : permThree01 (2 : Fin 3) = 2 := by decide
  have h020 : permThree02 (0 : Fin 3) = 2 := by decide
  have h021 : permThree02 (1 : Fin 3) = 1 := by decide
  have h022 : permThree02 (2 : Fin 3) = 0 := by decide
  have h120 : permThree12 (0 : Fin 3) = 0 := by decide
  have h121 : permThree12 (1 : Fin 3) = 2 := by decide
  have h122 : permThree12 (2 : Fin 3) = 1 := by decide
  have hc120 : permThree012 (0 : Fin 3) = 1 := by decide
  have hc121 : permThree012 (1 : Fin 3) = 2 := by decide
  have hc122 : permThree012 (2 : Fin 3) = 0 := by decide
  have hc210 : permThree021 (0 : Fin 3) = 2 := by decide
  have hc211 : permThree021 (1 : Fin 3) = 0 := by decide
  have hc212 : permThree021 (2 : Fin 3) = 1 := by decide
  simpa [complexProjectiveTensorMomentCoordinate,
    complexProjectiveRisingFactorial, Fin.prod_univ_three,
    projectiveThirdPermutationDelta,
    h010, h011, h012, h020, h021, h022, h120, h121, h122,
    hc120, hc121, hc122, hc210, hc211, hc212] using h

private theorem sum_projectiveThirdPermutationDelta_same
    {N : ℕ} (d : ℂ) (A : ConcreteMatrixState N) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
      (d * projectiveThirdPermutationDelta i j k l p q) *
        (A j i * A l k * A q p)) =
      d * (Matrix.trace A ^ 3 +
        3 * Matrix.trace A * Matrix.trace (A * A) +
        2 * Matrix.trace (A * A * A)) := by
  classical
  have hswap := sum_three_swap_first_third
    (fun x x₁ x₂ : Fin N ↦ d * A x x * A x₂ x₁ * A x₁ x₂)
  have hdiag :
      (∑ x, ∑ x₁, ∑ x₂, d * A x x * A x₁ x₁ * A x₂ x₂) =
        ∑ x, ∑ x₁, ∑ x₂, d * A x₂ x₂ * A x₁ x₁ * A x x := by
    apply sum_three_congr
    intros
    ring
  have htransOne :
      (∑ x, ∑ x₁, ∑ x₂, d * A x₁ x * A x x₁ * A x₂ x₂) =
        ∑ x, ∑ x₁, ∑ x₂, d * A x₂ x₂ * A x x₁ * A x₁ x := by
    apply sum_three_congr
    intros
    ring
  have htransTwo :
      (∑ x, ∑ x₁, ∑ x₂, d * A x₁ x * A x₂ x₂ * A x x₁) =
        ∑ x, ∑ x₁, ∑ x₂, d * A x₂ x₂ * A x x₁ * A x₁ x := by
    apply sum_three_congr
    intros
    ring
  have hcycleOne :
      (∑ x, ∑ x₁, ∑ x₂, d * A x₁ x * A x x₂ * A x₂ x₁) =
        ∑ x, ∑ x₁, ∑ x₂, d * A x x₂ * A x₂ x₁ * A x₁ x := by
    apply sum_three_congr
    intros
    ring
  have hcycleTwo :
      (∑ x, ∑ x₁, ∑ x₂, d * A x₁ x * A x₂ x₁ * A x x₂) =
        ∑ x, ∑ x₁, ∑ x₂, d * A x x₂ * A x₂ x₁ * A x₁ x := by
    apply sum_three_congr
    intros
    ring
  have htraceDiag :
      d * Matrix.trace A ^ 3 =
        ∑ x, ∑ x₁, ∑ x₂, d * A x₂ x₂ * A x₁ x₁ * A x x := by
    simp only [Matrix.trace, Matrix.diag_apply, pow_succ, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply sum_three_congr
    intros
    ring
  have htracePair :
      d * (Matrix.trace A * Matrix.trace (A * A)) =
        ∑ x, ∑ x₁, ∑ x₂, d * A x₂ x₂ * A x x₁ * A x₁ x := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply sum_three_congr
    intros
    ring
  have htraceCycle :
      d * Matrix.trace (A * A * A) =
        ∑ x, ∑ x₁, ∑ x₂, d * A x x₂ * A x₂ x₁ * A x₁ x := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply sum_three_congr
    intros
    ring
  conv_lhs =>
    unfold projectiveThirdPermutationDelta
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    simp
  simp only [mul_assoc] at hdiag htransOne htransTwo hswap hcycleOne hcycleTwo htraceDiag htracePair htraceCycle ⊢
  rw [hdiag, htransOne, htransTwo, hswap, hcycleOne, hcycleTwo]
  rw [← htraceDiag, ← htracePair, ← htraceCycle]
  ring

/-- A cube of one projective trace pairing is integrable. -/
theorem integrable_complexProjectiveTracePair_cube
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A ^ 3)
      (complexUnitSphereProbabilityMeasure N) := by
  rw [show (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A ^ 3) =
      fun v ↦ complexProjectiveTracePair v A *
        complexProjectiveTracePair v A * complexProjectiveTracePair v A by
    funext v
    ring]
  unfold complexProjectiveTracePair
  have hbase : Integrable (fun v : ComplexUnitSphere N ↦
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
        (complexRankOneProjection v i j *
          complexRankOneProjection v k l *
          complexRankOneProjection v p q) *
          (A j i * A l k * A q p))
      (complexUnitSphereProbabilityMeasure N) :=
    integrable_finsetSum _ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦
        integrable_finsetSum _ fun k _ ↦
          integrable_finsetSum _ fun l _ ↦
            integrable_finsetSum _ fun p _ ↦
              integrable_finsetSum _ fun q _ ↦
                (integrable_complexRankOneProjection_entry_mul_three
                  hN i j k l p q).mul_const _
  convert hbase using 1
  funext v
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem complexProjectiveTracePair_cube_eq_sum
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexProjectiveTracePair v A ^ 3 =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
        (complexRankOneProjection v i j *
          complexRankOneProjection v k l *
          complexRankOneProjection v p q) *
          (A j i * A l k * A q p) := by
  unfold complexProjectiveTracePair
  rw [pow_succ, pow_two]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The invariant cubic trace-pairing moment

`E[Tr(P_v A)^3] = ((Tr A)^3 + 3 Tr A Tr(A^2) + 2 Tr(A^3)) /
  (N(N+1)(N+2))`.

This is derived internally from the general projective tensor atom. -/
theorem integral_complexProjectiveTracePair_cube
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexProjectiveTracePair v A ^ 3
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹ : ℝ) : ℂ) *
        (Matrix.trace A ^ 3 +
          3 * Matrix.trace A * Matrix.trace (A * A) +
          2 * Matrix.trace (A * A * A)) := by
  rw [show (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A ^ 3) =
      fun v ↦ ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
        (complexRankOneProjection v i j *
          complexRankOneProjection v k l *
          complexRankOneProjection v p q) *
          (A j i * A l k * A q p) by
    funext v
    exact complexProjectiveTracePair_cube_eq_sum v A]
  calc
    (∫ v : ComplexUnitSphere N,
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
        (complexRankOneProjection v i j *
          complexRankOneProjection v k l *
          complexRankOneProjection v p q) *
          (A j i * A l k * A q p)
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
        ∫ v : ComplexUnitSphere N,
          (complexRankOneProjection v i j *
            complexRankOneProjection v k l *
            complexRankOneProjection v p q) *
            (A j i * A l k * A q p)
          ∂(complexUnitSphereProbabilityMeasure N) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro k _
            rw [integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro l _
              rw [integral_finsetSum]
              · apply Finset.sum_congr rfl
                intro p _
                rw [integral_finsetSum]
                exact fun q _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j k l p q).mul_const _
              · exact fun p _ ↦ integrable_finsetSum _ fun q _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j k l p q).mul_const _
            · exact fun l _ ↦ integrable_finsetSum _ fun p _ ↦
                integrable_finsetSum _ fun q _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j k l p q).mul_const _
          · exact fun k _ ↦ integrable_finsetSum _ fun l _ ↦
              integrable_finsetSum _ fun p _ ↦
                integrable_finsetSum _ fun q _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j k l p q).mul_const _
        · exact fun j _ ↦ integrable_finsetSum _ fun k _ ↦
            integrable_finsetSum _ fun l _ ↦
              integrable_finsetSum _ fun p _ ↦
                integrable_finsetSum _ fun q _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j k l p q).mul_const _
      · exact fun i _ ↦ integrable_finsetSum _ fun j _ ↦
          integrable_finsetSum _ fun k _ ↦
            integrable_finsetSum _ fun l _ ↦
              integrable_finsetSum _ fun p _ ↦
                integrable_finsetSum _ fun q _ ↦
                  (integrable_complexRankOneProjection_entry_mul_three
                    hN i j k l p q).mul_const _
    _ = ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹ : ℝ) : ℂ) *
        (Matrix.trace A ^ 3 +
          3 * Matrix.trace A * Matrix.trace (A * A) +
          2 * Matrix.trace (A * A * A)) := by
      simp_rw [integral_mul_const,
        integral_complexRankOneProjection_entry_mul_three hN]
      exact sum_projectiveThirdPermutationDelta_same _ A

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
