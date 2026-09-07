import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ComplexProjectiveTensorMomentInternal
import Mathlib.Tactic

/-!
# Concrete first and second complex-projective moments

This file derives the entrywise first and second moments needed by the
quadratic COE contraction from the internally proved low-order complex
projective tensor identity.  No external Collins--Sniady tensor atom is used.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Every coordinate of a rank-one projective matrix has norm at most one. -/
theorem norm_complexRankOneProjection_entry_le_one
    {N : ℕ} (v : ComplexUnitSphere N) (i j : Fin N) :
    ‖complexRankOneProjection v i j‖ ≤ 1 := by
  simp only [complexRankOneProjection, norm_mul, norm_star]
  have hi : ‖v.1 i‖ ≤ 1 := (PiLp.norm_apply_le v.1 i).trans_eq
    (mem_sphere_zero_iff_norm.mp v.2)
  have hj : ‖v.1 j‖ ≤ 1 := (PiLp.norm_apply_le v.1 j).trans_eq
    (mem_sphere_zero_iff_norm.mp v.2)
  nlinarith [norm_nonneg (v.1 i), norm_nonneg (v.1 j)]

/-- A single projective entry is integrable under the uniform direction
law. -/
theorem integrable_complexRankOneProjection_entry
    {N : ℕ} (hN : 1 ≤ N) (i j : Fin N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexRankOneProjection v i j)
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  apply (integrable_const (1 : ℝ)).mono
  · exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp
        (measurable_complexRankOneProjection N))).aestronglyMeasurable
  · filter_upwards [] with v
    rw [norm_one]
    exact norm_complexRankOneProjection_entry_le_one v i j

/-- A product of two projective entries is integrable. -/
theorem integrable_complexRankOneProjection_entry_mul
    {N : ℕ} (hN : 1 ≤ N) (i j k l : Fin N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexRankOneProjection v i j * complexRankOneProjection v k l)
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  apply (integrable_const (1 : ℝ)).mono
  · exact ((((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp
          (measurable_complexRankOneProjection N))).mul
      ((measurable_pi_apply l).comp
        ((measurable_pi_apply k).comp
          (measurable_complexRankOneProjection N))))).aestronglyMeasurable
  · filter_upwards [] with v
    rw [norm_one, norm_mul]
    have h₁ := norm_complexRankOneProjection_entry_le_one v i j
    have h₂ := norm_complexRankOneProjection_entry_le_one v k l
    nlinarith [norm_nonneg (complexRankOneProjection v i j),
      norm_nonneg (complexRankOneProjection v k l)]

/-- First entry moment `E P_ij = delta_ij/N`. -/
theorem integral_complexRankOneProjection_entry
    {N : ℕ} (hN : 1 ≤ N) (i j : Fin N) :
    (∫ v : ComplexUnitSphere N, complexRankOneProjection v i j
      ∂(complexUnitSphereProbabilityMeasure N)) =
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0) := by
  have h := complexProjectiveTensorMoment_le_four_internal
    (N := N) (r := 1) hN (by norm_num) (fun _ ↦ i) (fun _ ↦ j)
  simpa [complexProjectiveTensorMomentCoordinate,
    complexProjectiveSymmetrizerCoordinate,
    complexProjectiveRisingFactorial] using h

private theorem sum_perm_fin_two (F : Equiv.Perm (Fin 2) → ℂ) :
    (∑ x, F x) = F (Equiv.refl _) + F (Equiv.swap (0 : Fin 2) 1) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {Equiv.refl _, Equiv.swap (0 : Fin 2) 1} := by decide
  have hswap : Equiv.swap (0 : Fin 2) 1 ≠ Equiv.refl (Fin 2) := by
    decide
  rw [huniv, Finset.sum_insert]
  · simp
  · simpa using hswap.symm

/-- Second entry moment
`E[P_ij P_kl] = (delta_ij delta_kl + delta_il delta_kj)/(N(N+1))`. -/
theorem integral_complexRankOneProjection_entry_mul
    {N : ℕ} (hN : 1 ≤ N) (i j k l : Fin N) :
    (∫ v : ComplexUnitSphere N,
      complexRankOneProjection v i j * complexRankOneProjection v k l
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = l then 1 else 0) * (if k = j then 1 else 0)) := by
  have h := complexProjectiveTensorMoment_le_four_internal
    (N := N) (r := 2) hN (by norm_num)
      (fun a ↦ if a = 0 then i else k)
      (fun a ↦ if a = 0 then j else l)
  unfold complexProjectiveSymmetrizerCoordinate at h
  rw [sum_perm_fin_two] at h
  simpa [complexProjectiveTensorMomentCoordinate,
    complexProjectiveRisingFactorial, Fin.sum_univ_two,
    Finset.sum_insert] using h

/-! ## Trace-pairing consequences -/

/-- The linear trace pairing `Tr(P_v A)`, expanded in coordinates so that
the projective tensor identity applies without any hidden matrix-analysis
input. -/
def complexProjectiveTracePair {N : ℕ}
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℂ :=
  ∑ i, ∑ j, complexRankOneProjection v i j * A j i

theorem complexProjectiveTracePair_eq_trace {N : ℕ}
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexProjectiveTracePair v A =
      Matrix.trace (complexRankOneProjection v * A) := by
  simp only [complexProjectiveTracePair, Matrix.trace, Matrix.mul_apply]
  rfl

theorem integrable_complexProjectiveTracePair
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A)
      (complexUnitSphereProbabilityMeasure N) := by
  unfold complexProjectiveTracePair
  exact integrable_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦
      (integrable_complexRankOneProjection_entry hN i j).mul_const (A j i)

private theorem sum_first_projective_delta {N : ℕ}
    (d : ℂ) (A : ConcreteMatrixState N) :
    (∑ i, ∑ j, (d * (if i = j then 1 else 0)) * A j i) =
      d * Matrix.trace A := by
  classical
  calc
    (∑ i, ∑ j, (d * (if i = j then 1 else 0)) * A j i) =
        ∑ i, d * A i i := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j, (d * (if i = j then 1 else 0)) * A j i) =
            ∑ j, if j = i then d * A j i else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : j = i
          · subst j
            simp
          · have h' : i ≠ j := Ne.symm h
            simp [h, h']
        _ = d * A i i := by simp
    _ = d * Matrix.trace A := by
      rw [Matrix.trace, Finset.mul_sum]
      simp only [Matrix.diag_apply]

private theorem sum_second_projective_delta {N : ℕ}
    (d : ℂ) (A B : ConcreteMatrixState N) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        (d * ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = l then 1 else 0) * (if k = j then 1 else 0))) *
            (A j i * B l k)) =
      d * (Matrix.trace A * Matrix.trace B + Matrix.trace (A * B)) := by
  classical
  have hsplit :
      (∑ i, ∑ j, ∑ k, ∑ l,
          (d * ((if i = j then 1 else 0) * (if k = l then 1 else 0) +
            (if i = l then 1 else 0) * (if k = j then 1 else 0))) *
              (A j i * B l k)) =
        (∑ i, ∑ j, ∑ k, ∑ l,
          d * ((if i = j then 1 else 0) * (if k = l then 1 else 0)) *
            (A j i * B l k)) +
        (∑ i, ∑ j, ∑ k, ∑ l,
          d * ((if i = l then 1 else 0) * (if k = j then 1 else 0)) *
            (A j i * B l k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hdiag :
      (∑ i, ∑ j, ∑ k, ∑ l,
          d * ((if i = j then 1 else 0) * (if k = l then 1 else 0)) *
            (A j i * B l k)) =
        d * (Matrix.trace A * Matrix.trace B) := by
    calc
      (∑ i, ∑ j, ∑ k, ∑ l,
          d * ((if i = j then 1 else 0) * (if k = l then 1 else 0)) *
            (A j i * B l k)) =
          ∑ i, ∑ j, ∑ k, ∑ l,
            if j = i then
              (if l = k then d * (A j i * B l k) else 0)
            else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        by_cases hij : j = i
        · subst j
          by_cases hkl : l = k
          · subst l
            simp
          · have hkl' : k ≠ l := Ne.symm hkl
            simp [hkl, hkl']
        · have hij' : i ≠ j := Ne.symm hij
          simp [hij, hij']
      _ = ∑ i, ∑ k, d * (A i i * B k k) := by simp
      _ = d * (Matrix.trace A * Matrix.trace B) := by
        simp only [Matrix.trace, Matrix.diag_apply,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
  have hcross :
      (∑ i, ∑ j, ∑ k, ∑ l,
          d * ((if i = l then 1 else 0) * (if k = j then 1 else 0)) *
            (A j i * B l k)) = d * Matrix.trace (A * B) := by
    calc
      (∑ i, ∑ j, ∑ k, ∑ l,
          d * ((if i = l then 1 else 0) * (if k = j then 1 else 0)) *
            (A j i * B l k)) =
          ∑ i, ∑ j, ∑ k, ∑ l,
            if l = i then
              (if k = j then d * (A j i * B l k) else 0)
            else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        by_cases hil : l = i
        · subst l
          by_cases hkj : k = j
          · subst k
            simp
          · simp [hkj]
        · have hil' : i ≠ l := Ne.symm hil
          simp [hil, hil']
      _ = ∑ i, ∑ j, d * (A j i * B i j) := by simp
      _ = d * Matrix.trace (A * B) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Finset.mul_sum]
        rw [Finset.sum_comm]
  rw [hsplit, hdiag, hcross]
  ring

/-- `E Tr(P_v A) = Tr(A)/N`, obtained internally from the first entry
moment. -/
theorem integral_complexProjectiveTracePair
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N, complexProjectiveTracePair v A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A := by
  unfold complexProjectiveTracePair
  calc
    (∫ v : ComplexUnitSphere N,
        ∑ i, ∑ j, complexRankOneProjection v i j * A j i
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∑ i, ∫ v : ComplexUnitSphere N,
          ∑ j, complexRankOneProjection v i j * A j i
          ∂(complexUnitSphereProbabilityMeasure N) :=
      integral_finsetSum Finset.univ (fun i _ ↦
        integrable_finsetSum Finset.univ fun j _ ↦
          (integrable_complexRankOneProjection_entry hN i j).mul_const (A j i))
    _ = ∑ i, ∑ j, ∫ v : ComplexUnitSphere N,
          complexRankOneProjection v i j * A j i
          ∂(complexUnitSphereProbabilityMeasure N) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum Finset.univ (fun j _ ↦
        (integrable_complexRankOneProjection_entry hN i j).mul_const (A j i))
    _ = (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A := by
      simp_rw [integral_mul_const,
        integral_complexRankOneProjection_entry hN]
      exact sum_first_projective_delta _ A

/-- A product of two trace pairings is integrable. -/
theorem integrable_complexProjectiveTracePair_mul
    {N : ℕ} (hN : 1 ≤ N)
    (A B : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A * complexProjectiveTracePair v B)
      (complexUnitSphereProbabilityMeasure N) := by
  unfold complexProjectiveTracePair
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hreorder : ∀ (v : ComplexUnitSphere N) (i j k l : Fin N),
      complexRankOneProjection v i j * A j i *
          (complexRankOneProjection v k l * B l k) =
        (complexRankOneProjection v i j * complexRankOneProjection v k l) *
          (A j i * B l k) := by
    intros
    ring
  simp_rw [hreorder]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦
      integrable_finsetSum _ fun k _ ↦
        integrable_finsetSum _ fun l _ ↦
          (integrable_complexRankOneProjection_entry_mul hN i j k l).mul_const
            (A j i * B l k)

/-- The invariant second trace-pairing moment

`E[Tr(P_v A) Tr(P_v B)] = (Tr A Tr B + Tr(AB))/(N(N+1))`.

No downstream score expression appears in this statement. -/
theorem integral_complexProjectiveTracePair_mul
    {N : ℕ} (hN : 1 ≤ N)
    (A B : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexProjectiveTracePair v A * complexProjectiveTracePair v B
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        (Matrix.trace A * Matrix.trace B + Matrix.trace (A * B)) := by
  unfold complexProjectiveTracePair
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hreorder : ∀ (v : ComplexUnitSphere N) (i j k l : Fin N),
      complexRankOneProjection v i j * A j i *
          (complexRankOneProjection v k l * B l k) =
        (complexRankOneProjection v i j * complexRankOneProjection v k l) *
          (A j i * B l k) := by
    intros
    ring
  simp_rw [hreorder]
  calc
    (∫ v : ComplexUnitSphere N,
        ∑ i, ∑ j, ∑ k, ∑ l,
          (complexRankOneProjection v i j *
              complexRankOneProjection v k l) * (A j i * B l k)
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∑ i, ∑ j, ∑ k, ∑ l,
            ∫ v : ComplexUnitSphere N,
            (complexRankOneProjection v i j *
                complexRankOneProjection v k l) * (A j i * B l k)
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
            exact fun l _ ↦
              (integrable_complexRankOneProjection_entry_mul hN i j k l).mul_const _
          · exact fun k _ ↦ integrable_finsetSum _ fun l _ ↦
              (integrable_complexRankOneProjection_entry_mul hN i j k l).mul_const _
        · exact fun j _ ↦ integrable_finsetSum _ fun k _ ↦
            integrable_finsetSum _ fun l _ ↦
              (integrable_complexRankOneProjection_entry_mul hN i j k l).mul_const _
      · exact fun i _ ↦ integrable_finsetSum _ fun j _ ↦
          integrable_finsetSum _ fun k _ ↦
            integrable_finsetSum _ fun l _ ↦
              (integrable_complexRankOneProjection_entry_mul hN i j k l).mul_const _
    _ = ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          (Matrix.trace A * Matrix.trace B + Matrix.trace (A * B)) := by
      simp_rw [integral_mul_const,
        integral_complexRankOneProjection_entry_mul hN]
      exact sum_second_projective_delta _ A B

/-! ## Centered-entry covariance -/

/-- Entry of `Q_v=P_v-I/N`. -/
def complexCenteredRankOneProjection (N : ℕ)
    (v : ComplexUnitSphere N) (i j : Fin N) : ℂ :=
  complexRankOneProjection v i j -
    (((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0)

theorem integrable_complexCenteredRankOneProjection_entry
    {N : ℕ} (hN : 1 ≤ N) (i j : Fin N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredRankOneProjection N v i j)
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold complexCenteredRankOneProjection
  exact (integrable_complexRankOneProjection_entry hN i j).sub
    (integrable_const _)

theorem integrable_complexCenteredRankOneProjection_entry_mul
    {N : ℕ} (hN : 1 ≤ N) (i j k l : Fin N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredRankOneProjection N v i j *
        complexCenteredRankOneProjection N v k l)
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold complexCenteredRankOneProjection
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0)
  let b : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * (if k = l then 1 else 0)
  have hPi := integrable_complexRankOneProjection_entry hN i j
  have hPk := integrable_complexRankOneProjection_entry hN k l
  have hbase := integrable_complexRankOneProjection_entry_mul hN i j k l
  have hsum : Integrable (fun v : ComplexUnitSphere N ↦
      complexRankOneProjection v i j * complexRankOneProjection v k l -
        complexRankOneProjection v i j * b -
        a * complexRankOneProjection v k l + a * b)
      (complexUnitSphereProbabilityMeasure N) :=
    ((hbase.sub (hPi.mul_const b)).sub (hPk.const_mul a)).add (integrable_const _)
  convert hsum using 1 <;> funext v <;> simp only [a, b] <;> ring

/-- Exact centered-entry second moment. -/
theorem integral_complexCenteredRankOneProjection_entry_mul
    {N : ℕ} (hN : 1 ≤ N) (i j k l : Fin N) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredRankOneProjection N v i j *
        complexCenteredRankOneProjection N v k l
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          (if i = l then 1 else 0) * (if k = j then 1 else 0) -
        ((((N : ℝ) ^ 2 * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNp : (N : ℝ) + 1 ≠ 0 := by positivity
  have hdenOne : (N : ℝ) + (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hdenTwo : (N : ℝ) ^ 2 + (N : ℝ) ^ 3 ≠ 0 := by positivity
  have hdenEqOne :
      (N : ℝ) * ((N : ℝ) + 1) = (N : ℝ) + (N : ℝ) ^ 2 := by
    ring
  have hdenEqTwo :
      (N : ℝ) ^ 2 * ((N : ℝ) + 1) =
        (N : ℝ) ^ 2 + (N : ℝ) ^ 3 := by
    ring
  have hcoefR :
      ((N : ℝ) + (N : ℝ) ^ 2)⁻¹ - ((N : ℝ)⁻¹) ^ 2 =
        -(((N : ℝ) ^ 2 + (N : ℝ) ^ 3)⁻¹) := by
    field_simp [hNr, hdenOne, hdenTwo]
    ring
  have hcoefC :
      (((((N : ℝ) + (N : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) -
          (((N : ℝ)⁻¹ : ℝ) : ℂ) ^ 2 =
        -((((((N : ℝ) ^ 2 + (N : ℝ) ^ 3)⁻¹ : ℝ)) : ℂ)) := by
    exact_mod_cast hcoefR
  unfold complexCenteredRankOneProjection
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0)
  let b : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * (if k = l then 1 else 0)
  have hexpand : (fun v : ComplexUnitSphere N ↦
      (complexRankOneProjection v i j - a) *
        (complexRankOneProjection v k l - b)) =
      (fun v ↦
        complexRankOneProjection v i j * complexRankOneProjection v k l -
          complexRankOneProjection v i j * b -
          a * complexRankOneProjection v k l + a * b) := by
    funext v
    ring
  rw [hexpand]
  have hPi := integrable_complexRankOneProjection_entry hN i j
  have hPk := integrable_complexRankOneProjection_entry hN k l
  have hbase := integrable_complexRankOneProjection_entry_mul hN i j k l
  rw [integral_add]
  · rw [integral_sub]
    · rw [integral_sub]
      · simp_rw [integral_mul_const, integral_const_mul]
        rw [integral_complexRankOneProjection_entry_mul hN,
          integral_complexRankOneProjection_entry hN,
          integral_complexRankOneProjection_entry hN]
        simp only [integral_const, measureReal_def,
          IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul]
        simp only [a, b]
        rw [hdenEqOne, hdenEqTwo]
        linear_combination
          ((if i = j then (1 : ℂ) else 0) *
            (if k = l then (1 : ℂ) else 0)) * hcoefC
      · exact hbase
      · exact hPi.mul_const b
    · exact hbase.sub (hPi.mul_const b)
    · exact hPk.const_mul a
  · exact (hbase.sub (hPi.mul_const b)).sub (hPk.const_mul a)
  · exact integrable_const _

/-! ## Centered trace-pairing covariance -/

def complexCenteredProjectiveTracePair {N : ℕ}
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℂ :=
  complexProjectiveTracePair v A -
    (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A

theorem integrable_complexCenteredProjectiveTracePair
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v A)
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold complexCenteredProjectiveTracePair
  exact (integrable_complexProjectiveTracePair hN A).sub (integrable_const _)

theorem integrable_complexCenteredProjectiveTracePair_mul
    {N : ℕ} (hN : 1 ≤ N) (A B : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v A *
        complexCenteredProjectiveTracePair v B)
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A
  let b : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace B
  have hA := integrable_complexProjectiveTracePair hN A
  have hB := integrable_complexProjectiveTracePair hN B
  have hAB := integrable_complexProjectiveTracePair_mul hN A B
  have hsum : Integrable (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A * complexProjectiveTracePair v B -
        complexProjectiveTracePair v A * b -
        a * complexProjectiveTracePair v B + a * b)
      (complexUnitSphereProbabilityMeasure N) :=
    ((hAB.sub (hA.mul_const b)).sub (hB.const_mul a)).add (integrable_const _)
  unfold complexCenteredProjectiveTracePair
  convert hsum using 1 <;> funext v <;> simp only [a, b] <;> ring

/-- Covariance form of the second complex-projective moment. -/
theorem integral_complexCenteredProjectiveTracePair_mul
    {N : ℕ} (hN : 1 ≤ N) (A B : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveTracePair v A *
        complexCenteredProjectiveTracePair v B
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
        (Matrix.trace (A * B) -
          (((N : ℝ)⁻¹ : ℝ) : ℂ) *
            Matrix.trace A * Matrix.trace B) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNp : (N : ℝ) + 1 ≠ 0 := by positivity
  have hden : (N : ℝ) + (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hdenEq :
      (N : ℝ) * ((N : ℝ) + 1) = (N : ℝ) + (N : ℝ) ^ 2 := by
    ring
  have hcoefR :
      ((N : ℝ) + (N : ℝ) ^ 2)⁻¹ - ((N : ℝ)⁻¹) ^ 2 =
        -(((N : ℝ) + (N : ℝ) ^ 2)⁻¹ * (N : ℝ)⁻¹) := by
    field_simp [hNr, hden]
    ring
  have hcoefC :
      (((((N : ℝ) + (N : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) -
          (((N : ℝ)⁻¹ : ℝ) : ℂ) ^ 2 =
        -((((((N : ℝ) + (N : ℝ) ^ 2)⁻¹ : ℝ)) : ℂ) *
          (((N : ℝ)⁻¹ : ℝ) : ℂ)) := by
    exact_mod_cast hcoefR
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A
  let b : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace B
  have hA := integrable_complexProjectiveTracePair hN A
  have hB := integrable_complexProjectiveTracePair hN B
  have hAB := integrable_complexProjectiveTracePair_mul hN A B
  unfold complexCenteredProjectiveTracePair
  change (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v A - a) *
        (complexProjectiveTracePair v B - b)
      ∂(complexUnitSphereProbabilityMeasure N)) = _
  have hexpand : (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A - a) *
        (complexProjectiveTracePair v B - b)) =
      (fun v ↦ complexProjectiveTracePair v A *
          complexProjectiveTracePair v B -
        complexProjectiveTracePair v A * b -
        a * complexProjectiveTracePair v B + a * b) := by
    funext v
    ring
  rw [hexpand, integral_add]
  · rw [integral_sub]
    · rw [integral_sub]
      · simp_rw [integral_mul_const, integral_const_mul]
        rw [integral_complexProjectiveTracePair_mul hN,
          integral_complexProjectiveTracePair hN,
          integral_complexProjectiveTracePair hN]
        simp only [integral_const, measureReal_def,
          IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul]
        simp only [a, b]
        rw [hdenEq]
        linear_combination (Matrix.trace A * Matrix.trace B) * hcoefC
      · exact hAB
      · exact hA.mul_const b
    · exact hAB.sub (hA.mul_const b)
    · exact hB.const_mul a
  · exact (hAB.sub (hA.mul_const b)).sub (hB.const_mul a)
  · exact integrable_const _

/-! ## Centered sandwich contraction -/

/-- Coordinate expansion of `Tr(Q_v W Q_v Y)`. -/
def complexCenteredProjectiveSandwich {N : ℕ}
    (v : ComplexUnitSphere N)
    (W Y : ConcreteMatrixState N) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    complexCenteredRankOneProjection N v a b * W b c *
      complexCenteredRankOneProjection N v c d * Y d a

theorem integrable_complexCenteredProjectiveSandwich
    {N : ℕ} (hN : 1 ≤ N) (W Y : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveSandwich v W Y)
      (complexUnitSphereProbabilityMeasure N) := by
  unfold complexCenteredProjectiveSandwich
  have hreorder : ∀ (v : ComplexUnitSphere N) (a b c d : Fin N),
      complexCenteredRankOneProjection N v a b * W b c *
          complexCenteredRankOneProjection N v c d * Y d a =
        (complexCenteredRankOneProjection N v a b *
          complexCenteredRankOneProjection N v c d) * (W b c * Y d a) := by
    intros
    ring
  simp_rw [hreorder]
  exact integrable_finsetSum _ fun a _ ↦
    integrable_finsetSum _ fun b _ ↦
      integrable_finsetSum _ fun c _ ↦
        integrable_finsetSum _ fun d _ ↦
          (integrable_complexCenteredRankOneProjection_entry_mul
            hN a b c d).mul_const _

private theorem sum_centered_sandwich_delta {N : ℕ}
    (u v : ℂ) (W Y : ConcreteMatrixState N) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      (u * (if a = d then 1 else 0) * (if c = b then 1 else 0) -
        v * (if a = b then 1 else 0) * (if c = d then 1 else 0)) *
          (W b c * Y d a)) =
      u * (Matrix.trace W * Matrix.trace Y) -
        v * Matrix.trace (W * Y) := by
  classical
  have hsplit :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (u * (if a = d then 1 else 0) * (if c = b then 1 else 0) -
          v * (if a = b then 1 else 0) * (if c = d then 1 else 0)) *
            (W b c * Y d a)) =
        (∑ a, ∑ b, ∑ c, ∑ d,
          u * (if a = d then 1 else 0) * (if c = b then 1 else 0) *
            (W b c * Y d a)) -
        (∑ a, ∑ b, ∑ c, ∑ d,
          v * (if a = b then 1 else 0) * (if c = d then 1 else 0) *
            (W b c * Y d a)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have htraceProd :
      (∑ a, ∑ b, ∑ c, ∑ d,
        u * (if a = d then 1 else 0) * (if c = b then 1 else 0) *
          (W b c * Y d a)) =
        u * (Matrix.trace W * Matrix.trace Y) := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          if d = a then (if c = b then u * (W b c * Y d a) else 0)
          else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        by_cases had : d = a
        · subst d
          by_cases hcb : c = b
          · subst c
            simp
          · simp [hcb]
        · have had' : a ≠ d := Ne.symm had
          simp [had, had']
      _ = ∑ a, ∑ b, u * (W b b * Y a a) := by simp
      _ = u * (Matrix.trace W * Matrix.trace Y) := by
        simp only [Matrix.trace, Matrix.diag_apply,
          Finset.sum_mul, Finset.mul_sum]
  have htraceMul :
      (∑ a, ∑ b, ∑ c, ∑ d,
        v * (if a = b then 1 else 0) * (if c = d then 1 else 0) *
          (W b c * Y d a)) = v * Matrix.trace (W * Y) := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          if b = a then (if d = c then v * (W b c * Y d a) else 0)
          else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        by_cases hab : b = a
        · subst b
          by_cases hcd : d = c
          · subst d
            simp
          · have hcd' : c ≠ d := Ne.symm hcd
            simp [hcd, hcd']
        · have hab' : a ≠ b := Ne.symm hab
          simp [hab, hab']
      _ = ∑ a, ∑ c, v * (W a c * Y c a) := by simp
      _ = v * Matrix.trace (W * Y) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Finset.mul_sum]
  rw [hsplit, htraceProd, htraceMul]

/-- Exact second-projective-moment contraction for the centered sandwich. -/
theorem integral_complexCenteredProjectiveSandwich
    {N : ℕ} (hN : 1 ≤ N) (W Y : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveSandwich v W Y
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          (Matrix.trace W * Matrix.trace Y) -
        ((((N : ℝ) ^ 2 * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          Matrix.trace (W * Y) := by
  unfold complexCenteredProjectiveSandwich
  have hreorder : ∀ (v : ComplexUnitSphere N) (a b c d : Fin N),
      complexCenteredRankOneProjection N v a b * W b c *
          complexCenteredRankOneProjection N v c d * Y d a =
        (complexCenteredRankOneProjection N v a b *
          complexCenteredRankOneProjection N v c d) * (W b c * Y d a) := by
    intros
    ring
  simp_rw [hreorder]
  calc
    (∫ v : ComplexUnitSphere N,
        ∑ a, ∑ b, ∑ c, ∑ d,
          (complexCenteredRankOneProjection N v a b *
            complexCenteredRankOneProjection N v c d) * (W b c * Y d a)
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          ∫ v : ComplexUnitSphere N,
            (complexCenteredRankOneProjection N v a b *
              complexCenteredRankOneProjection N v c d) * (W b c * Y d a)
            ∂(complexUnitSphereProbabilityMeasure N) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro a _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro b _
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro c _
            rw [integral_finsetSum]
            exact fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b c d).mul_const _
          · exact fun c _ ↦ integrable_finsetSum _ fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b c d).mul_const _
        · exact fun b _ ↦ integrable_finsetSum _ fun c _ ↦
            integrable_finsetSum _ fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b c d).mul_const _
      · exact fun a _ ↦ integrable_finsetSum _ fun b _ ↦
          integrable_finsetSum _ fun c _ ↦
            integrable_finsetSum _ fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b c d).mul_const _
    _ = ((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          (Matrix.trace W * Matrix.trace Y) -
        ((((N : ℝ) ^ 2 * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
          Matrix.trace (W * Y) := by
      simp_rw [integral_mul_const,
        integral_complexCenteredRankOneProjection_entry_mul hN]
      exact sum_centered_sandwich_delta _ _ W Y

/-! ## Centered conjugate-sandwich contraction -/

/-- Coordinate expansion of `Tr(Q_v R conjugate(Q_v) Rᴴ)`.  Hermiticity of
`Q_v` replaces `conjugate(Q_v)_{cd}` by `Q_v{}_{dc}`. -/
def complexCenteredProjectiveConjugateSandwich {N : ℕ}
    (v : ComplexUnitSphere N) (R : ConcreteMatrixState N) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    complexCenteredRankOneProjection N v a b * R b c *
      complexCenteredRankOneProjection N v d c * star (R a d)

theorem integrable_complexCenteredProjectiveConjugateSandwich
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveConjugateSandwich v R)
      (complexUnitSphereProbabilityMeasure N) := by
  unfold complexCenteredProjectiveConjugateSandwich
  have hreorder : ∀ (v : ComplexUnitSphere N) (a b c d : Fin N),
      complexCenteredRankOneProjection N v a b * R b c *
          complexCenteredRankOneProjection N v d c * star (R a d) =
        (complexCenteredRankOneProjection N v a b *
          complexCenteredRankOneProjection N v d c) *
            (R b c * star (R a d)) := by
    intros
    ring
  simp_rw [hreorder]
  exact integrable_finsetSum _ fun a _ ↦
    integrable_finsetSum _ fun b _ ↦
      integrable_finsetSum _ fun c _ ↦
        integrable_finsetSum _ fun d _ ↦
          (integrable_complexCenteredRankOneProjection_entry_mul
            hN a b d c).mul_const _

private theorem sum_centered_conjugate_sandwich_delta {N : ℕ}
    (u v : ℂ) (R : ConcreteMatrixState N) (hR : R.IsSymm) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      (u * (if a = c then 1 else 0) * (if d = b then 1 else 0) -
        v * (if a = b then 1 else 0) * (if d = c then 1 else 0)) *
          (R b c * star (R a d))) =
      (u - v) * Matrix.trace (R * R.conjTranspose) := by
  classical
  have hsymm : ∀ i j, R j i = R i j := Matrix.IsSymm.ext_iff.mp hR
  have hsplit :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (u * (if a = c then 1 else 0) * (if d = b then 1 else 0) -
          v * (if a = b then 1 else 0) * (if d = c then 1 else 0)) *
            (R b c * star (R a d))) =
        (∑ a, ∑ b, ∑ c, ∑ d,
          u * (if a = c then 1 else 0) * (if d = b then 1 else 0) *
            (R b c * star (R a d))) -
        (∑ a, ∑ b, ∑ c, ∑ d,
          v * (if a = b then 1 else 0) * (if d = c then 1 else 0) *
            (R b c * star (R a d))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hu :
      (∑ a, ∑ b, ∑ c, ∑ d,
        u * (if a = c then 1 else 0) * (if d = b then 1 else 0) *
          (R b c * star (R a d))) =
        u * Matrix.trace (R * R.conjTranspose) := by
    calc
      _ = ∑ a, ∑ b, u * (R b a * star (R a b)) := by
        simp
      _ = ∑ a, ∑ b, u * (R a b * star (R a b)) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [hsymm a b]
      _ = u * Matrix.trace (R * R.conjTranspose) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Finset.mul_sum]
  have hv :
      (∑ a, ∑ b, ∑ c, ∑ d,
        v * (if a = b then 1 else 0) * (if d = c then 1 else 0) *
          (R b c * star (R a d))) =
        v * Matrix.trace (R * R.conjTranspose) := by
    calc
      _ = ∑ a, ∑ c, v * (R a c * star (R a c)) := by simp
      _ = v * Matrix.trace (R * R.conjTranspose) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Finset.mul_sum]
  rw [hsplit, hu, hv]
  ring

/-- Exact contraction of the conjugate sandwich for a symmetric `R`. -/
theorem integral_complexCenteredProjectiveConjugateSandwich
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveConjugateSandwich v R
      ∂(complexUnitSphereProbabilityMeasure N)) =
      (((((N : ℝ) - 1) /
        ((N : ℝ) ^ 2 * ((N : ℝ) + 1))) : ℝ) : ℂ) *
          Matrix.trace (R * R.conjTranspose) := by
  unfold complexCenteredProjectiveConjugateSandwich
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNp : (N : ℝ) + 1 ≠ 0 := by positivity
  have hreorder : ∀ (w : ComplexUnitSphere N) (a b c d : Fin N),
      complexCenteredRankOneProjection N w a b * R b c *
          complexCenteredRankOneProjection N w d c * star (R a d) =
        (complexCenteredRankOneProjection N w a b *
          complexCenteredRankOneProjection N w d c) *
            (R b c * star (R a d)) := by
    intros
    ring
  simp_rw [hreorder]
  calc
    (∫ w : ComplexUnitSphere N,
        ∑ a, ∑ b, ∑ c, ∑ d,
          (complexCenteredRankOneProjection N w a b *
            complexCenteredRankOneProjection N w d c) *
              (R b c * star (R a d))
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          ∫ w : ComplexUnitSphere N,
            (complexCenteredRankOneProjection N w a b *
              complexCenteredRankOneProjection N w d c) *
                (R b c * star (R a d))
            ∂(complexUnitSphereProbabilityMeasure N) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro a _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro b _
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro c _
            rw [integral_finsetSum]
            exact fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b d c).mul_const _
          · exact fun c _ ↦ integrable_finsetSum _ fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b d c).mul_const _
        · exact fun b _ ↦ integrable_finsetSum _ fun c _ ↦
            integrable_finsetSum _ fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b d c).mul_const _
      · exact fun a _ ↦ integrable_finsetSum _ fun b _ ↦
          integrable_finsetSum _ fun c _ ↦
            integrable_finsetSum _ fun d _ ↦
              (integrable_complexCenteredRankOneProjection_entry_mul
                hN a b d c).mul_const _
    _ = (((((N : ℝ) - 1) /
          ((N : ℝ) ^ 2 * ((N : ℝ) + 1))) : ℝ) : ℂ) *
          Matrix.trace (R * R.conjTranspose) := by
      simp_rw [integral_mul_const,
        integral_complexCenteredRankOneProjection_entry_mul hN]
      rw [sum_centered_conjugate_sandwich_delta _ _ R hR]
      congr 1
      push_cast
      field_simp [hNr, hNp]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
