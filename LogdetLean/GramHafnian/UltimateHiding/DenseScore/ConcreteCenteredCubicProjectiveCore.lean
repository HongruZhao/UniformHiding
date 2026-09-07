import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicDifferentialBasics
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveSecondMoment
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic

/-!
# Axiom-free projective centering geometry for the cubic endpoint

This module contains only the matrix identity `P_v = Q_v + I/N` and the
zero-mean/integrability facts needed to integrate a trilinear form along the
centered projective direction.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The centered projective direction is entrywise the centered rank-one
projection already used in the projective moment API. -/
theorem concreteCenteredOrbitalDirection_apply_eq
    {N : ℕ} (v : ComplexUnitSphere N) (i j : Fin N) :
    concreteCenteredOrbitalDirection N v i j =
      complexCenteredRankOneProjection N v i j := by
  simp [concreteCenteredOrbitalDirection,
    complexCenteredRankOneProjection, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply]

/-- The first centered projective matrix moment vanishes entrywise. -/
theorem integral_complexCenteredRankOneProjection_entry_eq_zero
    {N : ℕ} (hN : 1 ≤ N) (i j : Fin N) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredRankOneProjection N v i j
        ∂(complexUnitSphereProbabilityMeasure N)) = 0 := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hP := integrable_complexRankOneProjection_entry hN i j
  have hc : Integrable (fun _ : ComplexUnitSphere N ↦
      ((((N : ℝ)⁻¹ : ℝ) : ℂ) * (if i = j then 1 else 0)))
      (complexUnitSphereProbabilityMeasure N) := integrable_const _
  unfold complexCenteredRankOneProjection
  rw [integral_sub hP hc, integral_complexRankOneProjection_entry hN,
    integral_const]
  simp only [measureReal_def, IsProbabilityMeasure.measure_univ,
    ENNReal.toReal_one, one_smul]
  ring

/-- The real coordinate vector of the centered projective direction is
Bochner integrable. -/
theorem integrable_concreteCenteredOrbitalCoordinates
    {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
      (complexUnitSphereProbabilityMeasure N) := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  apply Integrable.of_eval
  intro b
  fin_cases b
  · simpa [concreteMatrixRealCoordinates,
      concreteCenteredOrbitalDirection_apply_eq] using
      (integrable_complexCenteredRankOneProjection_entry hN i j).re
  · simpa [concreteMatrixRealCoordinates,
      concreteCenteredOrbitalDirection_apply_eq] using
      (integrable_complexCenteredRankOneProjection_entry hN i j).im

/-- Internal projective centering: every real coordinate of `E_v Q_v`
vanishes. -/
theorem integral_concreteCenteredOrbitalCoordinates_eq_zero
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ v : ComplexUnitSphere N,
      concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)
      ∂(complexUnitSphereProbabilityMeasure N)) = 0 := by
  have hq := integrable_concreteCenteredOrbitalCoordinates hN
  ext i j b
  rw [eval_integral (fun i ↦ hq.eval i) i,
    eval_integral (fun j ↦ (hq.eval i).eval j) j,
    eval_integral (fun b ↦ ((hq.eval i).eval j).eval b) b]
  fin_cases b
  · change (∫ v : ComplexUnitSphere N,
        concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v) i j (0 : Fin 2)
          ∂(complexUnitSphereProbabilityMeasure N)) = 0
    rw [show (fun v : ComplexUnitSphere N ↦
        concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v) i j 0) =
        fun v ↦ (complexCenteredRankOneProjection N v i j).re by
      funext v
      simp [concreteMatrixRealCoordinates,
        concreteCenteredOrbitalDirection_apply_eq]]
    calc
      (∫ v : ComplexUnitSphere N,
          (complexCenteredRankOneProjection N v i j).re
            ∂(complexUnitSphereProbabilityMeasure N)) =
          (∫ v : ComplexUnitSphere N,
            complexCenteredRankOneProjection N v i j
              ∂(complexUnitSphereProbabilityMeasure N)).re := by
        simpa only [RCLike.re_eq_complex_re] using
          integral_re (integrable_complexCenteredRankOneProjection_entry hN i j)
      _ = 0 := by
        rw [integral_complexCenteredRankOneProjection_entry_eq_zero hN i j]
        rfl
  · change (∫ v : ComplexUnitSphere N,
        concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v) i j (1 : Fin 2)
          ∂(complexUnitSphereProbabilityMeasure N)) = 0
    rw [show (fun v : ComplexUnitSphere N ↦
        concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v) i j 1) =
        fun v ↦ (complexCenteredRankOneProjection N v i j).im by
      funext v
      simp [concreteMatrixRealCoordinates,
        concreteCenteredOrbitalDirection_apply_eq]]
    calc
      (∫ v : ComplexUnitSphere N,
          (complexCenteredRankOneProjection N v i j).im
            ∂(complexUnitSphereProbabilityMeasure N)) =
          (∫ v : ComplexUnitSphere N,
            complexCenteredRankOneProjection N v i j
              ∂(complexUnitSphereProbabilityMeasure N)).im := by
        simpa only [RCLike.im_eq_complex_im] using
          integral_im (integrable_complexCenteredRankOneProjection_entry hN i j)
      _ = 0 := by
        rw [integral_complexCenteredRankOneProjection_entry_eq_zero hN i j]
        rfl

/-- A fixed continuous linear functional has zero mean on `Q_v`. -/
theorem integral_trilinear_two_fixed_centered_eq_zero
    {N : ℕ} (hN : 1 ≤ N)
    (T : SymmetricRealTrilinearForm (ConcreteMatrixRealCoordinates N))
    (x y : ConcreteMatrixRealCoordinates N) :
    (∫ v : ComplexUnitSphere N,
      T.form x y
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
        ∂(complexUnitSphereProbabilityMeasure N)) = 0 := by
  let L : ConcreteMatrixRealCoordinates N →L[ℝ] ℝ := T.form x y
  have hq := integrable_concreteCenteredOrbitalCoordinates hN
  rw [show (fun v : ComplexUnitSphere N ↦
      T.form x y
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))) =
      fun v ↦ L
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)) by rfl,
    L.integral_comp_comm hq,
    integral_concreteCenteredOrbitalCoordinates_eq_zero hN]
  simp

/-- Matrix identity `P_v=Q_v+I/N`, with real scalar multiplication. -/
theorem complexRankOneProjection_eq_centered_add
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    complexRankOneProjection v =
      concreteCenteredOrbitalDirection N v +
        (N : ℝ)⁻¹ • (1 : ConcreteMatrixState N) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  ext i j
  simp only [concreteCenteredOrbitalDirection, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- In dimension one the centered projective direction is zero, hence the
averaged centered cubic score vanishes. -/
theorem integral_concreteCenteredDensityScoreThree_fin_one_eq_zero
    {K : ℕ} (A : ConcreteMatrixState 1) :
    (∫ v : ComplexUnitSphere 1,
      concreteCenteredDensityScore 3 1 K v A
        ∂(complexUnitSphereProbabilityMeasure 1)) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  exact concreteCenteredDensityScore_fin_one_eq_zero (by omega) v A

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
