import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7_ExactProof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredCubicDefinitions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredCubicProjectiveCore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteRankOneCubicAverage
import Mathlib.Tactic

/-!
# Exact-H7 adapter for the averaged centered cubic density

The legacy identification theorem is retained unchanged.  This module repeats
its purely algebraic consumer proof with the foundations-only `H7Exact`
witness, so downstream score modules can avoid the legacy H7 declaration
without creating an import cycle through the witness type definition.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Exact R25 density identification, now consuming the proved H7 witness. -/
theorem integral_concreteCenteredDensityScoreThree_eq_density_of_H7Exact
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredDensityScore 3 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteAveragedCenteredCubicDensity N K A := by
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  let W := H7Exact.coeCorner_cubicDifferentialWitness_external_derived
    hN (by omega : 2 * N + 8 ≤ K) A hsymm hsupport
  let T := W.differential
  let q : ComplexUnitSphere N → ConcreteMatrixRealCoordinates N :=
    fun v ↦ concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)
  let p : ComplexUnitSphere N → ConcreteMatrixRealCoordinates N :=
    fun v ↦ concreteMatrixRealCoordinates (complexRankOneProjection v)
  let i : ConcreteMatrixRealCoordinates N :=
    concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)
  let a : ℝ := (N : ℝ)⁻¹
  let mixed : ComplexUnitSphere N → ℝ := fun v ↦ T.form i (q v) (q v)
  let linear : ComplexUnitSphere N → ℝ := fun v ↦ T.form i i (q v)
  let centered : ComplexUnitSphere N → ℝ :=
    fun v ↦ concreteCenteredDensityScore 3 N K v A
  let rankOne : ComplexUnitSphere N → ℝ :=
    fun v ↦ concreteRankOneDensityScoreThree N K v A
  let central : ℝ := concreteCentralDensityScoreThree N K A
  have hpoint : rankOne = fun v ↦
      centered v + 3 * a * mixed v + 3 * a ^ 2 * linear v + a ^ 3 * central := by
    funext v
    have hp : p v = q v + a • i := by
      have hmat := complexRankOneProjection_eq_centered_add hN v
      change concreteMatrixRealCoordinates (complexRankOneProjection v) =
        concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v) +
          (N : ℝ)⁻¹ •
            concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)
      rw [hmat, concreteMatrixRealCoordinates_add,
        concreteMatrixRealCoordinates_smul]
    have hpolar := T.diagonal_add_smul (q v) i a
    rw [← hp] at hpolar
    calc
      rankOne v = T.form (p v) (p v) (p v) := by
        simpa only [rankOne, p] using (W.rankOne_diagonal v).symm
      _ = T.form (q v) (q v) (q v) + 3 * a * T.form i (q v) (q v) +
          3 * a ^ 2 * T.form i i (q v) + a ^ 3 * T.form i i i := hpolar
      _ = centered v + 3 * a * mixed v + 3 * a ^ 2 * linear v +
          a ^ 3 * central := by
        rw [W.centered_diagonal v, W.central_diagonal]
  have hcentered : Integrable centered sphere := by
    simpa only [centered, sphere] using W.centered_integrable
  have hmixed : Integrable mixed sphere := by
    simpa only [mixed, q, i, T, sphere] using W.mixed_integrable
  have hlinear : Integrable linear sphere := by
    have hq := integrable_concreteCenteredOrbitalCoordinates hN
    let L : ConcreteMatrixRealCoordinates N →L[ℝ] ℝ := T.form i i
    exact L.integrable_comp (by simpa only [q, sphere] using hq)
  have hconst : Integrable (fun _ : ComplexUnitSphere N ↦ central) sphere :=
    integrable_const central
  have hthreeMixed : Integrable (fun v ↦ 3 * a * mixed v) sphere :=
    hmixed.const_mul (3 * a)
  have hthreeLinear : Integrable (fun v ↦ 3 * a ^ 2 * linear v) sphere :=
    hlinear.const_mul (3 * a ^ 2)
  have haCentral : Integrable (fun _ : ComplexUnitSphere N ↦ a ^ 3 * central)
      sphere := integrable_const _
  have hrankOne : Integrable rankOne sphere := by
    rw [hpoint]
    exact ((hcentered.add hthreeMixed).add hthreeLinear).add haCentral
  have hlinearMean : (∫ v, linear v ∂sphere) = 0 := by
    simpa only [linear, q, i, T, sphere] using
      integral_trilinear_two_fixed_centered_eq_zero hN T i i
  have hmixedMean : (∫ v, mixed v ∂sphere) =
      concreteMixedScalarQuadraticDensity N K A := by
    simpa only [mixed, q, i, T, sphere] using W.mixed_mean
  have hrankMean : (∫ v, rankOne v ∂sphere) =
      concreteAveragedRankOneCubicDensity N K A := by
    simpa only [rankOne, sphere] using
      integral_concreteRankOneDensityScoreThree hN hdense A hsymm hsupport
  have hmean : (∫ v, rankOne v ∂sphere) =
      (∫ v, centered v ∂sphere) +
        3 * a * (∫ v, mixed v ∂sphere) +
        3 * a ^ 2 * (∫ v, linear v ∂sphere) + a ^ 3 * central := by
    rw [hpoint]
    have hsumOne : Integrable (fun v ↦ centered v + 3 * a * mixed v) sphere :=
      hcentered.add hthreeMixed
    have hsumTwo : Integrable
        (fun v ↦ centered v + 3 * a * mixed v + 3 * a ^ 2 * linear v)
        sphere := hsumOne.add hthreeLinear
    calc
      (∫ v, centered v + 3 * a * mixed v + 3 * a ^ 2 * linear v +
          a ^ 3 * central ∂sphere) =
          (∫ v, centered v + 3 * a * mixed v + 3 * a ^ 2 * linear v
            ∂sphere) +
            ∫ _ : ComplexUnitSphere N, a ^ 3 * central ∂sphere :=
        integral_add hsumTwo haCentral
      _ = ((∫ v, centered v + 3 * a * mixed v ∂sphere) +
            ∫ v, 3 * a ^ 2 * linear v ∂sphere) +
            ∫ _ : ComplexUnitSphere N, a ^ 3 * central ∂sphere := by
        rw [integral_add hsumOne hthreeLinear]
      _ = (((∫ v, centered v ∂sphere) +
            ∫ v, 3 * a * mixed v ∂sphere) +
            ∫ v, 3 * a ^ 2 * linear v ∂sphere) +
            ∫ _ : ComplexUnitSphere N, a ^ 3 * central ∂sphere := by
        rw [integral_add hcentered hthreeMixed]
      _ = (∫ v, centered v ∂sphere) +
            3 * a * (∫ v, mixed v ∂sphere) +
            3 * a ^ 2 * (∫ v, linear v ∂sphere) + a ^ 3 * central := by
        rw [integral_const_mul, integral_const_mul, integral_const]
        simp only [measureReal_def, IsProbabilityMeasure.measure_univ,
          ENNReal.toReal_one, one_smul]
  rw [hrankMean, hmixedMean, hlinearMean] at hmean
  change (∫ v, centered v ∂sphere) = _
  rw [concreteAveragedCenteredCubicDensity]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  dsimp only [a] at hmean
  field_simp [hNr] at hmean ⊢
  linarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
