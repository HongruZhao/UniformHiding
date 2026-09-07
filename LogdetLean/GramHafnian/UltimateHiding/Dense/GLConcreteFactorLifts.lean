import LogdetLean.GramHafnian.UltimateHiding.Dense.GLUnitaryCongruenceAdapter
import LogdetLean.GramHafnian.UltimateHiding.Dense.BetaTailConcrete
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete
import LogdetLean.GramHafnian.UltimateHiding.Dense.ConcreteFactorUnitaryInvariance
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteOrbitalEventGeometry

/-!
# Concrete H2 factors as measurable `GL_N(C)`-valued random variables

The Gelfand-pair adapter acts with probability laws on `GL_N(C)`, whereas the
concrete radial and orbital constructions were originally recorded as matrix
factors.  This module supplies the elementary bridge:

* the centered orbital factor is invertible for every radius and direction;
* the one-column factor is invertible on its actual beta support `q > 0`;
* off that support its `GL` lift is defined to be the identity;
* the lift agrees almost everywhere with the original matrix factor and its
  pushforward law is a probability measure.

No commutation statement or scientific axiom is used.
-/

open MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-! ## A reusable rank-one affine inverse -/

theorem rankOneAffine_mul (N : ℕ)
    (P : ConcreteMatrixState N) (hP : P * P = P) (a b : ℂ) :
    (1 + a • P) * (1 + b • P) =
      1 + (a + b + a * b) • P := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hP, one_smul, smul_smul]
  module

theorem rankOneAffine_isUnit
    {N : ℕ} (P : ConcreteMatrixState N) (hP : P * P = P)
    (c r : ℂ) (hc : c ≠ 0) (hr : r ≠ 0) :
    IsUnit (c • (1 + (r - 1) • P)) := by
  let X : ConcreteMatrixState N := 1 + (r - 1) • P
  let Y : ConcreteMatrixState N := 1 + (r⁻¹ - 1) • P
  have hcoeff : (r - 1) + (r⁻¹ - 1) + (r - 1) * (r⁻¹ - 1) = 0 := by
    field_simp [hr]
    ring
  have hcoeff' : (r⁻¹ - 1) + (r - 1) + (r⁻¹ - 1) * (r - 1) = 0 := by
    field_simp [hr]
    ring
  have hXY : X * Y = 1 := by
    dsimp only [X, Y]
    rw [rankOneAffine_mul N P hP, hcoeff]
    simp
  have hYX : Y * X = 1 := by
    dsimp only [X, Y]
    rw [rankOneAffine_mul N P hP, hcoeff']
    simp
  refine isUnit_iff_exists.mpr
    ⟨c⁻¹ • Y, ?_, ?_⟩
  · change (c • X) * (c⁻¹ • Y) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hXY]
    simp [hc]
  · change (c⁻¹ • Y) * (c • X) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hYX]
    simp [hc]

/-! ## The everywhere-invertible orbital lift -/

theorem concreteOrbitalFactor_isUnit
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) (v : ComplexUnitSphere N) :
    IsUnit (concreteOrbitalFactor N s v) := by
  have hright : concreteOrbitalFactor N s v *
      concreteOrbitalFactor N (-s) v = 1 := by
    have h := concreteOrbitalFactor_mul hN s (-s) v
    simpa [concreteOrbitalFactor] using h
  have hleft : concreteOrbitalFactor N (-s) v *
      concreteOrbitalFactor N s v = 1 := by
    have h := concreteOrbitalFactor_mul hN (-s) s v
    simpa [concreteOrbitalFactor] using h
  exact isUnit_iff_exists.mpr
    ⟨concreteOrbitalFactor N (-s) v, hright, hleft⟩

/-- The centered orbital factor as an element of `GL_N(C)`. -/
def concreteOrbitalFactorGLLift
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) (v : ComplexUnitSphere N) :
    ComplexMatrixGL N :=
  (concreteOrbitalFactor_isUnit hN s v).unit

@[simp]
theorem concreteOrbitalFactorGLLift_val
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) (v : ComplexUnitSphere N) :
    (concreteOrbitalFactorGLLift hN s v : ConcreteMatrixState N) =
      concreteOrbitalFactor N s v :=
  IsUnit.unit_spec _

theorem measurable_concreteOrbitalFactorGLLift
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    Measurable (concreteOrbitalFactorGLLift hN s) := by
  rw [measurable_comap_iff]
  change Measurable fun v : ComplexUnitSphere N ↦
    (concreteOrbitalFactorGLLift hN s v : ConcreteMatrixState N)
  convert measurable_concreteOrbitalFactor N s using 1
  funext v
  exact concreteOrbitalFactorGLLift_val hN s v

/-- A unit vector in `ℂ^N` forces the coordinate dimension to be positive. -/
theorem complexUnitSphere_dimension_pos
    {N : ℕ} (v : ComplexUnitSphere N) : 1 ≤ N := by
  by_contra hN
  have hzero : N = 0 := by omega
  subst N
  have hvzero : v.1 = 0 := Subsingleton.elim _ _
  have hvnorm : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  rw [hvzero, norm_zero] at hvnorm
  norm_num at hvnorm

/-- Public proof-free orbital lift.  Positivity of the dimension is recovered
from the supplied unit direction. -/
def concreteOrbitalFactorGL
    (N : ℕ) (s : ℝ) (v : ComplexUnitSphere N) : ComplexMatrixGL N :=
  concreteOrbitalFactorGLLift (complexUnitSphere_dimension_pos v) s v

@[simp]
theorem complexMatrixGLVal_concreteOrbitalFactorGL
    (N : ℕ) (s : ℝ) (v : ComplexUnitSphere N) :
    complexMatrixGLVal N (concreteOrbitalFactorGL N s v) =
      concreteOrbitalFactor N s v := by
  exact concreteOrbitalFactorGLLift_val
    (complexUnitSphere_dimension_pos v) s v

theorem measurable_concreteOrbitalFactorGL (N : ℕ) (s : ℝ) :
    Measurable (concreteOrbitalFactorGL N s) := by
  rw [measurable_comap_iff]
  change Measurable fun v : ComplexUnitSphere N ↦
    complexMatrixGLVal N (concreteOrbitalFactorGL N s v)
  convert measurable_concreteOrbitalFactor N s using 1
  funext v
  exact complexMatrixGLVal_concreteOrbitalFactorGL N s v

/-! ## The supported one-column lift -/

theorem concreteOneColumnFactor_isUnit_of_pos
    {m N : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : 0 < q)
    (v : ComplexUnitSphere N) :
    IsUnit (concreteOneColumnFactor m N q v) := by
  let P := complexRankOneProjection v
  let c : ℂ := (Real.sqrt (((m + 1 : ℕ) : ℝ) / (m : ℝ)) : ℝ)
  let r : ℂ := (Real.sqrt q : ℝ)
  have hP : P * P = P := complexRankOneProjection_mul_self v
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hratio : 0 < (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by positivity
  have hcR : 0 < Real.sqrt (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
    Real.sqrt_pos.2 hratio
  have hrR : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (ne_of_gt hcR)
  have hr : r ≠ 0 := by
    dsimp only [r]
    exact_mod_cast (ne_of_gt hrR)
  have hcast : (((Real.sqrt q - 1 : ℝ) : ℂ)) = r - 1 := by
    simp [r]
  unfold concreteOneColumnFactor
  change IsUnit (c • (1 + (((Real.sqrt q - 1 : ℝ) : ℂ)) • P))
  rw [hcast]
  exact rankOneAffine_isUnit P hP c r hc hr

/-- The one-column factor lifted to `GL_N(C)` on `q > 0`, with identity as a
measurable harmless fallback off that support. -/
def concreteOneColumnFactorGLLift
    {m N : ℕ} (hm : 1 ≤ m) (q : ℝ) (v : ComplexUnitSphere N) :
    ComplexMatrixGL N :=
  if hq : 0 < q then
    (concreteOneColumnFactor_isUnit_of_pos hm hq v).unit
  else
    1

@[simp]
theorem concreteOneColumnFactorGLLift_val_of_pos
    {m N : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : 0 < q)
    (v : ComplexUnitSphere N) :
    (concreteOneColumnFactorGLLift hm q v : ConcreteMatrixState N) =
      concreteOneColumnFactor m N q v := by
  simp [concreteOneColumnFactorGLLift, hq]

@[simp]
theorem concreteOneColumnFactorGLLift_val_of_nonpos
    {m N : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : ¬ 0 < q)
    (v : ComplexUnitSphere N) :
    (concreteOneColumnFactorGLLift hm q v : ConcreteMatrixState N) = 1 := by
  simp [concreteOneColumnFactorGLLift, hq]

theorem measurable_concreteOneColumnFactorGLLift
    {m N : ℕ} (hm : 1 ≤ m) :
    Measurable fun p : ℝ × ComplexUnitSphere N ↦
      concreteOneColumnFactorGLLift hm p.1 p.2 := by
  rw [measurable_comap_iff]
  change Measurable fun p : ℝ × ComplexUnitSphere N ↦
    (concreteOneColumnFactorGLLift hm p.1 p.2 : ConcreteMatrixState N)
  have heq : (fun p : ℝ × ComplexUnitSphere N ↦
      (concreteOneColumnFactorGLLift hm p.1 p.2 : ConcreteMatrixState N)) =
      fun p ↦ if 0 < p.1 then concreteOneColumnFactor m N p.1 p.2 else 1 := by
    funext p
    by_cases hp : 0 < p.1
    · simp [hp]
    · simp [hp]
  rw [heq]
  exact Measurable.ite
    (measurableSet_lt measurable_const measurable_fst)
    (measurable_concreteOneColumnFactor m N) measurable_const

/-- On the literal beta/sphere parameter law, the supported `GL` lift has
exactly the original concrete matrix value almost everywhere. -/
theorem concreteOneColumnFactorGLLift_val_ae
    {m N : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) :
    (fun p : ℝ × ComplexUnitSphere N ↦
        (concreteOneColumnFactorGLLift hm p.1 p.2 : ConcreteMatrixState N))
      =ᵐ[concreteOneColumnParameterLaw m N]
    (fun p ↦ concreteOneColumnFactor m N p.1 p.2) := by
  let _ : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hsupport : ∀ᵐ q ∂(oneColumnBetaLaw m N),
      q ∈ Set.Ioo (0 : ℝ) 1 :=
    mem_ae_iff.mpr (oneColumnBetaLaw_compl_Ioo_eq_zero m N)
  unfold concreteOneColumnParameterLaw oneColumnParameterLaw
  have hsupportProd : ∀ᵐ p ∂((oneColumnBetaLaw m N).prod
      (complexUnitSphereProbabilityMeasure N)), p.1 ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioo.preimage measurable_fst)]
    filter_upwards [hsupport] with q hq
    filter_upwards [] with v
    exact hq
  filter_upwards [hsupportProd] with p hp
  exact concreteOneColumnFactorGLLift_val_of_pos hm hp.1 p.2

/-- Public total one-column lift.  It is the exact factor when `m > 0` and
`q > 0`; the identity is used on the irrelevant complement. -/
def concreteOneColumnFactorGL
    (m N : ℕ) (q : ℝ) (v : ComplexUnitSphere N) : ComplexMatrixGL N :=
  if hm : 1 ≤ m then concreteOneColumnFactorGLLift hm q v else 1

@[simp]
theorem complexMatrixGLVal_concreteOneColumnFactorGL_of_pos
    {m N : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : 0 < q)
    (v : ComplexUnitSphere N) :
    complexMatrixGLVal N (concreteOneColumnFactorGL m N q v) =
      concreteOneColumnFactor m N q v := by
  simp [concreteOneColumnFactorGL, hm, hq, complexMatrixGLVal]

theorem measurable_concreteOneColumnFactorGL (m N : ℕ) :
    Measurable fun p : ℝ × ComplexUnitSphere N ↦
      concreteOneColumnFactorGL m N p.1 p.2 := by
  by_cases hm : 1 ≤ m
  · simpa only [concreteOneColumnFactorGL, hm, dite_true] using
      measurable_concreteOneColumnFactorGLLift (N := N) hm
  · simp only [concreteOneColumnFactorGL, hm, dite_false]
    exact measurable_const

theorem complexMatrixGLVal_concreteOneColumnFactorGL_ae
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (fun p : ℝ × ComplexUnitSphere N ↦
        complexMatrixGLVal N (concreteOneColumnFactorGL m N p.1 p.2))
      =ᵐ[concreteOneColumnParameterLaw m N]
    (fun p ↦ concreteOneColumnFactor m N p.1 p.2) := by
  have hm : 1 ≤ m := hN.trans hNm
  have hval := concreteOneColumnFactorGLLift_val_ae hN hm
  filter_upwards [hval] with p hp
  simpa [concreteOneColumnFactorGL, hm, complexMatrixGLVal] using hp

/-! ## Probability factor laws and their matrix pushforwards -/

/-- Probability law on `GL_N(C)` of the centered orbital factor. -/
def concreteOrbitalGLFactorLaw (N : ℕ) (s : ℝ) :
    Measure (ComplexMatrixGL N) :=
  Measure.map (concreteOrbitalFactorGL N s)
    (complexUnitSphereProbabilityMeasure N)

theorem concreteOrbitalGLFactorLaw_isProbability
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    IsProbabilityMeasure (concreteOrbitalGLFactorLaw N s) := by
  let _ : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold concreteOrbitalGLFactorLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_concreteOrbitalFactorGL N s).aemeasurable

theorem map_complexMatrixGLVal_concreteOrbitalGLFactorLaw
    (N : ℕ) (s : ℝ) :
    Measure.map (complexMatrixGLVal N) (concreteOrbitalGLFactorLaw N s) =
      concreteOrbitalFactorLaw N s := by
  unfold concreteOrbitalGLFactorLaw concreteOrbitalFactorLaw
  rw [Measure.map_map (measurable_complexMatrixGLVal N)
    (measurable_concreteOrbitalFactorGL N s)]
  apply Measure.map_congr
  filter_upwards [] with v
  exact complexMatrixGLVal_concreteOrbitalFactorGL N s v

/-- Probability law on `GL_N(C)` of the supported one-column factor lift. -/
def concreteOneColumnGLFactorLaw (m N : ℕ) :
    Measure (ComplexMatrixGL N) :=
  Measure.map
    (fun p : ℝ × ComplexUnitSphere N ↦
      concreteOneColumnFactorGL m N p.1 p.2)
    (concreteOneColumnParameterLaw m N)

theorem concreteOneColumnGLFactorLaw_isProbability
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    IsProbabilityMeasure (concreteOneColumnGLFactorLaw m N) := by
  let _ : IsProbabilityMeasure (concreteOneColumnParameterLaw m N) :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  unfold concreteOneColumnGLFactorLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_concreteOneColumnFactorGL m N).aemeasurable

theorem map_complexMatrixGLVal_concreteOneColumnGLFactorLaw
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Measure.map (complexMatrixGLVal N) (concreteOneColumnGLFactorLaw m N) =
      concreteOneColumnFactorLaw m N := by
  unfold concreteOneColumnGLFactorLaw concreteOneColumnFactorLaw
  rw [Measure.map_map (measurable_complexMatrixGLVal N)
    (measurable_concreteOneColumnFactorGL m N)]
  exact Measure.map_congr
    (complexMatrixGLVal_concreteOneColumnFactorGL_ae hN hNm)

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
