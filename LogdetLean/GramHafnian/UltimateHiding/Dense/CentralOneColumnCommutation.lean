import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnFactorSplit
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConvolution
import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Central congruence commutes with a concrete one-column update

The scalar part of the same-beta decomposition is central in
`GL_N(Complex)`.  This file proves the resulting pointwise update identity
and the corresponding *global* kernel commutation internally.  It is the
elementary half of radial propagation; the noncentral orbital half is the
separately audited Gelfand-pair input.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- The deterministic Markov kernel associated with scalar transpose
congruence. -/
def concreteCentralMatrixKernel (N : ℕ) (s : ℝ) :
    Kernel (ConcreteMatrixState N) (ConcreteMatrixState N) :=
  Kernel.deterministic (concreteCentralMatrixUpdate N s)
    (measurable_concreteCentralMatrixUpdate N s)

theorem concreteCentralMatrixKernel_isMarkov (N : ℕ) (s : ℝ) :
    IsMarkovKernel (concreteCentralMatrixKernel N s) := by
  unfold concreteCentralMatrixKernel
  infer_instance

/-- Scalar congruence is literal scalar multiplication of the state. -/
theorem concreteCentralMatrixUpdate_eq_smul
    (N : ℕ) (s : ℝ) (A : ConcreteMatrixState N) :
    concreteCentralMatrixUpdate N s A =
      ((((Real.exp s) ^ 2 : ℝ) : ℂ)) • A := by
  classical
  ext i j
  simp [concreteCentralMatrixUpdate, concreteCentralFactor,
    Matrix.mul_apply, Matrix.one_apply]
  ring

/-- A central scalar congruence commutes pointwise with every concrete
one-column congruence. -/
theorem concreteCentralMatrixUpdate_oneColumn_commute
    (m N : ℕ) (s q : ℝ) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    concreteCentralMatrixUpdate N s
        (concreteOneColumnMatrixUpdate m N q v A) =
      concreteOneColumnMatrixUpdate m N q v
        (concreteCentralMatrixUpdate N s A) := by
  rw [concreteCentralMatrixUpdate_eq_smul,
    concreteCentralMatrixUpdate_eq_smul]
  unfold concreteOneColumnMatrixUpdate
  simp [Matrix.mul_smul, Matrix.smul_mul]

set_option maxHeartbeats 1000000 in
/-- The deterministic central kernel commutes globally with the concrete
one-column Markov kernel.  No Haar invariance or external theorem is used. -/
theorem concreteCentralKernel_oneColumn_commute
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) (s : ℝ) :
    KernelsCommute (concreteCentralMatrixKernel N s)
      (concreteOneColumnMatrixKernel m N) := by
  let _ : IsProbabilityMeasure (concreteOneColumnParameterLaw m N) :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  unfold KernelsCommute
  rw [concreteCentralMatrixKernel,
    Kernel.deterministic_comp_eq_map,
    Kernel.comp_deterministic_eq_comap]
  unfold concreteOneColumnMatrixKernel concreteAmbientOneColumnKernel
    ambientOneColumnKernel
  ext A : 1
  rw [Kernel.map_apply _ (measurable_concreteCentralMatrixUpdate N s)]
  rw [Kernel.comap_apply]
  rw [independentUpdateKernel_apply
    (oneColumnParameterLaw m N (complexUnitSphereProbabilityMeasure N))
    (fun xp ↦ concreteOneColumnMatrixUpdate m N xp.2.1 xp.2.2 xp.1)
    (concreteOneColumnParameterLaw_isProbability hN hNm)
    (measurable_concreteOneColumnMatrixUpdate m N) A]
  rw [independentUpdateKernel_apply
    (oneColumnParameterLaw m N (complexUnitSphereProbabilityMeasure N))
    (fun xp ↦ concreteOneColumnMatrixUpdate m N xp.2.1 xp.2.2 xp.1)
    (concreteOneColumnParameterLaw_isProbability hN hNm)
    (measurable_concreteOneColumnMatrixUpdate m N)
    (concreteCentralMatrixUpdate N s A)]
  · have hinner : Measurable
        (fun p : ℝ × ComplexUnitSphere N ↦
          concreteOneColumnMatrixUpdate m N p.1 p.2 A) := by
      unfold concreteOneColumnMatrixUpdate
      have hF := measurable_concreteOneColumnFactor m N
      have hFA := measurable_complexMatrix_mul hF
        (measurable_const : Measurable
          (fun _ : ℝ × ComplexUnitSphere N ↦ A))
      exact measurable_complexMatrix_mul hFA
        (measurable_complexMatrix_transpose hF)
    have hright : Measurable
        (fun p : ℝ × ComplexUnitSphere N ↦
          concreteOneColumnMatrixUpdate m N p.1 p.2
            (concreteCentralMatrixUpdate N s A)) := by
      unfold concreteOneColumnMatrixUpdate
      have hF := measurable_concreteOneColumnFactor m N
      have hFA := measurable_complexMatrix_mul hF
        (measurable_const : Measurable
          (fun _ : ℝ × ComplexUnitSphere N ↦
            concreteCentralMatrixUpdate N s A))
      exact measurable_complexMatrix_mul hFA
        (measurable_complexMatrix_transpose hF)
    ext B hB
    rw [Measure.map_apply (measurable_concreteCentralMatrixUpdate N s) hB,
      Measure.map_apply hinner
        ((measurable_concreteCentralMatrixUpdate N s) hB),
      Measure.map_apply hright hB]
    congr 1
    ext p
    simp only [Set.mem_preimage]
    rw [concreteCentralMatrixUpdate_oneColumn_commute]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
