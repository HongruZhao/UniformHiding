import LogdetLean.GramHafnian.UltimateHiding.Dense.BetaTailConcrete
import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnRecursion
import LogdetLean.GramHafnian.UltimateHiding.Normalized
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Concrete one-column parameters

This file removes the arbitrary direction-law parameter from the ambient
kernel.  The direction is the normalized additive-Haar surface measure on the
unit sphere of `ℂ^N`, and the radial coordinate is the literal beta law from
`Parameters`.

The remaining equality between the Haar/Stiefel Gram law and this kernel is a
geometric polar-decomposition theorem not presently available in Mathlib; it
is not postulated here.
-/

open scoped ENNReal
open MeasureTheory ProbabilityTheory Metric

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- Unit sphere in `ℂ^N`, regarded as a finite-dimensional real normed
space. -/
abbrev ComplexUnitSphere (N : ℕ) :=
  sphere (0 : EuclideanSpace ℂ (Fin N)) 1

/-- Unnormalized rotation-invariant surface measure constructed from additive
Haar measure by polar coordinates. -/
def complexUnitSphereSurfaceMeasure (N : ℕ) :
    Measure (ComplexUnitSphere N) :=
  (volume : Measure (EuclideanSpace ℂ (Fin N))).toSphere

/-- Uniform probability measure on the complex unit sphere. -/
def complexUnitSphereProbabilityMeasure (N : ℕ) :
    Measure (ComplexUnitSphere N) :=
  let σ := complexUnitSphereSurfaceMeasure N
  (σ Set.univ)⁻¹ • σ

theorem complexUnitSphereProbabilityMeasure_isProbability
    {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) := by
  let _ : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  let σ := complexUnitSphereSurfaceMeasure N
  let _ : IsFiniteMeasure σ := by
    dsimp [σ, complexUnitSphereSurfaceMeasure]
    infer_instance
  have hσne : σ Set.univ ≠ 0 := by
    intro hzero
    have hmeasure : σ = 0 := Measure.measure_univ_eq_zero.mp hzero
    exact (Measure.toSphere_ne_zero
      (volume : Measure (EuclideanSpace ℂ (Fin N)))) hmeasure
  have hσtop : σ Set.univ ≠ ∞ :=
    ne_of_lt (measure_lt_top σ Set.univ)
  refine ⟨?_⟩
  unfold complexUnitSphereProbabilityMeasure
  dsimp only
  rw [Measure.smul_apply]
  change ((complexUnitSphereSurfaceMeasure N Set.univ)⁻¹ *
    complexUnitSphereSurfaceMeasure N Set.univ) = 1
  exact ENNReal.inv_mul_cancel (by simpa [σ] using hσne)
    (by simpa [σ] using hσtop)

/-- The fully concrete joint law of the beta scalar and independent uniform
complex direction. -/
def concreteOneColumnParameterLaw (m N : ℕ) :
    Measure (ℝ × ComplexUnitSphere N) :=
  oneColumnParameterLaw m N (complexUnitSphereProbabilityMeasure N)

theorem concreteOneColumnParameterLaw_isProbability
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    IsProbabilityMeasure (concreteOneColumnParameterLaw m N) := by
  exact oneColumnParameterLaw_isProbability
    (complexUnitSphereProbabilityMeasure N) hN hNm
    (complexUnitSphereProbabilityMeasure_isProbability hN)

/-- Ambient update kernel with both parameter laws fixed to the actual beta
and uniform-sphere measures. -/
def concreteAmbientOneColumnKernel
    {State : Type*} [MeasurableSpace State]
    (m N : ℕ)
    (update : ℝ → ComplexUnitSphere N → State → State) :
    Kernel State State :=
  ambientOneColumnKernel m N (complexUnitSphereProbabilityMeasure N) update

theorem concreteAmbientOneColumnKernel_isMarkov
    {State : Type*} [MeasurableSpace State]
    {m N : ℕ}
    (update : ℝ → ComplexUnitSphere N → State → State)
    (hN : 1 ≤ N) (hNm : N ≤ m)
    (hupdate : Measurable fun xp :
      State × (ℝ × ComplexUnitSphere N) ↦
        update xp.2.1 xp.2.2 xp.1) :
    IsMarkovKernel (concreteAmbientOneColumnKernel m N update) := by
  exact ambientOneColumnKernel_isMarkov
    (complexUnitSphereProbabilityMeasure N) update hN hNm
    (complexUnitSphereProbabilityMeasure_isProbability hN) hupdate

/-- Rank-one Hermitian projection associated with a complex unit direction. -/
def complexRankOneProjection {N : ℕ} (v : ComplexUnitSphere N) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j ↦ v.1 i * star (v.1 j)

theorem measurable_complexRankOneProjection (N : ℕ) :
    Measurable (complexRankOneProjection :
      ComplexUnitSphere N → Matrix (Fin N) (Fin N) ℂ) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  change Measurable fun v : ComplexUnitSphere N ↦ v.1 i * star (v.1 j)
  fun_prop

theorem measurable_complexMatrix_mul
    {X l m n : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m] [Fintype n]
    {A : X → Matrix l m ℂ} {B : X → Matrix m n ℂ}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x * B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun q _ ↦
    ((measurable_pi_apply q).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply q).comp hB))

theorem measurable_complexMatrix_transpose
    {X l m : Type*} [MeasurableSpace X]
    [Fintype l] [Fintype m]
    {A : X → Matrix l m ℂ} (hA : Measurable A) :
    Measurable (fun x ↦ (A x).transpose) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hA)

/-- Concrete positive congruence factor
`sqrt((m+1)/m) (I + (sqrt q - 1) P_v)`.

On the beta support and for a unit vector this is the same factor as
`exp(a_m I + b_m P_v)` in the proof note. -/
def concreteOneColumnFactor
    (m N : ℕ) (q : ℝ) (v : ComplexUnitSphere N) :
    Matrix (Fin N) (Fin N) ℂ :=
  (((Real.sqrt (((m + 1 : ℕ) : ℝ) / (m : ℝ)) : ℝ) : ℂ)) •
    (1 + (((Real.sqrt q - 1 : ℝ) : ℂ)) • complexRankOneProjection v)

theorem measurable_concreteOneColumnFactor (m N : ℕ) :
    Measurable fun p : ℝ × ComplexUnitSphere N ↦
      concreteOneColumnFactor m N p.1 p.2 := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [concreteOneColumnFactor, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, complexRankOneProjection]
  fun_prop

/-- Literal congruence update of a complex symmetric Gram matrix. -/
def concreteOneColumnMatrixUpdate
    (m N : ℕ) (q : ℝ) (v : ComplexUnitSphere N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  concreteOneColumnFactor m N q v * A *
    (concreteOneColumnFactor m N q v).transpose

theorem measurable_concreteOneColumnMatrixUpdate (m N : ℕ) :
    Measurable fun xp :
      Matrix (Fin N) (Fin N) ℂ × (ℝ × ComplexUnitSphere N) ↦
        concreteOneColumnMatrixUpdate m N xp.2.1 xp.2.2 xp.1 := by
  have hF : Measurable fun xp :
      Matrix (Fin N) (Fin N) ℂ × (ℝ × ComplexUnitSphere N) ↦
        concreteOneColumnFactor m N xp.2.1 xp.2.2 :=
    (measurable_concreteOneColumnFactor m N).comp measurable_snd
  have hA : Measurable fun xp :
      Matrix (Fin N) (Fin N) ℂ × (ℝ × ComplexUnitSphere N) ↦ xp.1 :=
    measurable_fst
  have hFA := measurable_complexMatrix_mul hF hA
  have hFT := measurable_complexMatrix_transpose hF
  exact measurable_complexMatrix_mul hFA hFT

/-- The actual beta/sphere congruence kernel appearing in the one-column
recursion. -/
def concreteOneColumnMatrixKernel (m N : ℕ) :
    Kernel (Matrix (Fin N) (Fin N) ℂ)
      (Matrix (Fin N) (Fin N) ℂ) :=
  concreteAmbientOneColumnKernel m N
    (concreteOneColumnMatrixUpdate m N)

theorem concreteOneColumnMatrixKernel_isMarkov
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    IsMarkovKernel (concreteOneColumnMatrixKernel m N) := by
  exact concreteAmbientOneColumnKernel_isMarkov
    (concreteOneColumnMatrixUpdate m N) hN hNm
    (measurable_concreteOneColumnMatrixUpdate m N)

/-- Congruence by the concrete factor preserves complex symmetry. -/
theorem concreteOneColumnMatrixUpdate_transpose
    (m N : ℕ) (q : ℝ) (v : ComplexUnitSphere N)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    (concreteOneColumnMatrixUpdate m N q v A).transpose =
      concreteOneColumnMatrixUpdate m N q v A.transpose := by
  unfold concreteOneColumnMatrixUpdate
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem concreteOneColumnMatrixUpdate_symmetric
    (m N : ℕ) (q : ℝ) (v : ComplexUnitSphere N)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.transpose = A) :
    (concreteOneColumnMatrixUpdate m N q v A).transpose =
      concreteOneColumnMatrixUpdate m N q v A := by
  rw [concreteOneColumnMatrixUpdate_transpose, hA]

/-- The literal law of the normalized Haar transpose-Gram corner at ambient
dimension `m`, with row dimension `N` and retained-column count `K`.

This is the paper's `mu_{m,K}`. -/
def concreteHaarAmbientLaw
    (H : LocalAnticoncentration.UnitaryHaarProbabilityFamily)
    (N K m : ℕ) : Measure (Matrix (Fin N) (Fin N) ℂ) :=
  normalizedHaarTransposeGramLaw H m N K

/-- The exact geometric statement still required to identify the concrete
beta/sphere kernel with Haar deletion.  It is deliberately a proposition,
not an axiom: at every `m >= K`, applying the concrete congruence kernel to
`mu_{m,K}` must give `mu_{m+1,K}`. -/
def ConcreteHaarOneColumnRecursion
    (H : LocalAnticoncentration.UnitaryHaarProbabilityFamily)
    (N K : ℕ) : Prop :=
  AmbientOneColumnRecursion
    (concreteHaarAmbientLaw H N K)
    (fun m ↦ concreteOneColumnMatrixKernel m N)
    K

/-- The concrete Haar recursion is exactly an instance of the generic ambient
recursion interface, with no arbitrary direction law or update remaining. -/
theorem ConcreteHaarOneColumnRecursion.toAmbient
    {H : LocalAnticoncentration.UnitaryHaarProbabilityFamily} {N K : ℕ}
    (hrec : ConcreteHaarOneColumnRecursion H N K) :
    AmbientOneColumnRecursion
      (concreteHaarAmbientLaw H N K)
      (fun m ↦ concreteOneColumnMatrixKernel m N)
      K :=
  hrec

/-- One explicit step of the concrete Haar deletion recursion. -/
theorem ConcreteHaarOneColumnRecursion.step_eq
    {H : LocalAnticoncentration.UnitaryHaarProbabilityFamily} {N K m : ℕ}
    (hrec : ConcreteHaarOneColumnRecursion H N K) (hm : K ≤ m) :
    concreteHaarAmbientLaw H N K (m + 1) =
      concreteOneColumnMatrixKernel m N ∘ₘ
        concreteHaarAmbientLaw H N K m :=
  hrec m hm

/-- Two explicit steps of the concrete Haar deletion recursion. -/
theorem ConcreteHaarOneColumnRecursion.two_steps
    {H : LocalAnticoncentration.UnitaryHaarProbabilityFamily} {N K m : ℕ}
    (hrec : ConcreteHaarOneColumnRecursion H N K) (hm : K ≤ m) :
    concreteHaarAmbientLaw H N K (m + 2) =
      (concreteOneColumnMatrixKernel (m + 1) N ∘ₖ
          concreteOneColumnMatrixKernel m N) ∘ₘ
        concreteHaarAmbientLaw H N K m :=
  AmbientOneColumnRecursion.two_steps
    (law := concreteHaarAmbientLaw H N K)
    (step := fun r ↦ concreteOneColumnMatrixKernel r N)
    (start := K) hrec hm

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
