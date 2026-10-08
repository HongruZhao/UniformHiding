import A1.HaarBridgeMeasure
import A3.ComplexGaussianIsotropy
import A3.ComplexGaussianVectorProbability
import A3.GSVAESupport

open MeasureTheory ProbabilityTheory Matrix WithLp
open LogdetLean.GramHafnian LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def unitaryEuclideanLinearEquiv {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  ((WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (UnitaryGroup.toLinearEquiv U)).trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

theorem unitaryEuclideanLinearEquiv_inner {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (unitaryEuclideanLinearEquiv U x) (unitaryEuclideanLinearEquiv U y) =
      inner ℂ x y := by
  have hU : (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose * U = 1 := U.property.1
  change ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ ofLp y) ⬝ᵥ
      star ((U : Matrix (Fin n) (Fin n) ℂ) *ᵥ ofLp x) = ofLp y ⬝ᵥ star (ofLp x)
  rw [dotProduct_comm, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, hU, Matrix.vecMul_one, dotProduct_comm]

def unitaryEuclideanIsometry {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (unitaryEuclideanLinearEquiv U).isometryOfInner (unitaryEuclideanLinearEquiv_inner U)

def unitaryEuclideanRealIsometry {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  { (unitaryEuclideanIsometry U).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (unitaryEuclideanIsometry U).norm_map }

def unitaryVectorRotation {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  (MeasurableEquiv.toLp 2 (Fin n → ℂ)).trans
    ((unitaryEuclideanRealIsometry U).toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm)

theorem unitaryVectorRotation_apply {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (z : Fin n → ℂ) : unitaryVectorRotation U z = (U : Matrix (Fin n) (Fin n) ℂ) *ᵥ z :=
  rfl

/-- Left unitary rotation preserves the literal independent circular Gaussian vector. -/
theorem measurePreserving_unitaryVectorRotation {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (unitaryVectorRotation U) (circularGaussianVector n)
      (circularGaussianVector n) := by
  let E := EuclideanSpace ℂ (Fin n)
  let scale : E → E := fun x ↦ (Real.sqrt 2)⁻¹ • x
  let eLp := MeasurableEquiv.toLp 2 (Fin n → ℂ)
  let eReal := unitaryEuclideanRealIsometry U
  let eRep := eReal.toMeasurableEquiv
  let muScaled : Measure E := (stdGaussian E).map scale
  have hLp : MeasurePreserving eLp (circularGaussianVector n) muScaled :=
    ⟨eLp.measurable, A3Research.map_toLp_circularGaussianVector n⟩
  have hRep : MeasurePreserving eRep muScaled muScaled := by
    refine ⟨eRep.measurable, ?_⟩
    have hscale : Measurable scale := by fun_prop
    have hcomm : eRep ∘ scale = scale ∘ eRep := by
      funext x
      exact eReal.map_smul (Real.sqrt 2)⁻¹ x
    dsimp only [muScaled]
    rw [Measure.map_map eRep.measurable hscale, hcomm,
      ← Measure.map_map hscale eRep.measurable]
    change ((stdGaussian E).map eReal).map scale = _
    rw [stdGaussian_map eReal]
  exact (MeasurePreserving.symm eLp hLp).comp (hRep.comp hLp)

theorem gaussian_matrix_measure_uncurry (n m : ℕ) :
    (standardComplexGaussianRectangularMeasure n m).map
      (MeasurableEquiv.curry (Fin n) (Fin m) ℂ).symm =
        Measure.pi (fun _ : Fin n × Fin m ↦ circularGaussian) := by
  rw [standardComplexGaussianRectangularMeasure_eq_pi]
  have h := Measure.infinitePi_map_curry_symm
    (fun _ : Fin n ↦ fun _ : Fin m ↦ circularGaussian)
  simpa only [Measure.infinitePi_eq_pi] using h

theorem gaussian_matrix_measure_curry (n m : ℕ) :
    (Measure.pi (fun _ : Fin n × Fin m ↦ circularGaussian)).map
      (MeasurableEquiv.curry (Fin n) (Fin m) ℂ) =
        standardComplexGaussianRectangularMeasure n m := by
  rw [standardComplexGaussianRectangularMeasure_eq_pi]
  have h := Measure.infinitePi_map_curry
    (fun _ : Fin n ↦ fun _ : Fin m ↦ circularGaussian)
  simpa only [Measure.infinitePi_eq_pi] using h

theorem measurePreserving_gaussianMatrixTranspose (n m : ℕ) :
    MeasurePreserving (Matrix.transpose : Matrix (Fin n) (Fin m) ℂ →
      Matrix (Fin m) (Fin n) ℂ)
      (standardComplexGaussianRectangularMeasure n m)
      (standardComplexGaussianRectangularMeasure m n) := by
  let c1 := MeasurableEquiv.curry (Fin n) (Fin m) ℂ
  let swap := MeasurableEquiv.piCongrLeft (fun _ : Fin m × Fin n ↦ ℂ)
    (Equiv.prodComm (Fin n) (Fin m))
  let c2 := MeasurableEquiv.curry (Fin m) (Fin n) ℂ
  have h1 : MeasurePreserving c1.symm
      (standardComplexGaussianRectangularMeasure n m)
      (Measure.pi fun _ : Fin n × Fin m ↦ circularGaussian) :=
    ⟨c1.symm.measurable, gaussian_matrix_measure_uncurry n m⟩
  have hs : MeasurePreserving swap
      (Measure.pi fun _ : Fin n × Fin m ↦ circularGaussian)
      (Measure.pi fun _ : Fin m × Fin n ↦ circularGaussian) :=
    measurePreserving_piCongrLeft (fun _ ↦ circularGaussian) (Equiv.prodComm (Fin n) (Fin m))
  have h2 : MeasurePreserving c2
      (Measure.pi fun _ : Fin m × Fin n ↦ circularGaussian)
      (standardComplexGaussianRectangularMeasure m n) :=
    ⟨c2.measurable, gaussian_matrix_measure_curry m n⟩
  exact h2.comp (hs.comp h1)

/-- The exact rectangular source in A3/A1 is invariant under every left unitary. -/
theorem measurePreserving_unitaryGaussianMatrix {n m : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun G : Matrix (Fin n) (Fin m) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℂ) * G)
      (standardComplexGaussianRectangularMeasure n m)
      (standardComplexGaussianRectangularMeasure n m) := by
  have hpi := measurePreserving_pi (fun _ : Fin m ↦ circularGaussianVector n)
    (fun _ : Fin m ↦ circularGaussianVector n)
    (fun _ ↦ measurePreserving_unitaryVectorRotation U)
  have hcols : MeasurePreserving
      (fun G : Matrix (Fin m) (Fin n) ℂ ↦ fun j ↦ unitaryVectorRotation U (G j))
      (standardComplexGaussianRectangularMeasure m n)
      (standardComplexGaussianRectangularMeasure m n) := by
    simpa only [standardComplexGaussianRectangularMeasure_eq_pi,
      circularGaussianVector, LogdetLean.GramHafnian.LocalAnticoncentration.hidingReleaseComplexMatrixMeasurableSpace, Matrix] using hpi
  have h := (measurePreserving_gaussianMatrixTranspose m n).comp
    (hcols.comp (measurePreserving_gaussianMatrixTranspose n m))
  convert h using 1
  funext G i j
  rfl

end A1Research
