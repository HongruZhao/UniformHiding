import A1.DoubledRealCoordinateEquiv
import A3.ComplexGaussianIsotropy
import A3.GSVAESupport

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def doubledPairIndexEquiv (m : ℕ) : DoubledIndex m ≃ ((i : Fin m) × Fin 2) where
  toFun := Sum.elim (fun i ↦ ⟨i, 0⟩) (fun i ↦ ⟨i, 1⟩)
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv p := by cases p <;> simp
  right_inv p := by rcases p with ⟨i, j⟩; fin_cases j <;> simp

def unpackComplexCoordinates (m : ℕ) (z : Fin m → ℂ) : ((i : Fin m) × Fin 2) → ℝ :=
  fun p ↦ if p.2 = 0 then (z p.1).re else (z p.1).im

theorem measurable_unpackComplexCoordinates (m : ℕ) :
    Measurable (unpackComplexCoordinates m) := by
  unfold unpackComplexCoordinates
  apply measurable_pi_lambda
  intro p
  split_ifs <;> fun_prop

theorem unpack_packComplexCoordinates (m : ℕ) (z : ((i : Fin m) × Fin 2) → ℝ) :
    unpackComplexCoordinates m (A3Research.packComplexCoordinates m z) = z := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases j <;> simp [unpackComplexCoordinates, A3Research.packComplexCoordinates]

theorem map_unpackComplexCoordinates_circularGaussian (m : ℕ) :
    (LogdetLean.GramHafnian.circularGaussianVector m).map (unpackComplexCoordinates m) =
      Measure.pi (fun _ : ((i : Fin m) × Fin 2) ↦ gaussianReal 0 (1 / 2)) := by
  rw [← A3Research.map_packComplexCoordinates_halfGaussian m,
    Measure.map_map (measurable_unpackComplexCoordinates m)
      (by unfold A3Research.packComplexCoordinates; fun_prop)]
  have hcomp : unpackComplexCoordinates m ∘ A3Research.packComplexCoordinates m = id := by
    funext z
    exact unpack_packComplexCoordinates m z
  rw [hcomp, Measure.map_id]

def doubledRealRow {m : ℕ} (z : Fin m → ℂ) : DoubledIndex m → ℝ :=
  Sum.elim (fun i ↦ (z i).re) (fun i ↦ (z i).im)

theorem measurable_doubledRealRow (m : ℕ) :
    Measurable (doubledRealRow : (Fin m → ℂ) → DoubledIndex m → ℝ) := by
  apply measurable_pi_lambda
  rintro (i | i)
  · change Measurable (fun z : Fin m → ℂ ↦ (z i).re)
    fun_prop
  · change Measurable (fun z : Fin m → ℂ ↦ (z i).im)
    fun_prop

theorem map_doubledRealRow_circularGaussian (m : ℕ) :
    (LogdetLean.GramHafnian.circularGaussianVector m).map doubledRealRow =
      Measure.pi (fun _ : DoubledIndex m ↦ gaussianReal 0 (1 / 2)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : ((i : Fin m) × Fin 2) ↦ ℝ)
    (doubledPairIndexEquiv m)
  have hp := (measurePreserving_piCongrLeft
    (fun _ : ((i : Fin m) × Fin 2) ↦ gaussianReal 0 (1 / 2))
    (doubledPairIndexEquiv m)).symm
  have hrow : doubledRealRow = e.symm ∘ unpackComplexCoordinates m := by
    funext z i
    cases i <;> simp [e, doubledRealRow, unpackComplexCoordinates,
      doubledPairIndexEquiv, MeasurableEquiv.piCongrLeft]
  rw [hrow, ← Measure.map_map e.symm.measurable (measurable_unpackComplexCoordinates m),
    map_unpackComplexCoordinates_circularGaussian]
  exact hp.map_eq

def doubledRealGaussianSumMatrix {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n) (DoubledIndex m) ℝ := fun i ↦ doubledRealRow (G i)

def doubledRealGaussianMatrix {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n) (Fin (2 * m)) ℝ :=
  (doubledRealGaussianSumMatrix G).submatrix id (doubledIndexEquiv m).symm

def realHalfGaussianRows (n r : ℕ) : Measure (Fin n → Fin r → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ Measure.pi (fun _ : Fin r ↦ gaussianReal 0 (1 / 2)))

theorem measurable_doubledRealGaussianSumMatrix (n m : ℕ) :
    Measurable (doubledRealGaussianSumMatrix : Matrix (Fin n) (Fin m) ℂ → _) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_doubledRealRow m).comp (measurable_pi_apply i)

theorem measurable_doubledRealGaussianMatrix (n m : ℕ) :
    Measurable (doubledRealGaussianMatrix : Matrix (Fin n) (Fin m) ℂ → _) := by
  unfold doubledRealGaussianMatrix
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply ((doubledIndexEquiv m).symm j)).comp
    ((measurable_pi_apply i).comp (measurable_doubledRealGaussianSumMatrix n m))

theorem map_doubledRealGaussianSumMatrix (n m : ℕ) :
    (LogdetLean.GramHafnian.LocalAnticoncentration.standardComplexGaussianRectangularMeasure n m).map
      doubledRealGaussianSumMatrix =
      Measure.pi (fun _ : Fin n ↦
        Measure.pi (fun _ : DoubledIndex m ↦ gaussianReal 0 (1 / 2))) := by
  rw [LogdetLean.GramHafnian.UltimateHiding.DenseScore.standardComplexGaussianRectangularMeasure_eq_pi]
  change (Measure.pi (fun _ : Fin n ↦ LogdetLean.GramHafnian.circularGaussianVector m)).map
    (fun G : Fin n → Fin m → ℂ ↦ fun i ↦ doubledRealRow (G i)) = _
  letI : SigmaFinite ((LogdetLean.GramHafnian.circularGaussianVector m).map
      (doubledRealRow (m := m))) := by
    rw [map_doubledRealRow_circularGaussian]
    infer_instance
  rw [Measure.pi_map_pi (fun _ ↦ (measurable_doubledRealRow m).aemeasurable)]
  simp only [map_doubledRealRow_circularGaussian]

theorem map_doubledRealGaussianMatrix (n m : ℕ) :
    (LogdetLean.GramHafnian.LocalAnticoncentration.standardComplexGaussianRectangularMeasure n m).map
      doubledRealGaussianMatrix = realHalfGaussianRows n (2 * m) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * m) ↦ ℝ)
    (doubledIndexEquiv m)
  have he := (measurePreserving_piCongrLeft
    (fun _ : Fin (2 * m) ↦ gaussianReal 0 (1 / 2)) (doubledIndexEquiv m)).map_eq
  have hcomp : doubledRealGaussianMatrix =
      (fun G : Fin n → DoubledIndex m → ℝ ↦ fun i ↦ e (G i)) ∘
        doubledRealGaussianSumMatrix := by
    funext G i j
    simp [doubledRealGaussianMatrix, Matrix.submatrix, Function.comp_def, e,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  rw [hcomp, ← Measure.map_map (by fun_prop)
    (measurable_doubledRealGaussianSumMatrix n m), map_doubledRealGaussianSumMatrix,
    Measure.pi_map_pi (fun _ ↦ e.measurable.aemeasurable)]
  unfold realHalfGaussianRows
  congr 1
  funext i
  exact he

end A1Research
