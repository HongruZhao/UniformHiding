import A3.HermitianCoordinates
import A4.MatrixLaplaceUniqueness

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def realCoordinateTraceRepresentative {d : ℕ}
    (L : HermitianCoordinates d ℝ →ₗ[ℝ] ℝ) : MatsumotoPaper.Sym d :=
  MatsumotoPaper.symmetricTraceRepresentative (L.comp (hermitianCoordinateProjectionLinearMap d ℝ))

theorem trace_realCoordinateTraceRepresentative {d : ℕ}
    (L : HermitianCoordinates d ℝ →ₗ[ℝ] ℝ) (x : HermitianCoordinates d ℝ) :
    ((realCoordinateTraceRepresentative L).1 * hermitianMatrixOfCoordinates x).trace = L x := by
  have hx : (hermitianMatrixOfCoordinates x).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (hermitianMatrixOfCoordinates_isHermitian x)
  have ht := MatsumotoPaper.trace_symmetricTraceRepresentative
    (L.comp (hermitianCoordinateProjectionLinearMap d ℝ))
    (⟨hermitianMatrixOfCoordinates x, hx⟩ : MatsumotoPaper.Sym d)
  simpa only [realCoordinateTraceRepresentative, LinearMap.comp_apply,
    hermitianCoordinateProjectionLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    hermitianCoordinateProjection_ofCoordinates] using ht

theorem real_coordinate_laplace_integrable_direction {d : ℕ} {alpha : ℝ}
    {mu : Measure (HermitianCoordinates d ℝ)}
    (hlaplace : ∀ theta : Matrix (Fin d) (Fin d) ℝ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp (theta * hermitianMatrixOfCoordinates x).trace ∂mu) =
        Real.rpow (1 - theta).det (-alpha))
    (L : StrongDual ℝ (HermitianCoordinates d ℝ)) (t : ℝ)
    (hpos : (1 - t • (realCoordinateTraceRepresentative L.toLinearMap).1).PosDef) :
    Integrable (fun x ↦ Real.exp (t * L x)) mu := by
  have ht : (t • (realCoordinateTraceRepresentative L.toLinearMap).1).IsHermitian :=
    (Matrix.isHermitian_iff_isSymm.mpr (realCoordinateTraceRepresentative L.toLinearMap).2).smul
      (IsSelfAdjoint.all t)
  have htrace (x : HermitianCoordinates d ℝ) :
      ((t • (realCoordinateTraceRepresentative L.toLinearMap).1) *
        hermitianMatrixOfCoordinates x).trace = t * L x := by
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      trace_realCoordinateTraceRepresentative]
    rfl
  apply Integrable.of_integral_ne_zero
  have heq := hlaplace _ ht hpos
  simp_rw [htrace] at heq
  rw [heq]
  exact (Real.rpow_pos_of_pos hpos.det_pos _).ne'

theorem real_coordinate_law_eq_of_laplace {d : ℕ} {alpha : ℝ}
    {mu nu : Measure (HermitianCoordinates d ℝ)}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : ∀ theta : Matrix (Fin d) (Fin d) ℝ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp (theta * hermitianMatrixOfCoordinates x).trace ∂mu) =
        Real.rpow (1 - theta).det (-alpha))
    (hnu : ∀ theta : Matrix (Fin d) (Fin d) ℝ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp (theta * hermitianMatrixOfCoordinates x).trace ∂nu) =
        Real.rpow (1 - theta).det (-alpha)) : mu = nu := by
  apply A4Research.measure_eq_of_directional_mgf_eventually_eq
  · intro L
    rw [mem_interior_iff_mem_nhds]
    exact (A4Research.eventually_posDef_sub_smul Matrix.PosDef.one
      (Matrix.isHermitian_iff_isSymm.mpr (realCoordinateTraceRepresentative L.toLinearMap).2)).mono
        fun t ht ↦ real_coordinate_laplace_integrable_direction hmu L t ht
  · intro L
    rw [mem_interior_iff_mem_nhds]
    exact (A4Research.eventually_posDef_sub_smul Matrix.PosDef.one
      (Matrix.isHermitian_iff_isSymm.mpr (realCoordinateTraceRepresentative L.toLinearMap).2)).mono
        fun t ht ↦ real_coordinate_laplace_integrable_direction hnu L t ht
  intro L
  filter_upwards [A4Research.eventually_posDef_sub_smul Matrix.PosDef.one
    (Matrix.isHermitian_iff_isSymm.mpr (realCoordinateTraceRepresentative L.toLinearMap).2)] with t ht
  have hh : (t • (realCoordinateTraceRepresentative L.toLinearMap).1).IsHermitian :=
    (Matrix.isHermitian_iff_isSymm.mpr (realCoordinateTraceRepresentative L.toLinearMap).2).smul
      (IsSelfAdjoint.all t)
  have htrace (x : HermitianCoordinates d ℝ) :
      ((t • (realCoordinateTraceRepresentative L.toLinearMap).1) *
        hermitianMatrixOfCoordinates x).trace = t * L x := by
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      trace_realCoordinateTraceRepresentative]
    rfl
  have heq := (hmu _ hh ht).trans (hnu _ hh ht).symm
  simp_rw [htrace] at heq
  exact heq

end A3Research
