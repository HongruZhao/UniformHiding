import A3.HermitianTraceDual
import A4.LocalTransformUniqueness

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_complex_posDef_sub_smul {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef) (hB : B.IsHermitian) :
    ∀ᶠ t : ℝ in 𝓝 0, (A - t • B).PosDef := by
  have hcont : Continuous (fun z : ℝ × (Fin d → ℂ) ↦
      (star z.2 ⬝ᵥ ((A - z.1 • B) *ᵥ z.2)).re) := by
    unfold dotProduct mulVec
    fun_prop
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ Metric.sphere (0 : Fin d → ℂ) 1,
      0 < (star x ⬝ᵥ ((A - t • B) *ᵥ x)).re := by
    apply (isCompact_sphere (0 : Fin d → ℂ) 1).eventually_forall_of_forall_eventually
    intro x hx
    have hx0 : x ≠ 0 := by
      intro heq
      simpa [heq] using hx
    have hbase : 0 < (star x ⬝ᵥ (A *ᵥ x)).re := hA.re_dotProduct_pos hx0
    exact hcont.continuousAt.eventually (Ioi_mem_nhds (by simpa using hbase))
  filter_upwards [hpos] with t ht
  have hh : (A - t • B).IsHermitian := hA.isHermitian.sub (hB.smul (IsSelfAdjoint.all t))
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hh
  intro x hx
  let y : Fin d → ℂ := ‖x‖⁻¹ • x
  have hy : y ∈ Metric.sphere (0 : Fin d → ℂ) 1 :=
    mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hx)
  have hypos := ht y hy
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hscale : (star y ⬝ᵥ ((A - t • B) *ᵥ y)).re =
      (‖x‖⁻¹ * ‖x‖⁻¹) * (star x ⬝ᵥ ((A - t • B) *ᵥ x)).re := by
    simp only [y, star_smul, star_trivial, mulVec_smul, smul_dotProduct,
      dotProduct_smul, Complex.smul_re, smul_eq_mul]
    ring
  rw [hscale] at hypos
  apply Complex.pos_iff.mpr
  exact ⟨(mul_pos_iff_of_pos_left
    (mul_pos (inv_pos.mpr hnorm) (inv_pos.mpr hnorm))).mp hypos,
    (hh.im_star_dotProduct_mulVec_self x).symm⟩

def hermitianCoordinateMatrixLaw {d : ℕ} (mu : Measure (HermitianCoordinates d ℂ)) :
    Measure (Matrix (Fin d) (Fin d) ℂ) := mu.map hermitianMatrixOfCoordinates

theorem hermitianCoordinateMatrixLaw_probability {d : ℕ}
    (mu : Measure (HermitianCoordinates d ℂ)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (hermitianCoordinateMatrixLaw mu) :=
  Measure.isProbabilityMeasure_map
    (measurable_hermitianMatrixOfCoordinates d ℂ).aemeasurable

theorem complex_posDef_det_re_pos {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) : 0 < A.det.re := (Complex.pos_iff.mp hA.det_pos).1

theorem hermitian_laplace_integrable {d : ℕ} {alpha : ℝ}
    {mu : Measure (HermitianCoordinates d ℂ)}
    (hlaplace : ∀ theta : Matrix (Fin d) (Fin d) ℂ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re ∂mu) =
        Real.rpow ((1 - theta).det.re) (-alpha))
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    Integrable (fun x ↦ Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re) mu := by
  apply Integrable.of_integral_ne_zero
  rw [hlaplace theta htheta hpos]
  exact (Real.rpow_pos_of_pos (complex_posDef_det_re_pos hpos) _).ne'

theorem hermitian_laplace_integrable_direction {d : ℕ} {alpha : ℝ}
    {mu : Measure (HermitianCoordinates d ℂ)}
    (hlaplace : ∀ theta : Matrix (Fin d) (Fin d) ℂ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re ∂mu) =
        Real.rpow ((1 - theta).det.re) (-alpha))
    (L : StrongDual ℝ (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ)
    (hpos : (1 - t • hermitianTraceRepresentative L.toLinearMap).PosDef) :
    Integrable (fun X ↦ Real.exp (t * L X)) (hermitianCoordinateMatrixLaw mu) := by
  have hm : Continuous (fun X : Matrix (Fin d) (Fin d) ℂ ↦ Real.exp (t * L X)) := by fun_prop
  apply (integrable_map_measure hm.measurable.aestronglyMeasurable
    (measurable_hermitianMatrixOfCoordinates d ℂ).aemeasurable).mpr
  apply (hermitian_laplace_integrable hlaplace
    ((hermitianTraceRepresentative_isHermitian L.toLinearMap).smul
      (IsSelfAdjoint.all t)) hpos).congr
  apply Eventually.of_forall
  intro x
  dsimp only [Function.comp_def]
  rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
    trace_hermitianTraceRepresentative L.toLinearMap _
      (hermitianMatrixOfCoordinates_isHermitian x)]
  rfl

theorem hermitianCoordinateMatrixLaw_interior_integrableExpSet {d : ℕ} {alpha : ℝ}
    {mu : Measure (HermitianCoordinates d ℂ)}
    (hlaplace : ∀ theta : Matrix (Fin d) (Fin d) ℂ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re ∂mu) =
        Real.rpow ((1 - theta).det.re) (-alpha))
    (L : StrongDual ℝ (Matrix (Fin d) (Fin d) ℂ)) :
    0 ∈ interior (integrableExpSet L (hermitianCoordinateMatrixLaw mu)) := by
  rw [mem_interior_iff_mem_nhds]
  exact (eventually_complex_posDef_sub_smul Matrix.PosDef.one
    (hermitianTraceRepresentative_isHermitian L.toLinearMap)).mono fun t ht ↦
      hermitian_laplace_integrable_direction hlaplace L t ht

theorem hermitianCoordinateMatrixLaw_mgf {d : ℕ} {alpha : ℝ}
    {mu : Measure (HermitianCoordinates d ℂ)}
    (hlaplace : ∀ theta : Matrix (Fin d) (Fin d) ℂ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re ∂mu) =
        Real.rpow ((1 - theta).det.re) (-alpha))
    (L : StrongDual ℝ (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ)
    (hpos : (1 - t • hermitianTraceRepresentative L.toLinearMap).PosDef) :
    mgf L (hermitianCoordinateMatrixLaw mu) t =
      Real.rpow ((1 - t • hermitianTraceRepresentative L.toLinearMap).det.re) (-alpha) := by
  have hm : Continuous (fun X : Matrix (Fin d) (Fin d) ℂ ↦ Real.exp (t * L X)) := by fun_prop
  unfold hermitianCoordinateMatrixLaw
  rw [mgf_map (measurable_hermitianMatrixOfCoordinates d ℂ).aemeasurable
    hm.measurable.aestronglyMeasurable]
  change (∫ x, Real.exp (t * L (hermitianMatrixOfCoordinates x)) ∂mu) = _
  calc
    _ = ∫ x, Real.exp (((t • hermitianTraceRepresentative L.toLinearMap) *
        hermitianMatrixOfCoordinates x).trace).re ∂mu := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
        trace_hermitianTraceRepresentative L.toLinearMap _
          (hermitianMatrixOfCoordinates_isHermitian x)]
      rfl
    _ = _ := hlaplace _
      ((hermitianTraceRepresentative_isHermitian L.toLinearMap).smul
        (IsSelfAdjoint.all t)) hpos

/-- Actual Hermitian trace transforms determine probability measures in the independent coordinates. -/
theorem hermitian_coordinate_law_eq_of_laplace {d : ℕ} {alpha : ℝ}
    {mu nu : Measure (HermitianCoordinates d ℂ)}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : ∀ theta : Matrix (Fin d) (Fin d) ℂ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re ∂mu) =
        Real.rpow ((1 - theta).det.re) (-alpha))
    (hnu : ∀ theta : Matrix (Fin d) (Fin d) ℂ,
      theta.IsHermitian → (1 - theta).PosDef →
      (∫ x, Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re ∂nu) =
        Real.rpow ((1 - theta).det.re) (-alpha)) : mu = nu := by
  letI := hermitianCoordinateMatrixLaw_probability mu
  letI := hermitianCoordinateMatrixLaw_probability nu
  have heq : hermitianCoordinateMatrixLaw mu = hermitianCoordinateMatrixLaw nu := by
    apply A4Research.measure_eq_of_directional_mgf_eventually_eq
    · exact hermitianCoordinateMatrixLaw_interior_integrableExpSet hmu
    · exact hermitianCoordinateMatrixLaw_interior_integrableExpSet hnu
    intro L
    filter_upwards [eventually_complex_posDef_sub_smul Matrix.PosDef.one
      (hermitianTraceRepresentative_isHermitian L.toLinearMap)] with t ht
    exact (hermitianCoordinateMatrixLaw_mgf hmu L t ht).trans
      (hermitianCoordinateMatrixLaw_mgf hnu L t ht).symm
  have hp := congrArg (fun m ↦ m.map
    (hermitianCoordinateProjection : Matrix (Fin d) (Fin d) ℂ → _)) heq
  simpa [hermitianCoordinateMatrixLaw, Measure.map_map,
    (measurable_hermitianCoordinateProjection d ℂ),
    (measurable_hermitianMatrixOfCoordinates d ℂ), Function.comp_def] using hp

end A3Research
