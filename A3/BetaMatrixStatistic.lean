import A3.BetaMatrixKernel

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder ENNReal
open Matrix MeasureTheory Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

/-- The literal square-root representative on the complete coordinate pair space. -/
def betaMatrixJacobiCoordinates (p : HermitianCoordinates n K × HermitianCoordinates n K) :
    HermitianCoordinates n K :=
  let S := CFC.sqrt (hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2)
  hermitianCoordinateConjugationLinearMap S⁻¹ p.1

theorem betaMatrixJacobiCoordinates_sum_congruence
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) (x : HermitianCoordinates n K) :
    betaMatrixJacobiCoordinates
      (hermitianCoordinateConjugationLinearMap C x,
        hermitianCoordinateConjugationLinearMap C (hermitianComplementCoordinates x)) = x := by
  unfold betaMatrixJacobiCoordinates
  have hS : (C * C).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, hC.isHermitian.eq, Matrix.mul_one] using
      hC.isUnit.posDef_star_right_conjugate_iff.mpr Matrix.PosDef.one
  have hsqrt : CFC.sqrt (C * C) = C :=
    (CFC.sqrt_eq_iff (C * C) C hS.posSemidef.nonneg hC.posSemidef.nonneg).mpr rfl
  rw [hermitianConjugation_add_complement hC.isHermitian, hsqrt]
  change (hermitianCoordinateConjugationLinearMap C⁻¹ *
    hermitianCoordinateConjugationLinearMap C) x = x
  rw [← hermitianCoordinateConjugation_mul,
    Matrix.nonsing_inv_mul C ((Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit),
    hermitianCoordinateConjugation_one]
  rfl

section Measurable
variable [MeasurableSpace K] [BorelSpace K] [PolishSpace K]

theorem measurable_cfc_sqrt_realHermitianCoordinates (n : ℕ) :
    Measurable (fun x : HermitianCoordinates n ℝ ↦ CFC.sqrt (hermitianMatrixOfCoordinates x)) := by
  classical
  let s : Set (HermitianCoordinates n ℝ) :=
    {x | (hermitianMatrixOfCoordinates x).PosSemidef}
  have hs : MeasurableSet s := isClosed_wishartPositiveSemidefiniteDomain.measurableSet
  have hc : ContinuousOn (fun x : HermitianCoordinates n ℝ ↦
      CFC.sqrt (hermitianMatrixOfCoordinates x)) s :=
    by
      apply (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℝ)).comp
        continuous_hermitianMatrixOfCoordinates.continuousOn
      intro x hx
      exact hx.nonneg
  have hzero : ContinuousOn (fun _ : HermitianCoordinates n ℝ ↦
      (0 : Matrix (Fin n) (Fin n) ℝ)) sᶜ := continuous_const.continuousOn
  have hm : Measurable (s.piecewise
      (fun x ↦ CFC.sqrt (hermitianMatrixOfCoordinates x)) (fun _ ↦ 0)) :=
    hc.measurable_piecewise hzero hs
  have he : s.piecewise (fun x ↦ CFC.sqrt (hermitianMatrixOfCoordinates x)) (fun _ ↦ 0) =
      fun x ↦ CFC.sqrt (hermitianMatrixOfCoordinates x) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [Set.piecewise_eq_of_mem s _ _ hx]
    · rw [Set.piecewise_eq_of_notMem s _ _ hx]
      exact (CFC.sqrt_of_not_nonneg (fun h ↦ hx h.posSemidef)).symm
  rw [he] at hm
  exact hm

theorem measurable_cfc_sqrt_complexHermitianCoordinates (n : ℕ) :
    Measurable (fun x : HermitianCoordinates n ℂ ↦ CFC.sqrt (hermitianMatrixOfCoordinates x)) := by
  classical
  let s : Set (HermitianCoordinates n ℂ) :=
    {x | (hermitianMatrixOfCoordinates x).PosSemidef}
  have hs : MeasurableSet s := isClosed_wishartPositiveSemidefiniteDomain.measurableSet
  have hc : ContinuousOn (fun x : HermitianCoordinates n ℂ ↦
      CFC.sqrt (hermitianMatrixOfCoordinates x)) s :=
    by
      apply (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℂ)).comp
        continuous_hermitianMatrixOfCoordinates.continuousOn
      intro x hx
      exact hx.nonneg
  have hzero : ContinuousOn (fun _ : HermitianCoordinates n ℂ ↦
      (0 : Matrix (Fin n) (Fin n) ℂ)) sᶜ := continuous_const.continuousOn
  have hm : Measurable (s.piecewise
      (fun x ↦ CFC.sqrt (hermitianMatrixOfCoordinates x)) (fun _ ↦ 0)) :=
    hc.measurable_piecewise hzero hs
  have he : s.piecewise (fun x ↦ CFC.sqrt (hermitianMatrixOfCoordinates x)) (fun _ ↦ 0) =
      fun x ↦ CFC.sqrt (hermitianMatrixOfCoordinates x) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [Set.piecewise_eq_of_mem s _ _ hx]
    · rw [Set.piecewise_eq_of_notMem s _ _ hx]
      exact (CFC.sqrt_of_not_nonneg (fun h ↦ hx h.posSemidef)).symm
  rw [he] at hm
  exact hm

theorem measurable_matrix_nonsing_inv_rclike :
    Measurable (fun A : Matrix (Fin n) (Fin n) K ↦ A⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable (fun A : Matrix (Fin n) (Fin n) K ↦ A.det⁻¹ * A.adjugate i j)
  exact continuous_id.matrix_det.measurable.inv.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      continuous_id.matrix_adjugate.measurable))

theorem measurable_betaMatrixJacobiCoordinates
    (hsqrt : Measurable (fun x : HermitianCoordinates n K ↦
      CFC.sqrt (hermitianMatrixOfCoordinates x))) :
    Measurable (betaMatrixJacobiCoordinates :
      HermitianCoordinates n K × HermitianCoordinates n K → _) := by
  have hsum : Measurable (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
      p.1 + p.2) := measurable_fst.add measurable_snd
  have hs := hsqrt.comp hsum
  have hi := measurable_matrix_nonsing_inv_rclike.comp hs
  have he : (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
      hermitianMatrixOfCoordinates (p.1 + p.2)) =
      fun p ↦ hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2 := by
    funext p
    exact (hermitianMatrixOfCoordinatesLinearMap n K).map_add p.1 p.2
  change Measurable (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
    (CFC.sqrt (hermitianMatrixOfCoordinates (p.1 + p.2)))⁻¹) at hi
  have hi' : Measurable (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
      (CFC.sqrt (hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2))⁻¹) :=
    by
      convert hi using 1
      funext p
      rw [congrFun he p]
  unfold betaMatrixJacobiCoordinates hermitianCoordinateConjugationLinearMap
    hermitianMatrixConjugationLinearMap
  change Measurable (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
    hermitianCoordinateProjection
      ((CFC.sqrt (hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2))⁻¹ *
        hermitianMatrixOfCoordinates p.1 *
          ((CFC.sqrt (hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2))⁻¹).conjTranspose))
  have hprod {f g : HermitianCoordinates n K × HermitianCoordinates n K →
      Matrix (Fin n) (Fin n) K} (hf : Measurable f) (hg : Measurable g) :
      Measurable (fun p ↦ f p * g p) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    change Measurable (fun p ↦ ∑ k, f p i k * g p k j)
    exact Finset.measurable_sum _ (fun k _ ↦
      (((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)).mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hg))))
  exact continuous_hermitianCoordinateProjection.measurable.comp
    (hprod (hprod hi' (continuous_hermitianMatrixOfCoordinates.measurable.comp measurable_fst))
      (continuous_id.matrix_conjTranspose.measurable.comp hi'))

theorem measurable_betaMatrixJacobiCoordinates_real (n : ℕ) :
    Measurable (betaMatrixJacobiCoordinates :
      HermitianCoordinates n ℝ × HermitianCoordinates n ℝ → _) :=
  measurable_betaMatrixJacobiCoordinates (measurable_cfc_sqrt_realHermitianCoordinates n)

theorem measurable_betaMatrixJacobiCoordinates_complex (n : ℕ) :
    Measurable (betaMatrixJacobiCoordinates :
      HermitianCoordinates n ℂ × HermitianCoordinates n ℂ → _) :=
  measurable_betaMatrixJacobiCoordinates (measurable_cfc_sqrt_complexHermitianCoordinates n)

end Measurable
end A3Research
