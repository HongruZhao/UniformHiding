import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16TestPairToBochner
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
# Smooth calculus for the centered coordinate flow

This deterministic module identifies the infinitesimal vector field used by
the corrected weak generator with the time derivative of the centered
coordinate flow.  It contains no determinant estimate, H5 input, event, or
scientific axiom.
-/

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The centered coordinate flow is jointly smooth in time and coordinates. -/
theorem h16CenteredCoordinateFlow_joint_contDiff
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    ContDiff ℝ ∞ (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      h16CenteredCoordinateFlow v p.1 p.2) := by
  unfold h16CenteredCoordinateFlow transposeCongruenceFlowCoordinates
  simp_rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate hN]
  apply contDiff_pi.2
  intro ij
  simp only [complexSymmetricCoordinatesOfMatrix,
    concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
    complexSymmetricMatrixOfCoordinates, complexRankOneProjection,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.one_apply]
  have hneg : ContDiff ℝ ∞ (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      ((Real.exp (-p.1 / (N : ℝ)) : ℝ) : ℂ)) := by
    have hproj : ContDiff ℝ ∞
        (fun p : ℝ × ComplexSymmetricCoordinates N ↦ p.1) := contDiff_fst
    exact Complex.ofRealCLM.contDiff.comp
      ((hproj.neg.div_const (N : ℝ)).exp)
  have hsub : ContDiff ℝ ∞ (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      ((Real.exp p.1 - 1 : ℝ) : ℂ)) := by
    have hproj : ContDiff ℝ ∞
        (fun p : ℝ × ComplexSymmetricCoordinates N ↦ p.1) := contDiff_fst
    exact Complex.ofRealCLM.contDiff.comp
      (hproj.exp.sub contDiff_const)
  have hfactor : ∀ i j : Fin N,
      ContDiff ℝ ∞ (fun p : ℝ × ComplexSymmetricCoordinates N ↦
        ((Real.exp (-p.1 / (N : ℝ)) : ℝ) : ℂ) •
          ((if i = j then 1 else 0) +
            ((Real.exp p.1 - 1 : ℝ) : ℂ) •
              ((v : EuclideanSpace ℂ (Fin N)).ofLp i *
                star ((v : EuclideanSpace ℂ (Fin N)).ofLp j)))) := by
    intro i j
    simpa only [smul_eq_mul] using
      hneg.mul (contDiff_const.add (hsub.mul contDiff_const))
  have hcoordinate : ∀ i j : Fin N,
      ContDiff ℝ ∞ (fun p : ℝ × ComplexSymmetricCoordinates N ↦
        if h : i ≤ j then p.2 ⟨(i, j), h⟩
        else p.2 ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩) := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [dif_pos hij]
      fun_prop
    · simp only [dif_neg hij]
      fun_prop
  apply ContDiff.sum
  intro j hj
  apply ContDiff.mul
  · apply ContDiff.sum
    intro j' hj'
    exact (hfactor ij.1.1 j').mul (hcoordinate j' j)
  · exact hfactor ij.1.2 j

/-- Every fixed-coordinate flow curve is smooth. -/
theorem h16CenteredCoordinateFlow_time_contDiff
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ h16CenteredCoordinateFlow v t x) := by
  change ContDiff ℝ ∞
    ((fun p : ℝ × ComplexSymmetricCoordinates N ↦
      h16CenteredCoordinateFlow v p.1 p.2) ∘ fun t : ℝ ↦ (t, x))
  exact (h16CenteredCoordinateFlow_joint_contDiff hN v).comp
    (contDiff_id.prodMk contDiff_const)

/-- The time derivative of the flow is its infinitesimal vector field at the
flowed point. -/
theorem h16CenteredCoordinateFlow_hasDerivAt
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    HasDerivAt (fun s : ℝ ↦ h16CenteredCoordinateFlow v s x)
      (h16CenteredCoordinateVectorField v
        (h16CenteredCoordinateFlow v t x)) t := by
  let f : ℝ → ComplexSymmetricCoordinates N := fun s ↦
    h16CenteredCoordinateFlow v s x
  let g : ℝ → ComplexSymmetricCoordinates N := fun u ↦
    h16CenteredCoordinateFlow v u (h16CenteredCoordinateFlow v t x)
  have hf : DifferentiableAt ℝ f t :=
    ((h16CenteredCoordinateFlow_time_contDiff hN v x).differentiable
      (by simp)).differentiableAt
  have hshift : (fun u : ℝ ↦ f (t + u)) = g := by
    funext u
    rw [add_comm]
    exact h16CenteredCoordinateFlow_add v u t x
  have hd : deriv f t = deriv g 0 := by
    have htranslate := deriv_comp_const_add f t 0
    rw [hshift] at htranslate
    simpa [f, g] using htranslate.symm
  have hfield : deriv g 0 =
      h16CenteredCoordinateVectorField v
        (h16CenteredCoordinateFlow v t x) := rfl
  exact (hf.hasDerivAt.congr_deriv (hd.trans hfield))

@[simp]
theorem h16CenteredCoordinateFlow_eq_realCLE
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredCoordinateFlow v t x =
      centeredTransposeCongruenceFlowCoordinateRealCLE v t x :=
  rfl

/-- The infinitesimal centered vector field is continuous. -/
theorem continuous_h16CenteredCoordinateVectorField
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    Continuous (h16CenteredCoordinateVectorField v) := by
  let F : (ℝ × ComplexSymmetricCoordinates N) →
      ComplexSymmetricCoordinates N := fun p ↦
    h16CenteredCoordinateFlow v p.1 p.2
  have hF : ContDiff ℝ ∞ F := h16CenteredCoordinateFlow_joint_contDiff hN v
  have hraw : Continuous (fun x : ComplexSymmetricCoordinates N ↦
      (fderiv ℝ F (0, x)) ((1 : ℝ), 0)) :=
    ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  apply hraw.congr
  intro x
  have hpair : HasDerivAt
      (fun t : ℝ ↦ ((t, x) : ℝ × ComplexSymmetricCoordinates N))
      ((1 : ℝ), 0) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).prodMk
      (hasDerivAt_const (x := (0 : ℝ)) x)
  have hcomp : HasDerivAt (fun t : ℝ ↦ F (t, x))
      ((fderiv ℝ F (0, x)) ((1 : ℝ), 0)) 0 :=
    ((hF.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt
      0 hpair
  exact hcomp.deriv.symm

/-- The centered flow pushes its infinitesimal vector field to itself. -/
theorem h16CenteredCoordinateFlow_vectorField
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredCoordinateFlow v t (h16CenteredCoordinateVectorField v x) =
      h16CenteredCoordinateVectorField v
        (h16CenteredCoordinateFlow v t x) := by
  let L := centeredTransposeCongruenceFlowCoordinateRealCLE v t
  let f : ℝ → ComplexSymmetricCoordinates N := fun s ↦
    h16CenteredCoordinateFlow v s x
  have hf : DifferentiableAt ℝ f 0 :=
    ((h16CenteredCoordinateFlow_time_contDiff hN v x).differentiable
      (by simp)).differentiableAt
  have hcomp : HasDerivAt (fun s : ℝ ↦ L (f s)) (L (deriv f 0)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt
  have heq : (fun s : ℝ ↦ L (f s)) =
      (fun s : ℝ ↦ h16CenteredCoordinateFlow v s
        (h16CenteredCoordinateFlow v t x)) := by
    funext s
    change h16CenteredCoordinateFlow v t
        (h16CenteredCoordinateFlow v s x) =
      h16CenteredCoordinateFlow v s
        (h16CenteredCoordinateFlow v t x)
    rw [← h16CenteredCoordinateFlow_add, ← h16CenteredCoordinateFlow_add]
    rw [add_comm]
  rw [h16CenteredCoordinateFlow_eq_realCLE]
  unfold h16CenteredCoordinateVectorField
  calc
    L (deriv f 0) = deriv (fun s : ℝ ↦ L (f s)) 0 := hcomp.deriv.symm
    _ = deriv (fun s : ℝ ↦ h16CenteredCoordinateFlow v s
        (h16CenteredCoordinateFlow v t x)) 0 :=
      congrArg (fun f : ℝ → ComplexSymmetricCoordinates N ↦ deriv f 0) heq
    _ = _ := rfl

/-- A smooth compactly supported test stays smooth after precomposition by a
fixed centered coordinate flow. -/
theorem h16_test_comp_centeredFlow_contDiff
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (hphi : ContDiff ℝ ∞ phi) :
    ContDiff ℝ ∞ (fun x ↦ phi (h16CenteredCoordinateFlow v t x)) := by
  exact hphi.comp
    ((centeredTransposeCongruenceFlowCoordinateRealCLE v t).contDiff)

/-- A compactly supported test stays compactly supported after
precomposition by a centered coordinate flow. -/
theorem h16_test_comp_centeredFlow_hasCompactSupport
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (hsupp : HasCompactSupport phi) :
    HasCompactSupport (fun x ↦ phi (h16CenteredCoordinateFlow v t x)) := by
  change HasCompactSupport
    (phi ∘ centeredTransposeCongruenceFlowCoordinateRealCLE v t)
  exact hsupp.comp_homeomorph
    (centeredTransposeCongruenceFlowCoordinateRealCLE v t).toHomeomorph

/-- The test generator commutes with transport by the centered flow. -/
theorem h16_fderiv_test_comp_centeredFlow_vectorField
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) (t : ℝ)
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (x : ComplexSymmetricCoordinates N) :
    (fderiv ℝ (fun y ↦ phi (h16CenteredCoordinateFlow v t y)) x)
        (h16CenteredCoordinateVectorField v x) =
      (fderiv ℝ phi (h16CenteredCoordinateFlow v t x))
        (h16CenteredCoordinateVectorField v
          (h16CenteredCoordinateFlow v t x)) := by
  have hflow : HasFDerivAt (h16CenteredCoordinateFlow v t)
      (centeredTransposeCongruenceFlowCoordinateRealCLE v t).toContinuousLinearMap x := by
    change HasFDerivAt
      (centeredTransposeCongruenceFlowCoordinateRealCLE v t)
      (centeredTransposeCongruenceFlowCoordinateRealCLE v t).toContinuousLinearMap x
    exact (centeredTransposeCongruenceFlowCoordinateRealCLE v t).hasFDerivAt
  have hcomp := (hphi.differentiable (by simp)).differentiableAt.hasFDerivAt.comp
    x hflow
  change (fderiv ℝ (phi ∘ h16CenteredCoordinateFlow v t) x)
      (h16CenteredCoordinateVectorField v x) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  apply congrArg (fderiv ℝ phi (h16CenteredCoordinateFlow v t x))
  calc
    (centeredTransposeCongruenceFlowCoordinateRealCLE v t).toContinuousLinearMap
        (h16CenteredCoordinateVectorField v x) =
        centeredTransposeCongruenceFlowCoordinateRealCLE v t
          (h16CenteredCoordinateVectorField v x) := rfl
    _ = h16CenteredCoordinateVectorField v
        (h16CenteredCoordinateFlow v t x) := by
      simpa only [h16CenteredCoordinateFlow_eq_realCLE] using
        h16CenteredCoordinateFlow_vectorField hN v t x

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
