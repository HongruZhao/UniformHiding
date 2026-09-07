import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCentralScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreOneDerived
import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.ScalarTransport
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Central determinant and likelihood calculus at the square COE base

This module isolates the pointwise second-order calculus needed for the
scalar congruence direction.  It specializes the moving determinant to
`Q = I` at the public endpoint.  The private inverse/resolvent lemmas are
the minimal branch refactored from `CenteredDensityScoreTwoScratch`: the
unused second determinant derivative and all projective contractions are
deliberately omitted.
-/

open Function
open Matrix Polynomial
open scoped BigOperators ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

set_option maxHeartbeats 2000000

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.CurrentPRL

section MatrixCalculus

variable {N : ℕ}

private theorem differentiableAt_det_matrix_path
    (F : ℂ → ConcreteMatrixState N) (x : ℂ)
    (hF : ∀ i j, DifferentiableAt ℂ (fun z ↦ F z i j) x) :
    DifferentiableAt ℂ (fun z ↦ Matrix.det (F z)) x := by
  classical
  rw [show (fun z ↦ Matrix.det (F z)) =
      fun z ↦ ∑ sigma : Equiv.Perm (Fin N),
        Equiv.Perm.sign sigma • ∏ i, F z (sigma i) i by
    funext z
    exact Matrix.det_apply (F z)]
  fun_prop

private theorem differentiableAt_adjugate_entry_matrix_path
    (F : ℂ → ConcreteMatrixState N) (x : ℂ)
    (hF : ∀ i j, DifferentiableAt ℂ (fun z ↦ F z i j) x)
    (i j : Fin N) :
    DifferentiableAt ℂ (fun z ↦ (F z).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply differentiableAt_det_matrix_path
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · fun_prop
  · exact hF a b

private theorem differentiableAt_nonsing_inv_entry_matrix_path
    (F : ℂ → ConcreteMatrixState N) (x : ℂ)
    (hF : ∀ i j, DifferentiableAt ℂ (fun z ↦ F z i j) x)
    (hunit : IsUnit (F x).det) (i j : Fin N) :
    DifferentiableAt ℂ (fun z ↦ (F z)⁻¹ i j) x := by
  have hdetDiff := differentiableAt_det_matrix_path F x hF
  have hdetNe : Matrix.det (F x) ≠ 0 :=
    (isUnit_iff_ne_zero.mp hunit)
  have hunitEv : ∀ᶠ z in nhds x, IsUnit (Matrix.det (F z)) := by
    filter_upwards [hdetDiff.continuousAt.eventually_ne hdetNe] with z hz
    exact isUnit_iff_ne_zero.mpr hz
  have heq : (fun z ↦ (F z)⁻¹ i j) =ᶠ[nhds x]
      fun z ↦ (Matrix.det (F z))⁻¹ * (F z).adjugate i j := by
    filter_upwards [hunitEv] with z hz
    rw [Matrix.nonsing_inv_apply (F z) hz]
    simp only [Matrix.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val,
      IsUnit.unit_spec]
  apply (heq.differentiableAt_iff).2
  exact hdetDiff.inv hdetNe |>.mul
    (differentiableAt_adjugate_entry_matrix_path F x hF i j)

private theorem hasDerivAt_nonsing_inv_entry_matrix_path
    (F : ℂ → ConcreteMatrixState N) (F' : ConcreteMatrixState N)
    (x : ℂ)
    (hF : ∀ i j, HasDerivAt (fun z ↦ F z i j) (F' i j) x)
    (hunit : IsUnit (F x).det) (i j : Fin N) :
    HasDerivAt (fun z ↦ (F z)⁻¹ i j)
      ((-(F x)⁻¹ * F' * (F x)⁻¹) i j) x := by
  let J : ℂ → ConcreteMatrixState N := fun z ↦ (F z)⁻¹
  let J' : ConcreteMatrixState N := fun a b ↦ deriv (fun z ↦ J z a b) x
  have hFdiff (a b : Fin N) :
      DifferentiableAt ℂ (fun z ↦ F z a b) x := (hF a b).differentiableAt
  have hJdiff (a b : Fin N) :
      DifferentiableAt ℂ (fun z ↦ J z a b) x :=
    differentiableAt_nonsing_inv_entry_matrix_path F x hFdiff hunit a b
  have hJ (a b : Fin N) :
      HasDerivAt (fun z ↦ J z a b) (J' a b) x :=
    (hJdiff a b).hasDerivAt
  have hunitEv : ∀ᶠ z in nhds x, IsUnit (Matrix.det (F z)) := by
    have hdetDiff := differentiableAt_det_matrix_path F x hFdiff
    have hdetNe : Matrix.det (F x) ≠ 0 := isUnit_iff_ne_zero.mp hunit
    filter_upwards [hdetDiff.continuousAt.eventually_ne hdetNe] with z hz
    exact isUnit_iff_ne_zero.mpr hz
  have hmatrix : F' * J x + F x * J' = 0 := by
    ext a b
    have hprod : HasDerivAt (fun z ↦ (F z * J z) a b)
        ((F' * J x + F x * J') a b) x := by
      simp only [Matrix.mul_apply, Matrix.add_apply]
      have hs := HasDerivAt.fun_sum (u := Finset.univ)
        (A := fun k z ↦ F z a k * J z k b)
        (A' := fun k ↦ F' a k * J x k b + F x a k * J' k b)
        (fun k _ ↦ (hF a k).mul (hJ k b))
      rw [← Finset.sum_add_distrib]
      exact hs
    have heq : (fun z ↦ (F z * J z) a b) =ᶠ[nhds x]
        fun _ ↦ (1 : ConcreteMatrixState N) a b := by
      filter_upwards [hunitEv] with z hz
      rw [show J z = (F z)⁻¹ by rfl, Matrix.mul_nonsing_inv _ hz]
    have hzero : HasDerivAt (fun _ : ℂ ↦
        (1 : ConcreteMatrixState N) a b) 0 x := hasDerivAt_const x _
    exact (hprod.congr_of_eventuallyEq heq.symm).unique hzero
  have hJmatrix : J' = -(F x)⁻¹ * F' * (F x)⁻¹ := by
    have hinvMul : (F x)⁻¹ * F x = 1 :=
      Matrix.nonsing_inv_mul _ hunit
    calc
      J' = 1 * J' := (Matrix.one_mul _).symm
      _ = ((F x)⁻¹ * F x) * J' := by rw [hinvMul]
      _ = (F x)⁻¹ * (F x * J') := by noncomm_ring
      _ = (F x)⁻¹ * (-(F' * J x)) := by
        have := congrArg (fun M ↦ M - F' * J x) hmatrix
        simp only [zero_sub] at this
        rw [← this]
        noncomm_ring
      _ = -(F x)⁻¹ * F' * (F x)⁻¹ := by
        unfold J
        noncomm_ring
  rw [← hJmatrix]
  exact hJ i j
local instance centeredMatrixNormedAddCommGroupTwo :
    NormedAddCommGroup (ConcreteMatrixState N) :=
  Matrix.linftyOpNormedAddCommGroup

local instance centeredMatrixNormedSpaceTwo :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance centeredMatrixAddCommGroupTwo :
    AddCommGroup (ConcreteMatrixState N) :=
  centeredMatrixNormedAddCommGroupTwo.toAddCommGroup

local instance centeredMatrixModuleTwo :
    Module ℂ (ConcreteMatrixState N) := centeredMatrixNormedSpaceTwo.toModule

local instance centeredMatrixPseudoMetricSpaceTwo :
    PseudoMetricSpace (ConcreteMatrixState N) :=
  centeredMatrixNormedAddCommGroupTwo.toPseudoMetricSpace

local instance centeredMatrixUniformSpaceTwo :
    UniformSpace (ConcreteMatrixState N) :=
  centeredMatrixPseudoMetricSpaceTwo.toUniformSpace

local instance centeredMatrixTopologicalSpaceTwo :
    TopologicalSpace (ConcreteMatrixState N) :=
  centeredMatrixUniformSpaceTwo.toTopologicalSpace

local instance centeredMatrixNormedRingTwo :
    NormedRing (ConcreteMatrixState N) := Matrix.linftyOpNormedRing

local instance centeredMatrixNormedAlgebraTwo :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra
private theorem trace_centeredNormalizedSupportDerivative_eq_of_isUnit_two
    (Q C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hHunit : IsUnit (1 - C.conjTranspose * C)) :
    Matrix.trace (centeredNormalizedSupportDerivative Q C) =
      4 * Matrix.trace
        (Q * (C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose)) := by
  let H : ConcreteMatrixState N := 1 - C.conjTranspose * C
  let G : ConcreteMatrixState N := 1 - C * C.conjTranspose
  let Z : ConcreteMatrixState N := C * H⁻¹ * C.conjTranspose
  have hHunit' : IsUnit H := by simpa only [H] using hHunit
  letI : Invertible H := hHunit'.invertible
  have hGt : G.transpose = H := by
    unfold G H
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      hC.eq, hC.conjTranspose.eq]
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_transpose, hGt]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hHunit'
  letI : Invertible G := hGunit.invertible
  have hGC : G * C = C * H := by
    unfold G H
    noncomm_ring
  have hGinv : G⁻¹ = 1 + Z := by
    rw [← Matrix.mul_one G⁻¹]
    apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible G 1 (1 + Z)).2
    rw [Matrix.mul_add, Matrix.mul_one]
    have hterm : G * Z = C * C.conjTranspose := by
      unfold Z
      calc
        G * (C * H⁻¹ * C.conjTranspose) =
            (G * C) * H⁻¹ * C.conjTranspose := by noncomm_ring
        _ = (C * H) * H⁻¹ * C.conjTranspose := by rw [hGC]
        _ = C * (H * H⁻¹) * C.conjTranspose := by noncomm_ring
        _ = C * C.conjTranspose := by
          rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]
    rw [hterm]
    unfold G
    noncomm_ring
  have hHinv_mul_CC : H⁻¹ * (C.conjTranspose * C) = H⁻¹ - 1 := by
    calc
      H⁻¹ * (C.conjTranspose * C) = H⁻¹ * (1 - H) := by
        unfold H
        noncomm_ring
      _ = H⁻¹ - H⁻¹ * H := by noncomm_ring
      _ = H⁻¹ - 1 := by rw [Matrix.inv_mul_of_invertible]
  have hCC_mul_Hinv : (C.conjTranspose * C) * H⁻¹ = H⁻¹ - 1 := by
    calc
      (C.conjTranspose * C) * H⁻¹ = (1 - H) * H⁻¹ := by
        unfold H
        noncomm_ring
      _ = H⁻¹ - H * H⁻¹ := by noncomm_ring
      _ = H⁻¹ - 1 := by rw [Matrix.mul_inv_of_invertible]
  have ht1 : Matrix.trace (H⁻¹ * (Q.transpose * (C.conjTranspose * C))) =
      Matrix.trace (H⁻¹ * Q.transpose) - Matrix.trace Q.transpose := by
    calc
      Matrix.trace (H⁻¹ * (Q.transpose * (C.conjTranspose * C))) =
          Matrix.trace (H⁻¹ * Q.transpose * (C.conjTranspose * C)) := by
            rw [Matrix.mul_assoc]
      _ = Matrix.trace ((C.conjTranspose * C) * H⁻¹ * Q.transpose) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace ((H⁻¹ - 1) * Q.transpose) := by rw [hCC_mul_Hinv]
      _ = _ := by
        rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul]
  have ht3 : Matrix.trace (H⁻¹ * ((C.conjTranspose * C) * Q.transpose)) =
      Matrix.trace (H⁻¹ * Q.transpose) - Matrix.trace Q.transpose := by
    calc
      Matrix.trace (H⁻¹ * ((C.conjTranspose * C) * Q.transpose)) =
          Matrix.trace ((H⁻¹ * (C.conjTranspose * C)) * Q.transpose) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace ((H⁻¹ - 1) * Q.transpose) := by rw [hHinv_mul_CC]
      _ = _ := by
        rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul]
  have ht2 : Matrix.trace (H⁻¹ * (C.conjTranspose * Q * C)) =
      Matrix.trace (Q * Z) := by
    calc
      Matrix.trace (H⁻¹ * (C.conjTranspose * Q * C)) =
          Matrix.trace (H⁻¹ * C.conjTranspose * Q * C) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace (C * (H⁻¹ * C.conjTranspose) * Q) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (Q * (C * (H⁻¹ * C.conjTranspose))) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Q * Z) := by
        unfold Z
        congr 2
        noncomm_ring
  have hbase : Matrix.trace (H⁻¹ * Q.transpose) - Matrix.trace Q.transpose =
      Matrix.trace (Q * Z) := by
    have hHt : H.transpose = G := by
      unfold H G
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        hC.conjTranspose.eq, hC.eq]
    have htr : Matrix.trace (H⁻¹ * Q.transpose) =
        Matrix.trace (Q * G⁻¹) := by
      calc
        Matrix.trace (H⁻¹ * Q.transpose) =
            Matrix.trace ((H⁻¹ * Q.transpose).transpose) :=
              (Matrix.trace_transpose _).symm
        _ = Matrix.trace (Q * G⁻¹) := by
          rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
            Matrix.transpose_transpose, hHt]
    rw [htr, hGinv, Matrix.mul_add, Matrix.mul_one,
      Matrix.trace_add, Matrix.trace_transpose]
    ring
  unfold centeredNormalizedSupportDerivative centeredSupportPathDerivative
  change Matrix.trace (H⁻¹ *
      (Q.transpose * C.conjTranspose * C +
        2 • (C.conjTranspose * Q * C) +
          C.conjTranspose * C * Q.transpose)) = 4 * Matrix.trace (Q * Z)
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add]
  have hmiddle : Matrix.trace (H⁻¹ * (2 • (C.conjTranspose * Q * C))) =
      2 * Matrix.trace (Q * Z) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, ht2]
    norm_num
  rw [show H⁻¹ * (Q.transpose * C.conjTranspose * C) =
      H⁻¹ * (Q.transpose * (C.conjTranspose * C)) by noncomm_ring]
  rw [ht1, ht3, hmiddle, hbase]
  ring

private def centeredMovedCornerTwo
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  transposeCongruenceFlow Q (-t) C

def centeredMovedDetTwo
    (Q C : ConcreteMatrixState N) (t : ℝ) : ℝ :=
  (Matrix.det (1 - (centeredMovedCornerTwo Q C t).conjTranspose *
    centeredMovedCornerTwo Q C t)).re

/-- In the scalar direction `Q = I`, the private centered congruence is the
literal `exp (-2t)` transport used by the coordinate jets. -/
theorem centeredMovedDetTwo_one_eq_exp_neg_two_smul
    (C : ConcreteMatrixState N) (t : ℝ) :
    centeredMovedDetTwo (1 : ConcreteMatrixState N) C t =
      (Matrix.det (1 -
        (((Real.exp (-2 * t) : ℝ) : ℂ) • C).conjTranspose *
          (((Real.exp (-2 * t) : ℝ) : ℂ) • C))).re := by
  have hcorner :
      centeredMovedCornerTwo (1 : ConcreteMatrixState N) C t =
        concreteCentralMatrixUpdate N (-t) C := by
    change transposeCongruence
        (NormedSpace.exp ((((-t : ℝ) : ℂ)) •
          (1 : ConcreteMatrixState N))) C =
      concreteCentralMatrixUpdate N (-t) C
    rw [Complex.ofReal_neg]
    have hexp :
        NormedSpace.exp ((-((t : ℝ) : ℂ)) •
          (1 : ConcreteMatrixState N)) =
        NormedSpace.exp (-((t : ℝ) : ℂ)) •
          (1 : ConcreteMatrixState N) :=
      matrix_exp_smul_one (-((t : ℝ) : ℂ))
    rw [hexp, ← Complex.exp_eq_exp_ℂ]
    simp [transposeCongruence, concreteCentralMatrixUpdate,
      concreteCentralFactor]
  unfold centeredMovedDetTwo
  rw [hcorner, concreteCentralMatrixUpdate_eq_exp_two_smul]
  congr 5
  · congr 1
    ring
  · congr 1
    ring

private def centeredMovedZTwo
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  let Ct := centeredMovedCornerTwo Q C t
  Ct * (1 - Ct.conjTranspose * Ct)⁻¹ * Ct.conjTranspose

private theorem centeredMovedCornerTwo_add
    (Q C : ConcreteMatrixState N) (y t : ℝ) :
    centeredMovedCornerTwo Q C (y + t) =
      centeredMovedCornerTwo Q (centeredMovedCornerTwo Q C y) t := by
  unfold centeredMovedCornerTwo
  rw [← transposeCongruenceFlow_add]
  congr 2
  ring

private theorem hasDerivAt_centeredMovedDetTwo
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) (hC : C.IsSymm)
    (y : ℝ)
    (hunit : IsUnit (Matrix.det
      (1 - (centeredMovedCornerTwo Q C y).conjTranspose *
        centeredMovedCornerTwo Q C y))) :
    HasDerivAt (centeredMovedDetTwo Q C)
      (4 * centeredMovedDetTwo Q C y *
        (Matrix.trace (Q * centeredMovedZTwo Q C y)).re) y := by
  let Cy := centeredMovedCornerTwo Q C y
  have hCy : Cy.IsSymm := by
    unfold Cy centeredMovedCornerTwo transposeCongruenceFlow
    exact transposeCongruence_isSymm _ hC
  have hcomplex := hasDerivAt_det_centeredHolomorphicSupportPath Q Cy
    (by simpa only [Cy] using hunit)
  have hreal := hcomplex.real_of_complex
  have hshift : HasDerivAt (fun t : ℝ ↦ centeredMovedDetTwo Q C (y + t))
      (Matrix.det (1 - Cy.conjTranspose * Cy) *
        Matrix.trace (centeredNormalizedSupportDerivative Q Cy)).re 0 := by
    convert hreal using 1
    funext t
    rw [centeredHolomorphicSupportPath_ofReal_eq Q Cy hQ t]
    unfold centeredMovedDetTwo
    rw [centeredMovedCornerTwo_add]
    rfl
  have hyraw : HasDerivAt (centeredMovedDetTwo Q C)
      (Matrix.det (1 - Cy.conjTranspose * Cy) *
        Matrix.trace (centeredNormalizedSupportDerivative Q Cy)).re y := by
    have hshift' : HasDerivAt
        (fun t : ℝ ↦ centeredMovedDetTwo Q C (y + t))
        (Matrix.det (1 - Cy.conjTranspose * Cy) *
          Matrix.trace (centeredNormalizedSupportDerivative Q Cy)).re
        (y - y) := by simpa using hshift
    have hh := hshift'.comp_sub_const y y
    simpa using hh
  have hHunit : IsUnit (1 - Cy.conjTranspose * Cy) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by simpa only [Cy] using hunit)
  have htrace :=
    trace_centeredNormalizedSupportDerivative_eq_of_isUnit_two Q Cy hCy hHunit
  rw [htrace] at hyraw
  have hHerm : (1 - Cy.conjTranspose * Cy).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self Cy)
  have hdetIm : (Matrix.det (1 - Cy.conjTranspose * Cy)).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    have hh := congrArg Matrix.det hHerm.eq
    rw [Matrix.det_conjTranspose] at hh
    exact hh
  convert hyraw using 1
  · unfold centeredMovedDetTwo centeredMovedZTwo
    rw [show centeredMovedCornerTwo Q C y = Cy by rfl]
    simp [Complex.mul_re, hdetIm]
    ring

private def centeredMovedZOutTwo
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  let Ct := centeredMovedCornerTwo Q C t
  (1 - Ct * Ct.conjTranspose)⁻¹ - 1

private theorem centeredHolomorphicOutputSupportPath_ofReal_eq_two
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) (t : ℝ) :
    centeredHolomorphicSupportPath Q.transpose C.conjTranspose (t : ℂ) =
      1 - centeredMovedCornerTwo Q C t *
        (centeredMovedCornerTwo Q C t).conjTranspose := by
  have hflow :
      transposeCongruenceFlow Q.transpose (-t) C.conjTranspose =
        (transposeCongruenceFlow Q (-t) C).conjTranspose := by
    rw [transposeCongruenceFlow_eq, transposeCongruenceFlow_eq]
    simp only [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose]
    rw [show ((((-t : ℝ) : ℂ) • Q.transpose).conjTranspose) =
        ((-t : ℂ) • Q.transpose) by
          rw [Matrix.conjTranspose_smul]
          simp [hQ.transpose.eq],
      show ((((-t : ℝ) : ℂ) • Q).conjTranspose) =
        ((-t : ℂ) • Q) by
          rw [Matrix.conjTranspose_smul, hQ.eq]
          simp]
    simp only [Matrix.transpose_transpose]
    simp only [Complex.ofReal_neg]
    noncomm_ring
  rw [centeredHolomorphicSupportPath_ofReal_eq Q.transpose C.conjTranspose
    hQ.transpose t, hflow]
  simp only [Matrix.conjTranspose_conjTranspose]
  rfl

private theorem output_inv_sub_one_eq_input_Z_two
    (D : ConcreteMatrixState N)
    (hHunit : IsUnit (1 - D.conjTranspose * D)) :
    (1 - D * D.conjTranspose)⁻¹ - 1 =
      D * (1 - D.conjTranspose * D)⁻¹ * D.conjTranspose := by
  let H : ConcreteMatrixState N := 1 - D.conjTranspose * D
  let G : ConcreteMatrixState N := 1 - D * D.conjTranspose
  have hHunit' : IsUnit H := by simpa only [H] using hHunit
  letI : Invertible H := hHunit'.invertible
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [show Matrix.det G = Matrix.det H by
      unfold G H
      exact Matrix.det_one_sub_mul_comm D D.conjTranspose]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hHunit'
  letI : Invertible G := hGunit.invertible
  have hGC : G * D = D * H := by
    unfold G H
    noncomm_ring
  have hGinv : G⁻¹ = 1 + D * H⁻¹ * D.conjTranspose := by
    rw [← Matrix.mul_one G⁻¹]
    apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible G 1
      (1 + D * H⁻¹ * D.conjTranspose)).2
    rw [Matrix.mul_add, Matrix.mul_one]
    have hterm : G * (D * H⁻¹ * D.conjTranspose) =
        D * D.conjTranspose := by
      calc
        G * (D * H⁻¹ * D.conjTranspose) =
            (G * D) * H⁻¹ * D.conjTranspose := by noncomm_ring
        _ = (D * H) * H⁻¹ * D.conjTranspose := by rw [hGC]
        _ = D * (H * H⁻¹) * D.conjTranspose := by noncomm_ring
        _ = D * D.conjTranspose := by
          rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]
    rw [hterm]
    unfold G
    noncomm_ring
  change G⁻¹ - 1 = D * H⁻¹ * D.conjTranspose
  rw [hGinv]
  abel

private theorem hasDerivAt_centeredMovedZOutTwo_entry
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C)))
    (i j : Fin N) :
    HasDerivAt (fun t : ℝ ↦ centeredMovedZOutTwo Q C t i j)
      ((-(1 - C * C.conjTranspose)⁻¹ *
          centeredSupportPathDerivative Q.transpose C.conjTranspose *
            (1 - C * C.conjTranspose)⁻¹) i j) 0 := by
  let F : ℂ → ConcreteMatrixState N := fun z ↦
    centeredHolomorphicSupportPath Q.transpose C.conjTranspose z
  let F' : ConcreteMatrixState N :=
    centeredSupportPathDerivative Q.transpose C.conjTranspose
  have hGunit : IsUnit (Matrix.det (1 - C * C.conjTranspose)) := by
    rw [Matrix.det_one_sub_mul_comm C C.conjTranspose]
    exact hunit
  have hInv := hasDerivAt_nonsing_inv_entry_matrix_path F F' 0
    (fun a b ↦ by
      simpa only [F, F'] using
        hasDerivAt_centeredHolomorphicSupportPath_entry
          Q.transpose C.conjTranspose a b)
    (by simpa [F, centeredHolomorphicSupportPath_zero] using hGunit) i j
  have hreal := hInv.comp_ofReal.sub_const ((1 : ConcreteMatrixState N) i j)
  have heq : (fun t : ℝ ↦ centeredMovedZOutTwo Q C t i j) =
      fun t : ℝ ↦ (F (t : ℂ))⁻¹ i j - (1 : ConcreteMatrixState N) i j := by
    funext t
    unfold centeredMovedZOutTwo
    dsimp only [F]
    simp only [Matrix.sub_apply]
    rw [centeredHolomorphicOutputSupportPath_ofReal_eq_two Q C hQ t]
  rw [heq]
  simpa [F, F', centeredHolomorphicSupportPath_zero] using hreal

private theorem hasDerivAt_trace_centeredMovedZOutTwo
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C))) :
    HasDerivAt
      (fun t : ℝ ↦ Matrix.trace (Q * centeredMovedZOutTwo Q C t))
      (Matrix.trace (Q * (-(1 - C * C.conjTranspose)⁻¹ *
        centeredSupportPathDerivative Q.transpose C.conjTranspose *
          (1 - C * C.conjTranspose)⁻¹))) 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (hasDerivAt_centeredMovedZOutTwo_entry Q C hQ hunit j i).const_mul
    (Q i j)

private theorem trace_centeredMovedZOutTwo_derivative_eq_two
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C))) :
    Matrix.trace (Q * (-(1 - C * C.conjTranspose)⁻¹ *
        centeredSupportPathDerivative Q.transpose C.conjTranspose *
          (1 - C * C.conjTranspose)⁻¹)) =
      -2 * (Matrix.trace (Q * (1 + centeredMovedZTwo Q C 0) * Q *
          centeredMovedZTwo Q C 0) +
        Matrix.trace (Q * ((1 - C * C.conjTranspose)⁻¹ * C) *
          Q.transpose *
            ((1 - C * C.conjTranspose)⁻¹ * C).conjTranspose)) := by
  let H : ConcreteMatrixState N := 1 - C.conjTranspose * C
  let G : ConcreteMatrixState N := 1 - C * C.conjTranspose
  let W : ConcreteMatrixState N := G⁻¹
  let Z : ConcreteMatrixState N := C * H⁻¹ * C.conjTranspose
  let T : ConcreteMatrixState N := W * C
  have hHunit : IsUnit H :=
    (Matrix.isUnit_iff_isUnit_det H).2 (by simpa only [H] using hunit)
  letI : Invertible H := hHunit.invertible
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [show Matrix.det G = Matrix.det H by
      unfold G H
      exact Matrix.det_one_sub_mul_comm C C.conjTranspose]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hHunit
  letI : Invertible G := hGunit.invertible
  have hWsub : W - 1 = Z := by
    unfold W G Z H
    exact output_inv_sub_one_eq_input_Z_two C
      (by simpa only [H] using hHunit)
  have hW : W = 1 + Z := by
    rw [← hWsub]
    abel
  have hWCC : W * (C * C.conjTranspose) = Z := by
    calc
      W * (C * C.conjTranspose) = W * (1 - G) := by
        unfold G
        noncomm_ring
      _ = W - W * G := by noncomm_ring
      _ = W - 1 := by rw [Matrix.inv_mul_of_invertible]
      _ = Z := hWsub
  have hCCW : (C * C.conjTranspose) * W = Z := by
    calc
      (C * C.conjTranspose) * W = (1 - G) * W := by
        unfold G
        noncomm_ring
      _ = W - G * W := by noncomm_ring
      _ = W - 1 := by rw [Matrix.mul_inv_of_invertible]
      _ = Z := hWsub
  have hWherm : W.IsHermitian := by
    unfold W G
    exact (Matrix.isHermitian_one.sub
      (Matrix.isHermitian_mul_conjTranspose_self C)).inv
  have hTstar : T.conjTranspose = C.conjTranspose * W := by
    unfold T
    rw [Matrix.conjTranspose_mul, hWherm.eq]
  have hD : centeredSupportPathDerivative Q.transpose C.conjTranspose =
      Q * C * C.conjTranspose + 2 • (C * Q.transpose * C.conjTranspose) +
        C * C.conjTranspose * Q := by
    unfold centeredSupportPathDerivative
    simp only [Matrix.transpose_transpose, Matrix.conjTranspose_conjTranspose]
  have hcycle : Matrix.trace (Q * Z * Q * W) =
      Matrix.trace (Q * W * Q * Z) := by
    calc
      Matrix.trace (Q * Z * Q * W) =
          Matrix.trace (W * (Q * Z) * Q) := by
            rw [show Q * Z * Q * W = (Q * Z) * Q * W by noncomm_ring,
              Matrix.trace_mul_cycle]
      _ = Matrix.trace (Q * W * (Q * Z)) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (Q * W * Q * Z) := by congr 1 <;> noncomm_ring
  change Matrix.trace (Q * (-W *
      centeredSupportPathDerivative Q.transpose C.conjTranspose * W)) = _
  rw [hD]
  have hleft : W * Q * C * C.conjTranspose * W = W * Q * Z := by
    calc
      W * Q * C * C.conjTranspose * W = W * Q *
          ((C * C.conjTranspose) * W) := by noncomm_ring
      _ = W * Q * Z := by rw [hCCW]
  have hmiddle : W * C * Q.transpose * C.conjTranspose * W =
      T * Q.transpose * T.conjTranspose := by
    rw [hTstar]
    unfold T
    noncomm_ring
  have hright : W * C * C.conjTranspose * Q * W = Z * Q * W := by
    calc
      W * C * C.conjTranspose * Q * W =
          (W * (C * C.conjTranspose)) * Q * W := by noncomm_ring
      _ = Z * Q * W := by rw [hWCC]
  have hmatrix :
      -W * (Q * C * C.conjTranspose +
          2 • (C * Q.transpose * C.conjTranspose) +
            C * C.conjTranspose * Q) * W =
        -(W * Q * Z + 2 • (T * Q.transpose * T.conjTranspose) + Z * Q * W) := by
    rw [two_smul, two_smul]
    calc
      -W * (Q * C * C.conjTranspose +
          (C * Q.transpose * C.conjTranspose +
            C * Q.transpose * C.conjTranspose) +
              C * C.conjTranspose * Q) * W =
          -(W * Q * C * C.conjTranspose * W +
            (W * C * Q.transpose * C.conjTranspose * W +
              W * C * Q.transpose * C.conjTranspose * W) +
                W * C * C.conjTranspose * Q * W) := by noncomm_ring
      _ = _ := by rw [hleft, hmiddle, hright]
  rw [hmatrix]
  simp only [Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_add,
    Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul]
  have hcycle' : Matrix.trace (Q * (Z * Q * W)) =
      Matrix.trace (Q * (W * Q * Z)) := by
    simpa only [Matrix.mul_assoc] using hcycle
  rw [two_smul]
  unfold centeredMovedZTwo centeredMovedCornerTwo
  simp only [neg_zero, transposeCongruenceFlow_zero]
  rw [show C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose = Z by rfl]
  rw [show (1 - C * C.conjTranspose)⁻¹ * C = T by rfl]
  have hfirst : Matrix.trace (Q * (W * Q * Z)) =
      Matrix.trace ((Q * 1 + Q * Z) * Q * Z) := by
    rw [hW]
    congr 1
    noncomm_ring
  rw [hcycle', hfirst]
  simp only [Matrix.mul_assoc]
  ring

private theorem iteratedDeriv_two_log_centeredMovedDetTwo
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) (hC : C.IsSymm)
    (hsupport : (1 - C.conjTranspose * C).PosDef) :
    iteratedDeriv 2 (fun t : ℝ ↦ Real.log (centeredMovedDetTwo Q C t)) 0 =
      (-8 * (Matrix.trace (Q * (1 + centeredMovedZTwo Q C 0) * Q *
          centeredMovedZTwo Q C 0) +
        Matrix.trace (Q * ((1 - C * C.conjTranspose)⁻¹ * C) *
          Q.transpose *
            ((1 - C * C.conjTranspose)⁻¹ * C).conjTranspose))).re := by
  let d : ℝ → ℝ := centeredMovedDetTwo Q C
  let a : ℝ → ℝ := fun t ↦
    (Matrix.trace (Q * centeredMovedZOutTwo Q C t)).re
  let S : ℂ := Matrix.trace (Q * (1 + centeredMovedZTwo Q C 0) * Q *
      centeredMovedZTwo Q C 0) +
    Matrix.trace (Q * ((1 - C * C.conjTranspose)⁻¹ * C) * Q.transpose *
      ((1 - C * C.conjTranspose)⁻¹ * C).conjTranspose)
  have hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hsupport.isUnit
  have hd0 : d 0 = (Matrix.det (1 - C.conjTranspose * C)).re := by
    simp [d, centeredMovedDetTwo, centeredMovedCornerTwo]
  have hpos0 : 0 < d 0 := by
    rw [hd0]
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hdAt := hasDerivAt_centeredMovedDetTwo Q C hQ hC 0
    (by simpa [centeredMovedCornerTwo] using hunit)
  have hpos : ∀ᶠ t in nhds 0, 0 < d t :=
    continuousAt_const.eventually_lt hdAt.continuousAt hpos0
  have hderivLog : (fun t ↦ deriv (fun s ↦ Real.log (d s)) t) =ᶠ[nhds 0]
      fun t ↦ 4 * a t := by
    filter_upwards [hpos] with t ht
    let Ct := centeredMovedCornerTwo Q C t
    have hdetNe : Matrix.det (1 - Ct.conjTranspose * Ct) ≠ 0 := by
      intro hz
      have hre : d t = 0 := by
        unfold d centeredMovedDetTwo
        rw [show centeredMovedCornerTwo Q C t = Ct by rfl, hz]
        rfl
      linarith
    have hunitDet : IsUnit (Matrix.det (1 - Ct.conjTranspose * Ct)) :=
      isUnit_iff_ne_zero.mpr hdetNe
    have hdt := hasDerivAt_centeredMovedDetTwo Q C hQ hC t
      (by simpa only [Ct] using hunitDet)
    have hmatrixUnit : IsUnit (1 - Ct.conjTranspose * Ct) :=
      (Matrix.isUnit_iff_isUnit_det _).2 hunitDet
    have hz : centeredMovedZOutTwo Q C t = centeredMovedZTwo Q C t := by
      unfold centeredMovedZOutTwo centeredMovedZTwo
      rw [show centeredMovedCornerTwo Q C t = Ct by rfl]
      exact output_inv_sub_one_eq_input_Z_two Ct hmatrixUnit
    have hlog := hdt.log (ne_of_gt ht)
    rw [hlog.deriv]
    unfold a
    rw [hz]
    calc
      4 * centeredMovedDetTwo Q C t *
            (Matrix.trace (Q * centeredMovedZTwo Q C t)).re /
          centeredMovedDetTwo Q C t =
          centeredMovedDetTwo Q C t *
            (4 * (Matrix.trace (Q * centeredMovedZTwo Q C t)).re) /
              centeredMovedDetTwo Q C t := by ring
      _ = _ := mul_div_cancel_left₀ _ (ne_of_gt ht)
  have haComplex := hasDerivAt_trace_centeredMovedZOutTwo Q C hQ hunit
  rw [trace_centeredMovedZOutTwo_derivative_eq_two Q C hQ hunit] at haComplex
  have ha : HasDerivAt a (-2 * S).re 0 := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 haComplex
    convert hh using 1 <;>
      first
      | rfl
      | (simp only [a, S, Function.comp_apply, Complex.reCLM_apply])
      | exact Subsingleton.elim _ _
  have hrhs : HasDerivAt (fun t ↦ 4 * a t) (4 * (-2 * S).re) 0 :=
    ha.const_mul 4
  have hderivLogAt : HasDerivAt (fun t ↦ deriv (fun s ↦ Real.log (d s)) t)
      (4 * (-2 * S).re) 0 :=
    hrhs.congr_of_eventuallyEq hderivLog
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hderivLogAt.deriv]
  unfold S
  simp [Complex.mul_re]
  ring

/-- Checked raw first logarithmic determinant derivative in the scalar
congruence direction `Q = I`.  It contains no density exponent or
symmetric-coordinate Jacobian. -/
theorem central_log_det_one_raw_checked
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 1
        (fun t : ℝ ↦ Real.log
          (centeredMovedDetTwo (1 : ConcreteMatrixState N)
            (unscaleCOECorner K A) t)) 0 =
      4 * (Matrix.trace (concreteCOEZ K A)).re := by
  let C := unscaleCOECorner K A
  have hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (by simpa only [C] using hsupport.isUnit)
  have hd := hasDerivAt_centeredMovedDetTwo
    (1 : ConcreteMatrixState N) C Matrix.isHermitian_one
      (by simpa only [C] using hsymm) 0
      (by simpa [centeredMovedCornerTwo] using hunit)
  have hd0 : centeredMovedDetTwo (1 : ConcreteMatrixState N) C 0 =
      (Matrix.det (1 - C.conjTranspose * C)).re := by
    simp [centeredMovedDetTwo, centeredMovedCornerTwo]
  have hpos : 0 < centeredMovedDetTwo (1 : ConcreteMatrixState N) C 0 := by
    rw [hd0]
    exact (RCLike.lt_iff_re_im.mp (by simpa only [C] using hsupport.det_pos)).1
  have hlog := hd.log hpos.ne'
  rw [iteratedDeriv_one, hlog.deriv]
  have hz : centeredMovedZTwo (1 : ConcreteMatrixState N) C 0 =
      concreteCOEZ K A := by
    simp [centeredMovedZTwo, centeredMovedCornerTwo, concreteCOEZ, C]
  rw [hz, Matrix.one_mul]
  calc
    4 * centeredMovedDetTwo (1 : ConcreteMatrixState N) C 0 *
          (Matrix.trace (concreteCOEZ K A)).re /
        centeredMovedDetTwo (1 : ConcreteMatrixState N) C 0 =
      centeredMovedDetTwo (1 : ConcreteMatrixState N) C 0 *
          (4 * (Matrix.trace (concreteCOEZ K A)).re) /
        centeredMovedDetTwo (1 : ConcreteMatrixState N) C 0 := by ring
    _ = 4 * (Matrix.trace (concreteCOEZ K A)).re :=
      mul_div_cancel_left₀ _ hpos.ne'

/-- Checked raw second logarithmic determinant derivative in the scalar
congruence direction `Q = I`.  It contains no density exponent or
symmetric-coordinate Jacobian. -/
theorem central_log_det_two_raw_checked
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 2
        (fun t : ℝ ↦ Real.log
          (centeredMovedDetTwo (1 : ConcreteMatrixState N)
            (unscaleCOECorner K A) t)) 0 =
      (-8 * (Matrix.trace
          ((1 + concreteCOEZ K A) * concreteCOEZ K A) +
        Matrix.trace
          (concreteCOET K A * (concreteCOET K A).conjTranspose))).re := by
  have h := iteratedDeriv_two_log_centeredMovedDetTwo
    (1 : ConcreteMatrixState N) (unscaleCOECorner K A)
    Matrix.isHermitian_one hsymm
    (by simpa [coeCornerSupport] using hsupport)
  simpa [centeredMovedZTwo, centeredMovedCornerTwo, concreteCOEZ, concreteCOET]
    using h

/-- Multiplying the raw second logarithmic determinant derivative by the
Friedman--Mello exponent gives exactly the project central second log score.
The only division cancellation uses the stated dense boundary inequality. -/
theorem central_log_det_two_times_exponent_eq_logScoreTwo
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    coeCornerDensityExponent N K *
        iteratedDeriv 2
          (fun t : ℝ ↦ Real.log
            (centeredMovedDetTwo (1 : ConcreteMatrixState N)
              (unscaleCOECorner K A) t)) 0 =
      concreteCentralLogScoreTwo N K A := by
  let c : ℝ := concreteCOEExponent N K
  let Z : ConcreteMatrixState N := concreteCOEZ K A
  let z₁ : ℝ := (Matrix.trace Z).re
  let z₂ : ℝ := (Matrix.trace (Z * Z)).re
  have hcpos : 0 < concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have hKr : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hboundary
    norm_num [Nat.cast_add, Nat.cast_mul] at hKr ⊢
    linarith
  have hc : c ≠ 0 := by simpa only [c] using hcpos.ne'
  have halpha : coeCornerDensityExponent N K = c / 2 := by rfl
  have htraceOne : concreteCOETraceOne N K A = c * z₁ := by
    simp [concreteCOETraceOne, concreteRealTrace, concreteCOEY,
      Matrix.trace_smul, Complex.mul_re, c, z₁, Z]
  have htraceTwo : concreteCOETraceTwo N K A = c ^ 2 * z₂ := by
    unfold concreteCOETraceTwo concreteRealTrace concreteCOEY
    change (Matrix.trace
      ((((c : ℝ) : ℂ) • Z) * (((c : ℝ) : ℂ) • Z))).re = c ^ 2 * z₂
    have hmat :
        (((c : ℝ) : ℂ) • Z) * (((c : ℝ) : ℂ) • Z) =
          ((((c : ℝ) : ℂ) ^ 2) • (Z * Z)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring
    rw [hmat, Matrix.trace_smul]
    norm_num [pow_two, Complex.mul_re, z₂]
  have hraw :
      iteratedDeriv 2
          (fun t : ℝ ↦ Real.log
            (centeredMovedDetTwo (1 : ConcreteMatrixState N)
              (unscaleCOECorner K A) t)) 0 =
        -16 * (z₁ + z₂) := by
    rw [central_log_det_two_raw_checked A hsymm hsupport,
      concreteCOET_mul_conjTranspose_eq_Z_mul_one_add_Z A hsupport]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.trace_add, Complex.add_re]
    norm_num [Complex.mul_re, z₁, z₂, Z]
    ring
  rw [halpha, hraw]
  unfold concreteCentralLogScoreTwo
  rw [htraceOne, htraceTwo]
  change c / 2 * (-16 * (z₁ + z₂)) =
    -8 * (c * z₁ + c ^ 2 * z₂ / c)
  field_simp [hc]
  ring

end MatrixCalculus

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
