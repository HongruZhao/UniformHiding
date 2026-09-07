import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7_Proof
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp

/-!
# Local smoothness of the explicit H7/H16 likelihood

This module proves the local calculus facts needed by the cubic differential
construction without changing the exact witness type or adding any scientific
input.
-/

open Function
open scoped Matrix Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

local instance h7MatrixNormedRing {N : ℕ} :
    NormedRing (ConcreteMatrixState N) := Matrix.linftyOpNormedRing

local instance h7MatrixNormedSpace {N : ℕ} :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h7MatrixNormedAlgebra {N : ℕ} :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

private def h7CoordinatesToMatrixCLM (N : ℕ) :
    ConcreteMatrixRealCoordinates N →L[ℝ] ConcreteMatrixState N :=
  (concreteMatrixRealCoordinatesLinearEquiv N).symm.toContinuousLinearEquiv.toContinuousLinearMap

private def h7MatrixTraceCLM (N : ℕ) :
    ConcreteMatrixState N →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (Fin N) ℝ ℂ).toContinuousLinearMap

private def h7MatrixEntryLinearMapReal (N : ℕ) (i j : Fin N) :
    ConcreteMatrixState N →ₗ[ℝ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def h7MatrixEntryCLM (N : ℕ) (i j : Fin N) :
    ConcreteMatrixState N →L[ℝ] ℂ :=
  (h7MatrixEntryLinearMapReal N i j).toContinuousLinearMap

private def h7MatrixTransposeCLM (N : ℕ) :
    ConcreteMatrixState N →L[ℝ] ConcreteMatrixState N :=
  (Matrix.transposeLinearEquiv (Fin N) (Fin N) ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

private def h7MatrixConjTransposeLinearMapReal (N : ℕ) :
    ConcreteMatrixState N →ₗ[ℝ] ConcreteMatrixState N where
  toFun M := M.conjTranspose
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' c A := by
    simpa using (Matrix.conjTranspose_smul c A)

private def h7MatrixConjTransposeCLM (N : ℕ) :
    ConcreteMatrixState N →L[ℝ] ConcreteMatrixState N :=
  (h7MatrixConjTransposeLinearMapReal N).toContinuousLinearMap

/-- Matrix determinant is real-smooth; this is the finite Leibniz polynomial
written explicitly for the calculus engine. -/
private theorem contDiff_matrixDet_real (N : ℕ) :
    ContDiff ℝ ⊤
      (fun M : Matrix (Fin N) (Fin N) ℂ ↦ Matrix.det M) := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  exact contDiff_const.mul <| contDiff_prod fun i _ ↦
    (h7MatrixEntryCLM N (σ i) i).contDiff

/-- On a supported state, the explicit coordinate likelihood is smooth at the
zero direction. -/
theorem h16CoordinateLikelihoodCore_contDiffAt_top
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ContDiffAt ℝ ⊤ (h16CoordinateLikelihoodCore K A) 0 := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  unfold h16CoordinateLikelihoodCore h16GeneralCOELikelihoodCore
  simp only [if_neg hbase]
  apply ContDiffAt.mul
  · have htraceC : ContDiffAt ℝ ⊤
        (fun x : ConcreteMatrixRealCoordinates N ↦
          Matrix.trace (concreteMatrixOfRealCoordinates x)) 0 := by
      change ContDiffAt ℝ ⊤
        ((h7MatrixTraceCLM N) ∘ (h7CoordinatesToMatrixCLM N)) 0
      exact (h7MatrixTraceCLM N).contDiff.contDiffAt.comp 0
        (h7CoordinatesToMatrixCLM N).contDiff.contDiffAt
    have htraceRe : ContDiffAt ℝ ⊤
        (fun x : ConcreteMatrixRealCoordinates N ↦
          (Matrix.trace (concreteMatrixOfRealCoordinates x)).re) 0 := by
      simpa [Function.comp_def, Complex.reCLM_apply] using
        Complex.reCLM.contDiff.contDiffAt.comp 0 htraceC
    simpa [smul_eq_mul, mul_assoc] using
      (htraceRe.const_smul (-2 * ((N : ℝ) + 1))).exp
  · apply ContDiffAt.rpow_const_of_ne
    · have hinverseC : ContDiffAt ℝ ⊤
          (fun x : ConcreteMatrixRealCoordinates N ↦
            let C := unscaleCOECorner K A
            let CH := transposeCongruenceFlow
              (concreteMatrixOfRealCoordinates x) (-1 : ℝ) C
            Matrix.det (1 - CH.conjTranspose * CH)) 0 := by
        apply (contDiff_matrixDet_real N).contDiffAt.comp 0
        have hcoords : ContDiffAt ℝ ⊤
            (concreteMatrixOfRealCoordinates :
              ConcreteMatrixRealCoordinates N → ConcreteMatrixState N) 0 := by
          change ContDiffAt ℝ ⊤ (h7CoordinatesToMatrixCLM N) 0
          exact (h7CoordinatesToMatrixCLM N).contDiff.contDiffAt
        have htranspose : ContDiffAt ℝ ⊤
            (fun x : ConcreteMatrixRealCoordinates N ↦
              (concreteMatrixOfRealCoordinates x).transpose) 0 := by
          change ContDiffAt ℝ ⊤
            ((h7MatrixTransposeCLM N) ∘ (h7CoordinatesToMatrixCLM N)) 0
          exact (h7MatrixTransposeCLM N).contDiff.contDiffAt.comp 0 hcoords
        have hleft : ContDiffAt ℝ ⊤
            (fun x : ConcreteMatrixRealCoordinates N ↦
              NormedSpace.exp (((-1 : ℝ) : ℂ) •
                concreteMatrixOfRealCoordinates x)) 0 := by
          have harg : ContDiffAt ℝ ⊤
              (fun x : ConcreteMatrixRealCoordinates N ↦
                (-1 : ℝ) • concreteMatrixOfRealCoordinates x) 0 :=
            hcoords.const_smul (-1 : ℝ)
          have hexp := ((NormedSpace.exp_analytic
              (𝕂 := ℂ) (𝔸 := ConcreteMatrixState N)
              ((-1 : ℝ) • concreteMatrixOfRealCoordinates
                (0 : ConcreteMatrixRealCoordinates N))).contDiffAt.restrict_scalars ℝ).comp
              0 harg
          convert hexp using 1
          funext x
          rfl
        have hright : ContDiffAt ℝ ⊤
            (fun x : ConcreteMatrixRealCoordinates N ↦
              NormedSpace.exp (((-1 : ℝ) : ℂ) •
                (concreteMatrixOfRealCoordinates x).transpose)) 0 := by
          have harg : ContDiffAt ℝ ⊤
              (fun x : ConcreteMatrixRealCoordinates N ↦
                (-1 : ℝ) • (concreteMatrixOfRealCoordinates x).transpose) 0 :=
            htranspose.const_smul (-1 : ℝ)
          have hexp := ((NormedSpace.exp_analytic
              (𝕂 := ℂ) (𝔸 := ConcreteMatrixState N)
              ((-1 : ℝ) • (concreteMatrixOfRealCoordinates
                (0 : ConcreteMatrixRealCoordinates N)).transpose)).contDiffAt.restrict_scalars ℝ).comp
              0 harg
          convert hexp using 1
          funext x
          rfl
        have hcorner : ContDiffAt ℝ ⊤
            (fun x : ConcreteMatrixRealCoordinates N ↦
              transposeCongruenceFlow (concreteMatrixOfRealCoordinates x)
                (-1 : ℝ) (unscaleCOECorner K A)) 0 := by
          rw [show (fun x : ConcreteMatrixRealCoordinates N ↦
              transposeCongruenceFlow (concreteMatrixOfRealCoordinates x)
                (-1 : ℝ) (unscaleCOECorner K A)) =
              (fun x ↦ NormedSpace.exp (((-1 : ℝ) : ℂ) •
                  concreteMatrixOfRealCoordinates x) * unscaleCOECorner K A *
                NormedSpace.exp (((-1 : ℝ) : ℂ) •
                  (concreteMatrixOfRealCoordinates x).transpose)) by
            funext x
            exact transposeCongruenceFlow_eq _ _ _]
          exact (hleft.mul contDiffAt_const).mul hright
        have hcornerStar : ContDiffAt ℝ ⊤
            (fun x : ConcreteMatrixRealCoordinates N ↦
              (transposeCongruenceFlow (concreteMatrixOfRealCoordinates x)
                (-1 : ℝ) (unscaleCOECorner K A)).conjTranspose) 0 := by
          change ContDiffAt ℝ ⊤ ((h7MatrixConjTransposeCLM N) ∘
            (fun x : ConcreteMatrixRealCoordinates N ↦
              transposeCongruenceFlow (concreteMatrixOfRealCoordinates x)
                (-1 : ℝ) (unscaleCOECorner K A))) 0
          exact (h7MatrixConjTransposeCLM N).contDiff.contDiffAt.comp 0 hcorner
        exact contDiffAt_const.sub (hcornerStar.mul hcorner)
      have hinverseRe : ContDiffAt ℝ ⊤
          (fun x : ConcreteMatrixRealCoordinates N ↦
            h16GeneralCOEInverseDeterminant K
              (concreteMatrixOfRealCoordinates x) A) 0 := by
        unfold h16GeneralCOEInverseDeterminant
        simpa [Function.comp_def, Complex.reCLM_apply] using
          Complex.reCLM.contDiff.contDiffAt.comp 0 hinverseC
      exact hinverseRe.div_const _
    · have hinverse0 :
          h16GeneralCOEInverseDeterminant K
              (concreteMatrixOfRealCoordinates (0 : ConcreteMatrixRealCoordinates N)) A =
            concreteCOEBaseDeterminant K A := by
        have hcoords0 :
            concreteMatrixOfRealCoordinates
                (0 : ConcreteMatrixRealCoordinates N) = 0 := by
          ext i j
          apply Complex.ext <;> simp [concreteMatrixOfRealCoordinates]
        rw [hcoords0]
        simp [h16GeneralCOEInverseDeterminant, concreteCOEBaseDeterminant,
          transposeCongruenceFlow, transposeCongruence]
      simpa only [hinverse0, div_self hbase] using (one_ne_zero : (1 : ℝ) ≠ 0)

/-- A local `C^3` hypothesis at the base point suffices for the diagonal
line-restriction identity.  This is the local counterpart of
`h16_iteratedDeriv_linear_restriction_three`, whose Mathlib chain rule is
stated using global `ContDiff`. -/
theorem iteratedDeriv_line_eq_iteratedFDeriv_diag_of_contDiffAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (hf : ContDiffAt ℝ 3 f 0) (x : V) :
    iteratedDeriv 3 (fun t : ℝ => f (t • x)) 0 =
      iteratedFDeriv ℝ 3 f 0 ![x, x, x] := by
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  have hline : (fun t : ℝ => f (t • x)) = f ∘ L := by
    funext t
    simp [L]
  rcases hf.contDiffOn' le_rfl (by norm_num) with ⟨s, hs_open, h0s, hfs⟩
  have hfs' : ContDiffOn ℝ 3 f s := by
    simpa using hfs
  have hpre_open : IsOpen (L ⁻¹' s) := hs_open.preimage L.continuous
  have h0pre : (0 : ℝ) ∈ L ⁻¹' s := by
    simpa [L] using h0s
  have hcompAt : ContDiffAt ℝ 3 (f ∘ L) 0 := by
    have hfL0 : ContDiffAt ℝ 3 f (L (0 : ℝ)) := by
      simpa [L] using hf
    exact hfL0.comp (0 : ℝ) L.contDiff.contDiffAt
  rw [hline,
    ← iteratedDerivWithin_eq_iteratedDeriv hpre_open.uniqueDiffOn hcompAt h0pre,
    iteratedDerivWithin_eq_iteratedFDerivWithin,
    L.iteratedFDerivWithin_comp_right hfs' hs_open.uniqueDiffOn
      hpre_open.uniqueDiffOn h0pre (by norm_num)]
  simp only [map_zero]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs_open.uniqueDiffOn hf h0s]
  have hdiag : (fun _ : Fin 3 => x) = ![x, x, x] := by
    funext i
    fin_cases i <;> rfl
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, hdiag]

/-- The supported literal H7 likelihood therefore has its third Frechet
diagonal identified with the ordinary third derivative along every real
matrix-coordinate line. -/
theorem h16CoordinateCubicValue_diagonal_eq_iteratedDeriv_local
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (x : ConcreteMatrixRealCoordinates N) :
    h16CoordinateCubicValue K A x x x =
      iteratedDeriv 3
        (fun t : ℝ => h16CoordinateLikelihoodCore K A (t • x)) 0 := by
  rw [h16CoordinateCubicValue_diagonal]
  exact (iteratedDeriv_line_eq_iteratedFDeriv_diag_of_contDiffAt
    (h16CoordinateLikelihoodCore K A)
    ((h16CoordinateLikelihoodCore_contDiffAt_top A hsupport).of_le (by norm_num)) x).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
