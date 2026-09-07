import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ThirdTraceKernelReduction
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-!
# H13 derivative-free `ell_1 ell_3` trace-word ledger

The earlier H13 reduction left the ordinary derivative of
`centeredThirdLogTraceKernel` as its deterministic boundary.  This module
computes that derivative exactly.  The result is a finite trace ledger made
from the two input/output resolvents and their first velocities.  It contains
three copies of the centered projective direction `Q`; multiplication by the
literal first score supplies the fourth copy.

No probability estimate or scientific declaration occurs here.
-/

open Function Matrix
open scoped Matrix Topology ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 2000000

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-! ## Finite matrix calculus instances -/

local instance h13LedgerMatrixNormedAddCommGroup {N : ℕ} :
    NormedAddCommGroup (ConcreteMatrixState N) :=
  Matrix.linftyOpNormedAddCommGroup

local instance h13LedgerMatrixNormedRing {N : ℕ} :
    NormedRing (ConcreteMatrixState N) :=
  { Matrix.linftyOpNormedRing with
    toAddCommGroup := h13LedgerMatrixNormedAddCommGroup.toAddCommGroup }

local instance h13LedgerMatrixComplexNormedSpace {N : ℕ} :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h13LedgerMatrixRealNormedSpace {N : ℕ} :
    NormedSpace ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h13LedgerMatrixAddCommGroup {N : ℕ} :
    AddCommGroup (ConcreteMatrixState N) :=
  h13LedgerMatrixNormedAddCommGroup.toAddCommGroup

local instance h13LedgerMatrixComplexModule {N : ℕ} :
    Module ℂ (ConcreteMatrixState N) :=
  h13LedgerMatrixComplexNormedSpace.toModule

local instance h13LedgerMatrixRealModule {N : ℕ} :
    Module ℝ (ConcreteMatrixState N) :=
  h13LedgerMatrixRealNormedSpace.toModule

local instance h13LedgerMatrixPseudoMetricSpace {N : ℕ} :
    PseudoMetricSpace (ConcreteMatrixState N) :=
  h13LedgerMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance h13LedgerMatrixUniformSpace {N : ℕ} :
    UniformSpace (ConcreteMatrixState N) :=
  h13LedgerMatrixPseudoMetricSpace.toUniformSpace

local instance h13LedgerMatrixTopologicalSpace {N : ℕ} :
    TopologicalSpace (ConcreteMatrixState N) :=
  h13LedgerMatrixUniformSpace.toTopologicalSpace

local instance h13LedgerMatrixComplexNormedAlgebra {N : ℕ} :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

local instance h13LedgerMatrixRealNormedAlgebra {N : ℕ} :
    NormedAlgebra ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

private def h13LedgerTraceCLM (N : ℕ) :
    ConcreteMatrixState N →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (Fin N) ℝ ℂ).toContinuousLinearMap

@[simp] private theorem h13LedgerTraceCLM_apply {N : ℕ}
    (M : ConcreteMatrixState N) :
    h13LedgerTraceCLM N M = Matrix.trace M := rfl

/-! ## The derivative-free ledger -/

/-- Velocity of `C_t = exp(-tQ) C exp(-tQ^T)` at zero. -/
def h13LedgerCornerVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  -(Q * C + C * Q.transpose)

/-- Velocity of `C_t^*` at zero, written without a derivative. -/
def h13LedgerCornerStarVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  -(Q.transpose * C.conjTranspose + C.conjTranspose * Q)

/-- Input gap `I-C^*C`. -/
def h13LedgerInputGap {N : ℕ}
    (C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  1 - C.conjTranspose * C

/-- Output gap `I-CC^*`. -/
def h13LedgerOutputGap {N : ℕ}
    (C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  1 - C * C.conjTranspose

/-- Velocity of the input gap. -/
def h13LedgerInputGapVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  -(h13LedgerCornerStarVelocity Q C * C +
    C.conjTranspose * h13LedgerCornerVelocity Q C)

/-- Velocity of the output gap. -/
def h13LedgerOutputGapVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  -(h13LedgerCornerVelocity Q C * C.conjTranspose +
    C * h13LedgerCornerStarVelocity Q C)

/-- Velocity of the input resolvent `(I-C^*C)^{-1}`. -/
def h13LedgerInputResolventVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  -(h13LedgerInputGap C)⁻¹ * h13LedgerInputGapVelocity Q C *
    (h13LedgerInputGap C)⁻¹

/-- Velocity of the output resolvent `(I-CC^*)^{-1}`. -/
def h13LedgerOutputResolventVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  -(h13LedgerOutputGap C)⁻¹ * h13LedgerOutputGapVelocity Q C *
    (h13LedgerOutputGap C)⁻¹

/-- Input-side beta-prime resolvent `Z=C(I-C^*C)^{-1}C^*`. -/
def h13LedgerZ {N : ℕ} (C : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  C * (h13LedgerInputGap C)⁻¹ * C.conjTranspose

/-- Output-side factor `T=(I-CC^*)^{-1}C`. -/
def h13LedgerT {N : ℕ} (C : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  (h13LedgerOutputGap C)⁻¹ * C

/-- Exact velocity of `Z`. -/
def h13LedgerZVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  h13LedgerCornerVelocity Q C * (h13LedgerInputGap C)⁻¹ * C.conjTranspose +
    C * h13LedgerInputResolventVelocity Q C * C.conjTranspose +
    C * (h13LedgerInputGap C)⁻¹ * h13LedgerCornerStarVelocity Q C

/-- Exact velocity of `T`. -/
def h13LedgerTVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  h13LedgerOutputResolventVelocity Q C * C +
    (h13LedgerOutputGap C)⁻¹ * h13LedgerCornerVelocity Q C

/-- Exact velocity of `T^*`. -/
def h13LedgerTStarVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  h13LedgerCornerStarVelocity Q C * (h13LedgerOutputGap C)⁻¹ +
    C.conjTranspose * h13LedgerOutputResolventVelocity Q C

/-- The cubic trace-word ledger obtained by differentiating the third-score
kernel.  Each of its four displayed terms is cubic in `Q`. -/
def h13ThirdTraceKernelVelocity {N : ℕ}
    (Q C : ConcreteMatrixState N) : ℂ :=
  Matrix.trace
      (Q * h13LedgerZVelocity Q C * Q * h13LedgerZ C) +
    Matrix.trace
      (Q * (1 + h13LedgerZ C) * Q * h13LedgerZVelocity Q C) +
    Matrix.trace
      (Q * h13LedgerTVelocity Q C * Q.transpose *
        (h13LedgerT C).conjTranspose) +
    Matrix.trace
      (Q * h13LedgerT C * Q.transpose * h13LedgerTStarVelocity Q C)

/-- The derivative-free scalar ledger for the literal product
`ell_1 ell_3`, before its deterministic coefficient is restored. -/
def h13OneThreeTraceWordLedger {N : ℕ}
    (Q C Y : ConcreteMatrixState N) : ℝ :=
  (Matrix.trace (Q * Y)).re * (h13ThirdTraceKernelVelocity Q C).re

/-! ## Matrix-path differentiation -/

private theorem h13_hasDerivAt_nonsingInv_of_hasDerivAt
    {N : ℕ} {F : ℝ → ConcreteMatrixState N}
    {x : ℝ} {F' : ConcreteMatrixState N}
    (hF : HasDerivAt F F' x) (hunit : IsUnit (F x)) :
    HasDerivAt (fun s : ℝ => (F s)⁻¹)
      (-((F x)⁻¹ * F' * (F x)⁻¹)) x := by
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit
  have hcomp := hinv.comp_hasDerivAt x hF
  have hinvEq : (F x)⁻¹ =
      (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := by
    calc
      (F x)⁻¹ = Ring.inverse (F x) := nonsing_inv_eq_ringInverse _
      _ = Ring.inverse (hunit.unit : ConcreteMatrixState N) :=
        congrArg Ring.inverse hunit.unit_spec.symm
      _ = (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := Ring.inverse_unit _
  convert hcomp using 1 <;> try rfl
  · funext s
    simp only [Function.comp_apply, nonsing_inv_eq_ringInverse]
  · simp only [ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply]
    rw [hinvEq]

private def h13MovedCorner {N : ℕ}
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  transposeCongruenceFlow Q (-t) C

private def h13MovedCornerStar {N : ℕ}
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  (h13MovedCorner Q C t).conjTranspose

private def h13MovedInputGap {N : ℕ}
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  1 - h13MovedCornerStar Q C t * h13MovedCorner Q C t

private def h13MovedOutputGap {N : ℕ}
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  1 - h13MovedCorner Q C t * h13MovedCornerStar Q C t

private def h13MovedZ {N : ℕ}
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  h13MovedCorner Q C t * (h13MovedInputGap Q C t)⁻¹ *
    h13MovedCornerStar Q C t

private def h13MovedT {N : ℕ}
    (Q C : ConcreteMatrixState N) (t : ℝ) : ConcreteMatrixState N :=
  (h13MovedOutputGap Q C t)⁻¹ * h13MovedCorner Q C t

@[simp] private theorem h13MovedCorner_zero {N : ℕ}
    (Q C : ConcreteMatrixState N) : h13MovedCorner Q C 0 = C := by
  simp [h13MovedCorner]

@[simp] private theorem h13MovedCornerStar_zero {N : ℕ}
    (Q C : ConcreteMatrixState N) : h13MovedCornerStar Q C 0 = C.conjTranspose := by
  simp [h13MovedCornerStar]

@[simp] private theorem h13MovedInputGap_zero {N : ℕ}
    (Q C : ConcreteMatrixState N) :
    h13MovedInputGap Q C 0 = h13LedgerInputGap C := by
  simp [h13MovedInputGap, h13LedgerInputGap]

@[simp] private theorem h13MovedOutputGap_zero {N : ℕ}
    (Q C : ConcreteMatrixState N) :
    h13MovedOutputGap Q C 0 = h13LedgerOutputGap C := by
  simp [h13MovedOutputGap, h13LedgerOutputGap]

@[simp] private theorem h13MovedZ_zero {N : ℕ}
    (Q C : ConcreteMatrixState N) : h13MovedZ Q C 0 = h13LedgerZ C := by
  simp [h13MovedZ, h13LedgerZ]

@[simp] private theorem h13MovedT_zero {N : ℕ}
    (Q C : ConcreteMatrixState N) : h13MovedT Q C 0 = h13LedgerT C := by
  simp [h13MovedT, h13LedgerT]

private theorem hasDerivAt_h13MovedCorner
    {N : ℕ} (Q C : ConcreteMatrixState N) :
    HasDerivAt (h13MovedCorner Q C)
      (h13LedgerCornerVelocity Q C) 0 := by
  let L : ConcreteMatrixState N := -Q
  let R : ConcreteMatrixState N := -Q.transpose
  have hL := hasDerivAt_exp_smul_const L (0 : ℝ)
  have hR := hasDerivAt_exp_smul_const R (0 : ℝ)
  have hprod := (hL.mul_const C).mul hR
  convert hprod using 1 <;> try rfl
  · funext t
    rw [h13MovedCorner, transposeCongruenceFlow_eq]
    simp only [L, R, neg_smul, Complex.ofReal_neg, Pi.mul_apply]
    have hleft : t • (-Q) = ((t : ℂ)) • (-Q) :=
      RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
    have hright : t • (-Q.transpose) = ((t : ℂ)) • (-Q.transpose) :=
      RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
    rw [hleft, hright]
    have hleftArg : -(((t : ℂ)) • Q) = ((t : ℂ)) • (-Q) := by module
    have hrightArg : -(((t : ℂ)) • Q.transpose) =
        ((t : ℂ)) • (-Q.transpose) := by module
    rw [hleftArg, hrightArg]
    rfl
  · simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul,
      Matrix.mul_one, L, R, h13LedgerCornerVelocity]
    noncomm_ring

private theorem h13MovedCornerStar_eq_expansion
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) :
    h13MovedCornerStar Q C = fun t : ℝ =>
      NormedSpace.exp (((t : ℂ)) • (-Q.transpose)) * C.conjTranspose *
        NormedSpace.exp (((t : ℂ)) • (-Q)) := by
  funext t
  unfold h13MovedCornerStar h13MovedCorner
  rw [transposeCongruenceFlow_eq, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul]
  simp only [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, map_neg]
  rw [hQ.eq, hQ.transpose.eq]
  simp only [Matrix.transpose_transpose, neg_smul, Complex.ofReal_neg]
  have hleftArg : -(((t : ℂ)) • Q.transpose) =
      ((t : ℂ)) • (-Q.transpose) := by module
  have hrightArg : -(((t : ℂ)) • Q) = ((t : ℂ)) • (-Q) := by module
  rw [hleftArg, hrightArg]
  noncomm_ring

private theorem hasDerivAt_h13MovedCornerStar
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) :
    HasDerivAt (h13MovedCornerStar Q C)
      (h13LedgerCornerStarVelocity Q C) 0 := by
  let L : ConcreteMatrixState N := -Q.transpose
  let R : ConcreteMatrixState N := -Q
  have hL := hasDerivAt_exp_smul_const L (0 : ℝ)
  have hR := hasDerivAt_exp_smul_const R (0 : ℝ)
  have hprod := (hL.mul_const C.conjTranspose).mul hR
  rw [h13MovedCornerStar_eq_expansion Q C hQ]
  convert hprod using 1 <;> try rfl
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul,
    Matrix.mul_one, L, R, h13LedgerCornerStarVelocity]
  noncomm_ring

private theorem hasDerivAt_h13MovedInputGap
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) :
    HasDerivAt (h13MovedInputGap Q C)
      (h13LedgerInputGapVelocity Q C) 0 := by
  have hc := hasDerivAt_h13MovedCorner Q C
  have hcs := hasDerivAt_h13MovedCornerStar Q C hQ
  have hprod := hcs.mul hc
  have hsub := (hasDerivAt_const (x := (0 : ℝ))
    (c := (1 : ConcreteMatrixState N))).sub hprod
  convert hsub using 1 <;> try rfl
  simp [h13MovedCorner, h13MovedCornerStar, h13MovedInputGap,
    h13LedgerInputGapVelocity]

private theorem hasDerivAt_h13MovedOutputGap
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) :
    HasDerivAt (h13MovedOutputGap Q C)
      (h13LedgerOutputGapVelocity Q C) 0 := by
  have hc := hasDerivAt_h13MovedCorner Q C
  have hcs := hasDerivAt_h13MovedCornerStar Q C hQ
  have hprod := hc.mul hcs
  have hsub := (hasDerivAt_const (x := (0 : ℝ))
    (c := (1 : ConcreteMatrixState N))).sub hprod
  convert hsub using 1 <;> try rfl
  simp [h13MovedCorner, h13MovedCornerStar, h13MovedOutputGap,
    h13LedgerOutputGapVelocity]

private theorem hasDerivAt_h13MovedInputResolvent
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (h13LedgerInputGap C)) :
    HasDerivAt (fun t : ℝ => (h13MovedInputGap Q C t)⁻¹)
      (h13LedgerInputResolventVelocity Q C) 0 := by
  have hgap := hasDerivAt_h13MovedInputGap Q C hQ
  have hzero : h13MovedInputGap Q C 0 = h13LedgerInputGap C := by
    simp [h13MovedInputGap, h13MovedCorner, h13MovedCornerStar,
      h13LedgerInputGap]
  have hinv := h13_hasDerivAt_nonsingInv_of_hasDerivAt hgap
    (by simpa only [hzero] using hunit)
  rw [hzero] at hinv
  convert hinv using 1 <;> try rfl
  unfold h13LedgerInputResolventVelocity
  noncomm_ring

private theorem hasDerivAt_h13MovedOutputResolvent
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (h13LedgerOutputGap C)) :
    HasDerivAt (fun t : ℝ => (h13MovedOutputGap Q C t)⁻¹)
      (h13LedgerOutputResolventVelocity Q C) 0 := by
  have hgap := hasDerivAt_h13MovedOutputGap Q C hQ
  have hzero : h13MovedOutputGap Q C 0 = h13LedgerOutputGap C := by
    simp [h13MovedOutputGap, h13MovedCorner, h13MovedCornerStar,
      h13LedgerOutputGap]
  have hinv := h13_hasDerivAt_nonsingInv_of_hasDerivAt hgap
    (by simpa only [hzero] using hunit)
  rw [hzero] at hinv
  convert hinv using 1 <;> try rfl
  unfold h13LedgerOutputResolventVelocity
  noncomm_ring

private theorem hasDerivAt_h13MovedZ
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (h13LedgerInputGap C)) :
    HasDerivAt (h13MovedZ Q C) (h13LedgerZVelocity Q C) 0 := by
  have hc := hasDerivAt_h13MovedCorner Q C
  have hcs := hasDerivAt_h13MovedCornerStar Q C hQ
  have hV := hasDerivAt_h13MovedInputResolvent Q C hQ hunit
  have hprod := (hc.mul hV).mul hcs
  convert hprod using 1 <;> try rfl
  simp only [h13LedgerZVelocity, h13MovedCorner_zero,
    h13MovedCornerStar_zero, h13MovedInputGap_zero, Pi.mul_apply]
  noncomm_ring

private theorem hasDerivAt_h13MovedT
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (h13LedgerOutputGap C)) :
    HasDerivAt (h13MovedT Q C) (h13LedgerTVelocity Q C) 0 := by
  have hc := hasDerivAt_h13MovedCorner Q C
  have hW := hasDerivAt_h13MovedOutputResolvent Q C hQ hunit
  have hprod := hW.mul hc
  convert hprod using 1 <;> try rfl
  simp only [h13LedgerTVelocity, h13MovedCorner_zero,
    h13MovedCornerStar_zero, h13MovedOutputGap_zero, Pi.mul_apply]

private theorem h13MovedT_conjTranspose_eq
    {N : ℕ} (Q C : ConcreteMatrixState N) :
    (fun t : ℝ => (h13MovedT Q C t).conjTranspose) =
      fun t => h13MovedCornerStar Q C t *
        (h13MovedOutputGap Q C t)⁻¹ := by
  funext t
  unfold h13MovedT
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  have hHerm : (h13MovedOutputGap Q C t).IsHermitian := by
    unfold h13MovedOutputGap h13MovedCornerStar
    exact Matrix.isHermitian_one.sub
      (Matrix.isHermitian_mul_conjTranspose_self (h13MovedCorner Q C t))
  rw [hHerm.eq]
  rfl

private theorem hasDerivAt_h13MovedTStar
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hunit : IsUnit (h13LedgerOutputGap C)) :
    HasDerivAt (fun t : ℝ => (h13MovedT Q C t).conjTranspose)
      (h13LedgerTStarVelocity Q C) 0 := by
  have hcs := hasDerivAt_h13MovedCornerStar Q C hQ
  have hW := hasDerivAt_h13MovedOutputResolvent Q C hQ hunit
  have hprod := hcs.mul hW
  rw [h13MovedT_conjTranspose_eq Q C]
  convert hprod using 1 <;> try rfl
  simp only [h13LedgerTStarVelocity, h13MovedCornerStar_zero,
    h13MovedOutputGap_zero]

/-! ## Exact kernel and score identities -/

/-- Exact derivative of the third-log trace kernel at the origin. -/
theorem hasDerivAt_centeredThirdLogTraceKernel_h13_internal
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hinput : IsUnit (h13LedgerInputGap C))
    (houtput : IsUnit (h13LedgerOutputGap C)) :
    HasDerivAt (centeredThirdLogTraceKernel Q C)
      (h13ThirdTraceKernelVelocity Q C) 0 := by
  have hZ := hasDerivAt_h13MovedZ Q C hQ hinput
  have hT := hasDerivAt_h13MovedT Q C hQ houtput
  have hTs := hasDerivAt_h13MovedTStar Q C hQ houtput
  have hOneZ := (hasDerivAt_const (x := (0 : ℝ))
    (c := (1 : ConcreteMatrixState N))).add hZ
  have hQconst := hasDerivAt_const (x := (0 : ℝ)) (c := Q)
  have hQtconst := hasDerivAt_const (x := (0 : ℝ)) (c := Q.transpose)
  have hfirstMat := (((hQconst.mul hOneZ).mul hQconst).mul hZ)
  have hsecondMat := (((hQconst.mul hT).mul hQtconst).mul hTs)
  have hfirst := (h13LedgerTraceCLM N).hasFDerivAt.comp_hasDerivAt 0 hfirstMat
  have hsecond := (h13LedgerTraceCLM N).hasFDerivAt.comp_hasDerivAt 0 hsecondMat
  have hsum := hfirst.add hsecond
  convert hsum using 1 <;> try rfl
  simp only [h13LedgerTraceCLM_apply, h13MovedZ_zero, h13MovedT_zero,
    h13LedgerZ, h13LedgerT, h13ThirdTraceKernelVelocity, Pi.mul_apply,
    Pi.add_apply, zero_mul, zero_add, add_zero, Matrix.zero_mul,
    Matrix.mul_zero]
  simp_rw [Matrix.trace_add]
  ring

/-- The remaining ordinary derivative in the old H13 reduction is exactly
the real part of the derivative-free trace ledger. -/
theorem deriv_centeredThirdLogTraceKernel_h13_internal
    {N : ℕ} (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian)
    (hinput : IsUnit (h13LedgerInputGap C))
    (houtput : IsUnit (h13LedgerOutputGap C)) :
    deriv (fun t : ℝ => -8 * (centeredThirdLogTraceKernel Q C t).re) 0 =
      -8 * (h13ThirdTraceKernelVelocity Q C).re := by
  have hkernel := hasDerivAt_centeredThirdLogTraceKernel_h13_internal
    Q C hQ hinput houtput
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hkernel
  exact (hre.const_mul (-8)).deriv

/-- On the literal COE support, the third centered logarithmic score is the
explicit derivative-free cubic trace ledger. -/
theorem concreteCenteredEll_three_eq_traceWordLedger_h13_internal
    {N K : ℕ} (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 3 N K (A, v) =
      -8 * coeCornerDensityExponent N K *
        (h13ThirdTraceKernelVelocity
          (concreteCenteredOrbitalDirection N v)
          (unscaleCOECorner K A)).re := by
  let Q := concreteCenteredOrbitalDirection N v
  let C := unscaleCOECorner K A
  have hQ : Q.IsHermitian := concreteCenteredOrbitalDirection_isHermitian v
  have hinput : IsUnit (h13LedgerInputGap C) := by
    unfold h13LedgerInputGap
    exact hsupport.isUnit
  have hinputDet : IsUnit (Matrix.det (h13LedgerInputGap C)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hinput
  have houtputDet : IsUnit (Matrix.det (h13LedgerOutputGap C)) := by
    unfold h13LedgerOutputGap
    rw [Matrix.det_one_sub_mul_comm]
    unfold h13LedgerInputGap at hinputDet
    exact hinputDet
  have houtput : IsUnit (h13LedgerOutputGap C) :=
    (Matrix.isUnit_iff_isUnit_det _).2 houtputDet
  unfold concreteCenteredEll
  rw [concreteCenteredLogScore_three_eq_traceKernel_deriv v A hsymm hsupport]
  rw [deriv_centeredThirdLogTraceKernel_h13_internal Q C hQ hinput houtput]
  ring

/-- Exact derivative-free formula for the literal H13 product. -/
theorem concreteCenteredEll_one_mul_three_eq_traceWordLedger_h13_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v) =
      -8 * concreteCOEExponent N K *
        h13OneThreeTraceWordLedger
          (concreteCenteredOrbitalDirection N v)
          (unscaleCOECorner K A) (concreteCOEY N K A) := by
  rw [concreteCenteredEll_one_eq_firstDensityScore_h13_internal
    hN hgap A v hsymm hsupport]
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
  rw [← trace_concreteCenteredOrbitalDirection_mul]
  norm_num [Complex.mul_re]
  rw [concreteCenteredEll_three_eq_traceWordLedger_h13_internal
    A v hsymm hsupport]
  unfold h13OneThreeTraceWordLedger
  unfold concreteCOEExponent coeCornerDensityExponent
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
