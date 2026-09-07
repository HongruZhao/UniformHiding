import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralTraceDerivative
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreTwoDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCOERawExternal
import Mathlib.Tactic
import Mathlib.Tactic.FunProp

/-!
# Exact central-shift cocycle for the literal H7 likelihood

This module contains the deterministic algebra behind the mixed H7 field.
Inverse central congruence sends `A` to `exp (-2s) A`; for `s >= 0` this
preserves the open matrix-ball support.  A further arbitrary coordinate
perturbation then factors from the literal determinant likelihood by the
central likelihood multiplier.  No cubic witness or mixed identity is used.
-/

open Function Matrix
open scoped Matrix Topology ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

local instance h7ShiftMatrixNormedRing {N : ℕ} :
    NormedRing (ConcreteMatrixState N) := Matrix.linftyOpNormedRing

local instance h7ShiftMatrixNormedSpace {N : ℕ} :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h7ShiftMatrixNormedAlgebra {N : ℕ} :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

private def h7ShiftCoordinatesToMatrixCLM (N : ℕ) :
    ConcreteMatrixRealCoordinates N →L[ℝ] ConcreteMatrixState N :=
  (concreteMatrixRealCoordinatesLinearEquiv N).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem h7_posDef_real_smul
    {N : ℕ} {M : ConcreteMatrixState N} (hM : M.PosDef)
    {a : ℝ} (ha : 0 < a) : (a • M).PosDef := by
  refine ⟨(hM.posSemidef.smul ha.le).isHermitian, ?_⟩
  intro x hx
  simpa only [Matrix.smul_apply, mul_smul_comm, smul_mul_assoc,
    ← Finsupp.smul_sum] using
    smul_pos ha (hM.2 hx)

/-- Inverse central scaling stays in the open COE matrix ball for nonnegative
time. -/
theorem h7InverseCentralScaledState_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    {s : ℝ} (hs : 0 ≤ s) :
    coeCornerSupport
      (unscaleCOECorner K (h7InverseCentralScaledState A s)) := by
  let C := unscaleCOECorner K A
  let B : ConcreteMatrixState N := C.conjTranspose * C
  let q : ℝ := Real.exp (-4 * s)
  have hqpos : 0 < q := Real.exp_pos _
  have hqle : q ≤ 1 := by
    dsimp only [q]
    rw [Real.exp_le_one_iff]
    linarith
  have hmain : (q • (1 - B)).PosDef :=
    h7_posDef_real_smul (by simpa only [C, B, coeCornerSupport] using hsupport)
      hqpos
  have hrest : ((1 - q) • (1 : ConcreteMatrixState N)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sub_nonneg.mpr hqle)
  have hsum := hmain.add_posSemidef hrest
  rw [unscaleCOECorner_inverseCentralScaledState]
  unfold coeCornerSupport
  have hsq : Real.exp (-2 * s) * Real.exp (-2 * s) = q := by
    dsimp only [q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod :
      (Real.exp (-2 * s) • C).conjTranspose *
          (Real.exp (-2 * s) • C) = q • B := by
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, B]
    rw [hsq]
  change (1 - (Real.exp (-2 * s) • C).conjTranspose *
    (Real.exp (-2 * s) • C)).PosDef
  rw [hprod]
  have hid :
      (1 : ConcreteMatrixState N) - q • B =
        q • (1 - B) + (1 - q) • (1 : ConcreteMatrixState N) := by
    module
  rw [hid]
  exact hsum

/-- Real inverse central scaling preserves complex symmetry. -/
theorem h7InverseCentralScaledState_isSymm
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm) (s : ℝ) :
    (unscaleCOECorner K (h7InverseCentralScaledState A s)).IsSymm := by
  rw [unscaleCOECorner_inverseCentralScaledState]
  exact hsymm.smul _

private theorem h7_commute_smul_one_left
    {N : ℕ} (z : ℂ) (M : ConcreteMatrixState N) :
    Commute (z • (1 : ConcreteMatrixState N)) M := by
  apply (commute_iff_eq _ _).2
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (Algebra.commutes z M)

private theorem h7_complex_smul_matrix_eq_real_smul
    {N : ℕ} (r : ℝ) (M : ConcreteMatrixState N) :
    (r : ℂ) • M = r • M := by
  ext i j
  rfl

private theorem h7_matrix_exp_central_add
    {N : ℕ} (s : ℝ) (H : ConcreteMatrixState N) :
    NormedSpace.exp (((-1 : ℝ) : ℂ) •
        (s • (1 : ConcreteMatrixState N) + H)) =
      (Real.exp (-s) : ℂ) •
        NormedSpace.exp (((-1 : ℝ) : ℂ) • H) := by
  rw [smul_add]
  have hscalar :
      (((-1 : ℝ) : ℂ) • (s • (1 : ConcreteMatrixState N))) =
        ((-s : ℝ) : ℂ) • (1 : ConcreteMatrixState N) := by
    ext i j
    simp [Matrix.smul_apply]
  rw [hscalar, Matrix.exp_add_of_commute _ _
    (h7_commute_smul_one_left ((-s : ℝ) : ℂ) _), matrix_exp_smul_one]
  rw [show NormedSpace.exp ((-s : ℝ) : ℂ) = (Real.exp (-s) : ℂ) by
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.ofReal_exp_ℝ_ℝ (-s)).symm]
  simp only [Matrix.smul_mul, Matrix.one_mul]

/-- Adding a central generator before inverse congruence is exactly the same
as first inverse-centrally scaling the state and then applying the remaining
generator. -/
theorem transposeCongruenceFlow_central_add_neg_one
    {N : ℕ} (s : ℝ) (H C : ConcreteMatrixState N) :
    transposeCongruenceFlow (s • (1 : ConcreteMatrixState N) + H) (-1 : ℝ) C =
      transposeCongruenceFlow H (-1 : ℝ) (Real.exp (-2 * s) • C) := by
  rw [transposeCongruenceFlow_eq, transposeCongruenceFlow_eq]
  have hleft := h7_matrix_exp_central_add s H
  have hright :
      NormedSpace.exp (((-1 : ℝ) : ℂ) •
          (s • (1 : ConcreteMatrixState N) + H).transpose) =
        (Real.exp (-s) : ℂ) •
          NormedSpace.exp (((-1 : ℝ) : ℂ) • H.transpose) := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]
    exact h7_matrix_exp_central_add s H.transpose
  rw [hleft, hright]
  have hexp : Real.exp (-s) * Real.exp (-s) = Real.exp (-2 * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show (Real.exp (-s) : ℂ) * Real.exp (-s) =
      (Real.exp (-2 * s) : ℂ) by exact_mod_cast hexp]
  exact h7_complex_smul_matrix_eq_real_smul _ _

/-- Exact determinant form of the central-shift cocycle. -/
theorem h16GeneralCOEInverseDeterminant_central_add
    {N K : ℕ} (s : ℝ) (H A : ConcreteMatrixState N) :
    h16GeneralCOEInverseDeterminant K
        (s • (1 : ConcreteMatrixState N) + H) A =
      h16GeneralCOEInverseDeterminant K H
        (h7InverseCentralScaledState A s) := by
  change (Matrix.det (1 -
      (transposeCongruenceFlow (s • (1 : ConcreteMatrixState N) + H) (-1 : ℝ)
        (unscaleCOECorner K A)).conjTranspose *
      transposeCongruenceFlow (s • (1 : ConcreteMatrixState N) + H) (-1 : ℝ)
        (unscaleCOECorner K A))).re =
    (Matrix.det (1 -
      (transposeCongruenceFlow H (-1 : ℝ)
        (unscaleCOECorner K (h7InverseCentralScaledState A s))).conjTranspose *
      transposeCongruenceFlow H (-1 : ℝ)
        (unscaleCOECorner K (h7InverseCentralScaledState A s)))).re
  rw [unscaleCOECorner_inverseCentralScaledState]
  rw [transposeCongruenceFlow_central_add_neg_one]

@[simp]
theorem h16GeneralCOEInverseDeterminant_zero
    {N K : ℕ} (A : ConcreteMatrixState N) :
    h16GeneralCOEInverseDeterminant K 0 A =
      concreteCOEBaseDeterminant K A := by
  simp [h16GeneralCOEInverseDeterminant, concreteCOEBaseDeterminant,
    transposeCongruenceFlow, transposeCongruence]

/-- The central inverse determinant is the base determinant of the inverse
centrally scaled state. -/
theorem h7CentralInverseDeterminant_eq_scaled_base
    {N K : ℕ} (s : ℝ) (A : ConcreteMatrixState N) :
    h7CentralInverseDeterminant K A s =
      concreteCOEBaseDeterminant K (h7InverseCentralScaledState A s) := by
  calc
    h7CentralInverseDeterminant K A s =
        h16GeneralCOEInverseDeterminant K
          (s • (1 : ConcreteMatrixState N)) A :=
      (h16GeneralCOEInverseDeterminant_central_line A s).symm
    _ = h16GeneralCOEInverseDeterminant K
          (s • (1 : ConcreteMatrixState N) + 0) A := by rw [add_zero]
    _ = h16GeneralCOEInverseDeterminant K 0
          (h7InverseCentralScaledState A s) :=
      h16GeneralCOEInverseDeterminant_central_add s 0 A
    _ = concreteCOEBaseDeterminant K
          (h7InverseCentralScaledState A s) :=
      h16GeneralCOEInverseDeterminant_zero _

/-- Trace splits into its central and residual components. -/
theorem trace_central_add_re
    {N : ℕ} (s : ℝ) (H : ConcreteMatrixState N) :
    (Matrix.trace (s • (1 : ConcreteMatrixState N) + H)).re =
      (N : ℝ) * s + (Matrix.trace H).re := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  simp
  ring

private theorem h16CoordinateInverseDeterminant_continuousAt
    {N K : ℕ} (A : ConcreteMatrixState N) :
    ContinuousAt
      (fun x : ConcreteMatrixRealCoordinates N ↦
        h16GeneralCOEInverseDeterminant K
          (concreteMatrixOfRealCoordinates x) A) 0 := by
  let C := unscaleCOECorner K A
  let L := h7ShiftCoordinatesToMatrixCLM N
  have hcoords : Continuous
      (concreteMatrixOfRealCoordinates :
        ConcreteMatrixRealCoordinates N → ConcreteMatrixState N) := by
    change Continuous L
    exact L.continuous
  have hexp : Continuous
      (NormedSpace.exp : ConcreteMatrixState N → ConcreteMatrixState N) :=
    continuous_iff_continuousAt.mpr fun M ↦
      (NormedSpace.exp_analytic (𝕂 := ℂ) M).continuousAt
  have hleft : Continuous
      (fun x : ConcreteMatrixRealCoordinates N ↦
        NormedSpace.exp (((-1 : ℝ) : ℂ) •
          concreteMatrixOfRealCoordinates x)) := by
    exact hexp.comp (hcoords.const_smul ((-1 : ℝ) : ℂ))
  have hright : Continuous
      (fun x : ConcreteMatrixRealCoordinates N ↦
        NormedSpace.exp (((-1 : ℝ) : ℂ) •
          (concreteMatrixOfRealCoordinates x).transpose)) := by
    exact hexp.comp
      (hcoords.matrix_transpose.const_smul ((-1 : ℝ) : ℂ))
  have hflow : Continuous
      (fun x : ConcreteMatrixRealCoordinates N ↦
        transposeCongruenceFlow (concreteMatrixOfRealCoordinates x)
          (-1 : ℝ) C) := by
    rw [show (fun x : ConcreteMatrixRealCoordinates N ↦
        transposeCongruenceFlow (concreteMatrixOfRealCoordinates x)
          (-1 : ℝ) C) =
      (fun x ↦ NormedSpace.exp (((-1 : ℝ) : ℂ) •
          concreteMatrixOfRealCoordinates x) * C *
        NormedSpace.exp (((-1 : ℝ) : ℂ) •
          (concreteMatrixOfRealCoordinates x).transpose)) by
      funext x
      exact transposeCongruenceFlow_eq _ _ _]
    exact (hleft.mul continuous_const).mul hright
  unfold h16GeneralCOEInverseDeterminant
  dsimp only
  apply Continuous.continuousAt
  exact Complex.continuous_re.comp
    ((continuous_const.sub (hflow.matrix_conjTranspose.mul hflow)).matrix_det)

/-- The literal likelihood obeys the central product cocycle whenever the
residual inverse determinant is nonnegative. -/
theorem h16GeneralCOELikelihoodCore_central_add_of_nonneg
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    {s : ℝ} (hs : 0 ≤ s) (H : ConcreteMatrixState N)
    (hdet : 0 ≤ h16GeneralCOEInverseDeterminant K H
      (h7InverseCentralScaledState A s)) :
    h16GeneralCOELikelihoodCore N K
        (s • (1 : ConcreteMatrixState N) + H) A =
      h7CentralLikelihoodCore K A s *
        h16GeneralCOELikelihoodCore N K H
          (h7InverseCentralScaledState A s) := by
  let A' := h7InverseCentralScaledState A s
  let b₀ := concreteCOEBaseDeterminant K A
  let bₛ := concreteCOEBaseDeterminant K A'
  let d := h16GeneralCOEInverseDeterminant K H A'
  let e := coeCornerDensityExponent N K
  have hsupport' : coeCornerSupport (unscaleCOECorner K A') :=
    h7InverseCentralScaledState_support A hsupport hs
  have hb₀pos : 0 < b₀ := by
    dsimp only [b₀, concreteCOEBaseDeterminant]
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hbₛpos : 0 < bₛ := by
    dsimp only [bₛ, concreteCOEBaseDeterminant, A']
    exact (RCLike.lt_iff_re_im.mp hsupport'.det_pos).1
  have hb₀ : b₀ ≠ 0 := hb₀pos.ne'
  have hbₛ : bₛ ≠ 0 := hbₛpos.ne'
  have hb₀' : concreteCOEBaseDeterminant K A ≠ 0 := by
    simpa only [b₀] using hb₀
  have hbₛ' : concreteCOEBaseDeterminant K A' ≠ 0 := by
    simpa only [bₛ] using hbₛ
  have hbₛ'' : concreteCOEBaseDeterminant K
      (h7InverseCentralScaledState A s) ≠ 0 := by
    simpa only [A'] using hbₛ'
  have hratio : d / b₀ = (bₛ / b₀) * (d / bₛ) := by
    field_simp [hb₀, hbₛ]
  have hfirst : 0 ≤ bₛ / b₀ := (div_pos hbₛpos hb₀pos).le
  have hsecond : 0 ≤ d / bₛ := div_nonneg hdet hbₛpos.le
  unfold h16GeneralCOELikelihoodCore h7CentralLikelihoodCore
  simp only [if_neg hb₀']
  rw [h16GeneralCOEInverseDeterminant_central_add]
  rw [h7CentralInverseDeterminant_eq_scaled_base]
  rw [trace_central_add_re]
  rw [if_neg hbₛ'']
  change Real.exp (-2 * ((N : ℝ) + 1) *
      ((N : ℝ) * s + (Matrix.trace H).re)) * (d / b₀) ^ e =
    (Real.exp (-2 * (N : ℝ) * ((N : ℝ) + 1) * s) *
      (bₛ / b₀) ^ e) *
    (Real.exp (-2 * ((N : ℝ) + 1) * (Matrix.trace H).re) *
      (d / bₛ) ^ e)
  rw [hratio, Real.mul_rpow hfirst hsecond]
  have hexparg :
      -2 * ((N : ℝ) + 1) * ((N : ℝ) * s + (Matrix.trace H).re) =
        (-2 * (N : ℝ) * ((N : ℝ) + 1) * s) +
          (-2 * ((N : ℝ) + 1) * (Matrix.trace H).re) := by
    ring
  rw [hexparg, Real.exp_add]
  ring

/-- Coordinate form of the cocycle, valid eventually around the residual
origin. -/
theorem h16CoordinateLikelihoodCore_central_translate_eventuallyEq
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    {s : ℝ} (hs : 0 ≤ s) :
    (fun x : ConcreteMatrixRealCoordinates N ↦
      h16CoordinateLikelihoodCore K A
        (s • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N) + x))
      =ᶠ[nhds 0]
    (fun x : ConcreteMatrixRealCoordinates N ↦
      h7CentralLikelihoodCore K A s *
        h16CoordinateLikelihoodCore K
          (h7InverseCentralScaledState A s) x) := by
  let A' := h7InverseCentralScaledState A s
  have hsupport' : coeCornerSupport (unscaleCOECorner K A') :=
    h7InverseCentralScaledState_support A hsupport hs
  have hbasepos : 0 < concreteCOEBaseDeterminant K A' := by
    unfold concreteCOEBaseDeterminant
    exact (RCLike.lt_iff_re_im.mp hsupport'.det_pos).1
  have hcont := h16CoordinateInverseDeterminant_continuousAt (K := K) A'
  have hbaseAt :
      0 < h16GeneralCOEInverseDeterminant K
        (concreteMatrixOfRealCoordinates
          (0 : ConcreteMatrixRealCoordinates N)) A' := by
    change 0 < h16GeneralCOEInverseDeterminant K 0 A'
    rw [h16GeneralCOEInverseDeterminant_zero]
    exact hbasepos
  have hevent : ∀ᶠ x : ConcreteMatrixRealCoordinates N in nhds 0,
      0 < h16GeneralCOEInverseDeterminant K
        (concreteMatrixOfRealCoordinates x) A' :=
    hcont (isOpen_Ioi.mem_nhds hbaseAt)
  filter_upwards [hevent] with x hx
  unfold h16CoordinateLikelihoodCore
  have hmatrix :
      concreteMatrixOfRealCoordinates
          (s • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N) + x) =
        s • (1 : ConcreteMatrixState N) + concreteMatrixOfRealCoordinates x := by
    change (concreteMatrixRealCoordinatesLinearEquiv N).symm
        (s • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N) + x) = _
    rw [map_add, map_smul]
    rw [show (concreteMatrixRealCoordinatesLinearEquiv N).symm
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)) = 1 by
      exact (concreteMatrixRealCoordinatesLinearEquiv N).symm_apply_apply 1]
    rfl
  rw [hmatrix]
  exact h16GeneralCOELikelihoodCore_central_add_of_nonneg
    A hsupport hs (concreteMatrixOfRealCoordinates x) hx.le

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
