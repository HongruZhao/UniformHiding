import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredRankOneDensityScores
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import Mathlib.Tactic

/-!
# First centered COE density score from the literal determinant

This module proves the pointwise first-score formula without an external
calculus assumption.  The proof differentiates a holomorphic support-matrix
path entrywise, derives the determinant derivative at the identity from the
Leibniz formula, normalizes by the positive-definite support determinant, and
then differentiates the real determinant ratio and its `Real.rpow` density.
-/

open Function
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem perm_erase_prod_one_apply_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (sigma : Equiv.Perm n) (i : n) :
    ∏ j ∈ Finset.univ.erase i,
        (1 : Matrix n n ℂ) (sigma j) j =
      if sigma = 1 then 1 else 0 := by
  classical
  by_cases hsigma : sigma = 1
  · subst sigma
    simp [Matrix.one_apply]
  · rw [if_neg hsigma]
    have hmoved : ∃ j, sigma j ≠ j := by
      by_contra h
      push_neg at h
      apply hsigma
      ext j
      simpa using h j
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ sigma j ≠ j := by
      by_cases hi : sigma i = i
      · obtain ⟨j, hj⟩ := hmoved
        exact ⟨j, fun hji ↦ hj (hji.symm ▸ hi), hj⟩
      · refine ⟨sigma i, hi, ?_⟩
        intro heq
        exact hi (sigma.injective heq)
    refine Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) ?_
    simp [Matrix.one_apply, hj]

theorem hasDerivAt_det_of_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : ℂ → Matrix n n ℂ) (F' : Matrix n n ℂ)
    (hF : ∀ i j, HasDerivAt (fun z ↦ F z i j) (F' i j) 0)
    (hF0 : F 0 = 1) :
    HasDerivAt (fun z ↦ Matrix.det (F z)) (Matrix.trace F') 0 := by
  classical
  rw [show (fun z ↦ Matrix.det (F z)) =
      fun z ↦ ∑ sigma : Equiv.Perm n,
        Equiv.Perm.sign sigma • ∏ i, F z (sigma i) i by
    funext z
    exact Matrix.det_apply (F z)]
  have hprod : ∀ sigma : Equiv.Perm n,
      HasDerivAt (fun z ↦ ∏ i, F z (sigma i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, F 0 (sigma j) j) *
          F' (sigma i) i) 0 := by
    intro sigma
    simpa only [smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (u := Finset.univ)
        (f := fun i z ↦ F z (sigma i) i)
        (f' := fun i ↦ F' (sigma i) i)
        (fun i _ ↦ hF (sigma i) i))
  have hsum : HasDerivAt
      (fun z ↦ ∑ sigma : Equiv.Perm n,
        Equiv.Perm.sign sigma • ∏ i, F z (sigma i) i)
      (∑ sigma : Equiv.Perm n,
        Equiv.Perm.sign sigma •
          ∑ i, (∏ j ∈ Finset.univ.erase i, F 0 (sigma j) j) *
            F' (sigma i) i) 0 := by
    apply HasDerivAt.fun_sum
    intro sigma _
    exact (hprod sigma).const_smul (Equiv.Perm.sign sigma)
  convert hsum using 1
  rw [hF0]
  simp_rw [perm_erase_prod_one_apply_eq]
  rw [Finset.sum_eq_single 1]
  · simp [Matrix.trace]
  · intro sigma _ hsigma
    simp [hsigma]
  · simp

section MatrixCalculus

variable {N : ℕ}

local instance centeredMatrixNormedAddCommGroup :
    NormedAddCommGroup (ConcreteMatrixState N) :=
  Matrix.linftyOpNormedAddCommGroup

local instance centeredMatrixNormedSpace :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance centeredMatrixAddCommGroup :
    AddCommGroup (ConcreteMatrixState N) :=
  centeredMatrixNormedAddCommGroup.toAddCommGroup

local instance centeredMatrixModule :
    Module ℂ (ConcreteMatrixState N) := centeredMatrixNormedSpace.toModule

local instance centeredMatrixPseudoMetricSpace :
    PseudoMetricSpace (ConcreteMatrixState N) :=
  centeredMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance centeredMatrixUniformSpace :
    UniformSpace (ConcreteMatrixState N) :=
  centeredMatrixPseudoMetricSpace.toUniformSpace

local instance centeredMatrixTopologicalSpace :
    TopologicalSpace (ConcreteMatrixState N) :=
  centeredMatrixUniformSpace.toTopologicalSpace

local instance centeredMatrixNormedRing :
    NormedRing (ConcreteMatrixState N) := Matrix.linftyOpNormedRing

local instance centeredMatrixNormedAlgebra :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

private def complexMatrixEntryLinearMap (i j : Fin N) :
    ConcreteMatrixState N →ₗ[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def complexMatrixEntryCLM (i j : Fin N) :
    ConcreteMatrixState N →L[ℂ] ℂ :=
  (complexMatrixEntryLinearMap i j).toContinuousLinearMap

def centeredHolomorphicSupportPath
    (Q C : ConcreteMatrixState N) (z : ℂ) : ConcreteMatrixState N :=
  1 -
    NormedSpace.exp (z • (-Q.transpose)) * C.conjTranspose *
      NormedSpace.exp (z • (-(2 : ℂ) • Q)) * C *
        NormedSpace.exp (z • (-Q.transpose))

def centeredSupportPathDerivative
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  Q.transpose * C.conjTranspose * C +
    2 • (C.conjTranspose * Q * C) +
      C.conjTranspose * C * Q.transpose

theorem centeredHolomorphicSupportPath_zero
    (Q C : ConcreteMatrixState N) :
    centeredHolomorphicSupportPath Q C 0 = 1 - C.conjTranspose * C := by
  simp [centeredHolomorphicSupportPath]

theorem concreteCenteredOrbitalDirection_isHermitian
    (v : ComplexUnitSphere N) :
    (concreteCenteredOrbitalDirection N v).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.conjTranspose_apply, concreteCenteredOrbitalDirection,
      complexRankOneProjection]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [Matrix.conjTranspose_apply, concreteCenteredOrbitalDirection,
      complexRankOneProjection, Matrix.one_apply, hij, hji]
    ring

theorem centeredHolomorphicSupportPath_ofReal_eq
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) (t : ℝ) :
    centeredHolomorphicSupportPath Q C (t : ℂ) =
      1 - (transposeCongruenceFlow Q (-t) C).conjTranspose *
        transposeCongruenceFlow Q (-t) C := by
  rw [transposeCongruenceFlow_eq]
  simp only [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose]
  unfold centeredHolomorphicSupportPath
  rw [show ((((-t : ℝ) : ℂ) • Q.transpose).conjTranspose) =
      ((-t : ℂ) • Q.transpose) by
        rw [Matrix.conjTranspose_smul]
        simp [hQ.transpose.eq],
    show ((((-t : ℝ) : ℂ) • Q).conjTranspose) =
      ((-t : ℂ) • Q) by
        rw [Matrix.conjTranspose_smul, hQ.eq]
        simp]
  have hleft : NormedSpace.exp ((t : ℂ) • (-Q.transpose)) =
      NormedSpace.exp ((-t : ℂ) • Q.transpose) := by
    congr 1
    module
  have hmiddle : NormedSpace.exp ((t : ℂ) • (-(2 : ℂ) • Q)) =
      NormedSpace.exp ((-t : ℂ) • Q) *
        NormedSpace.exp ((-t : ℂ) • Q) := by
    calc
      NormedSpace.exp ((t : ℂ) • (-(2 : ℂ) • Q)) =
          NormedSpace.exp (((-t : ℂ) • Q) + ((-t : ℂ) • Q)) := by
            congr 1
            module
      _ = _ := Matrix.exp_add_of_commute _ _ (Commute.refl _)
  rw [hleft, hmiddle]
  simp only [Complex.ofReal_neg]
  noncomm_ring

theorem hasDerivAt_centeredHolomorphicSupportPath_entry
    (Q C : ConcreteMatrixState N) (i j : Fin N) :
    HasDerivAt (fun z ↦ centeredHolomorphicSupportPath Q C z i j)
      (centeredSupportPathDerivative Q C i j) 0 := by
  have hleft := hasDerivAt_exp_smul_const
    (-Q.transpose) (0 : ℂ)
  have hmid := hasDerivAt_exp_smul_const
    (-(2 : ℂ) • Q) (0 : ℂ)
  have hright := hasDerivAt_exp_smul_const
    (-Q.transpose) (0 : ℂ)
  have hprod := ((((hleft.mul_const C.conjTranspose).mul hmid).mul_const C).mul hright)
  have hsub := (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ConcreteMatrixState N))).sub hprod
  have h := (complexMatrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt
    0 hsub
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul,
    Matrix.mul_one, Pi.mul_apply] at h
  have hraw :
      0 - (((-Q.transpose) * C.conjTranspose +
          C.conjTranspose * (-(2 : ℂ) • Q)) * C +
        C.conjTranspose * C * (-Q.transpose)) =
      centeredSupportPathDerivative Q C := by
    unfold centeredSupportPathDerivative
    simp only [sub_eq_add_neg, zero_add, neg_add_rev, Matrix.add_mul,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
      neg_neg, neg_smul]
    noncomm_ring
    rw [add_comm (2 • (C.conjTranspose * (Q * C)))
      (Q.transpose * (C.conjTranspose * C))]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp [Algebra.algebraMap_eq_smul_one]
    rw [two_smul, two_mul]
  rw [hraw] at h
  convert h using 1 <;>
    first
    | rfl
    | (funext z
       simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
       unfold centeredHolomorphicSupportPath complexMatrixEntryCLM
         complexMatrixEntryLinearMap
       rfl)
    | simp [complexMatrixEntryCLM, complexMatrixEntryLinearMap]
    | exact Subsingleton.elim _ _

def centeredNormalizedSupportPath
    (Q C : ConcreteMatrixState N) (z : ℂ) : ConcreteMatrixState N :=
  (1 - C.conjTranspose * C)⁻¹ * centeredHolomorphicSupportPath Q C z

def centeredNormalizedSupportDerivative
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  (1 - C.conjTranspose * C)⁻¹ * centeredSupportPathDerivative Q C

theorem centeredNormalizedSupportPath_zero
    (Q C : ConcreteMatrixState N)
    (hunit : IsUnit (1 - C.conjTranspose * C).det) :
    centeredNormalizedSupportPath Q C 0 = 1 := by
  letI : Invertible (1 - C.conjTranspose * C) :=
    ((Matrix.isUnit_iff_isUnit_det (1 - C.conjTranspose * C)).2 hunit).invertible
  rw [centeredNormalizedSupportPath,
    centeredHolomorphicSupportPath_zero]
  exact Matrix.inv_mul_of_invertible _

theorem hasDerivAt_centeredNormalizedSupportPath_entry
    (Q C : ConcreteMatrixState N) (i j : Fin N) :
    HasDerivAt (fun z ↦ centeredNormalizedSupportPath Q C z i j)
      (centeredNormalizedSupportDerivative Q C i j) 0 := by
  unfold centeredNormalizedSupportPath centeredNormalizedSupportDerivative
  simp only [Matrix.mul_apply]
  simpa only [smul_eq_mul] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun k z ↦ (1 - C.conjTranspose * C)⁻¹ i k *
        centeredHolomorphicSupportPath Q C z k j)
      (A' := fun k ↦ (1 - C.conjTranspose * C)⁻¹ i k *
        centeredSupportPathDerivative Q C k j)
      (fun k _ ↦
        (hasDerivAt_centeredHolomorphicSupportPath_entry Q C k j).const_mul
          ((1 - C.conjTranspose * C)⁻¹ i k)))

theorem hasDerivAt_det_centeredNormalizedSupportPath
    (Q C : ConcreteMatrixState N)
    (hunit : IsUnit (1 - C.conjTranspose * C).det) :
    HasDerivAt (fun z ↦ Matrix.det (centeredNormalizedSupportPath Q C z))
      (Matrix.trace (centeredNormalizedSupportDerivative Q C)) 0 := by
  apply hasDerivAt_det_of_eq_one
  · exact hasDerivAt_centeredNormalizedSupportPath_entry Q C
  · exact centeredNormalizedSupportPath_zero Q C hunit

theorem det_centeredHolomorphicSupportPath_factor
    (Q C : ConcreteMatrixState N)
    (hunit : IsUnit (1 - C.conjTranspose * C).det) (z : ℂ) :
    Matrix.det (centeredHolomorphicSupportPath Q C z) =
      Matrix.det (1 - C.conjTranspose * C) *
        Matrix.det (centeredNormalizedSupportPath Q C z) := by
  letI : Invertible (1 - C.conjTranspose * C) :=
    ((Matrix.isUnit_iff_isUnit_det (1 - C.conjTranspose * C)).2 hunit).invertible
  rw [← Matrix.det_mul]
  congr 1
  unfold centeredNormalizedSupportPath
  rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]

theorem hasDerivAt_det_centeredHolomorphicSupportPath
    (Q C : ConcreteMatrixState N)
    (hunit : IsUnit (1 - C.conjTranspose * C).det) :
    HasDerivAt (fun z ↦ Matrix.det (centeredHolomorphicSupportPath Q C z))
      (Matrix.det (1 - C.conjTranspose * C) *
        Matrix.trace (centeredNormalizedSupportDerivative Q C)) 0 := by
  have h := (hasDerivAt_det_centeredNormalizedSupportPath Q C hunit).const_mul
    (Matrix.det (1 - C.conjTranspose * C))
  convert h using 1 <;>
    first
    | rfl
    | exact Subsingleton.elim _ _
    | (funext z
       exact det_centeredHolomorphicSupportPath_factor Q C hunit z)

theorem hasDerivAt_concreteCOECenteredInverseDeterminant_raw
    {K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    let C := unscaleCOECorner K A
    let Q := concreteCenteredOrbitalDirection N v
    HasDerivAt
      (fun t ↦ concreteCOECenteredInverseDeterminant K v t A)
      (Matrix.det (1 - C.conjTranspose * C) *
        Matrix.trace (centeredNormalizedSupportDerivative Q C)).re 0 := by
  dsimp only
  let C := unscaleCOECorner K A
  let Q := concreteCenteredOrbitalDirection N v
  have hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C)) :=
    (Matrix.isUnit_iff_isUnit_det (1 - C.conjTranspose * C)).mp hsupport.isUnit
  have hcomplex := hasDerivAt_det_centeredHolomorphicSupportPath Q C hunit
  have hreal := hcomplex.real_of_complex
  convert hreal using 1
  funext t
  unfold concreteCOECenteredInverseDeterminant
  rw [show unscaleCOECorner K A = C by rfl]
  rw [centeredHolomorphicSupportPath_ofReal_eq Q C
    (concreteCenteredOrbitalDirection_isHermitian v) t]

theorem trace_centeredNormalizedSupportDerivative_eq
    (Q C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hH : (1 - C.conjTranspose * C).PosDef) :
    Matrix.trace (centeredNormalizedSupportDerivative Q C) =
      4 * Matrix.trace
        (Q * (C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose)) := by
  let H : ConcreteMatrixState N := 1 - C.conjTranspose * C
  let G : ConcreteMatrixState N := 1 - C * C.conjTranspose
  let Z : ConcreteMatrixState N := C * H⁻¹ * C.conjTranspose
  have hHunit : IsUnit H := hH.isUnit
  letI : Invertible H := hHunit.invertible
  have hGt : G.transpose = H := by
    unfold G H
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      hC.eq, hC.conjTranspose.eq]
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Matrix.det_transpose, hGt]
    exact (Matrix.isUnit_iff_isUnit_det H).mp hHunit
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

theorem hasDerivAt_concreteCOECenteredInverseDeterminant
    {K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    HasDerivAt
      (fun t ↦ concreteCOECenteredInverseDeterminant K v t A)
      (4 * concreteCOEBaseDeterminant K A *
        (Matrix.trace (concreteCenteredOrbitalDirection N v *
          concreteCOEZ K A)).re) 0 := by
  let C := unscaleCOECorner K A
  let Q := concreteCenteredOrbitalDirection N v
  have hraw :=
    hasDerivAt_concreteCOECenteredInverseDeterminant_raw v A hsupport
  dsimp only at hraw
  have htrace :=
    trace_centeredNormalizedSupportDerivative_eq Q C hsymm hsupport
  rw [htrace] at hraw
  have hdetIm : (Matrix.det (1 - C.conjTranspose * C)).im = 0 :=
    (RCLike.lt_iff_re_im.mp hsupport.det_pos).2.symm
  convert hraw using 1
  unfold concreteCOEBaseDeterminant concreteCOEZ
  change 4 * (Matrix.det (1 - C.conjTranspose * C)).re *
      (Matrix.trace (Q * (C * (1 - C.conjTranspose * C)⁻¹ *
        C.conjTranspose))).re =
    (Matrix.det (1 - C.conjTranspose * C) *
      (4 * Matrix.trace (Q *
        (C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose)))).re
  simp [Complex.mul_re, hdetIm]
  ring

theorem trace_concreteCenteredOrbitalDirection_mul
    (v : ComplexUnitSphere N) (Z : ConcreteMatrixState N) :
    Matrix.trace (concreteCenteredOrbitalDirection N v * Z) =
      complexCenteredProjectiveTracePair v Z := by
  rw [complexCenteredProjectiveTracePair,
    complexProjectiveTracePair_eq_trace]
  unfold concreteCenteredOrbitalDirection
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.one_mul]
  rfl

theorem hasDerivAt_concreteCOECenteredDeterminantRatio
    {K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    HasDerivAt
      (fun t ↦ concreteCOECenteredInverseDeterminant K v t A /
        concreteCOEBaseDeterminant K A)
      (4 * (complexCenteredProjectiveTracePair v
        (concreteCOEZ K A)).re) 0 := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  have h :=
    (hasDerivAt_concreteCOECenteredInverseDeterminant v A hsymm hsupport).div_const
      (concreteCOEBaseDeterminant K A)
  rw [trace_concreteCenteredOrbitalDirection_mul] at h
  have hcancel :
      (4 * concreteCOEBaseDeterminant K A *
          (complexCenteredProjectiveTracePair v (concreteCOEZ K A)).re) /
          concreteCOEBaseDeterminant K A =
        4 * (complexCenteredProjectiveTracePair v (concreteCOEZ K A)).re := by
    calc
      _ = concreteCOEBaseDeterminant K A *
          (4 * (complexCenteredProjectiveTracePair v
            (concreteCOEZ K A)).re) /
            concreteCOEBaseDeterminant K A := by ring
      _ = _ := mul_div_cancel_left₀ _ hbase
  simpa only [hcancel] using h

theorem hasDerivAt_concreteCenteredLikelihoodCore_one
    {K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    HasDerivAt (fun t ↦ concreteCenteredLikelihoodCore K v t A)
      (4 * (complexCenteredProjectiveTracePair v
        (concreteCOEZ K A)).re * coeCornerDensityExponent N K) 0 := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  have hratio :=
    hasDerivAt_concreteCOECenteredDeterminantRatio v A hsymm hsupport
  have hratio_zero :
      concreteCOECenteredInverseDeterminant K v 0 A /
        concreteCOEBaseDeterminant K A = 1 := by
    have heq : concreteCOECenteredInverseDeterminant K v 0 A =
        concreteCOEBaseDeterminant K A := by
      simp [concreteCOECenteredInverseDeterminant,
        concreteCOEBaseDeterminant, transposeCongruenceFlow,
        transposeCongruence]
    rw [heq, div_self hbase]
  have hrpow := hratio.rpow_const
    (p := coeCornerDensityExponent N K) (Or.inl (by simp [hratio_zero]))
  rw [show (fun t ↦ concreteCenteredLikelihoodCore K v t A) =
      fun t ↦ Real.rpow
        (concreteCOECenteredInverseDeterminant K v t A /
          concreteCOEBaseDeterminant K A)
        (coeCornerDensityExponent N K) by
      funext t
      simp [concreteCenteredLikelihoodCore, hbase]]
  simpa [hratio_zero] using hrpow

theorem complexCenteredProjectiveTracePair_smul
    (v : ComplexUnitSphere N) (z : ℂ) (Z : ConcreteMatrixState N) :
    complexCenteredProjectiveTracePair v (z • Z) =
      z * complexCenteredProjectiveTracePair v Z := by
  unfold complexCenteredProjectiveTracePair
  rw [complexProjectiveTracePair_eq_trace,
    complexProjectiveTracePair_eq_trace]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

theorem centeredLikelihoodDerivative_eq_firstDensityScore
    {K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    4 * (complexCenteredProjectiveTracePair v
        (concreteCOEZ K A)).re * coeCornerDensityExponent N K =
      concreteCenteredRankOneFirstDensityScore N K v A := by
  unfold concreteCenteredRankOneFirstDensityScore
  unfold concreteCenteredRankOneFirstDensityScoreComplex concreteCOEY
  rw [complexCenteredProjectiveTracePair_smul]
  unfold coeCornerDensityExponent concreteCOEExponent
  simp [Complex.mul_re]
  ring

theorem coeCorner_centeredDensityScore_one_eq_explicit_external_derived
    {N K : ℕ} (_hN : 1 ≤ N) (_hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredDensityScore 1 N K v A =
      concreteCenteredRankOneFirstDensityScore N K v A := by
  have hderiv :=
    hasDerivAt_concreteCenteredLikelihoodCore_one v A hsymm hsupport
  rw [concreteCenteredDensityScore, iteratedDeriv_one]
  rw [hderiv.deriv]
  exact centeredLikelihoodDerivative_eq_firstDensityScore v A

end MatrixCalculus

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
