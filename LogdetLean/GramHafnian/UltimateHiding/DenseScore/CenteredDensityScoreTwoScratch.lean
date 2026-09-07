import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLikelihoodLowBellCalculus
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreOneDerived
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

open Function
open Matrix Polynomial
open scoped BigOperators ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 2000000

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem perm_erase_prod_one_apply_eq_two
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
    refine Finset.prod_eq_zero
      (i := j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) ?_
    simp [Matrix.one_apply, hj]

private theorem hasDerivAt_det_of_eq_one_two
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
  simp_rw [perm_erase_prod_one_apply_eq_two]
  rw [Finset.sum_eq_single 1]
  · simp [Matrix.trace]
  · intro sigma _ hsigma
    simp [hsigma]
  · simp

section MatrixCalculus

variable {N : ℕ}

private theorem hasDerivAt_det_matrix_path_of_isUnit
    (F : ℂ → ConcreteMatrixState N) (F' : ConcreteMatrixState N)
    (x : ℂ)
    (hF : ∀ i j, HasDerivAt (fun z ↦ F z i j) (F' i j) x)
    (hunit : IsUnit (F x)) :
    HasDerivAt (fun z ↦ Matrix.det (F z))
      (Matrix.det (F x) * Matrix.trace ((F x)⁻¹ * F')) x := by
  let G : ℂ → ConcreteMatrixState N := fun z ↦ (F x)⁻¹ * F z
  have hdetUnit : IsUnit (Matrix.det (F x)) :=
    (Matrix.isUnit_iff_isUnit_det (F x)).mp hunit
  have hG0 : G x = 1 := by
    dsimp [G]
    exact Matrix.nonsing_inv_mul _ hdetUnit
  have hentry (i j : Fin N) :
      HasDerivAt (fun z ↦ G z i j) (((F x)⁻¹ * F') i j) x := by
    simp only [G, Matrix.mul_apply]
    apply HasDerivAt.fun_sum
    intro k _
    exact (hF k j).const_mul ((F x)⁻¹ i k)
  have hdetG : HasDerivAt (fun z ↦ Matrix.det (G z))
      (Matrix.trace ((F x)⁻¹ * F')) x := by
    let G0 : ℂ → ConcreteMatrixState N := fun z ↦ G (x + z)
    have hG0' : G0 0 = 1 := by simpa [G0] using hG0
    have hentry0 (i j : Fin N) :
        HasDerivAt (fun z ↦ G0 z i j) (((F x)⁻¹ * F') i j) 0 := by
      have hh : HasDerivAt (fun z ↦ G z i j)
          (((F x)⁻¹ * F') i j) (x + 0) := by
        simpa using hentry i j
      simpa only [G0] using hh.comp_const_add x 0
    have h := hasDerivAt_det_of_eq_one_two G0 ((F x)⁻¹ * F') hentry0 hG0'
    have hh : HasDerivAt (fun z ↦ Matrix.det (G0 z))
        (Matrix.trace ((F x)⁻¹ * F')) (x - x) := by
      simpa using h
    simpa only [G0, add_sub_cancel] using hh.comp_sub_const x x
  have hfactor : (fun z ↦ Matrix.det (F z)) =
      fun z ↦ Matrix.det (F x) * Matrix.det (G z) := by
    funext z
    have hmul : F x * G z = F z := by
      dsimp [G]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetUnit,
        Matrix.one_mul]
    rw [← hmul, Matrix.det_mul]
  rw [hfactor]
  exact hdetG.const_mul _

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

private theorem iteratedDeriv_two_det_matrix_path_of_isUnit
    (F : ℂ → ConcreteMatrixState N)
    (F₁ : ℂ → ConcreteMatrixState N) (F₂ : ConcreteMatrixState N)
    (x : ℂ)
    (hF : ∀ᶠ y in nhds x, ∀ i j,
      HasDerivAt (fun z ↦ F z i j) (F₁ y i j) y)
    (hF₁ : ∀ i j, HasDerivAt (fun z ↦ F₁ z i j) (F₂ i j) x)
    (hunit : IsUnit (Matrix.det (F x))) :
    iteratedDeriv 2 (fun z ↦ Matrix.det (F z)) x =
      Matrix.det (F x) *
        (Matrix.trace ((F x)⁻¹ * F₁ x) ^ 2 -
          Matrix.trace ((F x)⁻¹ * F₁ x * (F x)⁻¹ * F₁ x) +
          Matrix.trace ((F x)⁻¹ * F₂)) := by
  let d : ℂ → ℂ := fun z ↦ Matrix.det (F z)
  let J : ℂ → ConcreteMatrixState N := fun z ↦ (F z)⁻¹
  let T : ℂ → ℂ := fun z ↦ Matrix.trace (J z * F₁ z)
  have hFat : ∀ i j, HasDerivAt (fun z ↦ F z i j) (F₁ x i j) x := by
    exact mem_of_mem_nhds hF
  have hFdiff (i j : Fin N) :
      DifferentiableAt ℂ (fun z ↦ F z i j) x := (hFat i j).differentiableAt
  have hdet : HasDerivAt d
      (Matrix.det (F x) * Matrix.trace ((F x)⁻¹ * F₁ x)) x := by
    exact hasDerivAt_det_matrix_path_of_isUnit F (F₁ x) x hFat
      ((Matrix.isUnit_iff_isUnit_det (F x)).2 hunit)
  have hunitEv : ∀ᶠ y in nhds x, IsUnit (Matrix.det (F y)) := by
    filter_upwards
      [(differentiableAt_det_matrix_path F x hFdiff).continuousAt.eventually_ne
        (isUnit_iff_ne_zero.mp hunit)] with y hy
    exact isUnit_iff_ne_zero.mpr hy
  have hderivEq : (fun y ↦ deriv d y) =ᶠ[nhds x]
      fun y ↦ d y * T y := by
    filter_upwards [hF, hunitEv] with y hyF hyunit
    have hy := hasDerivAt_det_matrix_path_of_isUnit F (F₁ y) y
      (hyF) ((Matrix.isUnit_iff_isUnit_det (F y)).2 hyunit)
    exact hy.deriv
  have hJ (i j : Fin N) : HasDerivAt (fun z ↦ J z i j)
      ((-(F x)⁻¹ * F₁ x * (F x)⁻¹) i j) x := by
    exact hasDerivAt_nonsing_inv_entry_matrix_path F (F₁ x) x hFat hunit i j
  have hJF₁ (i j : Fin N) : HasDerivAt (fun z ↦ (J z * F₁ z) i j)
      (((-(F x)⁻¹ * F₁ x * (F x)⁻¹) * F₁ x +
        (F x)⁻¹ * F₂) i j) x := by
    simp only [Matrix.mul_apply, Matrix.add_apply]
    have hs := HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun k z ↦ J z i k * F₁ z k j)
      (A' := fun k ↦
        (-(F x)⁻¹ * F₁ x * (F x)⁻¹) i k * F₁ x k j +
          (F x)⁻¹ i k * F₂ k j)
      (fun k _ ↦ (hJ i k).mul (hF₁ k j))
    rw [← Finset.sum_add_distrib]
    exact hs
  have hT : HasDerivAt T
      (Matrix.trace
        ((-(F x)⁻¹ * F₁ x * (F x)⁻¹) * F₁ x +
          (F x)⁻¹ * F₂)) x := by
    simp only [T, Matrix.trace]
    exact HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun i z ↦ (J z * F₁ z) i i)
      (A' := fun i ↦
        ((-(F x)⁻¹ * F₁ x * (F x)⁻¹) * F₁ x +
          (F x)⁻¹ * F₂) i i)
      (fun i _ ↦ hJF₁ i i)
  have hrhs : HasDerivAt (fun y ↦ d y * T y)
      ((Matrix.det (F x) * Matrix.trace ((F x)⁻¹ * F₁ x)) * T x +
        d x * Matrix.trace
          ((-(F x)⁻¹ * F₁ x * (F x)⁻¹) * F₁ x +
            (F x)⁻¹ * F₂)) x := hdet.mul hT
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hderivEq.deriv_eq, hrhs.deriv]
  simp only [d, T, J]
  rw [Matrix.trace_add]
  have hneg :
      (-(F x)⁻¹ * F₁ x * (F x)⁻¹ * F₁ x) =
        -((F x)⁻¹ * F₁ x * (F x)⁻¹ * F₁ x) := by
    noncomm_ring
  rw [hneg, Matrix.trace_neg]
  ring

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

private def complexMatrixEntryLinearMapTwo (i j : Fin N) :
    ConcreteMatrixState N →ₗ[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def complexMatrixEntryCLMTwo (i j : Fin N) :
    ConcreteMatrixState N →L[ℂ] ℂ :=
  (complexMatrixEntryLinearMapTwo i j).toContinuousLinearMap

private def centeredHolomorphicSupportPathTwo
    (Q C : ConcreteMatrixState N) (z : ℂ) : ConcreteMatrixState N :=
  1 -
    NormedSpace.exp (z • (-Q.transpose)) * C.conjTranspose *
      NormedSpace.exp (z • (-(2 : ℂ) • Q)) * C *
        NormedSpace.exp (z • (-Q.transpose))

private def centeredSupportPathFirstTwo
    (Q C : ConcreteMatrixState N) (z : ℂ) : ConcreteMatrixState N :=
  let A := -Q.transpose
  let B := -(2 : ℂ) • Q
  let E := NormedSpace.exp (z • A)
  let M := NormedSpace.exp (z • B)
  (-((E * A) * C.conjTranspose * M * C * E +
    (E * C.conjTranspose * (M * B) * C * E) +
    (E * C.conjTranspose * M * C * (E * A))))

private def centeredSupportPathSecondTwo
    (Q C : ConcreteMatrixState N) : ConcreteMatrixState N :=
  let A := -Q.transpose
  let B := -(2 : ℂ) • Q
  (-(A * A * C.conjTranspose * C +
    2 • (A * C.conjTranspose * B * C) +
    2 • (A * C.conjTranspose * C * A) +
    C.conjTranspose * B * B * C +
    2 • (C.conjTranspose * B * C * A) +
    C.conjTranspose * C * A * A))

private theorem centeredHolomorphicSupportPathTwo_zero
    (Q C : ConcreteMatrixState N) :
    centeredHolomorphicSupportPathTwo Q C 0 = 1 - C.conjTranspose * C := by
  simp [centeredHolomorphicSupportPathTwo]

private theorem hasDerivAt_centeredHolomorphicSupportPathTwo_entry
    (Q C : ConcreteMatrixState N) (y : ℂ) (i j : Fin N) :
    HasDerivAt (fun z ↦ centeredHolomorphicSupportPathTwo Q C z i j)
      (centeredSupportPathFirstTwo Q C y i j) y := by
  let A := -Q.transpose
  let B := -(2 : ℂ) • Q
  have hleft := hasDerivAt_exp_smul_const A y
  have hmid := hasDerivAt_exp_smul_const B y
  have hright := hasDerivAt_exp_smul_const A y
  have hprod :=
    ((((hleft.mul_const C.conjTranspose).mul hmid).mul_const C).mul hright)
  have hsub :=
    (hasDerivAt_const (x := y) (c := (1 : ConcreteMatrixState N))).sub hprod
  have h := (complexMatrixEntryCLMTwo i j).hasFDerivAt.comp_hasDerivAt y hsub
  simp only [Pi.mul_apply] at h
  have hraw :
      0 - (((NormedSpace.exp (y • A) * A) * C.conjTranspose *
            NormedSpace.exp (y • B) +
          NormedSpace.exp (y • A) * C.conjTranspose *
            (NormedSpace.exp (y • B) * B)) * C *
            NormedSpace.exp (y • A) +
        NormedSpace.exp (y • A) * C.conjTranspose *
          NormedSpace.exp (y • B) * C *
            (NormedSpace.exp (y • A) * A)) =
        centeredSupportPathFirstTwo Q C y := by
    unfold centeredSupportPathFirstTwo
    change 0 - (((NormedSpace.exp (y • A) * A) * C.conjTranspose *
            NormedSpace.exp (y • B) +
          NormedSpace.exp (y • A) * C.conjTranspose *
            (NormedSpace.exp (y • B) * B)) * C *
            NormedSpace.exp (y • A) +
        NormedSpace.exp (y • A) * C.conjTranspose *
          NormedSpace.exp (y • B) * C *
            (NormedSpace.exp (y • A) * A)) =
      -((NormedSpace.exp (y • A) * A) * C.conjTranspose *
          NormedSpace.exp (y • B) * C * NormedSpace.exp (y • A) +
        NormedSpace.exp (y • A) * C.conjTranspose *
          (NormedSpace.exp (y • B) * B) * C * NormedSpace.exp (y • A) +
        NormedSpace.exp (y • A) * C.conjTranspose *
          NormedSpace.exp (y • B) * C *
            (NormedSpace.exp (y • A) * A))
    noncomm_ring
  rw [hraw] at h
  convert h using 1 <;>
    first
    | rfl
    | (funext z
       simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply]
       unfold centeredHolomorphicSupportPathTwo complexMatrixEntryCLMTwo
         complexMatrixEntryLinearMapTwo
       rfl)
    | simp [complexMatrixEntryCLMTwo, complexMatrixEntryLinearMapTwo]
    | exact Subsingleton.elim _ _

private theorem hasDerivAt_centeredSupportPathFirstTwo_entry
    (Q C : ConcreteMatrixState N) (i j : Fin N) :
    HasDerivAt (fun z ↦ centeredSupportPathFirstTwo Q C z i j)
      (centeredSupportPathSecondTwo Q C i j) 0 := by
  let A := -Q.transpose
  let B := -(2 : ℂ) • Q
  let E : ℂ → ConcreteMatrixState N := fun z ↦ NormedSpace.exp (z • A)
  let M : ℂ → ConcreteMatrixState N := fun z ↦ NormedSpace.exp (z • B)
  have hE := hasDerivAt_exp_smul_const A (0 : ℂ)
  have hM := hasDerivAt_exp_smul_const B (0 : ℂ)
  let Dleft : ConcreteMatrixState N :=
    (((A * A) * C.conjTranspose + A * C.conjTranspose * B) * C) +
      A * C.conjTranspose * C * A
  let Dmiddle : ConcreteMatrixState N :=
    ((A * C.conjTranspose * B + C.conjTranspose * (B * B)) * C) +
      C.conjTranspose * B * C * A
  let Dright : ConcreteMatrixState N :=
    ((A * C.conjTranspose + C.conjTranspose * B) * C) * A +
      C.conjTranspose * C * (A * A)
  have hleftRaw :=
    (((((hE.mul_const A).mul_const C.conjTranspose).mul hM).mul_const C).mul hE)
  simp only [zero_smul, NormedSpace.exp_zero,
    Matrix.one_mul, Matrix.mul_one, Pi.mul_apply] at hleftRaw
  have hleftDeriv :
      (A * A * C.conjTranspose + A * C.conjTranspose * B) * C +
        A * C.conjTranspose * C * A = Dleft := by
    dsimp [Dleft]
  rw [hleftDeriv] at hleftRaw
  have hmiddleRaw :=
    ((((hE.mul_const C.conjTranspose).mul (hM.mul_const B)).mul_const C).mul hE)
  simp only [zero_smul, NormedSpace.exp_zero,
    Matrix.one_mul, Matrix.mul_one, Pi.mul_apply] at hmiddleRaw
  have hmiddleDeriv :
      (A * C.conjTranspose * B + C.conjTranspose * (B * B)) * C +
        C.conjTranspose * B * C * A = Dmiddle := by
    dsimp [Dmiddle]
  rw [hmiddleDeriv] at hmiddleRaw
  have hrightRaw :=
    ((((hE.mul_const C.conjTranspose).mul hM).mul_const C).mul (hE.mul_const A))
  simp only [zero_smul, NormedSpace.exp_zero,
    Matrix.one_mul, Matrix.mul_one, Pi.mul_apply] at hrightRaw
  have hrightDeriv :
      (A * C.conjTranspose + C.conjTranspose * B) * C * A +
        C.conjTranspose * C * (A * A) = Dright := by
    dsimp [Dright]
  rw [hrightDeriv] at hrightRaw
  have hsum := ((hleftRaw.add hmiddleRaw).add hrightRaw).neg
  have hmatrix :
      -(Dleft + Dmiddle + Dright) =
      centeredSupportPathSecondTwo Q C := by
    change -(Dleft + Dmiddle + Dright) =
      -(A * A * C.conjTranspose * C +
        2 • (A * C.conjTranspose * B * C) +
        2 • (A * C.conjTranspose * C * A) +
        C.conjTranspose * B * B * C +
        2 • (C.conjTranspose * B * C * A) +
        C.conjTranspose * C * A * A)
    dsimp [Dleft, Dmiddle, Dright]
    rw [two_smul, two_smul, two_smul]
    noncomm_ring
  rw [hmatrix] at hsum
  have h := (complexMatrixEntryCLMTwo i j).hasFDerivAt.comp_hasDerivAt 0 hsum
  convert h using 1 <;>
    first
    | rfl
    | (funext z
       simp only [Function.comp_apply, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
       unfold centeredSupportPathFirstTwo E M A B
       rfl)
    | simp [complexMatrixEntryCLMTwo, complexMatrixEntryLinearMapTwo]
    | exact Subsingleton.elim _ _

private theorem iteratedDeriv_two_det_centeredHolomorphicSupportPathTwo
    (Q C : ConcreteMatrixState N)
    (hunit : IsUnit (1 - C.conjTranspose * C).det) :
    iteratedDeriv 2
        (fun z ↦ Matrix.det (centeredHolomorphicSupportPathTwo Q C z)) 0 =
      Matrix.det (1 - C.conjTranspose * C) *
        (Matrix.trace ((1 - C.conjTranspose * C)⁻¹ *
            centeredSupportPathFirstTwo Q C 0) ^ 2 -
          Matrix.trace ((1 - C.conjTranspose * C)⁻¹ *
            centeredSupportPathFirstTwo Q C 0 *
              (1 - C.conjTranspose * C)⁻¹ *
                centeredSupportPathFirstTwo Q C 0) +
          Matrix.trace ((1 - C.conjTranspose * C)⁻¹ *
            centeredSupportPathSecondTwo Q C)) := by
  have h := iteratedDeriv_two_det_matrix_path_of_isUnit
    (F := centeredHolomorphicSupportPathTwo Q C)
    (F₁ := centeredSupportPathFirstTwo Q C)
    (F₂ := centeredSupportPathSecondTwo Q C) (x := 0)
    (Filter.Eventually.of_forall fun y ↦
      hasDerivAt_centeredHolomorphicSupportPathTwo_entry Q C y)
    (hasDerivAt_centeredSupportPathFirstTwo_entry Q C)
    (by simpa [centeredHolomorphicSupportPathTwo_zero] using hunit)
  simpa only [centeredHolomorphicSupportPathTwo_zero] using h

private theorem concreteCenteredOrbitalDirection_apply_eq_projection_two
    (v : ComplexUnitSphere N) (i j : Fin N) :
    concreteCenteredOrbitalDirection N v i j =
      complexCenteredRankOneProjection N v i j := by
  simp [concreteCenteredOrbitalDirection, complexCenteredRankOneProjection,
    complexRankOneProjection, Matrix.one_apply]

private theorem trace_centered_sandwich_eq_two
    (v : ComplexUnitSphere N) (W Y : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * W *
          concreteCenteredOrbitalDirection N v * Y) =
      complexCenteredProjectiveSandwich v W Y := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    concreteCenteredOrbitalDirection_apply_eq_projection_two,
    complexCenteredProjectiveSandwich]
  apply Finset.sum_congr rfl
  intro a _
  have hexpand (d : Fin N) :
      (∑ c, (∑ b, complexCenteredRankOneProjection N v a b * W b c) *
          complexCenteredRankOneProjection N v c d) * Y d a =
        ∑ c, ∑ b, complexCenteredRankOneProjection N v a b * W b c *
          complexCenteredRankOneProjection N v c d * Y d a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [hexpand]
  let f : Fin N → Fin N → Fin N → ℂ := fun b c d ↦
    complexCenteredRankOneProjection N v a b * W b c *
      complexCenteredRankOneProjection N v c d * Y d a
  change (∑ d, ∑ c, ∑ b, f b c d) = ∑ b, ∑ c, ∑ d, f b c d
  calc
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ c, ∑ d, ∑ b, f b c d :=
      Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ d, f b c d := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, f b c d := Finset.sum_comm

private theorem trace_centered_conjugate_sandwich_eq_two
    (v : ComplexUnitSphere N) (R : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * R *
          (concreteCenteredOrbitalDirection N v).transpose *
            R.conjTranspose) =
      complexCenteredProjectiveConjugateSandwich v R := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    concreteCenteredOrbitalDirection_apply_eq_projection_two,
    complexCenteredProjectiveConjugateSandwich, Matrix.transpose_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hexpand (d : Fin N) :
      (∑ c, (∑ b, complexCenteredRankOneProjection N v a b * R b c) *
          complexCenteredRankOneProjection N v d c) * star (R a d) =
        ∑ c, ∑ b, complexCenteredRankOneProjection N v a b * R b c *
          complexCenteredRankOneProjection N v d c * star (R a d) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [hexpand]
  let f : Fin N → Fin N → Fin N → ℂ := fun b c d ↦
    complexCenteredRankOneProjection N v a b * R b c *
      complexCenteredRankOneProjection N v d c * star (R a d)
  change (∑ d, ∑ c, ∑ b, f b c d) = ∑ b, ∑ c, ∑ d, f b c d
  calc
    (∑ d, ∑ c, ∑ b, f b c d) = ∑ c, ∑ d, ∑ b, f b c d :=
      Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ d, f b c d := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, f b c d := Finset.sum_comm

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

private def centeredMovedDetTwo
    (Q C : ConcreteMatrixState N) (t : ℝ) : ℝ :=
  (Matrix.det (1 - (centeredMovedCornerTwo Q C t).conjTranspose *
    centeredMovedCornerTwo Q C t)).re

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

/-! ## One further derivative: exact residual kernel for the third log-score

The second-log-score proof above identifies its trace energy at the origin.
For the third log-score, the genuinely new object is the derivative of that
same trace energy along the moved corner.  The next lemmas isolate this
derivative without postulating a bound for it.
-/

/-- The complex trace energy whose first path derivative is the third
log-determinant derivative. -/
def centeredThirdLogTraceKernel
    (Q C : ConcreteMatrixState N) (t : ℝ) : ℂ :=
  let Ct := transposeCongruenceFlow Q (-t) C
  let Zt := Ct * (1 - Ct.conjTranspose * Ct)⁻¹ * Ct.conjTranspose
  let Tt := (1 - Ct * Ct.conjTranspose)⁻¹ * Ct
  Matrix.trace (Q * (1 + Zt) * Q * Zt) +
    Matrix.trace (Q * Tt * Q.transpose * Tt.conjTranspose)

private theorem hasDerivAt_trace_centeredMovedZOutTwo_at
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) (y : ℝ)
    (hunit : IsUnit (Matrix.det
      (1 - (centeredMovedCornerTwo Q C y).conjTranspose *
        centeredMovedCornerTwo Q C y))) :
    HasDerivAt
      (fun t : ℝ ↦ Matrix.trace (Q * centeredMovedZOutTwo Q C t))
      (-2 * centeredThirdLogTraceKernel Q C y) y := by
  let Cy := centeredMovedCornerTwo Q C y
  have hbase := hasDerivAt_trace_centeredMovedZOutTwo Q Cy hQ
    (by simpa only [Cy] using hunit)
  rw [trace_centeredMovedZOutTwo_derivative_eq_two Q Cy hQ
    (by simpa only [Cy] using hunit)] at hbase
  have hvalue :
      -2 * (Matrix.trace (Q * (1 + centeredMovedZTwo Q Cy 0) * Q *
          centeredMovedZTwo Q Cy 0) +
        Matrix.trace (Q * ((1 - Cy * Cy.conjTranspose)⁻¹ * Cy) *
          Q.transpose *
            ((1 - Cy * Cy.conjTranspose)⁻¹ * Cy).conjTranspose)) =
        -2 * centeredThirdLogTraceKernel Q C y := by
    simp only [centeredThirdLogTraceKernel, Cy, centeredMovedZTwo,
      centeredMovedCornerTwo, neg_zero, transposeCongruenceFlow_zero]
  rw [hvalue] at hbase
  have hshiftFun :
      (fun t : ℝ ↦ Matrix.trace
        (Q * centeredMovedZOutTwo Q C (y + t))) =
      (fun t : ℝ ↦ Matrix.trace
        (Q * centeredMovedZOutTwo Q Cy t)) := by
    funext t
    unfold centeredMovedZOutTwo
    rw [centeredMovedCornerTwo_add]
  have hshift : HasDerivAt
      (fun t : ℝ ↦ Matrix.trace
        (Q * centeredMovedZOutTwo Q C (y + t)))
      (-2 * centeredThirdLogTraceKernel Q C y) 0 := by
    rw [hshiftFun]
    exact hbase
  have hshift' : HasDerivAt
      (fun t : ℝ ↦ Matrix.trace
        (Q * centeredMovedZOutTwo Q C (y + t)))
      (-2 * centeredThirdLogTraceKernel Q C y) (y - y) := by
    simpa using hshift
  simpa using hshift'.comp_sub_const y y

private theorem iteratedDeriv_two_log_centeredMovedDetTwo_at
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) (hC : C.IsSymm)
    (y : ℝ) (hy : 0 < centeredMovedDetTwo Q C y) :
    iteratedDeriv 2
        (fun t : ℝ ↦ Real.log (centeredMovedDetTwo Q C t)) y =
      -8 * (centeredThirdLogTraceKernel Q C y).re := by
  let d : ℝ → ℝ := centeredMovedDetTwo Q C
  let a : ℝ → ℝ := fun t ↦
    (Matrix.trace (Q * centeredMovedZOutTwo Q C t)).re
  have hdetNe : Matrix.det
      (1 - (centeredMovedCornerTwo Q C y).conjTranspose *
        centeredMovedCornerTwo Q C y) ≠ 0 := by
    intro hz
    have hzero : d y = 0 := by
      unfold d centeredMovedDetTwo
      rw [hz]
      rfl
    linarith
  have hunit : IsUnit (Matrix.det
      (1 - (centeredMovedCornerTwo Q C y).conjTranspose *
        centeredMovedCornerTwo Q C y)) := isUnit_iff_ne_zero.mpr hdetNe
  have hdAt := hasDerivAt_centeredMovedDetTwo Q C hQ hC y hunit
  have hpos : ∀ᶠ t in nhds y, 0 < d t :=
    continuousAt_const.eventually_lt hdAt.continuousAt (by simpa only [d] using hy)
  have hderivLog :
      (fun t ↦ deriv (fun s ↦ Real.log (d s)) t) =ᶠ[nhds y]
        fun t ↦ 4 * a t := by
    filter_upwards [hpos] with t ht
    have hdetNeT : Matrix.det
        (1 - (centeredMovedCornerTwo Q C t).conjTranspose *
          centeredMovedCornerTwo Q C t) ≠ 0 := by
      intro hz
      have hzero : d t = 0 := by
        unfold d centeredMovedDetTwo
        rw [hz]
        rfl
      linarith
    have hdt := hasDerivAt_centeredMovedDetTwo Q C hQ hC t
      (isUnit_iff_ne_zero.mpr hdetNeT)
    have hmatrixUnit : IsUnit
        (1 - (centeredMovedCornerTwo Q C t).conjTranspose *
          centeredMovedCornerTwo Q C t) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hdetNeT)
    have hz : centeredMovedZOutTwo Q C t = centeredMovedZTwo Q C t := by
      unfold centeredMovedZOutTwo centeredMovedZTwo
      exact output_inv_sub_one_eq_input_Z_two
        (centeredMovedCornerTwo Q C t) hmatrixUnit
    have hlog := hdt.log (ne_of_gt ht)
    rw [hlog.deriv]
    dsimp only [a, d]
    rw [hz]
    calc
      4 * centeredMovedDetTwo Q C t *
            (Matrix.trace (Q * centeredMovedZTwo Q C t)).re /
          centeredMovedDetTwo Q C t =
          centeredMovedDetTwo Q C t *
            (4 * (Matrix.trace (Q * centeredMovedZTwo Q C t)).re) /
              centeredMovedDetTwo Q C t := by ring
      _ = _ := mul_div_cancel_left₀ _ (ne_of_gt ht)
  have haComplex :=
    hasDerivAt_trace_centeredMovedZOutTwo_at Q C hQ y hunit
  have ha : HasDerivAt a
      (-2 * centeredThirdLogTraceKernel Q C y).re y := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y haComplex
    convert hh using 1 <;>
      first
      | rfl
      | simp only [a, Function.comp_apply, Complex.reCLM_apply]
      | exact Subsingleton.elim _ _
  have hrhs : HasDerivAt (fun t ↦ 4 * a t)
      (4 * (-2 * centeredThirdLogTraceKernel Q C y).re) y :=
    ha.const_mul 4
  have hderivLogAt : HasDerivAt
      (fun t ↦ deriv (fun s ↦ Real.log (d s)) t)
      (4 * (-2 * centeredThirdLogTraceKernel Q C y).re) y :=
    hrhs.congr_of_eventuallyEq hderivLog
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hderivLogAt.deriv]
  simp [Complex.mul_re]
  ring

/-- Exact third-log-determinant reduction: the remaining calculus is the
ordinary derivative of `centeredThirdLogTraceKernel`. -/
theorem iteratedDeriv_three_log_centeredMovedDetTwo
    (Q C : ConcreteMatrixState N) (hQ : Q.IsHermitian) (hC : C.IsSymm)
    (hsupport : (1 - C.conjTranspose * C).PosDef) :
    iteratedDeriv 3
        (fun t : ℝ ↦ Real.log (centeredMovedDetTwo Q C t)) 0 =
      deriv (fun t : ℝ ↦
        -8 * (centeredThirdLogTraceKernel Q C t).re) 0 := by
  have hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hsupport.isUnit
  have hdAt := hasDerivAt_centeredMovedDetTwo Q C hQ hC 0
    (by simpa [centeredMovedCornerTwo] using hunit)
  have hzero : 0 < centeredMovedDetTwo Q C 0 := by
    simp only [centeredMovedDetTwo, centeredMovedCornerTwo, neg_zero,
      transposeCongruenceFlow_zero]
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hpos : ∀ᶠ t in nhds 0, 0 < centeredMovedDetTwo Q C t :=
    continuousAt_const.eventually_lt hdAt.continuousAt hzero
  have heq :
      (fun t ↦ iteratedDeriv 2
        (fun s : ℝ ↦ Real.log (centeredMovedDetTwo Q C s)) t) =ᶠ[nhds 0]
      (fun t ↦ -8 * (centeredThirdLogTraceKernel Q C t).re) := by
    filter_upwards [hpos] with t ht
    exact iteratedDeriv_two_log_centeredMovedDetTwo_at Q C hQ hC t ht
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
    heq.deriv_eq]

/-- On the open COE support, the literal third logarithmic score is exactly
the first path derivative of the explicit trace-resolvent kernel above. -/
theorem concreteCenteredLogScore_three_eq_traceKernel_deriv
    {K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredLogScore 3 N K v A =
      coeCornerDensityExponent N K *
        deriv (fun t : ℝ ↦ -8 *
          (centeredThirdLogTraceKernel
            (concreteCenteredOrbitalDirection N v)
            (unscaleCOECorner K A) t).re) 0 := by
  let C := unscaleCOECorner K A
  let Q := concreteCenteredOrbitalDirection N v
  let d : ℝ → ℝ := centeredMovedDetTwo Q C
  let p : ℝ := coeCornerDensityExponent N K
  let L : ℝ → ℝ := fun t ↦ p * (Real.log (d t) - Real.log (d 0))
  have hQ : Q.IsHermitian := concreteCenteredOrbitalDirection_isHermitian v
  have hsupport' : (1 - C.conjTranspose * C).PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [C] using hsupport
  have hlogd := iteratedDeriv_three_log_centeredMovedDetTwo Q C hQ
    (by simpa only [C] using hsymm) hsupport'
  have hd0 : d 0 = concreteCOEBaseDeterminant K A := by
    simp [d, C, Q, centeredMovedDetTwo, centeredMovedCornerTwo,
      concreteCOEBaseDeterminant]
  have hbasePos : 0 < d 0 := by
    rw [hd0]
    unfold concreteCOEBaseDeterminant
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (by simpa only [C] using hsupport.isUnit)
  have hdAt := hasDerivAt_centeredMovedDetTwo Q C hQ
    (by simpa only [C] using hsymm) 0
    (by simpa [centeredMovedCornerTwo] using hunit)
  have hpos : ∀ᶠ t in nhds 0, 0 < d t :=
    continuousAt_const.eventually_lt hdAt.continuousAt hbasePos
  have hlike :
      (fun t ↦ Real.log (concreteCenteredLikelihoodCore K v t A)) =ᶠ[nhds 0]
        L := by
    filter_upwards [hpos] with t ht
    have hratio : 0 < d t / d 0 := div_pos ht hbasePos
    unfold L p
    rw [show concreteCenteredLikelihoodCore K v t A =
        Real.rpow (d t / d 0) (coeCornerDensityExponent N K) by
      unfold concreteCenteredLikelihoodCore
      rw [if_neg (ne_of_gt (by simpa [hd0] using hbasePos))]
      congr 2
      exact hd0.symm]
    rw [show Real.log (Real.rpow (d t / d 0)
          (coeCornerDensityExponent N K)) =
        coeCornerDensityExponent N K * Real.log (d t / d 0) by
      exact Real.log_rpow hratio _]
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hbasePos)]
  unfold concreteCenteredLogScore
  rw [hlike.iteratedDeriv_eq 3]
  unfold L
  rw [iteratedDeriv_const_mul_field]
  have hsub : iteratedDeriv 3
      (fun t ↦ Real.log (d t) - Real.log (d 0)) 0 =
      iteratedDeriv 3 (fun t ↦ Real.log (d t)) 0 := by
    simpa [sub_eq_add_neg, add_comm] using
      (iteratedDeriv_const_add (f := fun t ↦ Real.log (d t))
        (x := (0 : ℝ)) (n := 3) (by norm_num) (-Real.log (d 0)))
  rw [hsub, hlogd]

private theorem concreteCenteredLogScore_two_eq_unscaled_trace_two
    {K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredLogScore 2 N K v A =
      (-8 * coeCornerDensityExponent N K *
        (Matrix.trace (concreteCenteredOrbitalDirection N v *
            (1 + concreteCOEZ K A) * concreteCenteredOrbitalDirection N v *
              concreteCOEZ K A) +
          Matrix.trace (concreteCenteredOrbitalDirection N v *
            concreteCOET K A *
              (concreteCenteredOrbitalDirection N v).transpose *
                (concreteCOET K A).conjTranspose))).re := by
  let C := unscaleCOECorner K A
  let Q := concreteCenteredOrbitalDirection N v
  let d : ℝ → ℝ := centeredMovedDetTwo Q C
  let p : ℝ := coeCornerDensityExponent N K
  let L : ℝ → ℝ := fun t ↦ p * (Real.log (d t) - Real.log (d 0))
  have hQ : Q.IsHermitian := by
    exact concreteCenteredOrbitalDirection_isHermitian v
  have hsupport' : (1 - C.conjTranspose * C).PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [C] using hsupport
  have hlogd := iteratedDeriv_two_log_centeredMovedDetTwo Q C hQ
    (by simpa only [C] using hsymm) hsupport'
  have hd0 : d 0 = concreteCOEBaseDeterminant K A := by
    simp [d, C, Q, centeredMovedDetTwo, centeredMovedCornerTwo,
      concreteCOEBaseDeterminant]
  have hbasePos : 0 < d 0 := by
    rw [hd0]
    unfold concreteCOEBaseDeterminant
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hunit : IsUnit (Matrix.det (1 - C.conjTranspose * C)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (by simpa only [C] using hsupport.isUnit)
  have hdAt := hasDerivAt_centeredMovedDetTwo Q C hQ
    (by simpa only [C] using hsymm) 0
    (by simpa [centeredMovedCornerTwo] using hunit)
  have hpos : ∀ᶠ t in nhds 0, 0 < d t :=
    continuousAt_const.eventually_lt hdAt.continuousAt hbasePos
  have hlike :
      (fun t ↦ Real.log (concreteCenteredLikelihoodCore K v t A)) =ᶠ[nhds 0]
        L := by
    filter_upwards [hpos] with t ht
    have hratio : 0 < d t / d 0 := div_pos ht hbasePos
    unfold L p
    rw [show concreteCenteredLikelihoodCore K v t A =
        Real.rpow (d t / d 0) (coeCornerDensityExponent N K) by
      unfold concreteCenteredLikelihoodCore
      rw [if_neg (ne_of_gt (by simpa [hd0] using hbasePos))]
      congr 2
      · exact hd0.symm
      ]
    rw [show Real.log (Real.rpow (d t / d 0)
          (coeCornerDensityExponent N K)) =
        coeCornerDensityExponent N K * Real.log (d t / d 0) by
      exact Real.log_rpow hratio _]
    rw [Real.log_div (ne_of_gt ht) (ne_of_gt hbasePos)]
  unfold concreteCenteredLogScore
  rw [hlike.iteratedDeriv_eq 2]
  unfold L
  rw [iteratedDeriv_const_mul_field]
  have hsub : iteratedDeriv 2
      (fun t ↦ Real.log (d t) - Real.log (d 0)) 0 =
      iteratedDeriv 2 (fun t ↦ Real.log (d t)) 0 := by
    simpa [sub_eq_add_neg, add_comm] using
      (iteratedDeriv_const_add (f := fun t ↦ Real.log (d t))
        (x := (0 : ℝ)) (n := 2) (by norm_num) (-Real.log (d 0)))
  rw [hsub, hlogd]
  unfold p Q C centeredMovedZTwo centeredMovedCornerTwo
  simp only [neg_zero, transposeCongruenceFlow_zero]
  unfold concreteCOEZ concreteCOET
  simp [Complex.mul_re]
  ring

private theorem concreteCenteredLogScore_two_eq_sandwiches_two
    {K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredLogScore 2 N K v A =
      (-4 * (complexCenteredProjectiveSandwich v
          (concreteCOEWMatrix N K A) (concreteCOEY N K A) +
        complexCenteredProjectiveConjugateSandwich v
          (concreteCOERMatrix N K A))).re := by
  let Q := concreteCenteredOrbitalDirection N v
  let Z := concreteCOEZ K A
  let T := concreteCOET K A
  let c := concreteCOEExponent N K
  have hk : (2 * (N : ℝ) + 8 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hboundary
  have hcpos : 0 < c := by
    unfold c concreteCOEExponent
    linarith
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hY : concreteCOEY N K A = ((c : ℝ) : ℂ) • Z := by
    rfl
  have hW : concreteCOEWMatrix N K A = 1 + Z := by
    unfold concreteCOEWMatrix
    rw [hY]
    simp only [smul_smul]
    rw [show (((c⁻¹ : ℝ) : ℂ) * ((c : ℝ) : ℂ)) = 1 by
      norm_cast
      exact inv_mul_cancel₀ hc, one_smul]
  have hB : complexCenteredProjectiveSandwich v
      (concreteCOEWMatrix N K A) (concreteCOEY N K A) =
      (c : ℂ) * Matrix.trace (Q * (1 + Z) * Q * Z) := by
    rw [← trace_centered_sandwich_eq_two v]
    rw [hW, hY]
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    congr 1
  have hR : concreteCOERMatrix N K A =
      ((Real.sqrt c : ℝ) : ℂ) • T := by rfl
  have hsqrt : ((Real.sqrt c : ℝ) : ℂ) *
      ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    norm_cast
    simpa only [pow_two] using Real.sq_sqrt hcpos.le
  have hC : complexCenteredProjectiveConjugateSandwich v
      (concreteCOERMatrix N K A) =
      (c : ℂ) * Matrix.trace (Q * T * Q.transpose * T.conjTranspose) := by
    rw [← trace_centered_conjugate_sandwich_eq_two v]
    rw [hR, Matrix.conjTranspose_smul]
    have hstar : star ((Real.sqrt c : ℝ) : ℂ) =
        ((Real.sqrt c : ℝ) : ℂ) := by simp
    rw [hstar]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
      smul_smul, smul_eq_mul]
    rw [hsqrt]
  rw [concreteCenteredLogScore_two_eq_unscaled_trace_two v A hsymm hsupport]
  rw [hB, hC]
  unfold coeCornerDensityExponent c concreteCOEExponent
  simp [Complex.mul_re]
  ring

private theorem complexCenteredProjectiveTracePair_im_zero_two
    (v : ComplexUnitSphere N) (Y : ConcreteMatrixState N)
    (hY : Y.IsHermitian) :
    (complexCenteredProjectiveTracePair v Y).im = 0 := by
  rw [← trace_concreteCenteredOrbitalDirection_mul]
  have hQ := concreteCenteredOrbitalDirection_isHermitian v
  apply Complex.conj_eq_iff_im.mp
  calc
    star (Matrix.trace (concreteCenteredOrbitalDirection N v * Y)) =
        Matrix.trace
          ((concreteCenteredOrbitalDirection N v * Y).conjTranspose) := by
      rw [Matrix.trace_conjTranspose]
    _ = Matrix.trace (Y * concreteCenteredOrbitalDirection N v) := by
      rw [Matrix.conjTranspose_mul, hY.eq, hQ.eq]
    _ = Matrix.trace (concreteCenteredOrbitalDirection N v * Y) :=
      Matrix.trace_mul_comm _ _

theorem coeCorner_centeredDensityScore_two_eq_explicit_external_derived
    {K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredDensityScore 2 N K v A =
      concreteCenteredRankOneSecondDensityScore N K v A := by
  rw [coeCorner_centeredDensityScore_two_eq_Bell hN v A hsupport]
  have hlogOne : concreteCenteredLogScore 1 N K v A =
      concreteCenteredRankOneFirstDensityScore N K v A := by
    calc
      concreteCenteredLogScore 1 N K v A =
          concreteCenteredDensityScore 1 N K v A :=
        (coeCorner_centeredDensityScore_one_eq_logScore hN v A hsupport).symm
      _ = concreteCenteredRankOneFirstDensityScore N K v A :=
        coeCorner_centeredDensityScore_one_eq_explicit_external_derived
          hN hboundary v A hsymm hsupport
  rw [hlogOne,
    concreteCenteredLogScore_two_eq_sandwiches_two hboundary v A hsymm hsupport]
  have him := complexCenteredProjectiveTracePair_im_zero_two v
    (concreteCOEY N K A) (concreteCOEY_isHermitian_of_support A hsupport)
  have hsq :
      (complexCenteredProjectiveTracePair v (concreteCOEY N K A) ^ 2).re =
        (complexCenteredProjectiveTracePair v (concreteCOEY N K A)).re ^ 2 := by
    rw [pow_two]
    simp [Complex.mul_re, him]
    ring
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
    concreteCenteredRankOneSecondDensityScore
    concreteCenteredRankOneSecondDensityScoreComplex
  simp [Complex.mul_re, Complex.sub_re, him, hsq]
  ring

end MatrixCalculus

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
