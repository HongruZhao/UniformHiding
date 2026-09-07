import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnConcrete
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Right-unitary transitivity on complex row-Gram fibers

This is the finite-dimensional orbit lemma needed in the internal H1 proof.
It includes rank-deficient matrices: equality of the Hermitian row Gram
matrices produces an isometry between the spans of the two row families,
which is extended to the whole column space and represented by a unitary
matrix.
-/

open scoped ComplexConjugate InnerProductSpace ENNReal MeasureTheory Matrix
  BoundedContinuousFunction
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.CurrentPRL

local instance h1MatrixBorelSpace (N m : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin m) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin m → ℂ))

/-- The linear combination map associated with a finite vector family. -/
def rowFamilyCombination {n E : Type*} [Fintype n]
    [AddCommMonoid E] [Module ℂ E] (u : n → E) :
    (n → ℂ) →ₗ[ℂ] E where
  toFun a := ∑ i, a i • u i
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_eq_mul, smul_smul]

theorem rowFamilyCombination_inner_eq
    {n E : Type*} [Fintype n]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : n → E)
    (hinner : ∀ i j, ⟪u i, u j⟫_ℂ = ⟪v i, v j⟫_ℂ)
    (a b : n → ℂ) :
    ⟪rowFamilyCombination u a, rowFamilyCombination u b⟫_ℂ =
      ⟪rowFamilyCombination v a, rowFamilyCombination v b⟫_ℂ := by
  change ⟪∑ i, a i • u i, ∑ j, b j • u j⟫_ℂ =
    ⟪∑ i, a i • v i, ∑ j, b j • v j⟫_ℂ
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hinner]

/-- Two finite vector families with the same Gram matrix are carried to one
another by a unitary operator on the ambient finite-dimensional complex
inner-product space.  No linear-independence hypothesis is needed. -/
theorem exists_linearIsometryEquiv_map_family_of_inner_eq
    {n E : Type*} [Fintype n]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (u v : n → E)
    (hinner : ∀ i j, ⟪u i, u j⟫_ℂ = ⟪v i, v j⟫_ℂ) :
    ∃ T : E ≃ₗᵢ[ℂ] E, ∀ i, T (u i) = v i := by
  classical
  let fu : (n → ℂ) →ₗ[ℂ] E := rowFamilyCombination u
  let fv : (n → ℂ) →ₗ[ℂ] E := rowFamilyCombination v
  have hcomb (a b : n → ℂ) :
      ⟪fu a, fu b⟫_ℂ = ⟪fv a, fv b⟫_ℂ :=
    rowFamilyCombination_inner_eq u v hinner a b
  have hker : LinearMap.ker fu = LinearMap.ker fv := by
    ext a
    simp only [LinearMap.mem_ker]
    constructor
    · intro ha
      have hz : ⟪fv a, fv a⟫_ℂ = 0 := by
        rw [← hcomb a a, ha]
        simp
      exact inner_self_eq_zero.mp hz
    · intro ha
      have hz : ⟪fu a, fu a⟫_ℂ = 0 := by
        rw [hcomb a a, ha]
        simp
      exact inner_self_eq_zero.mp hz
  let qeq : ((n → ℂ) ⧸ LinearMap.ker fu) ≃ₗ[ℂ]
      ((n → ℂ) ⧸ LinearMap.ker fv) :=
    Submodule.quotEquivOfEq _ _ hker
  let e : LinearMap.range fu ≃ₗ[ℂ] LinearMap.range fv :=
    fu.quotKerEquivRange.symm |>.trans (qeq.trans fv.quotKerEquivRange)
  have he_apply (a : n → ℂ) :
      e ⟨fu a, ⟨a, rfl⟩⟩ = ⟨fv a, ⟨a, rfl⟩⟩ := by
    let xa : LinearMap.range fu := ⟨fu a, ⟨a, rfl⟩⟩
    let ya : LinearMap.range fv := ⟨fv a, ⟨a, rfl⟩⟩
    change e xa = ya
    change fv.quotKerEquivRange
        (qeq (fu.quotKerEquivRange.symm xa)) = ya
    have hpre : fu.quotKerEquivRange.symm xa =
        (LinearMap.ker fu).mkQ a := by
      apply fu.quotKerEquivRange.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (LinearMap.quotKerEquivRange_apply_mk fu a).symm
    rw [hpre]
    rw [show qeq ((LinearMap.ker fu).mkQ a) =
        (LinearMap.ker fv).mkQ a by
      exact Submodule.quotEquivOfEq_mk _ _ hker a]
    apply Subtype.ext
    exact LinearMap.quotKerEquivRange_apply_mk fv a
  have he_inner (x y : LinearMap.range fu) :
      ⟪e x, e y⟫_ℂ = ⟪x, y⟫_ℂ := by
    rcases x.2 with ⟨a, ha⟩
    rcases y.2 with ⟨b, hb⟩
    have hx : x = ⟨fu a, ⟨a, rfl⟩⟩ := Subtype.ext ha.symm
    have hy : y = ⟨fu b, ⟨b, rfl⟩⟩ := Subtype.ext hb.symm
    rw [hx, hy, he_apply, he_apply]
    change ⟪fv a, fv b⟫_ℂ = ⟪fu a, fu b⟫_ℂ
    exact (hcomb a b).symm
  let eIso : LinearMap.range fu ≃ₗᵢ[ℂ] LinearMap.range fv :=
    e.isometryOfInner he_inner
  let L : LinearMap.range fu →ₗᵢ[ℂ] E :=
    (LinearMap.range fv).subtypeₗᵢ.comp eIso.toLinearIsometry
  let A : E →ₗᵢ[ℂ] E := L.extend
  let T : E ≃ₗᵢ[ℂ] E := A.toLinearIsometryEquiv rfl
  refine ⟨T, fun i ↦ ?_⟩
  let a : n → ℂ := Pi.single i 1
  have hfua : fu a = u i := by
    simp [fu, rowFamilyCombination, a]
  have hfva : fv a = v i := by
    simp [fv, rowFamilyCombination, a]
  let ui : LinearMap.range fu := ⟨fu a, ⟨a, rfl⟩⟩
  have hA : A (fu a) = L ui := by
    simpa [ui, A] using LinearIsometry.extend_apply L ui
  change A (u i) = v i
  rw [← hfua, ← hfva, hA]
  change ((eIso ui : LinearMap.range fv) : E) = fv a
  change ((e ui : LinearMap.range fv) : E) = fv a
  rw [show ui = ⟨fu a, ⟨a, rfl⟩⟩ from rfl, he_apply]

/-- A matrix row as a vector in the Euclidean column space. -/
def h1MatrixRow {N m : ℕ} (X : Matrix (Fin N) (Fin m) ℂ)
    (i : Fin N) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 (X i)

@[simp]
theorem h1MatrixRow_apply {N m : ℕ}
    (X : Matrix (Fin N) (Fin m) ℂ) (i : Fin N) (j : Fin m) :
    h1MatrixRow X i j = X i j := rfl

private theorem exists_rightUnitary_of_row_map
    {N m : ℕ} (X Y : Matrix (Fin N) (Fin m) ℂ)
    (T : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin m))
    (hT : ∀ i, T (h1MatrixRow X i) = h1MatrixRow Y i) :
    ∃ V : Matrix.unitaryGroup (Fin m) ℂ,
      X * (V : Matrix (Fin m) (Fin m) ℂ) = Y := by
  let b := EuclideanSpace.basisFun (Fin m) ℂ
  let A : Matrix (Fin m) (Fin m) ℂ :=
    T.toMatrix b.toBasis b.toBasis
  let U : Matrix.unitaryGroup (Fin m) ℂ :=
    ⟨A, T.toMatrix_mem_unitaryGroup b b⟩
  let V : Matrix.unitaryGroup (Fin m) ℂ :=
    Matrix.UnitaryGroup.transpose U
  refine ⟨V, ?_⟩
  ext i j
  have hcoord := congrArg
    (fun z : EuclideanSpace ℂ (Fin m) ↦ z j) (hT i)
  have hcoord' : (T (h1MatrixRow X i)) j = Y i j := hcoord
  have hmul := T.toLinearEquiv.toLinearMap.toMatrix_mulVec_repr
    b.toBasis b.toBasis (h1MatrixRow X i)
  have hentry := congrFun hmul j
  change (X * (V : Matrix (Fin m) (Fin m) ℂ)) i j = Y i j
  rw [Matrix.mul_apply]
  change (∑ k, X i k * A j k) = Y i j
  have hentry' : (∑ k, A j k * X i k) =
      (T (h1MatrixRow X i)) j := by
    simpa [A, b, Matrix.mulVec, dotProduct] using hentry
  rw [← hcoord', ← hentry']
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

/-- Equal Hermitian row-Gram matrices lie in the same right-unitary orbit.
This is valid even on singular fibers. -/
theorem exists_rightUnitary_of_hermitianRowGram_eq
    {N m : ℕ} (X Y : Matrix (Fin N) (Fin m) ℂ)
    (hgram : X * X.conjTranspose = Y * Y.conjTranspose) :
    ∃ V : Matrix.unitaryGroup (Fin m) ℂ,
      X * (V : Matrix (Fin m) (Fin m) ℂ) = Y := by
  have hinner (i j : Fin N) :
      ⟪h1MatrixRow X i, h1MatrixRow X j⟫_ℂ =
        ⟪h1MatrixRow Y i, h1MatrixRow Y j⟫_ℂ := by
    have hij := congrArg
      (fun A : Matrix (Fin N) (Fin N) ℂ ↦ A j i) hgram
    simpa [h1MatrixRow, PiLp.inner_apply, RCLike.inner_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm] using hij
  obtain ⟨T, hT⟩ := exists_linearIsometryEquiv_map_family_of_inner_eq
    (h1MatrixRow X) (h1MatrixRow Y) hinner
  exact exists_rightUnitary_of_row_map X Y T hT

/-! ## Haar averaging on right-unitary row orbits -/

/-- Right multiplication of a rectangular matrix by a unitary matrix. -/
def h1RightUnitaryAction {N m : ℕ}
    (V : Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin N) (Fin m) ℂ) : Matrix (Fin N) (Fin m) ℂ :=
  X * (V : Matrix (Fin m) (Fin m) ℂ)

theorem continuous_h1RightUnitaryAction {N m : ℕ}
    (V : Matrix.unitaryGroup (Fin m) ℂ) :
    Continuous (h1RightUnitaryAction (N := N) V) := by
  unfold h1RightUnitaryAction
  fun_prop

theorem continuous_uncurry_h1RightUnitaryAction (N m : ℕ) :
    Continuous (fun p : Matrix (Fin N) (Fin m) ℂ ×
        Matrix.unitaryGroup (Fin m) ℂ ↦
      h1RightUnitaryAction p.2 p.1) := by
  unfold h1RightUnitaryAction
  fun_prop

theorem measurable_uncurry_h1RightUnitaryAction (N m : ℕ) :
    Measurable (fun p : Matrix (Fin N) (Fin m) ℂ ×
        Matrix.unitaryGroup (Fin m) ℂ ↦
      h1RightUnitaryAction p.2 p.1) := by
  unfold h1RightUnitaryAction
  exact measurable_complexMatrix_mul measurable_fst
    (measurable_subtype_coe.comp measurable_snd)

def h1RightUnitaryActionContinuousMap (N m : ℕ) :
    ContinuousMap
      (Matrix (Fin N) (Fin m) ℂ × Matrix.unitaryGroup (Fin m) ℂ)
      (Matrix (Fin N) (Fin m) ℂ) :=
  ⟨fun p ↦ h1RightUnitaryAction p.2 p.1,
    continuous_uncurry_h1RightUnitaryAction N m⟩

theorem h1RightUnitaryAction_comp {N m : ℕ}
    (V W : Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin N) (Fin m) ℂ) :
    h1RightUnitaryAction V (h1RightUnitaryAction W X) =
      h1RightUnitaryAction (W * V) X := by
  simp [h1RightUnitaryAction, Matrix.mul_assoc]

/-- Haar-average of a bounded continuous test function along a rectangular
matrix's right-unitary orbit. -/
def h1RowOrbitAverage {N m : ℕ}
    (f : Matrix (Fin N) (Fin m) ℂ →ᵇ ℝ)
    (X : Matrix (Fin N) (Fin m) ℂ) : ℝ :=
  ∫ V : Matrix.unitaryGroup (Fin m) ℂ,
    f (h1RightUnitaryAction V X) ∂(unitaryHaarProbabilityMeasure m)

theorem stronglyMeasurable_h1RowOrbitAverage {N m : ℕ}
    (f : Matrix (Fin N) (Fin m) ℂ →ᵇ ℝ) :
    StronglyMeasurable (h1RowOrbitAverage f) := by
  let μG : Measure (Matrix.unitaryGroup (Fin m) ℂ) :=
    unitaryHaarProbabilityMeasure m
  letI : IsProbabilityMeasure μG :=
    unitaryHaarProbabilityMeasure_isProbability m
  have hjoint : Measurable
      (fun p : Matrix (Fin N) (Fin m) ℂ ×
          Matrix.unitaryGroup (Fin m) ℂ ↦
        f (h1RightUnitaryAction p.2 p.1)) :=
    f.continuous.measurable.comp
      (measurable_uncurry_h1RightUnitaryAction N m)
  change StronglyMeasurable (fun X : Matrix (Fin N) (Fin m) ℂ ↦
    ∫ V : Matrix.unitaryGroup (Fin m) ℂ,
      f (h1RightUnitaryAction V X) ∂μG)
  exact hjoint.stronglyMeasurable.integral_prod_right'

theorem measurable_h1RowOrbitAverage {N m : ℕ}
    (f : Matrix (Fin N) (Fin m) ℂ →ᵇ ℝ) :
    Measurable (h1RowOrbitAverage f) :=
  (stronglyMeasurable_h1RowOrbitAverage f).measurable

/-- The orbit average depends only on the Hermitian row Gram matrix. -/
theorem h1RowOrbitAverage_eq_of_hermitianRowGram_eq
    {N m : ℕ}
    (f : Matrix (Fin N) (Fin m) ℂ →ᵇ ℝ)
    (X Y : Matrix (Fin N) (Fin m) ℂ)
    (hgram : X * X.conjTranspose = Y * Y.conjTranspose) :
    h1RowOrbitAverage f X = h1RowOrbitAverage f Y := by
  obtain ⟨W, hW⟩ :=
    exists_rightUnitary_of_hermitianRowGram_eq X Y hgram
  let μG := unitaryHaarProbabilityMeasure m
  letI : Measure.IsHaarMeasure μG :=
    canonicalUnitaryHaarProbabilityFamily.isHaar m
  have hW' : h1RightUnitaryAction W X = Y := hW
  rw [← hW']
  unfold h1RowOrbitAverage
  simpa only [h1RightUnitaryAction_comp] using
    (integral_mul_left_eq_self
      (μ := μG)
      (fun V : Matrix.unitaryGroup (Fin m) ℂ ↦
        f (h1RightUnitaryAction V X)) W).symm

theorem integral_comp_h1RightUnitaryAction_eq_of_map_eq
    {N m : ℕ} {μ : Measure (Matrix (Fin N) (Fin m) ℂ)}
    (f : Matrix (Fin N) (Fin m) ℂ →ᵇ ℝ)
    (V : Matrix.unitaryGroup (Fin m) ℂ)
    (hinv : Measure.map (h1RightUnitaryAction (N := N) V) μ = μ) :
    (∫ X, f (h1RightUnitaryAction V X) ∂μ) = ∫ X, f X ∂μ := by
  calc
    (∫ X, f (h1RightUnitaryAction V X) ∂μ) =
        ∫ X, f X
          ∂Measure.map (h1RightUnitaryAction (N := N) V) μ := by
      rw [integral_map
        (continuous_h1RightUnitaryAction (N := N) V).measurable.aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
    _ = ∫ X, f X ∂μ := by rw [hinv]

/-- Averaging along right-unitary orbits does not change the integral under
an invariant probability measure. -/
theorem integral_eq_h1RowOrbitAverage_of_invariant
    {N m : ℕ} (μ : Measure (Matrix (Fin N) (Fin m) ℂ))
    [IsProbabilityMeasure μ]
    (hinv : ∀ V : Matrix.unitaryGroup (Fin m) ℂ,
      Measure.map (h1RightUnitaryAction (N := N) V) μ = μ)
    (f : Matrix (Fin N) (Fin m) ℂ →ᵇ ℝ) :
    (∫ X, f X ∂μ) = ∫ X, h1RowOrbitAverage f X ∂μ := by
  let μG : Measure (Matrix.unitaryGroup (Fin m) ℂ) :=
    unitaryHaarProbabilityMeasure m
  letI : IsProbabilityMeasure μG :=
    unitaryHaarProbabilityMeasure_isProbability m
  let F : Matrix (Fin N) (Fin m) ℂ ×
      Matrix.unitaryGroup (Fin m) ℂ →ᵇ ℝ :=
    f.compContinuous (h1RightUnitaryActionContinuousMap N m)
  have hFint : Integrable
      (Function.uncurry fun X : Matrix (Fin N) (Fin m) ℂ ↦
        fun V : Matrix.unitaryGroup (Fin m) ℂ ↦
          f (h1RightUnitaryAction V X)) (μ.prod μG) := by
    have hmeas : AEStronglyMeasurable
        (Function.uncurry fun X : Matrix (Fin N) (Fin m) ℂ ↦
          fun V : Matrix.unitaryGroup (Fin m) ℂ ↦
            f (h1RightUnitaryAction V X)) (μ.prod μG) :=
      (f.continuous.measurable.comp
        (measurable_uncurry_h1RightUnitaryAction N m)).aestronglyMeasurable
    refine ⟨hmeas, (hasFiniteIntegral_def _ _).mp ?_⟩
    calc
      ∫⁻ p, ‖f (h1RightUnitaryAction p.2 p.1)‖₊ ∂(μ.prod μG) ≤
          ‖F‖₊ * ((μ.prod μG) Set.univ) :=
        F.lintegral_nnnorm_le (μ.prod μG)
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top
        (measure_lt_top (μ.prod μG) Set.univ)
  have hswap :
      (∫ X, h1RowOrbitAverage f X ∂μ) =
        ∫ V : Matrix.unitaryGroup (Fin m) ℂ,
          (∫ X, f (h1RightUnitaryAction V X) ∂μ) ∂μG := by
    simpa only [h1RowOrbitAverage, μG] using integral_integral_swap hFint
  rw [hswap]
  simp_rw [integral_comp_h1RightUnitaryAction_eq_of_map_eq f _ (hinv _)]
  simp

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
