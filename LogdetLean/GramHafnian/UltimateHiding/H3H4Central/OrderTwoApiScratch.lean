import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.CoordinateDensityConditional
import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.ScalarTransport
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

#check CStarMatrix.ofMatrixL
#check CStarMatrix.ofMatrixStarAlgEquiv
#check CStarMatrix.norm_entry_le_norm
#check Matrix.PosDef.isStrictlyPositive
#check Matrix.IsStrictlyPositive.posDef
#check Matrix.PosSemidef.nonneg
#check CStarAlgebra.norm_le_one_iff_of_nonneg
#check CStarAlgebra.norm_mem_spectrum_of_nonneg
#check spectrum.mem_iff
#check IsUnit.sub_iff
#check Real.contDiff_rpow_const_of_le
#check ContDiff.fderiv_right
#check ContDiff.clm_apply
#check HasFDerivAt.comp_hasDerivAt
#check ProperSpace.isCompact_closedBall
#check MeasureTheory.measure_closedBall_lt_top
#check MeasureTheory.integrableOn_const
#check Fin.pos_iff_nonempty
#check frontier_subset_closure

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

@[fun_prop]
theorem contDiff_complex_ofReal_scratch :
    ContDiff ℝ ⊤ (fun r : ℝ => (r : ℂ)) := by
  rw [show (fun r : ℝ => (r : ℂ)) = (Complex.ofRealCLM : ℝ → ℂ) by
    funext r
    exact (Complex.ofRealCLM_apply r).symm]
  exact Complex.ofRealCLM.contDiff

@[fun_prop]
theorem contDiff_complex_star_scratch :
    ContDiff ℝ ⊤ (fun z : ℂ => star z) := by
  rw [show (fun z : ℂ => star z) = (Complex.conjCLE : ℂ → ℂ) by
    funext z
    simpa only [Complex.star_def] using (Complex.conjCLE_apply z).symm]
  exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff

def complexSymmetricMatrixOfCoordinatesLinearMapScratch (N : ℕ) :
    ComplexSymmetricCoordinates N →ₗ[ℝ] ConcreteMatrixState N where
  toFun := complexSymmetricMatrixOfCoordinates
  map_add' x y := by
    ext i j
    by_cases hij : i ≤ j <;>
      simp [complexSymmetricMatrixOfCoordinates, hij]
  map_smul' r x := by
    ext i j
    by_cases hij : i ≤ j <;>
      simp [complexSymmetricMatrixOfCoordinates, hij]

def complexSymmetricMatrixOfCoordinatesCLMScratch (N : ℕ) :
    ComplexSymmetricCoordinates N →L[ℝ] ConcreteMatrixState N :=
  ⟨complexSymmetricMatrixOfCoordinatesLinearMapScratch N,
    (complexSymmetricMatrixOfCoordinatesLinearMapScratch N).continuous_of_finiteDimensional⟩

@[fun_prop]
theorem contDiff_complexSymmetricMatrixOfCoordinates_scratch (N : ℕ) :
    ContDiff ℝ ⊤
      (complexSymmetricMatrixOfCoordinates (N := N)) := by
  change ContDiff ℝ ⊤ (complexSymmetricMatrixOfCoordinatesCLMScratch N)
  exact (complexSymmetricMatrixOfCoordinatesCLMScratch N).contDiff

def concreteMatrixEntryLinearMapScratch (N : ℕ) (i j : Fin N) :
    ConcreteMatrixState N →ₗ[ℝ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def concreteMatrixEntryCLMScratch (N : ℕ) (i j : Fin N) :
    ConcreteMatrixState N →L[ℝ] ℂ :=
  (concreteMatrixEntryLinearMapScratch N i j).toContinuousLinearMap

def complexSymmetricCoordinateEntryCLMScratch
    (N : ℕ) (i j : Fin N) :
    ComplexSymmetricCoordinates N →L[ℝ] ℂ :=
  (concreteMatrixEntryCLMScratch N i j).comp
    (complexSymmetricMatrixOfCoordinatesCLMScratch N)

@[fun_prop]
theorem contDiff_complexSymmetricMatrixOfCoordinates_apply_scratch
    (N : ℕ) (i j : Fin N) :
    ContDiff ℝ ⊤
      (fun x : ComplexSymmetricCoordinates N =>
        complexSymmetricMatrixOfCoordinates x i j) := by
  change ContDiff ℝ ⊤ (complexSymmetricCoordinateEntryCLMScratch N i j)
  exact (complexSymmetricCoordinateEntryCLMScratch N i j).contDiff

theorem coeCornerSupport_iff_cstar_norm_lt_one_scratch
    {N : ℕ} (hN : 1 ≤ N) (C : ConcreteMatrixState N) :
    coeCornerSupport C ↔ ‖C‖ < 1 := by
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
  let a : ConcreteMatrixState N := star C * C
  have ha : 0 ≤ a := by
    exact star_mul_self_nonneg C
  constructor
  · intro hsupport
    have hgap : (1 - a).PosDef := by
      change (1 - C.conjTranspose * C).PosDef at hsupport
      simpa only [a, Matrix.star_eq_conjTranspose] using hsupport
    have hgap_nonneg : 0 ≤ 1 - a := hgap.posSemidef.nonneg
    have ha_le : a ≤ 1 := sub_nonneg.mp hgap_nonneg
    have hnorma_le : ‖a‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg a ha).2 ha_le
    by_contra hnot
    have hCge : 1 ≤ ‖C‖ := le_of_not_gt hnot
    have hnorma : ‖a‖ = ‖C‖ * ‖C‖ := by
      simpa only [a] using CStarRing.norm_star_mul_self (x := C)
    have hnorma_ge : 1 ≤ ‖a‖ := by
      rw [hnorma]
      nlinarith [norm_nonneg C]
    have hnorma_eq : ‖a‖ = 1 := le_antisymm hnorma_le hnorma_ge
    have hspectrum : (1 : ℝ) ∈ spectrum ℝ a := by
      rw [← hnorma_eq]
      exact CStarAlgebra.norm_mem_spectrum_of_nonneg ha
    have hnotunit : ¬IsUnit ((algebraMap ℝ _ 1) - a) :=
      spectrum.mem_iff.mp hspectrum
    apply hnotunit
    simpa using hgap.isUnit
  · intro hnorm
    have hnorma : ‖a‖ = ‖C‖ * ‖C‖ := by
      simpa only [a] using CStarRing.norm_star_mul_self (x := C)
    have hnorma_lt : ‖a‖ < 1 := by
      rw [hnorma]
      nlinarith [norm_nonneg C]
    have ha_upper : a ≤ algebraMap ℝ _ ‖a‖ :=
      (CStarAlgebra.norm_le_iff_le_algebraMap a (norm_nonneg a) ha).1 le_rfl
    have hscalar :
        IsStrictlyPositive
          (algebraMap ℝ (ConcreteMatrixState N) (1 - ‖a‖)) :=
      isStrictlyPositive_algebraMap (sub_pos.mpr hnorma_lt)
    have hlower :
        algebraMap ℝ (ConcreteMatrixState N) (1 - ‖a‖) ≤ 1 - a := by
      simpa only [map_sub, map_one] using sub_le_sub_left ha_upper 1
    have hgap : (1 - a).PosDef :=
      Matrix.isStrictlyPositive_iff_posDef.mp (hscalar.of_le hlower)
    change (1 - C.conjTranspose * C).PosDef
    simpa only [a, Matrix.star_eq_conjTranspose] using hgap

def coeCentralTransportCornerScratch (N : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ConcreteMatrixState N :=
  ((((Real.exp (-2 * p.1) : ℝ) : ℂ)) •
    complexSymmetricMatrixOfCoordinates p.2)

def coeCentralTransportGapScratch (N : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ConcreteMatrixState N :=
  1 - (coeCentralTransportCornerScratch N p).conjTranspose *
    coeCentralTransportCornerScratch N p

def coeCentralTransportDetScratch (N : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ℝ :=
  (Matrix.det (coeCentralTransportGapScratch N p)).re

theorem contDiff_coeCentralTransportDetScratch (N : ℕ) :
    ContDiff ℝ ⊤ (coeCentralTransportDetScratch N) := by
  classical
  rw [show coeCentralTransportDetScratch N =
      fun p : ℝ × ComplexSymmetricCoordinates N =>
        Complex.reCLM (∑ sigma : Equiv.Perm (Fin N),
          Equiv.Perm.sign sigma •
            ∏ i, coeCentralTransportGapScratch N p (sigma i) i) by
    funext p
    unfold coeCentralTransportDetScratch
    simpa only [Complex.reCLM_apply] using
      congrArg Complex.re (Matrix.det_apply (coeCentralTransportGapScratch N p))]
  unfold coeCentralTransportGapScratch coeCentralTransportCornerScratch
  apply Complex.reCLM.contDiff.comp
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply]
  fun_prop

def coeCentralTimeDirectionScratch (N : ℕ) :
    ℝ × ComplexSymmetricCoordinates N := (1, 0)

def coeCentralTransportDetJetOneScratch (N : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ℝ :=
  (fderiv ℝ (coeCentralTransportDetScratch N) p)
    (coeCentralTimeDirectionScratch N)

def coeCentralTransportDetJetTwoScratch (N : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ℝ :=
  (fderiv ℝ (coeCentralTransportDetJetOneScratch N) p)
    (coeCentralTimeDirectionScratch N)

theorem contDiff_coeCentralTransportDetJetOneScratch (N : ℕ) :
    ContDiff ℝ ⊤ (coeCentralTransportDetJetOneScratch N) := by
  unfold coeCentralTransportDetJetOneScratch
  exact ((contDiff_coeCentralTransportDetScratch N).fderiv_right
      (m := ⊤) (by simp)).clm_apply contDiff_const

theorem contDiff_coeCentralTransportDetJetTwoScratch (N : ℕ) :
    ContDiff ℝ ⊤ (coeCentralTransportDetJetTwoScratch N) := by
  unfold coeCentralTransportDetJetTwoScratch
  exact ((contDiff_coeCentralTransportDetJetOneScratch N).fderiv_right
      (m := ⊤) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_coeCentralTransportDetScratch
    (N : ℕ) (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt (fun u => coeCentralTransportDetScratch N (u, x))
      (coeCentralTransportDetJetOneScratch N (t, x)) t := by
  have hp : HasDerivAt
      (fun u : ℝ => (u, x)) (coeCentralTimeDirectionScratch N) t := by
    simpa [coeCentralTimeDirectionScratch] using
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (((contDiff_coeCentralTransportDetScratch N).differentiable (by simp))
    (t, x)).hasFDerivAt.comp_hasDerivAt t hp

theorem hasDerivAt_coeCentralTransportDetJetOneScratch
    (N : ℕ) (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt (fun u => coeCentralTransportDetJetOneScratch N (u, x))
      (coeCentralTransportDetJetTwoScratch N (t, x)) t := by
  have hp : HasDerivAt
      (fun u : ℝ => (u, x)) (coeCentralTimeDirectionScratch N) t := by
    simpa [coeCentralTimeDirectionScratch] using
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (((contDiff_coeCentralTransportDetJetOneScratch N).differentiable (by simp))
    (t, x)).hasFDerivAt.comp_hasDerivAt t hp

theorem hasDerivAt_ite_of_eq_scratch
    {p : ℝ → Prop} [DecidablePred p]
    {f g : ℝ → ℝ} {f' : ℝ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g f' x)
    (hfg : f x = g x) :
    HasDerivAt (fun y => if p y then f y else g y) f' x := by
  rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_tendsto]
  have hf' := hf.hasFDerivAt
  have hg' := hg.hasFDerivAt
  rw [hasFDerivAt_iff_tendsto] at hf' hg'
  have h := Filter.Tendsto.if' (p := p) hf' hg'
  convert h using 1
  funext y
  by_cases hy : p y <;> by_cases hx : p x <;>
    simp only [hy, hx, if_true, if_false] <;> rw [hfg]

def coeCentralRealDimensionScratch (N : ℕ) : ℝ :=
  (N * (N + 1) : ℕ)

def coeCentralTransportCoefficientScratch (N K : ℕ) (t : ℝ) : ℝ :=
  (coeCornerRawMass N K)⁻¹.toReal *
    Real.exp (-2 * coeCentralRealDimensionScratch N * t)

def coeCentralTransportRawJetZeroScratch (N K : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ℝ :=
  coeCentralTransportCoefficientScratch N K p.1 *
    (coeCentralTransportDetScratch N p) ^
      (coeCornerDensityExponent N K)

def coeCentralTransportRawJetOneScratch (N K : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ℝ :=
  coeCentralTransportCoefficientScratch N K p.1 *
    (-2 * coeCentralRealDimensionScratch N *
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K) +
      coeCornerDensityExponent N K *
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K - 1) *
        coeCentralTransportDetJetOneScratch N p)

def coeCentralTransportRawJetTwoScratch (N K : ℕ)
    (p : ℝ × ComplexSymmetricCoordinates N) : ℝ :=
  coeCentralTransportCoefficientScratch N K p.1 *
    (4 * (coeCentralRealDimensionScratch N) ^ 2 *
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K) -
      4 * coeCentralRealDimensionScratch N *
        coeCornerDensityExponent N K *
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K - 1) *
        coeCentralTransportDetJetOneScratch N p +
      coeCornerDensityExponent N K *
        (coeCornerDensityExponent N K - 1) *
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K - 2) *
        (coeCentralTransportDetJetOneScratch N p) ^ 2 +
      coeCornerDensityExponent N K *
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K - 1) *
        coeCentralTransportDetJetTwoScratch N p)

def coeCentralTransportRawJetScratch (N K : ℕ) (j : Fin 3)
    (p : ℝ × ComplexSymmetricCoordinates N) : ℝ :=
  ![coeCentralTransportRawJetZeroScratch N K,
    coeCentralTransportRawJetOneScratch N K,
    coeCentralTransportRawJetTwoScratch N K] j p

def coeCentralTransportOpenSupportScratch (N : ℕ) (t : ℝ) :
    Set (ComplexSymmetricCoordinates N) :=
  {x | ‖coeCentralTransportCornerScratch N (t, x)‖ < 1}

def coeCentralTransportJetScratch (N K : ℕ) (j : Fin 3)
    (t : ℝ) (x : ComplexSymmetricCoordinates N) : ℝ := by
  classical
  exact if x ∈ coeCentralTransportOpenSupportScratch N t then
      coeCentralTransportRawJetScratch N K j (t, x)
    else 0

theorem coeCentral_exponent_two_le_scratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    (2 : ℝ) ≤ coeCornerDensityExponent N K := by
  have hthree := coe_boundary_exponent_gt_three hboundary
  unfold coeCornerDensityExponent
  linarith

theorem coeCentral_exponent_sub_one_one_le_scratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    (1 : ℝ) ≤ coeCornerDensityExponent N K - 1 := by
  linarith [coeCentral_exponent_two_le_scratch hboundary]

theorem coeCentral_exponent_sub_two_nonneg_scratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    (0 : ℝ) ≤ coeCornerDensityExponent N K - 2 := by
  linarith [coeCentral_exponent_two_le_scratch hboundary]

theorem contDiff_coeCentralTransportCoefficient_uncurry_scratch
    (N K : ℕ) :
    ContDiff ℝ ⊤
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        coeCentralTransportCoefficientScratch N K p.1) := by
  unfold coeCentralTransportCoefficientScratch
  fun_prop

theorem contDiff_coeCentralTransportDet_rpow_scratch
    (N K : ℕ) {n : ℕ}
    (h : (n : ℝ) ≤ coeCornerDensityExponent N K) :
    ContDiff ℝ n
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K)) := by
  exact (Real.contDiff_rpow_const_of_le h).comp
    ((contDiff_coeCentralTransportDetScratch N).of_le (by simp))

theorem contDiff_coeCentralTransportDet_rpow_sub_one_scratch
    (N K : ℕ) {n : ℕ}
    (h : (n : ℝ) ≤ coeCornerDensityExponent N K - 1) :
    ContDiff ℝ n
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K - 1)) := by
  exact (Real.contDiff_rpow_const_of_le h).comp
    ((contDiff_coeCentralTransportDetScratch N).of_le (by simp))

theorem contDiff_coeCentralTransportDet_rpow_sub_two_scratch
    (N K : ℕ)
    (h : (0 : ℝ) ≤ coeCornerDensityExponent N K - 2) :
    ContDiff ℝ 0
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        (coeCentralTransportDetScratch N p) ^
          (coeCornerDensityExponent N K - 2)) := by
  exact (Real.contDiff_rpow_const_of_le (n := 0) (by simpa using h)).comp
    ((contDiff_coeCentralTransportDetScratch N).of_le (by simp))

theorem contDiff_two_coeCentralTransportRawJetZeroScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    ContDiff ℝ 2 (coeCentralTransportRawJetZeroScratch N K) := by
  unfold coeCentralTransportRawJetZeroScratch
  exact (contDiff_coeCentralTransportCoefficient_uncurry_scratch N K).of_le
      (by simp) |>.mul
    (contDiff_coeCentralTransportDet_rpow_scratch N K
      (coeCentral_exponent_two_le_scratch hboundary))

theorem contDiff_one_coeCentralTransportRawJetOneScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    ContDiff ℝ 1 (coeCentralTransportRawJetOneScratch N K) := by
  unfold coeCentralTransportRawJetOneScratch
  have ha := (contDiff_coeCentralTransportCoefficient_uncurry_scratch N K).of_le
    (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)
  have hq := contDiff_coeCentralTransportDet_rpow_scratch N K (n := 1)
    (by simpa only [Nat.cast_one] using
      (show (1 : ℝ) ≤ coeCornerDensityExponent N K by
        linarith [coeCentral_exponent_two_le_scratch hboundary]))
  have hqm := contDiff_coeCentralTransportDet_rpow_sub_one_scratch N K (n := 1)
    (by simpa only [Nat.cast_one] using
      coeCentral_exponent_sub_one_one_le_scratch hboundary)
  have hqone := (contDiff_coeCentralTransportDetJetOneScratch N).of_le
    (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)
  have hterm0 : ContDiff ℝ 1
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        -2 * coeCentralRealDimensionScratch N *
          (coeCentralTransportDetScratch N p) ^
            (coeCornerDensityExponent N K)) :=
    contDiff_const.mul hq
  have hterm1 : ContDiff ℝ 1
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        coeCornerDensityExponent N K *
          (coeCentralTransportDetScratch N p) ^
            (coeCornerDensityExponent N K - 1) *
          coeCentralTransportDetJetOneScratch N p) :=
    (contDiff_const.mul hqm).mul hqone
  exact ha.mul (hterm0.add hterm1)

theorem continuous_coeCentralTransportRawJetTwoScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    Continuous (coeCentralTransportRawJetTwoScratch N K) := by
  unfold coeCentralTransportRawJetTwoScratch
  have ha := (contDiff_coeCentralTransportCoefficient_uncurry_scratch N K).of_le
    (show (0 : WithTop ℕ∞) ≤ ⊤ by simp)
  have hq := contDiff_coeCentralTransportDet_rpow_scratch N K
    (n := 0) (by
      simpa only [Nat.cast_zero] using
        (show (0 : ℝ) ≤ coeCornerDensityExponent N K by
          linarith [coeCentral_exponent_two_le_scratch hboundary]))
  have hqm := contDiff_coeCentralTransportDet_rpow_sub_one_scratch N K
    (n := 0) (by
      simpa only [Nat.cast_zero] using
        (show (0 : ℝ) ≤ coeCornerDensityExponent N K - 1 by
          linarith [coeCentral_exponent_sub_one_one_le_scratch hboundary]))
  have hqmm := contDiff_coeCentralTransportDet_rpow_sub_two_scratch N K
    (coeCentral_exponent_sub_two_nonneg_scratch hboundary)
  have hqone := (contDiff_coeCentralTransportDetJetOneScratch N).of_le
    (show (0 : WithTop ℕ∞) ≤ ⊤ by simp)
  have hqtwo := (contDiff_coeCentralTransportDetJetTwoScratch N).of_le
    (show (0 : WithTop ℕ∞) ≤ ⊤ by simp)
  have hterm0 : ContDiff ℝ 0
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        4 * (coeCentralRealDimensionScratch N) ^ 2 *
          (coeCentralTransportDetScratch N p) ^
            (coeCornerDensityExponent N K)) :=
    contDiff_const.mul hq
  have hterm1 : ContDiff ℝ 0
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        4 * coeCentralRealDimensionScratch N *
          coeCornerDensityExponent N K *
          (coeCentralTransportDetScratch N p) ^
            (coeCornerDensityExponent N K - 1) *
          coeCentralTransportDetJetOneScratch N p) :=
    ((contDiff_const.mul hqm).mul hqone)
  have hterm2 : ContDiff ℝ 0
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        coeCornerDensityExponent N K *
          (coeCornerDensityExponent N K - 1) *
          (coeCentralTransportDetScratch N p) ^
            (coeCornerDensityExponent N K - 2) *
          (coeCentralTransportDetJetOneScratch N p) ^ 2) :=
    (contDiff_const.mul hqmm).mul (hqone.pow 2)
  have hterm3 : ContDiff ℝ 0
      (fun p : ℝ × ComplexSymmetricCoordinates N =>
        coeCornerDensityExponent N K *
          (coeCentralTransportDetScratch N p) ^
            (coeCornerDensityExponent N K - 1) *
          coeCentralTransportDetJetTwoScratch N p) :=
    (contDiff_const.mul hqm).mul hqtwo
  exact (ha.mul (((hterm0.sub hterm1).add hterm2).add hterm3)).continuous

theorem hasDerivAt_coeCentralTransportCoefficientScratch
    (N K : ℕ) (t : ℝ) :
    HasDerivAt (coeCentralTransportCoefficientScratch N K)
      (-2 * coeCentralRealDimensionScratch N *
        coeCentralTransportCoefficientScratch N K t) t := by
  unfold coeCentralTransportCoefficientScratch
  have hinner : HasDerivAt
      (fun u : ℝ => -2 * coeCentralRealDimensionScratch N * u)
      (-2 * coeCentralRealDimensionScratch N) t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul
        (-2 * coeCentralRealDimensionScratch N)
  have hexp := (Real.hasDerivAt_exp
    (-2 * coeCentralRealDimensionScratch N * t)).comp t hinner
  convert hexp.const_mul ((coeCornerRawMass N K)⁻¹.toReal) using 1 <;>
    first | rfl | ring | exact Subsingleton.elim _ _

theorem hasDerivAt_coeCentralTransportRawJetZeroScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt
      (fun u => coeCentralTransportRawJetZeroScratch N K (u, x))
      (coeCentralTransportRawJetOneScratch N K (t, x)) t := by
  have hqpow :=
    (hasDerivAt_coeCentralTransportDetScratch N x t).rpow_const
      (p := coeCornerDensityExponent N K)
      (Or.inr (by linarith [coeCentral_exponent_two_le_scratch hboundary]))
  have h := (hasDerivAt_coeCentralTransportCoefficientScratch N K t).mul hqpow
  convert h using 1 <;>
    first
    | rfl
    | exact Subsingleton.elim _ _
    | (unfold coeCentralTransportRawJetOneScratch; ring)

theorem hasDerivAt_coeCentralTransportRawJetOneScratch
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt
      (fun u => coeCentralTransportRawJetOneScratch N K (u, x))
      (coeCentralTransportRawJetTwoScratch N K (t, x)) t := by
  have hq := hasDerivAt_coeCentralTransportDetScratch N x t
  have hqone := hasDerivAt_coeCentralTransportDetJetOneScratch N x t
  have hqpow := hq.rpow_const
    (p := coeCornerDensityExponent N K)
    (Or.inr (by linarith [coeCentral_exponent_two_le_scratch hboundary]))
  have hqpowm := hq.rpow_const
    (p := coeCornerDensityExponent N K - 1)
    (Or.inr (coeCentral_exponent_sub_one_one_le_scratch hboundary))
  have hbracket :=
    (hqpow.const_mul (-2 * coeCentralRealDimensionScratch N)).add
      ((hqpowm.mul hqone).const_mul (coeCornerDensityExponent N K))
  have h := (hasDerivAt_coeCentralTransportCoefficientScratch N K t).mul hbracket
  convert h using 1 <;>
    first
    | rfl
    | exact Subsingleton.elim _ _
    | (funext u
       unfold coeCentralTransportRawJetOneScratch
       simp only [Pi.add_apply, Pi.mul_apply]
       ring)
    | (unfold coeCentralTransportRawJetTwoScratch
       simp only [Pi.add_apply, Pi.mul_apply]
       rw [show coeCornerDensityExponent N K - 1 - 1 =
           coeCornerDensityExponent N K - 2 by ring]
       ring)

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
