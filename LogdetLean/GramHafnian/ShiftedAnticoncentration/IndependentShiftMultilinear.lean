import LogdetLean.GramHafnian.ShiftedAnticoncentration.GramHafnianMultilinear
import LogdetLean.GramHafnian.ShiftedAnticoncentration.IndependentShiftGaussianKernel
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Independent shifts of finite Gaussian multilinear forms

A noncentral circular Gaussian linear form has no larger radial Laplace
transform than its centered counterpart.  This file applies that one-column
kernel successively to a finite continuous multilinear form.  At every step,
the shifted column is integrated out and a fresh, unshifted Gaussian column
is reintroduced before the remaining columns are treated.

The final specialization applies this replacement theorem to the continuous
multilinear realization of the Gaussian Gram hafnian.  The random shift may
have arbitrary dependence among its columns; only independence between the
whole shift matrix and the iid Gaussian matrix is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

private def continuousLinearTransposeCoefficients
    {k : ℕ} (L : (Fin k → ℂ) →L[ℂ] ℂ) : Fin k → ℂ :=
  fun i => L (Pi.single i 1)

private theorem continuousLinear_eq_iidCircularTransposeLinearForm
    {k : ℕ} (L : (Fin k → ℂ) →L[ℂ] ℂ) (x : Fin k → ℂ) :
    L x =
      iidCircularTransposeLinearForm
        (continuousLinearTransposeCoefficients L) x := by
  classical
  calc
    L x = L (∑ i, (x i) • Pi.single i 1) :=
      congrArg L (pi_eq_sum_univ' x)
    _ = ∑ i, L ((x i) • Pi.single i 1) := by simp
    _ = iidCircularTransposeLinearForm
        (continuousLinearTransposeCoefficients L) x := by
      simp only [map_smul, iidCircularTransposeLinearForm,
        continuousLinearTransposeCoefficients, smul_eq_mul]

/-- The one-column replacement step.  The last equality in the proof
explicitly represents the upper bound by an integral over a fresh centered
circular Gaussian column. -/
theorem continuousLinear_circularGaussian_add_laplace_le
    {k : ℕ} (L : (Fin k → ℂ) →L[ℂ] ℂ)
    (b : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Fin k → ℂ,
        Real.exp (-t * ‖L x + b‖ ^ 2) ∂circularGaussianVector k) ≤
      ∫ x : Fin k → ℂ,
        Real.exp (-t * ‖L x‖ ^ 2) ∂circularGaussianVector k := by
  let y := continuousLinearTransposeCoefficients L
  calc
    (∫ x : Fin k → ℂ,
        Real.exp (-t * ‖L x + b‖ ^ 2) ∂circularGaussianVector k) =
      ∫ x : Fin k → ℂ,
        Real.exp (-t * ‖iidCircularTransposeLinearForm y x + b‖ ^ 2)
          ∂(Measure.pi fun _ : Fin k => circularGaussian) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [continuousLinear_eq_iidCircularTransposeLinearForm]
    _ ≤ (1 + t * circularCoefficientEnergy y)⁻¹ :=
      integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add_le
        y b t ht
    _ = ∫ x : Fin k → ℂ,
        Real.exp (-t * ‖iidCircularTransposeLinearForm y x‖ ^ 2)
          ∂(Measure.pi fun _ : Fin k => circularGaussian) :=
      (integral_exp_neg_norm_sq_iidCircularTransposeLinearForm y t ht).symm
    _ = ∫ x : Fin k → ℂ,
        Real.exp (-t * ‖L x‖ ^ 2) ∂circularGaussianVector k := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [continuousLinear_eq_iidCircularTransposeLinearForm]

private theorem integrable_multilinear_laplace
    {n k : ℕ}
    (F : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin k → ℂ) ℂ)
    (Z : Fin n → Fin k → ℂ) (w : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    Integrable
      (fun X : Fin n → Fin k → ℂ =>
        Real.exp (-t * ‖F (fun i => X i + Z i) - w‖ ^ 2))
      (Measure.pi fun _ : Fin n => circularGaussianVector k) := by
  have hcont : Continuous
      (fun X : Fin n → Fin k → ℂ =>
        Real.exp (-t * ‖F (fun i => X i + Z i) - w‖ ^ 2)) := by
    fun_prop
  apply Integrable.of_bound hcont.aestronglyMeasurable 1
  filter_upwards [] with X
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))

private theorem integrable_multilinear_centered_laplace
    {n k : ℕ}
    (F : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin k → ℂ) ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable
      (fun X : Fin n → Fin k → ℂ =>
        Real.exp (-t * ‖F X‖ ^ 2))
      (Measure.pi fun _ : Fin n => circularGaussianVector k) := by
  simpa using
    integrable_multilinear_laplace F
      (fun _ : Fin n => (0 : Fin k → ℂ)) 0 t ht

private theorem integral_pi_succ_eq_prod
    {n k : ℕ} (G : (Fin (n + 1) → Fin k → ℂ) → ℝ) :
    (∫ X : Fin (n + 1) → Fin k → ℂ, G X
        ∂(Measure.pi fun _ : Fin (n + 1) => circularGaussianVector k)) =
      ∫ p : (Fin k → ℂ) × (Fin n → Fin k → ℂ),
        G (Fin.cons p.1 p.2)
        ∂((circularGaussianVector k).prod
          (Measure.pi fun _ : Fin n => circularGaussianVector k)) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Fin k → ℂ) 0
  have h :=
    ((measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => circularGaussianVector k) 0).symm).integral_comp' G
  have he (p : (Fin k → ℂ) × (Fin n → Fin k → ℂ)) :
      e.symm p = Fin.cons p.1 p.2 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv]
  calc
    (∫ X : Fin (n + 1) → Fin k → ℂ, G X
        ∂(Measure.pi fun _ : Fin (n + 1) => circularGaussianVector k)) =
      ∫ p : (Fin k → ℂ) × (Fin n → Fin k → ℂ), G (e.symm p)
        ∂((circularGaussianVector k).prod
          (Measure.pi fun _ : Fin n => circularGaussianVector k)) := h.symm
    _ = ∫ p : (Fin k → ℂ) × (Fin n → Fin k → ℂ),
        G (Fin.cons p.1 p.2)
        ∂((circularGaussianVector k).prod
          (Measure.pi fun _ : Fin n => circularGaussianVector k)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [he]

/-- Finite product-Gaussian replacement for a continuous multilinear form.
The shift is deterministic here.  The proof replaces the columns one at a
time, and each one-column kernel is rewritten as an integral over a fresh
unshifted Gaussian column before the induction proceeds. -/
theorem continuousMultilinearMap_productGaussian_shift_laplace_le
    {n k : ℕ} (hn : 1 ≤ n)
    (F : ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin k → ℂ) ℂ)
    (Z : Fin n → Fin k → ℂ) (w : ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ X : Fin n → Fin k → ℂ,
        Real.exp (-t * ‖F (fun i => X i + Z i) - w‖ ^ 2)
        ∂(Measure.pi fun _ : Fin n => circularGaussianVector k)) ≤
      ∫ X : Fin n → Fin k → ℂ,
        Real.exp (-t * ‖F X‖ ^ 2)
        ∂(Measure.pi fun _ : Fin n => circularGaussianVector k) := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          let L : (Fin k → ℂ) →L[ℂ] ℂ :=
            F.toContinuousLinearMap
              (fun _ : Fin 1 => (0 : Fin k → ℂ)) 0
          have hL (x : Fin k → ℂ) :
              L x = F (fun _ : Fin 1 => x) := by
            rw [show L x =
                F (Function.update
                  (fun _ : Fin 1 => (0 : Fin k → ℂ)) 0 x) by
              exact ContinuousMultilinearMap.toContinuousLinearMap_apply
                F (fun _ : Fin 1 => (0 : Fin k → ℂ)) 0 x]
            congr 1
            funext i
            fin_cases i
            simp
          have hleft :
              (fun X : Fin 1 → Fin k → ℂ =>
                Real.exp (-t * ‖F (fun i => X i + Z i) - w‖ ^ 2)) =
              fun X : Fin 1 → Fin k → ℂ =>
                Real.exp
                  (-t * ‖L (X 0) + (L (Z 0) - w)‖ ^ 2) := by
            funext X
            have harg :
                (fun i : Fin 1 => X i + Z i) =
                  fun _ : Fin 1 => X 0 + Z 0 := by
              funext i
              fin_cases i
              rfl
            rw [harg, ← hL (X 0 + Z 0), map_add]
            simp only [sub_eq_add_neg, add_assoc]
          have hright :
              (fun X : Fin 1 → Fin k → ℂ =>
                Real.exp (-t * ‖F X‖ ^ 2)) =
              fun X : Fin 1 → Fin k → ℂ =>
                Real.exp (-t * ‖L (X 0)‖ ^ 2) := by
            funext X
            have harg : X = fun _ : Fin 1 => X 0 := by
              funext i
              fin_cases i
              rfl
            rw [harg, ← hL (X 0)]
          change (∫ X : Fin 1 → Fin k → ℂ,
              Real.exp (-t * ‖F (fun i => X i + Z i) - w‖ ^ 2)
              ∂(Measure.pi fun _ : Fin 1 => circularGaussianVector k)) ≤
            ∫ X : Fin 1 → Fin k → ℂ,
              Real.exp (-t * ‖F X‖ ^ 2)
              ∂(Measure.pi fun _ : Fin 1 => circularGaussianVector k)
          rw [hleft, hright]
          have hEvalLeft : AEStronglyMeasurable
              (fun x : Fin k → ℂ =>
                Real.exp (-t * ‖L x + (L (Z 0) - w)‖ ^ 2))
              (circularGaussianVector k) :=
            (by fun_prop : Continuous (fun x : Fin k → ℂ =>
              Real.exp (-t * ‖L x + (L (Z 0) - w)‖ ^ 2))).aestronglyMeasurable
          have hEvalRight : AEStronglyMeasurable
              (fun x : Fin k → ℂ => Real.exp (-t * ‖L x‖ ^ 2))
              (circularGaussianVector k) :=
            (by fun_prop : Continuous (fun x : Fin k → ℂ =>
              Real.exp (-t * ‖L x‖ ^ 2))).aestronglyMeasurable
          calc
            (∫ X : Fin 1 → Fin k → ℂ,
                Real.exp (-t * ‖L (X 0) + (L (Z 0) - w)‖ ^ 2)
                ∂(Measure.pi fun _ : Fin 1 => circularGaussianVector k)) =
              ∫ x : Fin k → ℂ,
                Real.exp (-t * ‖L x + (L (Z 0) - w)‖ ^ 2)
                ∂circularGaussianVector k :=
              integral_comp_eval (μ := fun _ : Fin 1 => circularGaussianVector k)
                (i := 0) hEvalLeft
            _ ≤ ∫ x : Fin k → ℂ,
                Real.exp (-t * ‖L x‖ ^ 2) ∂circularGaussianVector k :=
              continuousLinear_circularGaussian_add_laplace_le
                L (L (Z 0) - w) t ht
            _ = ∫ X : Fin 1 → Fin k → ℂ,
                Real.exp (-t * ‖L (X 0)‖ ^ 2)
                ∂(Measure.pi fun _ : Fin 1 => circularGaussianVector k) :=
              (integral_comp_eval
                (μ := fun _ : Fin 1 => circularGaussianVector k)
                (i := 0) hEvalRight).symm
      | succ n =>
          let muTail : Measure (Fin (n + 1) → Fin k → ℂ) :=
            Measure.pi fun _ : Fin (n + 1) => circularGaussianVector k
          let shiftedIntegrand :
              (Fin k → ℂ) × (Fin (n + 1) → Fin k → ℂ) → ℝ :=
            fun p =>
              Real.exp
                (-t * ‖F
                  (Fin.cons (p.1 + Z 0)
                    (fun i => p.2 i + Z i.succ)) - w‖ ^ 2)
          let tailReplacedIntegrand :
              (Fin k → ℂ) × (Fin (n + 1) → Fin k → ℂ) → ℝ :=
            fun p =>
              Real.exp (-t * ‖F (Fin.cons (p.1 + Z 0) p.2)‖ ^ 2)
          let centeredIntegrand :
              (Fin k → ℂ) × (Fin (n + 1) → Fin k → ℂ) → ℝ :=
            fun p =>
              Real.exp (-t * ‖F (Fin.cons p.1 p.2)‖ ^ 2)
          have hconsShift
              (p : (Fin k → ℂ) × (Fin (n + 1) → Fin k → ℂ)) :
              (fun i : Fin ((n + 1) + 1) =>
                (@Fin.cons (n + 1) (fun _ => Fin k → ℂ) p.1 p.2) i + Z i) =
                @Fin.cons (n + 1) (fun _ => Fin k → ℂ) (p.1 + Z 0)
                  (fun i => p.2 i + Z i.succ) := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp
            · simp
          have hShiftInt : Integrable shiftedIntegrand
              ((circularGaussianVector k).prod muTail) := by
            apply Integrable.of_bound (by fun_prop) 1
            filter_upwards [] with p
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr ht) (sq_nonneg _))
          have hTailInt : Integrable tailReplacedIntegrand
              ((circularGaussianVector k).prod muTail) := by
            apply Integrable.of_bound (by fun_prop) 1
            filter_upwards [] with p
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr ht) (sq_nonneg _))
          have hCenterInt : Integrable centeredIntegrand
              ((circularGaussianVector k).prod muTail) := by
            apply Integrable.of_bound (by fun_prop) 1
            filter_upwards [] with p
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr ht) (sq_nonneg _))
          rw [integral_pi_succ_eq_prod, integral_pi_succ_eq_prod]
          simp_rw [hconsShift]
          change (∫ p, shiftedIntegrand p
              ∂((circularGaussianVector k).prod muTail)) ≤
            ∫ p, centeredIntegrand p
              ∂((circularGaussianVector k).prod muTail)
          rw [integral_prod shiftedIntegrand hShiftInt,
            integral_prod centeredIntegrand hCenterInt]
          calc
            (∫ x, ∫ A, shiftedIntegrand (x, A) ∂muTail
                ∂circularGaussianVector k) ≤
              ∫ x, ∫ A, tailReplacedIntegrand (x, A) ∂muTail
                ∂circularGaussianVector k := by
                  apply integral_mono hShiftInt.integral_prod_left
                    hTailInt.integral_prod_left
                  intro x
                  simpa only [shiftedIntegrand, tailReplacedIntegrand,
                    ContinuousMultilinearMap.curryLeft_apply] using
                    ih (by omega) (F.curryLeft (x + Z 0))
                      (fun i : Fin (n + 1) => Z i.succ)
            _ = ∫ A, ∫ x, tailReplacedIntegrand (x, A)
                  ∂circularGaussianVector k ∂muTail :=
              integral_integral_swap hTailInt
            _ ≤ ∫ A, ∫ x, centeredIntegrand (x, A)
                  ∂circularGaussianVector k ∂muTail := by
              apply integral_mono hTailInt.integral_prod_right
                hCenterInt.integral_prod_right
              intro A
              let L : (Fin k → ℂ) →L[ℂ] ℂ :=
                F.toContinuousLinearMap
                  (Fin.cons (0 : Fin k → ℂ) A) 0
              have hL (x : Fin k → ℂ) :
                  L x = F (Fin.cons x A) := by
                rw [show L x =
                    F (Function.update
                      (Fin.cons (0 : Fin k → ℂ) A) 0 x) by
                  exact ContinuousMultilinearMap.toContinuousLinearMap_apply
                    F (Fin.cons (0 : Fin k → ℂ) A) 0 x]
                congr 1
                funext i
                refine Fin.cases ?_ (fun j => ?_) i
                · simp
                · simp
              have hShift (x : Fin k → ℂ) :
                  F (Fin.cons (x + Z 0) A) = L x + L (Z 0) := by
                rw [← hL (x + Z 0), map_add]
              have hShiftFun :
                  (fun x : Fin k → ℂ =>
                    tailReplacedIntegrand (x, A)) =
                    fun x : Fin k → ℂ =>
                      Real.exp (-t * ‖L x + L (Z 0)‖ ^ 2) := by
                funext x
                simp only [tailReplacedIntegrand]
                rw [hShift]
              have hCenterFun :
                  (fun x : Fin k → ℂ => centeredIntegrand (x, A)) =
                    fun x : Fin k → ℂ =>
                      Real.exp (-t * ‖L x‖ ^ 2) := by
                funext x
                simp only [centeredIntegrand]
                rw [hL]
              change (∫ x : Fin k → ℂ,
                  tailReplacedIntegrand (x, A) ∂circularGaussianVector k) ≤
                ∫ x : Fin k → ℂ,
                  centeredIntegrand (x, A) ∂circularGaussianVector k
              rw [hShiftFun, hCenterFun]
              exact continuousLinear_circularGaussian_add_laplace_le
                L (L (Z 0)) t ht
            _ = ∫ x, ∫ A, centeredIntegrand (x, A) ∂muTail
                  ∂circularGaussianVector k :=
              (integral_integral_swap hCenterInt).symm

/-- Deterministic matrix shifts cannot increase the radial Laplace transform
of the Gaussian Gram hafnian relative to its centered iid Gaussian law. -/
theorem deterministicShift_gramHafnian_laplace_le
    {r k : ℕ} (hr : 1 ≤ r)
    (Z : ComplexColumnMatrix r k) (w : ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ X : ComplexColumnMatrix r k,
        Real.exp
          (-t * ‖gramHafnianObservable r k
            (fun i => X i + Z i) - w‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure r k) ≤
      ∫ X : ComplexColumnMatrix r k,
        Real.exp (-t * ‖gramHafnianObservable r k X‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure r k := by
  simpa [circularGaussianColumnMatrixMeasure,
    gramHafnianContinuousMultilinear_apply] using
    continuousMultilinearMap_productGaussian_shift_laplace_le
      (n := 2 * r) (k := k) (by omega)
      (gramHafnianContinuousMultilinear r k) Z w t ht

/-- If an arbitrary shift matrix is independent of the iid circular Gaussian
matrix, then the same Laplace domination holds after averaging over the shift.
The shift law may couple all of its columns. -/
theorem independentShift_gramHafnian_laplace_le
    {r k : ℕ} (hr : 1 ≤ r)
    (nu : Measure (ComplexColumnMatrix r k)) [IsProbabilityMeasure nu]
    (w : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ p : ComplexColumnMatrix r k × ComplexColumnMatrix r k,
        Real.exp
          (-t * ‖gramHafnianObservable r k
            (fun i => p.1 i + p.2 i) - w‖ ^ 2)
        ∂((circularGaussianColumnMatrixMeasure r k).prod nu)) ≤
      ∫ X : ComplexColumnMatrix r k,
        Real.exp (-t * ‖gramHafnianObservable r k X‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure r k := by
  let mu := circularGaussianColumnMatrixMeasure r k
  let jointIntegrand :
      ComplexColumnMatrix r k × ComplexColumnMatrix r k → ℝ :=
    fun p =>
      Real.exp
        (-t * ‖gramHafnianObservable r k
          (fun i => p.1 i + p.2 i) - w‖ ^ 2)
  let centeredValue : ℝ :=
    ∫ X : ComplexColumnMatrix r k,
      Real.exp (-t * ‖gramHafnianObservable r k X‖ ^ 2) ∂mu
  have hJoint : Integrable jointIntegrand (mu.prod nu) := by
    have hcont : Continuous
        (fun p : ComplexColumnMatrix r k × ComplexColumnMatrix r k =>
          Real.exp
            (-t * ‖(gramHafnianContinuousMultilinear r k)
              (fun i => p.1 i + p.2 i) - w‖ ^ 2)) := by
      fun_prop
    have hmeas : AEStronglyMeasurable jointIntegrand (mu.prod nu) := by
      simpa only [jointIntegrand,
        gramHafnianContinuousMultilinear_apply] using
        hcont.aestronglyMeasurable
    apply Integrable.of_bound hmeas 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr ht) (sq_nonneg _))
  have hInner : Integrable
      (fun Z : ComplexColumnMatrix r k =>
        ∫ X : ComplexColumnMatrix r k, jointIntegrand (X, Z) ∂mu) nu :=
    hJoint.integral_prod_right
  have hConst : Integrable
      (fun _ : ComplexColumnMatrix r k => centeredValue) nu := by
    fun_prop
  change (∫ p, jointIntegrand p ∂mu.prod nu) ≤ centeredValue
  calc
    (∫ p, jointIntegrand p ∂mu.prod nu) =
      ∫ X, ∫ Z, jointIntegrand (X, Z) ∂nu ∂mu :=
        integral_prod jointIntegrand hJoint
    _ = ∫ Z, ∫ X, jointIntegrand (X, Z) ∂mu ∂nu :=
      integral_integral_swap hJoint
    _ ≤ ∫ _ : ComplexColumnMatrix r k, centeredValue ∂nu := by
      apply integral_mono hInner hConst
      intro Z
      exact deterministicShift_gramHafnian_laplace_le hr Z w t ht
    _ = centeredValue := by simp

end

end LogdetLean.GramHafnian
