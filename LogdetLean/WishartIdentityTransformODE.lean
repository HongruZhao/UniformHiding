import LogdetLean.WishartIdentityLogDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Logarithmic-derivative ODE for the identity Wishart product

This file connects the explicit digamma expression in
`WishartIdentityLogDerivative` to the actual finite Gamma product.  It proves
the differential equation `T_I' = L_I T_I` directly, without selecting a
branch of `log Gamma`.  This is the branch-safe form of the differentiation
used in Zhao, arXiv:2608.00565v1, Lemma 5.4.
-/

namespace LogdetLean

noncomputable section

set_option maxHeartbeats 800000

open Complex Set
open scoped BigOperators

/-- Logarithmic derivative of one identity diagonal factor, indexed in the
original `Fin p` coordinates. -/
def wishartIdentityStageLogDerivative
    (m n : ℕ) (z : ℂ) : ℂ :=
  Complex.digamma (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + z) +
    (Real.log m : ℂ) -
    Complex.log (((m : ℝ) / 2 : ℝ) + z) - 1

private theorem complex_half_dimension_axis_mem_slitPlane
    {m : ℕ} (hm : 0 < m) (u : ℝ) :
    (((m : ℝ) / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I ∈
      Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simpa using (show (0 : ℝ) < (m : ℝ) / 2 by positivity)

private theorem hasDerivAt_identityStageExponent_axis
    {m : ℕ} (hm : 0 < m) (u : ℝ) :
    HasDerivAt (complexWishartDiagonalStageExponent (m : ℝ) 1)
      ((Real.log m : ℂ) -
        Complex.log ((((m : ℝ) / 2 : ℝ) : ℂ) +
          (u : ℂ) * Complex.I) - 1)
      ((u : ℂ) * Complex.I) := by
  let M : ℂ := (((m : ℝ) / 2 : ℝ) : ℂ)
  let z : ℂ := (u : ℂ) * Complex.I
  have hshift : HasDerivAt (fun w : ℂ ↦ M + w) 1 z :=
    (hasDerivAt_id z).const_add M
  have hslit : M + z ∈ Complex.slitPlane := by
    simpa [M, z] using complex_half_dimension_axis_mem_slitPlane hm u
  have hlog := hshift.clog hslit
  have hmul := hshift.mul hlog
  have hlinear : HasDerivAt (fun w : ℂ ↦ w * (Real.log m : ℂ))
      (Real.log m : ℂ) z := by
    have hraw := (hasDerivAt_id z).mul_const (Real.log m : ℂ)
    have hraw' := hraw.congr_deriv (show
      (1 : ℂ) * (Real.log m : ℂ) = (Real.log m : ℂ) by ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _w ↦ rfl)
  unfold complexWishartDiagonalStageExponent
  dsimp
  have hraw := ((hasDerivAt_const z
    ((((m : ℝ) / 2) * Real.log ((m : ℝ) / 2) : ℝ) : ℂ)).add
      hlinear).sub hmul
  have hM0 : M + z ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hraw' := hraw.congr_deriv (show
      (0 : ℂ) + (Real.log m : ℂ) -
          (1 * Complex.log (M + z) + (M + z) * (1 / (M + z))) =
        (Real.log m : ℂ) - Complex.log (M + z) - 1 by
    field_simp [hM0]
    ring)
  apply hraw'.congr_of_eventuallyEq
  filter_upwards [] with w
  dsimp [M, z]
  simp only [one_mul]

private theorem hasDerivAt_Gamma_shift_axis
    {m n : ℕ} (hnm : n < m) (u : ℝ) :
    HasDerivAt
      (fun z : ℂ ↦ Complex.Gamma
        (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + z))
      (deriv Complex.Gamma
        (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) +
          (u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  let a : ℝ := ((m - n : ℕ) : ℝ) / 2
  have ha : 0 < a := by
    dsimp [a]
    have : 0 < m - n := Nat.sub_pos_of_lt hnm
    positivity
  have hG : HasDerivAt Complex.Gamma
      (deriv Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I))
      ((a : ℂ) + (u : ℂ) * Complex.I) := by
    exact (Complex.differentiableAt_Gamma _ (fun k heq ↦ by
      have hre := congrArg Complex.re heq
      simp at hre
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)).hasDerivAt
  have hshift : HasDerivAt (fun z : ℂ ↦ (a : ℂ) + z) 1
      ((u : ℂ) * Complex.I) :=
    (hasDerivAt_id _).const_add (a : ℂ)
  simpa [a, Function.comp_def] using hG.comp ((u : ℂ) * Complex.I) hshift

/-- One identity diagonal Gamma factor solves its scalar logarithmic-
derivative ODE on the whole imaginary axis. -/
theorem hasDerivAt_complexWishartIdentityStage_axis
    {m n : ℕ} (hm : 0 < m) (hnm : n < m) (u : ℝ) :
    HasDerivAt (complexWishartDiagonalStageTransform m n 1)
      (wishartIdentityStageLogDerivative m n ((u : ℂ) * Complex.I) *
        complexWishartDiagonalStageTransform m n 1
          ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  let a : ℝ := ((m - n : ℕ) : ℝ) / 2
  let z : ℂ := (u : ℂ) * Complex.I
  have ha : 0 < a := by
    dsimp [a]
    have : 0 < m - n := Nat.sub_pos_of_lt hnm
    positivity
  have hG := hasDerivAt_Gamma_shift_axis hnm u
  have hden : Complex.Gamma (a : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using ha)
  have hq : Complex.Gamma ((a : ℂ) + z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa [z] using ha)
  have hdig : deriv Complex.Gamma ((a : ℂ) + z) =
      Complex.digamma ((a : ℂ) + z) * Complex.Gamma ((a : ℂ) + z) := by
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [hq]
  have hquot := hG.div_const (Complex.Gamma (a : ℂ))
  have hquot' := hquot.congr_deriv (show
      deriv Complex.Gamma ((a : ℂ) + z) /
          Complex.Gamma (a : ℂ) =
        Complex.digamma ((a : ℂ) + z) *
          (Complex.Gamma ((a : ℂ) + z) /
            Complex.Gamma (a : ℂ)) by rw [hdig]; ring)
  have hE := hasDerivAt_identityStageExponent_axis hm u
  have hexp := hE.cexp
  have hprod := hquot'.mul hexp
  have hprod' := hprod.congr_deriv (show
      Complex.digamma ((a : ℂ) + z) *
            (Complex.Gamma ((a : ℂ) + z) / Complex.Gamma (a : ℂ)) *
            Complex.exp (complexWishartDiagonalStageExponent (m : ℝ) 1 z) +
          (Complex.Gamma ((a : ℂ) + z) / Complex.Gamma (a : ℂ)) *
            (Complex.exp (complexWishartDiagonalStageExponent (m : ℝ) 1 z) *
              ((Real.log m : ℂ) -
                Complex.log ((((m : ℝ) / 2 : ℝ) : ℂ) + z) - 1)) =
        (Complex.digamma ((a : ℂ) + z) + (Real.log m : ℂ) -
            Complex.log ((((m : ℝ) / 2 : ℝ) : ℂ) + z) - 1) *
          ((Complex.Gamma ((a : ℂ) + z) / Complex.Gamma (a : ℂ)) *
            Complex.exp (complexWishartDiagonalStageExponent (m : ℝ) 1 z)) by
      ring)
  unfold complexWishartDiagonalStageTransform
    wishartIdentityStageLogDerivative at ⊢
  dsimp [a, z] at hprod' ⊢
  simp only [mul_one]
  change HasDerivAt
    ((fun x : ℂ ↦
      Complex.Gamma (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + x) /
        Complex.Gamma (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ))) *
      (fun x : ℂ ↦
        Complex.exp (complexWishartDiagonalStageExponent (m : ℝ) 1 x)))
    _ _
  exact hprod'

/-- Reindexing identity: the sum of the original `Fin p` stage logarithmic
derivatives is the cancellation-preserving beta-coordinate expression. -/
theorem sum_wishartIdentityStageLogDerivative_eq
    {m p : ℕ} (hpm : p ≤ m) (z : ℂ) :
    ∑ i : Fin p, wishartIdentityStageLogDerivative m i.1 z =
      wishartIdentityLogDerivative m p z := by
  induction p with
  | zero => simp [wishartIdentityStageLogDerivative,
      wishartIdentityLogDerivative]
  | succ p ih =>
      have hpm' : p ≤ m := by omega
      rw [Fin.sum_univ_castSucc]
      have hcast :
          (∑ i : Fin p,
            wishartIdentityStageLogDerivative m i.castSucc.1 z) =
          ∑ i : Fin p, wishartIdentityStageLogDerivative m i.1 z := by
        apply Finset.sum_congr rfl
        intro i _hi
        rfl
      rw [hcast]
      rw [ih hpm']
      unfold wishartIdentityLogDerivative
      by_cases hp0 : p = 0
      · subst p
        simp [wishartIdentityStageLogDerivative, betaShapeTotal]
      · have hp2 : 2 ≤ p + 1 := by omega
        rw [Finset.sum_Icc_succ_top hp2]
        have hshape : (((m - p : ℕ) : ℝ) / 2) =
            betaShapeA m (p + 1) := by
          unfold betaShapeA
          rw [Nat.cast_sub hpm']
          push_cast
          ring
        simp only [Fin.last, wishartIdentityStageLogDerivative]
        rw [hshape]
        have hsum :
            (∑ x ∈ Finset.Icc 2 p,
              (Complex.digamma ((betaShapeA m x : ℂ) + z) -
                Complex.digamma ((betaShapeTotal m : ℂ) + z))) =
            ∑ x ∈ Finset.Icc 2 p,
              (-Complex.digamma ((betaShapeTotal m : ℂ) + z) +
                Complex.digamma ((betaShapeA m x : ℂ) + z)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        rw [hsum]
        unfold betaShapeTotal
        push_cast
        ring

/-- The full finite identity transform solves `T_I'=L_I T_I` on the
imaginary axis. -/
theorem hasDerivAt_complexWishartIdentityTransform_axis
    {m p : ℕ} (hm : 0 < m) (hpm : p ≤ m) (u : ℝ) :
    HasDerivAt (complexWishartIdentityTransform m p)
      (wishartIdentityLogDerivative m p ((u : ℂ) * Complex.I) *
        complexWishartIdentityTransform m p ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  let F : Fin p → ℂ → ℂ := fun i ↦
    complexWishartDiagonalStageTransform m i.1 1
  let L : Fin p → ℂ := fun i ↦
    wishartIdentityStageLogDerivative m i.1 ((u : ℂ) * Complex.I)
  have hdiff (i : Fin p) : HasDerivAt (F i)
      (L i * F i ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
    exact hasDerivAt_complexWishartIdentityStage_axis hm
      (lt_of_lt_of_le i.2 hpm) u
  have hfinite (s : Finset (Fin p)) : HasDerivAt
      (fun z : ℂ ↦ ∏ i ∈ s, F i z)
      ((∑ i ∈ s, L i) * ∏ i ∈ s, F i ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
    induction s using Finset.induction with
    | empty => simpa using (hasDerivAt_const ((u : ℂ) * Complex.I) (1 : ℂ))
    | @insert a s ha ih =>
        simp only [Finset.prod_insert ha, Finset.sum_insert ha]
        have hmul := (hdiff a).mul ih
        apply hmul.congr_deriv
        ring
  have hall := hfinite Finset.univ
  unfold complexWishartIdentityTransform
  have hall' := hall.congr_deriv (show
      (∑ i ∈ (Finset.univ : Finset (Fin p)), L i) *
          ∏ i ∈ (Finset.univ : Finset (Fin p)),
            F i ((u : ℂ) * Complex.I) =
        wishartIdentityLogDerivative m p ((u : ℂ) * Complex.I) *
          ∏ i : Fin p, complexWishartDiagonalStageTransform m i.1 1
            ((u : ℂ) * Complex.I) by
    simpa [L, F] using congrArg
      (fun q : ℂ ↦ q *
        ∏ i : Fin p, complexWishartDiagonalStageTransform m i.1 1
          ((u : ℂ) * Complex.I))
      (sum_wishartIdentityStageLogDerivative_eq hpm
        ((u : ℂ) * Complex.I)))
  exact hall'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _z ↦ rfl)

end

end LogdetLean
