import A4.WishartDensityDeterminantTilt
import A4.WishartDensityInverseIntegrability
import Mathlib.Algebra.Polynomial.BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research

open MatsumotoPaper

/-- Gamma's recurrence expanded through an arbitrary positive real-shape
integer decrement, with all finite factors explicit. -/
theorem gamma_eq_descendingProduct_mul {a : ℝ} (n : ℕ) (ha : 0 < a - (n : ℝ)) :
    Real.Gamma a = (∏ r : Fin n, (a - (r : ℝ) - 1)) * Real.Gamma (a - (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha' : 0 < a - (n : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one] at ha
      linarith
    have hbase : 0 < a - (n : ℝ) - 1 := by
      rw [Nat.cast_add, Nat.cast_one] at ha
      linarith
    have hrec : Real.Gamma (a - (n : ℝ)) =
        (a - (n : ℝ) - 1) * Real.Gamma (a - (n : ℝ) - 1) := by
      calc
        Real.Gamma (a - (n : ℝ)) = Real.Gamma ((a - (n : ℝ) - 1) + 1) :=
          congrArg Real.Gamma (by ring)
        _ = _ := Real.Gamma_add_one hbase.ne' 
    rw [ih ha', hrec, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [show a - ((n : ℝ) + 1) = a - (n : ℝ) - 1 by ring]
    ring

/-- The integer negative Gamma ratio is a finite rational product. -/
theorem gamma_ratio_sub_nat {a : ℝ} (n : ℕ) (ha : 0 < a - (n : ℝ)) :
    Real.Gamma (a - (n : ℝ)) / Real.Gamma a =
      (∏ r : Fin n, (a - (r : ℝ) - 1))⁻¹ := by
  have hprod : 0 < ∏ r : Fin n, (a - (r : ℝ) - 1) := by
    apply Finset.prod_pos
    intro r _
    have hr : (r : ℝ) + 1 ≤ n := by exact_mod_cast r.isLt
    linarith
  rw [gamma_eq_descendingProduct_mul n ha]
  field_simp [(Real.Gamma_pos_of_pos ha).ne', hprod.ne']

/-- The common polynomial denominator for all degree-n inverse Wishart entry
moments. Its factors are precisely the finite Gamma-decrement factors. -/
def inverseShapeDenominator (d n : ℕ) : Polynomial ℝ :=
  ∏ i : Fin d, ∏ r : Fin n,
    (Polynomial.X - Polynomial.C ((i : ℝ) / 2 + (r : ℝ) + 1))

theorem inverseShapeDenominator_eval (d n : ℕ) (beta : ℝ) :
    (inverseShapeDenominator d n).eval beta =
      ∏ i : Fin d, ∏ r : Fin n, (beta - (i : ℝ) / 2 - (r : ℝ) - 1) := by
  simp only [inverseShapeDenominator, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro r _
  ring

/-- The denominator is an actual nonzero monic polynomial in the real shape. -/
theorem inverseShapeDenominator_monic (d n : ℕ) :
    (inverseShapeDenominator d n).Monic := by
  unfold inverseShapeDenominator
  apply Polynomial.monic_prod_of_monic
  intro i _
  apply Polynomial.monic_prod_of_monic
  intro r _
  exact Polynomial.monic_X_sub_C _

theorem inverseShapeDenominator_ne_zero (d n : ℕ) : inverseShapeDenominator d n ≠ 0 :=
  (inverseShapeDenominator_monic d n).ne_zero

/-- The original A4 gap places every denominator factor strictly above zero. -/
theorem inverseShapeDenominator_eval_pos {d n : ℕ} {beta gamma : ℝ}
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    0 < (inverseShapeDenominator d n).eval beta := by
  rw [inverseShapeDenominator_eval]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro r _
  have hi := bartlettShape_sub_degree_pos hgamma hgap i
  have hr : (r : ℝ) + 1 ≤ n := by exact_mod_cast r.isLt
  unfold bartlettShape at hi
  linarith

/-- The complete Matsumoto Gamma normalization at integer negative degree is
exactly the reciprocal of the explicit common polynomial denominator. -/
theorem gammaProduct_inverseShapeDenominator {d n : ℕ} {beta gamma : ℝ}
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    (∏ i : Fin d, Real.Gamma (bartlettShape beta i - (n : ℝ)) /
      Real.Gamma (bartlettShape beta i)) = ((inverseShapeDenominator d n).eval beta)⁻¹ := by
  rw [inverseShapeDenominator_eval, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [gamma_ratio_sub_nat n (bartlettShape_sub_degree_pos hgamma hgap i)]
  rfl

/-- Every inverse entry moment is a direct polynomial adjugate moment under
the actual shifted Wishart law, with the complete arbitrary-scale factor. -/
theorem inverse_entry_integral_eq_shifted_adjugate {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (V : W_d d (beta - (n : ℝ)) sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (i j : Fin n → Fin d) :
    (∫ w : SymPosDef d, ∏ k : Fin n, w.1⁻¹ (i k) (j k) ∂W.toMeasure) =
      (Matrix.det sigma.1 ^ (-(n : ℝ)) / (inverseShapeDenominator d n).eval beta) *
        (∫ w : SymPosDef d, ∏ k : Fin n, w.1.adjugate (i k) (j k) ∂V.toMeasure) := by
  have hb : ((d : ℝ) - 1) / 2 < beta := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hbn : ((d : ℝ) - 1) / 2 < beta - (n : ℝ) := by linarith
  have hweighted := wishart_integral_det_rpow_mul (p := -(n : ℝ)) W
    (show W_d d (beta + -(n : ℝ)) sigma from by simpa only [sub_eq_add_neg] using V)
    hb (by simpa only [sub_eq_add_neg] using hbn)
    (fun w : SymPosDef d => ∏ k : Fin n, w.1.adjugate (i k) (j k))
  have hfun : (fun w : SymPosDef d => ∏ k : Fin n, w.1⁻¹ (i k) (j k)) =
      (fun w => Matrix.det w.1 ^ (-(n : ℝ)) * ∏ k : Fin n, w.1.adjugate (i k) (j k)) :=
    funext (fun w => inverse_prod_entries_eq_det_adjugate w i j)
  rw [hfun]
  convert hweighted using 1
  · rw [div_eq_mul_inv]
    congr 2
    simpa only [sub_eq_add_neg] using (gammaProduct_inverseShapeDenominator hgamma hgap).symm

end A4Research
