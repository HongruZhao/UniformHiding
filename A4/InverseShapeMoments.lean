import A4.PolynomialShapeMoments
import A4.WishartDensityInverseShift
import Mathlib.Algebra.Polynomial.Roots

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

/-- A genuine polynomial numerator for a degree-n inverse entry moment.
The denominator is the explicit Matsumoto Gamma-decrement polynomial. -/
def inverseEntryProductShapeNumerator {d n : ℕ} (i j : Fin n → Fin d)
    (sigma : RealMatrix d) : Polynomial ℝ :=
  Polynomial.C (Matrix.det sigma ^ (-(n : ℝ))) *
    (adjugateEntryProductShapePolynomial i j sigma).comp
      (Polynomial.X - Polynomial.C (n : ℝ))

theorem eval_inverseEntryProductShapeNumerator {d n : ℕ} (i j : Fin n → Fin d)
    (sigma : RealMatrix d) (beta : ℝ) :
    (inverseEntryProductShapeNumerator i j sigma).eval beta =
      Matrix.det sigma ^ (-(n : ℝ)) *
        (adjugateEntryProductShapePolynomial i j sigma).eval (beta - (n : ℝ)) := by
  simp only [inverseEntryProductShapeNumerator, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]

/-- All inverse entry moments, at the exact original real-shape gap, are
rational functions of shape with explicitly proved numerator and denominator.
The shifted law used in the proof is constructed, rather than assumed. -/
theorem W_d.integral_prod_inverse_entries_eq_eval_quotient
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (i j : Fin n → Fin d) :
    (∫ w : SymPosDef d, ∏ k : Fin n, w.1⁻¹ (i k) (j k) ∂W.toMeasure) =
      (inverseEntryProductShapeNumerator i j sigma.1).eval beta /
        (A4Research.inverseShapeDenominator d n).eval beta := by
  have hbn : ((d : ℝ) - 1) / 2 < beta - (n : ℝ) := by linarith
  let V := A4Research.recursiveBartlettScaledLaw d (beta - (n : ℝ)) sigma hbn
  rw [A4Research.inverse_entry_integral_eq_shifted_adjugate W V hgamma hgap i j,
    V.integral_prod_adjugate_entries_eq_eval_shapePolynomial,
    eval_inverseEntryProductShapeNumerator]
  ring

/-- Clearing the finitely many proved inverse-moment denominators produces
one literal polynomial. It is used to continue Gaussian entry recurrences
to every real shape in the paper's sharp range. -/
def clearedInverseMomentIdentityPolynomial {d : ℕ} {I : Type*} [Fintype I]
    [DecidableEq I] (degree : I → ℕ) (i j : ∀ a, Fin (degree a) → Fin d)
    (sigma : RealMatrix d) (coefficient : I → Polynomial ℝ) (rhs : Polynomial ℝ) :
    Polynomial ℝ :=
  (∑ a : I, coefficient a * inverseEntryProductShapeNumerator (i a) (j a) sigma *
    ∏ b ∈ Finset.univ.erase a, A4Research.inverseShapeDenominator d (degree b)) -
  rhs * ∏ a : I, A4Research.inverseShapeDenominator d (degree a)

theorem eval_clearedInverseMomentIdentityPolynomial {d n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (degree : I → ℕ)
    (i j : ∀ a, Fin (degree a) → Fin d)
    (coefficient : I → Polynomial ℝ) (rhs : Polynomial ℝ)
    {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hdegree : ∀ a, degree a ≤ n)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    (clearedInverseMomentIdentityPolynomial degree i j sigma.1 coefficient rhs).eval beta =
      (∏ a : I, (A4Research.inverseShapeDenominator d (degree a)).eval beta) *
        ((∑ a : I, (coefficient a).eval beta *
          (∫ w : SymPosDef d, ∏ k : Fin (degree a),
            w.1⁻¹ (i a k) (j a k) ∂W.toMeasure)) - rhs.eval beta) := by
  have hga : ∀ a, (degree a : ℝ) - 1 < gamma := by
    intro a
    have hle : (degree a : ℝ) ≤ n := by exact_mod_cast hdegree a
    linarith
  have hden : ∀ a, (A4Research.inverseShapeDenominator d (degree a)).eval beta ≠ 0 :=
    fun a ↦ (A4Research.inverseShapeDenominator_eval_pos hgamma (hga a)).ne'
  simp only [clearedInverseMomentIdentityPolynomial, Polynomial.eval_sub,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [W.integral_prod_inverse_entries_eq_eval_quotient hgamma (hga a)]
    have hprod := Finset.prod_erase_mul (s := Finset.univ)
      (f := fun b ↦ (A4Research.inverseShapeDenominator d (degree b)).eval beta)
      (Finset.mem_univ a)
    rw [← hprod]
    field_simp [hden a]
    <;> ring
  · ring

/-- An all-degree entry recurrence proved at every sufficiently large
Gaussian sample shape holds at every real shape in the original A4 range.
Only the displayed sample recurrence is an input to this interpolation
bridge; the law construction and rational moment formula are unconditional. -/
theorem W_d.inverseMomentLinearIdentity_of_nat
    {d n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (degree : I → ℕ) (i j : ∀ a, Fin (degree a) → Fin d)
    (coefficient : I → Polynomial ℝ) (rhs : Polynomial ℝ)
    {sigma : SymPosDef d} (hdegree : ∀ a, degree a ≤ n) (bound : ℕ)
    (hsample : ∀ k : ℕ, bound ≤ k → ∀ V : W_d d ((k : ℝ) / 2) sigma,
      (∑ a : I, (coefficient a).eval ((k : ℝ) / 2) *
        (∫ w : SymPosDef d, ∏ r : Fin (degree a),
          w.1⁻¹ (i a r) (j a r) ∂V.toMeasure)) = rhs.eval ((k : ℝ) / 2))
    {beta gamma : ℝ} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    (∑ a : I, (coefficient a).eval beta *
      (∫ w : SymPosDef d, ∏ r : Fin (degree a),
        w.1⁻¹ (i a r) (j a r) ∂W.toMeasure)) = rhs.eval beta := by
  let P := clearedInverseMomentIdentityPolynomial degree i j sigma.1 coefficient rhs
  let sample : ℕ → ℝ := fun t ↦ ((bound + d + n + 2 + t : ℕ) : ℝ)
  have hinj : Function.Injective sample := by
    intro t u h
    dsimp only [sample] at h
    have hnat : bound + d + n + 2 + t = bound + d + n + 2 + u := by
      exact_mod_cast h
    omega
  have hzero : P = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective hinj).mono
    rintro x ⟨t, rfl⟩
    let k : ℕ := 2 * (bound + d + n + 2 + t)
    have hk : bound ≤ k := by dsimp [k]; omega
    have hshape : (k : ℝ) / 2 = sample t := by
      simp only [k, sample, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hgap' : (n : ℝ) - 1 < sample t - ((d : ℝ) + 1) / 2 := by
      simp only [sample, Nat.cast_add, Nat.cast_ofNat]
      have hb := Nat.cast_nonneg (α := ℝ) bound
      have hd := Nat.cast_nonneg (α := ℝ) d
      have ht := Nat.cast_nonneg (α := ℝ) t
      linarith
    have hb : ((d : ℝ) - 1) / 2 < sample t := by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    let V := A4Research.recursiveBartlettScaledLaw d ((k : ℝ) / 2) sigma
      (by rw [hshape]; exact hb)
    have hs := hsample k hk V
    change P.eval (sample t) = (0 : Polynomial ℝ).eval (sample t)
    rw [Polynomial.eval_zero, ← hshape]
    change (clearedInverseMomentIdentityPolynomial degree i j sigma.1 coefficient rhs).eval
      ((k : ℝ) / 2) = 0
    rw [eval_clearedInverseMomentIdentityPolynomial degree i j coefficient rhs V hdegree
      rfl (by rw [hshape]; exact hgap'), hs, sub_self, mul_zero]
  have hga : ∀ a, (degree a : ℝ) - 1 < gamma := by
    intro a
    have hle : (degree a : ℝ) ≤ n := by exact_mod_cast hdegree a
    linarith
  have hden : (∏ a : I, (A4Research.inverseShapeDenominator d (degree a)).eval beta) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ ↦
      (A4Research.inverseShapeDenominator_eval_pos hgamma (hga a)).ne')
  have h := congrArg (fun Q : Polynomial ℝ ↦ Q.eval beta) hzero
  change (clearedInverseMomentIdentityPolynomial degree i j sigma.1 coefficient rhs).eval beta =
    (0 : Polynomial ℝ).eval beta at h
  rw [eval_clearedInverseMomentIdentityPolynomial degree i j coefficient rhs W hdegree
    hgamma hgap, Polynomial.eval_zero] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hden)

end MatsumotoPaper
