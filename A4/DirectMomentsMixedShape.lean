import A4.DirectMomentsPolarization
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

set_option maxHeartbeats 1200000

/-- Formal determinant recurrence over any commutative coefficient ring. -/
def momentPolynomialOver {R : Type*} [CommRing R] (D : Polynomial R) : ℕ → Polynomial R
  | 0 => 1
  | n + 1 =>
    -(∑ k ∈ Finset.range (n + 1),
      (Polynomial.X * Polynomial.C (n.choose k : R) +
        Polynomial.C (n.choose (k + 1) : R)) *
      Polynomial.C ((k + 1).factorial * D.coeff (k + 1)) *
      momentPolynomialOver D (n - k))
termination_by n => n
decreasing_by omega

theorem natDegree_momentPolynomialOver_le {R : Type*} [CommRing R]
    (D : Polynomial R) (n : ℕ) : (momentPolynomialOver D n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [momentPolynomialOver]
    | succ n =>
      rw [momentPolynomialOver, Polynomial.natDegree_neg]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      have hlinear :
          (Polynomial.X * Polynomial.C (n.choose k : R) +
            Polynomial.C (n.choose (k + 1) : R)).natDegree ≤ 1 := by
        apply Polynomial.natDegree_add_le_of_degree_le
        · exact (Polynomial.natDegree_mul_C_le _ _).trans Polynomial.natDegree_X_le
        · simp
      have hscalar :
          ((Polynomial.X * Polynomial.C (n.choose k : R) +
            Polynomial.C (n.choose (k + 1) : R)) *
            Polynomial.C ((k + 1).factorial * D.coeff (k + 1))).natDegree ≤ 1 :=
        (Polynomial.natDegree_mul_C_le _ _).trans hlinear
      exact (Polynomial.natDegree_mul_le_of_le hscalar
        (ih (n - k) (by omega))).trans (by omega)

theorem map_momentPolynomialOver {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (D : Polynomial R) (n : ℕ) :
    (momentPolynomialOver D n).map f = momentPolynomialOver (D.map f) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [momentPolynomialOver]
    | succ n =>
      conv_lhs => rw [momentPolynomialOver]
      conv_rhs => rw [momentPolynomialOver]
      simp only [Polynomial.map_neg, Polynomial.map_sum, Polynomial.map_mul,
        Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
        map_natCast, map_mul, Polynomial.coeff_map]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro k _
      rw [ih (n - k) (by omega)]
      simp only [Polynomial.map_natCast]

theorem iteratedDeriv_polynomial_eval (P : Polynomial ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ ↦ P.eval t) x =
      ((Polynomial.derivative^[n]) P).eval x := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (fun t : ℝ ↦ P.eval t) = fun t : ℝ ↦ P.derivative.eval t :=
      funext fun t ↦ P.deriv
    rw [hderiv, ih]
    rw [Function.iterate_succ_apply]

theorem iteratedDeriv_polynomial_eval_zero (P : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ ↦ P.eval t) 0 = (n.factorial : ℝ) * P.coeff n := by
  rw [iteratedDeriv_polynomial_eval, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, mul_comm]

theorem momentPolynomialOver_directionDetPolynomial {d : ℕ}
    (theta sigma : RealMatrix d) (n : ℕ) :
    momentPolynomialOver (directionDetPolynomial theta sigma) n =
      directionalMomentPolynomial theta sigma n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [momentPolynomialOver, directionalMomentPolynomial]
    | succ n =>
      conv_lhs => rw [momentPolynomialOver]
      conv_rhs => rw [directionalMomentPolynomial]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro k _
      rw [iteratedDeriv_polynomial_eval_zero, ih (n - k) (by omega)]

/-- A real linear combination of the symmetric trace directions. -/
def traceDirectionCombination {d m : ℕ} (theta : Fin m → Sym d)
    (t : Fin m → ℝ) : Sym d :=
  ⟨∑ i : Fin m, t i • (theta i).1, by
    change (∑ i : Fin m, t i • (theta i).1).transpose = _
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [(theta i).2]⟩

theorem traceObservable_traceDirectionCombination {d m : ℕ}
    (theta : Fin m → Sym d) (t : Fin m → ℝ) (w : SymPosDef d) :
    traceObservable (traceDirectionCombination theta t) w =
      ∑ i : Fin m, t i * traceObservable (theta i) w := by
  simp [traceObservable, traceDirectionCombination, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul]

/-- A symmetric matrix whose coefficients are polynomials in all trace
directions at once. -/
def polynomialTraceDirections {d m : ℕ} (theta : Fin m → Sym d) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin m) ℝ) :=
  fun i j ↦ ∑ a : Fin m, MvPolynomial.X a * MvPolynomial.C ((theta a).1 i j)

def mixedDirectionDetPolynomial {d m : ℕ} (theta : Fin m → Sym d)
    (sigma : RealMatrix d) : Polynomial (MvPolynomial (Fin m) ℝ) :=
  Matrix.det (1 + (Polynomial.X : Polynomial (MvPolynomial (Fin m) ℝ)) •
    (-(polynomialTraceDirections theta * sigma.map MvPolynomial.C)).map Polynomial.C)

theorem map_mixedDirectionDetPolynomial {d m : ℕ} (theta : Fin m → Sym d)
    (sigma : RealMatrix d) (t : Fin m → ℝ) :
    (mixedDirectionDetPolynomial theta sigma).map (MvPolynomial.eval t) =
      directionDetPolynomial (traceDirectionCombination theta t).1 sigma := by
  classical
  unfold mixedDirectionDetPolynomial directionDetPolynomial
  rw [show Polynomial.map (MvPolynomial.eval t) =
    (Polynomial.mapRingHom (MvPolynomial.eval t) :
      Polynomial (MvPolynomial (Fin m) ℝ) → Polynomial ℝ) from rfl]
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  simp [RingHom.mapMatrix, Matrix.map,
    Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.neg_apply,
    Matrix.mul_apply, polynomialTraceDirections, traceDirectionCombination,
    Finset.sum_mul, Polynomial.coe_mapRingHom, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_neg, MvPolynomial.eval_C, MvPolynomial.eval_X, map_sum,
    map_mul, map_neg, Matrix.sum_apply, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  by_cases h : i = j <;> simp [h, mul_comm]

/-- The bivariate formal moment polynomial: shape is the outer polynomial
variable and the trace directions are its multivariate coefficients. -/
def mixedDirectionMomentPolynomial {d m : ℕ} (theta : Fin m → Sym d)
    (sigma : RealMatrix d) (n : ℕ) : Polynomial (MvPolynomial (Fin m) ℝ) :=
  momentPolynomialOver (mixedDirectionDetPolynomial theta sigma) n

theorem eval_eval_mixedDirectionMomentPolynomial {d m : ℕ}
    (theta : Fin m → Sym d) (sigma : RealMatrix d) (n : ℕ)
    (beta : ℝ) (t : Fin m → ℝ) :
    MvPolynomial.eval t
      ((mixedDirectionMomentPolynomial theta sigma n).eval (MvPolynomial.C beta)) =
      (directionalMomentPolynomial (traceDirectionCombination theta t).1 sigma n).eval beta := by
  rw [← Polynomial.eval_map_apply]
  simp only [MvPolynomial.eval_C, mixedDirectionMomentPolynomial,
    map_momentPolynomialOver, map_mixedDirectionDetPolynomial,
    momentPolynomialOver_directionDetPolynomial]

theorem W_d.eval_mixedDirectionMomentPolynomial {d m : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Fin m → Sym d) (n : ℕ) :
    (mixedDirectionMomentPolynomial theta sigma.1 n).eval (MvPolynomial.C beta) =
      observableMomentPolynomial (n := n) W.toMeasure
        (fun i w ↦ traceObservable (theta i) w) := by
  apply MvPolynomial.funext
  intro t
  rw [eval_eval_mixedDirectionMomentPolynomial,
    ← W.integral_traceObservable_pow_eq_eval_momentPolynomial,
    eval_observableMomentPolynomial]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w ↦ by
      change traceObservable (traceDirectionCombination theta t) w ^ n =
        (∑ j : Fin m, t j * traceObservable (theta j) w) ^ n
      rw [traceObservable_traceDirectionCombination]
  · intro c
    exact W.integrable_prod_traceObservable (fun i ↦ theta (c i))

/-- Coefficient extraction in the trace variables, applied independently to
each coefficient of an outer shape polynomial. -/
def polynomialDirectionCoefficient {m : ℕ} (e : Fin m →₀ ℕ) :
    Polynomial (MvPolynomial (Fin m) ℝ) →ₗ[ℝ] Polynomial ℝ :=
  Polynomial.lsum (fun k ↦ (Polynomial.monomial k).comp (MvPolynomial.lcoeff ℝ e))

@[simp] theorem polynomialDirectionCoefficient_monomial {m : ℕ}
    (e : Fin m →₀ ℕ) (k : ℕ) (a : MvPolynomial (Fin m) ℝ) :
    polynomialDirectionCoefficient e (Polynomial.monomial k a) =
      Polynomial.monomial k (MvPolynomial.coeff e a) := by
  simp [polynomialDirectionCoefficient, Polynomial.lsum, MvPolynomial.lcoeff]

theorem coeff_polynomialDirectionCoefficient {m : ℕ} (e : Fin m →₀ ℕ)
    (P : Polynomial (MvPolynomial (Fin m) ℝ)) (k : ℕ) :
    (polynomialDirectionCoefficient e P).coeff k = MvPolynomial.coeff e (P.coeff k) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial j a =>
    rw [polynomialDirectionCoefficient_monomial]
    simp only [Polynomial.coeff_monomial]
    split_ifs <;> simp

theorem natDegree_polynomialDirectionCoefficient_le {m : ℕ} (e : Fin m →₀ ℕ)
    (P : Polynomial (MvPolynomial (Fin m) ℝ)) :
    (polynomialDirectionCoefficient e P).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_polynomialDirectionCoefficient, Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  simp

theorem eval_polynomialDirectionCoefficient {m : ℕ} (e : Fin m →₀ ℕ)
    (P : Polynomial (MvPolynomial (Fin m) ℝ)) (beta : ℝ) :
    (polynomialDirectionCoefficient e P).eval beta =
      MvPolynomial.coeff e (P.eval (MvPolynomial.C beta)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial k a =>
    rw [polynomialDirectionCoefficient_monomial]
    simp only [Polynomial.eval_monomial, ← map_pow]
    rw [mul_comm a, MvPolynomial.coeff_C_mul]
    ring

/-- The mixed degree-`n` moment polynomial in the shape, for any list of
symmetric trace directions. -/
def mixedShapeMomentPolynomial {d n : ℕ} (theta : Fin n → Sym d)
    (sigma : RealMatrix d) : Polynomial ℝ :=
  ((n.factorial : ℝ)⁻¹) • polynomialDirectionCoefficient (allOnesExponent n)
    (mixedDirectionMomentPolynomial theta sigma n)

theorem natDegree_mixedShapeMomentPolynomial_le {d n : ℕ}
    (theta : Fin n → Sym d) (sigma : RealMatrix d) :
    (mixedShapeMomentPolynomial theta sigma).natDegree ≤ n :=
  (Polynomial.natDegree_smul_le _ _).trans
    ((natDegree_polynomialDirectionCoefficient_le _ _).trans
      (natDegree_momentPolynomialOver_le _ n))

/-- Every mixed moment of the exact real-shape law is a degree-`n` polynomial
in the shape. This includes arbitrary repeated matrix entries through the
previously checked entry trace directions. -/
theorem W_d.integral_prod_traceObservable_eq_eval_mixedShapeMomentPolynomial
    {d n : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (theta : Fin n → Sym d) :
    (∫ w, ∏ i : Fin n, traceObservable (theta i) w ∂W.toMeasure) =
      (mixedShapeMomentPolynomial theta sigma.1).eval beta := by
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [mixedShapeMomentPolynomial, Polynomial.eval_smul,
    eval_polynomialDirectionCoefficient, W.eval_mixedDirectionMomentPolynomial,
    coeff_allOnes_observableMomentPolynomial]
  · simp only [smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · intro c
    exact W.integrable_prod_traceObservable (fun i ↦ theta (c i))

end MatsumotoPaper
