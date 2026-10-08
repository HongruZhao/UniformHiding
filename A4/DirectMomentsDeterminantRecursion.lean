import A4.DirectMomentsAnalytic

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

/-- A real-polynomial evaluation wrapper with the same real normed-space
instances as the scalar moment-generating-function API. -/
theorem contDiff_realPolynomial_eval (Q : Polynomial ℝ) (n : ℕ) :
    ContDiff ℝ n (fun t : ℝ ↦ Q.eval t) := by
  induction Q using Polynomial.induction_on' with
  | add f g hf hg => simpa only [Polynomial.eval_add] using hf.add hg
  | monomial k a =>
    convert! (contDiff_const (c := a)).mul (contDiff_id.pow k) using 1
    ext t
    simp

/-- The polynomial whose real evaluation is the determinant in a scalar
direction of the original matrix Laplace transform. -/
def directionDetPolynomial {d : ℕ} (theta sigma : RealMatrix d) : Polynomial ℝ :=
  Matrix.det (1 + (Polynomial.X : Polynomial ℝ) •
    (-(theta * sigma)).map Polynomial.C)

/-- Evaluation commutes with this finite determinant. -/
theorem eval_directionDetPolynomial {d : ℕ} (theta sigma : RealMatrix d) (t : ℝ) :
    (directionDetPolynomial theta sigma).eval t =
      Matrix.det (1 - (t • theta) * sigma) := by
  change (Polynomial.evalRingHom t)
    (Matrix.det (1 + Polynomial.X • (-(theta * sigma)).map Polynomial.C)) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix, Matrix.map, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_mul]
  split_ifs <;> simp <;> ring

@[simp] theorem eval_directionDetPolynomial_zero {d : ℕ}
    (theta sigma : RealMatrix d) : (directionDetPolynomial theta sigma).eval 0 = 1 := by
  simp [eval_directionDetPolynomial]

/-- The exact Wishart transform is a real power of the directional determinant
polynomial in a neighborhood of zero. -/
theorem W_d.mgf_traceObservable_eq_detPolynomial_eventually {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) :
    mgf (traceObservable theta) W.toMeasure =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ Real.rpow ((directionDetPolynomial theta.1 sigma.1).eval t) (-beta)) := by
  simpa only [eval_directionDetPolynomial] using W.mgf_traceObservable_eventually theta

/-- The determinant transform satisfies its first-order polynomial differential
identity throughout a neighborhood of zero. This identity works for every real
shape carried by the exact `W_d` law. -/
theorem W_d.mgf_traceObservable_derivative_ode_eventually {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) :
    (fun t ↦ (directionDetPolynomial theta.1 sigma.1).eval t *
      deriv (mgf (traceObservable theta) W.toMeasure) t) =ᶠ[𝓝 (0 : ℝ)]
    (fun t ↦ -beta * (directionDetPolynomial theta.1 sigma.1).derivative.eval t *
      mgf (traceObservable theta) W.toMeasure t) := by
  let P := directionDetPolynomial theta.1 sigma.1
  have heq := W.mgf_traceObservable_eq_detPolynomial_eventually theta
  have htheta : theta.1.IsHermitian := by
    simpa only [Matrix.isHermitian_iff_isSymm] using theta.2
  filter_upwards [A4Research.eventually_posDef_sub_smul sigma.2.inv htheta,
    heq, heq.deriv] with t ht hvalue hderiv
  have hp : 0 < P.eval t := by
    change 0 < (directionDetPolynomial theta.1 sigma.1).eval t
    rw [eval_directionDetPolynomial]
    exact laplace_determinant_pos sigma ⟨t • theta.1, theta.2.smul t⟩ ht
  have hpowderiv := (Real.hasDerivAt_rpow_const
    (x := P.eval t) (p := -beta) (Or.inl hp.ne')).comp t (P.hasDerivAt t)
  have hd : deriv (fun t ↦ (P.eval t) ^ (-beta)) t =
      (-beta * (P.eval t) ^ (-beta - 1)) * P.derivative.eval t := by
    simpa only [Function.comp_def] using hpowderiv.deriv
  have hpow : P.eval t * (P.eval t) ^ (-beta - 1) = (P.eval t) ^ (-beta) := by
    conv_lhs => lhs; rw [← Real.rpow_one (P.eval t)]
    rw [← Real.rpow_add hp]
    congr 1
    ring
  change P.eval t * deriv (mgf (traceObservable theta) W.toMeasure) t =
    -beta * P.derivative.eval t * mgf (traceObservable theta) W.toMeasure t
  rw [hderiv, hvalue]
  change P.eval t * deriv (fun t ↦ (P.eval t) ^ (-beta)) t =
    -beta * P.derivative.eval t * (P.eval t) ^ (-beta)
  rw [hd]
  calc
    _ = -beta * P.derivative.eval t *
        (P.eval t * (P.eval t) ^ (-beta - 1)) := by ring
    _ = _ := by rw [hpow]

/-- An all-degree recurrence identity for the direct directional moments.
Its determinant factors are finite polynomial derivatives, so this supplies
a degree-lowering analytic route to the full moment tensor without any
integer-shape restriction. The combinatorial matching expansion remains a
separate obligation. -/
theorem W_d.directional_moment_polynomial_identity {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
      iteratedDeriv k (fun t ↦ (directionDetPolynomial theta.1 sigma.1).eval t) 0 *
      (∫ w, traceObservable theta w ^ (n - k + 1) ∂W.toMeasure)) =
    -beta * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
      iteratedDeriv (k + 1)
        (fun t ↦ (directionDetPolynomial theta.1 sigma.1).eval t) 0 *
      (∫ w, traceObservable theta w ^ (n - k) ∂W.toMeasure) := by
  let P := directionDetPolynomial theta.1 sigma.1
  let G := mgf (traceObservable theta) W.toMeasure
  have hzero := W.interior_integrableExpSet_traceObservable theta
  have hG : ContDiffAt ℝ n G 0 := (analyticAt_mgf hzero).contDiffAt
  have hG' : ContDiffAt ℝ n (deriv G) 0 := by
    simpa only [iteratedDeriv_one] using
      (analyticAt_iteratedDeriv_mgf hzero 1).contDiffAt (n := n)
  have hP : ContDiffAt ℝ n (fun t ↦ P.eval t) 0 := by
    exact (contDiff_realPolynomial_eval P n).contDiffAt
  have hP' : ContDiffAt ℝ n (deriv (fun t ↦ P.eval t)) 0 := by
    have hdfun : deriv (fun t ↦ P.eval t) = (fun t ↦ P.derivative.eval t) :=
      funext (fun t ↦ P.deriv)
    rw [hdfun]
    exact (contDiff_realPolynomial_eval P.derivative n).contDiffAt
  have hode : (fun t ↦ P.eval t * deriv G t) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ -beta * deriv (fun t ↦ P.eval t) t * G t) := by
    simpa only [Polynomial.deriv] using W.mgf_traceObservable_derivative_ode_eventually theta
  have hderiv := hode.iteratedDeriv_eq n
  have hright : (fun t ↦ -beta * deriv (fun t ↦ P.eval t) t * G t) =
      (fun t ↦ -beta * (deriv (fun t ↦ P.eval t) t * G t)) := by
    funext t
    ring
  rw [hright, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul hP hG', iteratedDeriv_fun_mul hP' hG] at hderiv
  simpa only [← iteratedDeriv_succ', G, iteratedDeriv_mgf_zero hzero,
    Pi.pow_apply] using hderiv

/-- Explicit degree-lowering recursion for every direct directional moment.
The moment in degree `n+1` depends only on moments in degrees at most `n`
and on the finite directional determinant polynomial. -/
theorem W_d.directional_moment_recurrence {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) (n : ℕ) :
    (∫ w, traceObservable theta w ^ (n + 1) ∂W.toMeasure) =
      -(∑ k ∈ Finset.range (n + 1),
        (beta * (n.choose k : ℝ) + (n.choose (k + 1) : ℝ)) *
          iteratedDeriv (k + 1)
            (fun t ↦ (directionDetPolynomial theta.1 sigma.1).eval t) 0 *
          (∫ w, traceObservable theta w ^ (n - k) ∂W.toMeasure)) := by
  let P := directionDetPolynomial theta.1 sigma.1
  let moment := fun r : ℕ ↦ ∫ w, traceObservable theta w ^ r ∂W.toMeasure
  let coeff := fun k : ℕ ↦ iteratedDeriv k (fun t : ℝ ↦ P.eval t) 0
  have hcoeff0 : coeff 0 = 1 := by
    simp only [coeff, iteratedDeriv_zero, P, eval_directionDetPolynomial_zero]
  have h := W.directional_moment_polynomial_identity theta n
  change (∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * coeff k * moment (n - k + 1)) =
    -beta * ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * coeff (k + 1) * moment (n - k) at h
  have hsplit : (∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * coeff k * moment (n - k + 1)) =
      moment (n + 1) + ∑ k ∈ Finset.range n,
        (n.choose (k + 1) : ℝ) * coeff (k + 1) * moment (n - (k + 1) + 1) := by
    rw [Finset.sum_range_succ']
    simp [hcoeff0, add_comm]
  have htail : (∑ k ∈ Finset.range n,
      (n.choose (k + 1) : ℝ) * coeff (k + 1) * moment (n - (k + 1) + 1)) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose (k + 1) : ℝ) * coeff (k + 1) * moment (n - k) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt := Finset.mem_range.mp hk
    have hsub : n - (k + 1) + 1 = n - k := by omega
    rw [hsub]
  rw [hsplit, htail] at h
  have hcombine : (∑ k ∈ Finset.range (n + 1),
      (beta * (n.choose k : ℝ) + (n.choose (k + 1) : ℝ)) *
        coeff (k + 1) * moment (n - k)) =
      beta * (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * coeff (k + 1) * moment (n - k)) +
      ∑ k ∈ Finset.range (n + 1),
        (n.choose (k + 1) : ℝ) * coeff (k + 1) * moment (n - k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change moment (n + 1) = -(∑ k ∈ Finset.range (n + 1),
    (beta * (n.choose k : ℝ) + (n.choose (k + 1) : ℝ)) *
      coeff (k + 1) * moment (n - k))
  rw [hcombine]
  linarith

end MatsumotoPaper
