import A4.LaplaceIntegrability
import A4.PositiveDefiniteNeighborhood
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace MatsumotoPaper

/-- The scalar random variable obtained from a symmetric matrix direction. -/
def traceObservable {d : ℕ} (theta : Sym d) (w : SymPosDef d) : ℝ :=
  Matrix.trace (theta.1 * w.1)

/-- The Wishart matrix transform supplies an open scalar exponential-moment
domain in every symmetric direction. No restriction on the real shape is added. -/
theorem W_d.interior_integrableExpSet_traceObservable {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) :
    (0 : ℝ) ∈ interior (integrableExpSet (traceObservable theta) W.toMeasure) := by
  apply mem_interior_iff_mem_nhds.mpr
  have htheta : theta.1.IsHermitian := by
    simpa only [Matrix.isHermitian_iff_isSymm] using theta.2
  filter_upwards [A4Research.eventually_posDef_sub_smul sigma.2.inv htheta] with t ht
  have h := W.integrable_etr ⟨t • theta.1, theta.2.smul t⟩ ht
  simpa only [integrableExpSet, mem_setOf_eq, etr, traceObservable,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using h

/-- Every finite scalar moment in a symmetric direction is integrable. -/
theorem W_d.integrable_traceObservable_pow {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) (n : ℕ) :
    Integrable (fun w ↦ traceObservable theta w ^ n) W.toMeasure :=
  integrable_pow_of_mem_interior_integrableExpSet
    (W.interior_integrableExpSet_traceObservable theta) n

/-- Every finite scalar `L^p` norm exists in a symmetric direction. -/
theorem W_d.memLp_traceObservable {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) (p : ℝ≥0) :
    MemLp (traceObservable theta) p W.toMeasure :=
  memLp_of_mem_interior_integrableExpSet
    (W.interior_integrableExpSet_traceObservable theta) p

/-- The scalar moment-generating function agrees locally with the determinant
formula in the exact original matrix-law definition. -/
theorem W_d.mgf_traceObservable_eventually {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) :
    mgf (traceObservable theta) W.toMeasure =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ Real.rpow (Matrix.det (1 - (t • theta.1) * sigma.1)) (-beta)) := by
  have htheta : theta.1.IsHermitian := by
    simpa only [Matrix.isHermitian_iff_isSymm] using theta.2
  filter_upwards [A4Research.eventually_posDef_sub_smul sigma.2.inv htheta] with t ht
  simpa only [mgf, etr, traceObservable, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul] using
    W.laplace_transform ⟨t • theta.1, theta.2.smul t⟩ ht

/-- For every degree, direct scalar trace moments are exactly the derivatives
of the Wishart determinant transform. This is an all-degree consequence of
the original Laplace characterization; it does not yet expand the derivatives
into A4's perfect-matching coefficients. -/
theorem W_d.integral_traceObservable_pow {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) (n : ℕ) :
    (∫ w, traceObservable theta w ^ n ∂W.toMeasure) =
      iteratedDeriv n
        (fun t : ℝ ↦ Real.rpow (Matrix.det (1 - (t • theta.1) * sigma.1)) (-beta))
        0 := by
  calc
    _ = iteratedDeriv n (mgf (traceObservable theta) W.toMeasure) 0 := by
      simpa only [Pi.pow_apply] using
        (iteratedDeriv_mgf_zero (W.interior_integrableExpSet_traceObservable theta) n).symm
    _ = _ := (W.mgf_traceObservable_eventually theta).iteratedDeriv_eq n

/-- Products of arbitrarily many symmetric trace observables are integrable.
The proof uses all-order scalar exponential moments and finite-product Hölder. -/
theorem W_d.integrable_prod_traceObservable {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Fin n → Sym d) :
    Integrable (fun w ↦ ∏ i : Fin n, traceObservable (theta i) w) W.toMeasure := by
  letI : IsProbabilityMeasure W.toMeasure := W.probability
  by_cases hn : n = 0
  · subst n
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : SymPosDef d ↦ (1 : ℝ)) W.toMeasure)
  have hsum : (∑ i : Fin n, ((n : ℝ≥0∞)⁻¹))⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hn) (ENNReal.natCast_ne_top n)]
    simp
  have hprod := MemLp.prod' (s := Finset.univ) (p := fun _ : Fin n ↦ (n : ℝ≥0∞))
    (fun i _ ↦ W.memLp_traceObservable (theta i) (n : ℝ≥0))
  apply memLp_one_iff_integrable.mp
  simpa only [hsum] using hprod

/-- A symmetric matrix direction representing one matrix entry under the trace pairing. -/
def entryTraceDirection {d : ℕ} (i j : Fin d) : Sym d :=
  ⟨(1 / 2 : ℝ) • (Matrix.single i j 1 + Matrix.single j i 1), by
    apply Matrix.IsSymm.smul
    unfold Matrix.IsSymm
    rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single]
    exact add_comm _ _⟩

/-- Symmetry makes the off-diagonal averaging in the entry trace direction exact. -/
theorem traceObservable_entryTraceDirection {d : ℕ} (i j : Fin d) (w : SymPosDef d) :
    traceObservable (entryTraceDirection i j) w = w.1 i j := by
  have hw : w.1.IsSymm := by
    simpa only [Matrix.isHermitian_iff_isSymm] using w.2.isHermitian
  simp only [traceObservable, entryTraceDirection, Matrix.smul_mul, Matrix.add_mul,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_single_mul, smul_eq_mul,
    one_mul, hw.apply i j]
  ring

/-- Every finite product of real Wishart entries is integrable, for arbitrary
indices and degree. This covers each entry monomial in the direct A4 contraction. -/
theorem W_d.integrable_prod_entries {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (i j : Fin n → Fin d) :
    Integrable (fun w ↦ ∏ k : Fin n, w.1 (i k) (j k)) W.toMeasure := by
  simpa only [traceObservable_entryTraceDirection] using
    W.integrable_prod_traceObservable (fun k ↦ entryTraceDirection (i k) (j k))

/-- The complex embedding of every finite entry product is integrable. -/
theorem W_d.integrable_prod_complex_entries {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (i j : Fin n → Fin d) :
    Integrable (fun w ↦ ∏ k : Fin n, (w.1 (i k) (j k) : ℂ)) W.toMeasure := by
  apply ((W.integrable_prod_entries i j).ofReal (𝕜 := ℂ)).congr
  filter_upwards [] with w
  push_cast
  rfl

/-- The entire direct contraction in A4 is integrable for every degree and
arbitrary complex test matrices and permutation. -/
theorem W_d.integrable_T {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (g : Equiv.Perm (Fin (2 * n))) (m : Fin n → ComplexMatrix d) :
    Integrable (fun w ↦ T g w.1 m) W.toMeasure := by
  unfold T
  apply integrable_finsetSum
  intro j _
  exact (W.integrable_prod_complex_entries
    (fun i ↦ j (g (leftSlot i))) (fun i ↦ j (g (rightSlot i)))).const_mul _

/-- The direct contraction is the finite contraction of its entry-moment
tensor. All integrability obligations needed to distribute the integral have
been proved from the Laplace law. -/
theorem W_d.expectation_T_eq_entryMoments {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (g : Equiv.Perm (Fin (2 * n))) (m : Fin n → ComplexMatrix d) :
    expectation W (fun w ↦ T g w.1 m) =
      ∑ j : Fin (2 * n) → Fin d,
        (∏ i : Fin n, m i (j (leftSlot i)) (j (rightSlot i))) *
          Complex.ofReal (∫ w, ∏ i : Fin n,
            w.1 (j (g (leftSlot i))) (j (g (rightSlot i))) ∂W.toMeasure) := by
  unfold expectation T
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    congr 1
    calc
      _ = ∫ w, Complex.ofReal (∏ i : Fin n,
          w.1 (j (g (leftSlot i))) (j (g (rightSlot i)))) ∂W.toMeasure := by
        apply integral_congr_ae
        filter_upwards [] with w
        push_cast
        rfl
      _ = _ := integral_complex_ofReal
  · intro j _
    exact (W.integrable_prod_complex_entries
      (fun i ↦ j (g (leftSlot i))) (fun i ↦ j (g (rightSlot i)))).const_mul _

/-- The first determinant derivative in a fixed direction, proved using the
matrix determinant polynomial rather than eigenvalue differentiation. -/
theorem hasDerivAt_det_identity_sub_smul_mul {d : ℕ}
    (theta sigma : RealMatrix d) :
    HasDerivAt (fun t : ℝ ↦ Matrix.det (1 - (t • theta) * sigma))
      (-Matrix.trace (theta * sigma)) 0 := by
  let M : RealMatrix d := -(theta * sigma)
  let P : Polynomial ℝ :=
    Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)
  have hcoeff : P.derivative.eval 0 = Matrix.trace M :=
    Matrix.derivative_det_one_add_X_smul M
  have h := P.hasDerivAt (0 : ℝ)
  rw [hcoeff] at h
  have hpoly : (fun x : ℝ ↦ P.eval x) =
      (fun t : ℝ ↦ Matrix.det (1 - (t • theta) * sigma)) := by
    funext t
    change (Polynomial.evalRingHom t)
      (Matrix.det (1 + Polynomial.X • M.map Polynomial.C)) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix, Matrix.map, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply, M, Matrix.smul_mul]
    split_ifs <;> simp <;> ring
  rw [hpoly] at h
  simpa [M] using h

/-- The first trace moment is the shape times the scale trace pairing. -/
theorem W_d.integral_traceObservable {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (theta : Sym d) :
    (∫ w, traceObservable theta w ∂W.toMeasure) =
      beta * Matrix.trace (theta.1 * sigma.1) := by
  have hdet := hasDerivAt_det_identity_sub_smul_mul theta.1 sigma.1
  have hdet0 : Matrix.det (1 - ((0 : ℝ) • theta.1) * sigma.1) = 1 := by simp
  have hpow := (Real.hasDerivAt_rpow_const
    (x := Matrix.det (1 - ((0 : ℝ) • theta.1) * sigma.1))
    (p := -beta) (Or.inl (by simp))).comp (0 : ℝ) hdet
  have hmom := W.integral_traceObservable_pow theta 1
  simp only [pow_one, iteratedDeriv_one] at hmom
  rw [hmom]
  simpa [Function.comp_def] using hpow.deriv

/-- The matrix-entry mean follows without integer-shape or rank restrictions. -/
theorem W_d.integral_entry {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) (i j : Fin d) :
    (∫ w, w.1 i j ∂W.toMeasure) = beta * sigma.1 i j := by
  have h := W.integral_traceObservable (entryTraceDirection i j)
  change (∫ w, traceObservable (entryTraceDirection i j) w ∂W.toMeasure) =
    beta * traceObservable (entryTraceDirection i j) sigma at h
  simpa only [traceObservable_entryTraceDirection] using h

end MatsumotoPaper
