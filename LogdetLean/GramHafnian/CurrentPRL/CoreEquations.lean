import LogdetLean.GramHafnian.ShiftedAnticoncentration

/-!
# Paper facing endpoints for the current PRL

This module gives stable names to the internally proved equations used in
``Quadratic Small Ball Anticoncentration for Gaussian Gram Hafnians``.
The theorem names follow the equation numbers in the current manuscript.

No external scientific assumption is introduced here.  The finite Haar
transport is deliberately isolated in `ExternalHiding.lean`.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace LogdetLean.GramHafnian.CurrentPRL

noncomputable section

open LogdetLean.GramHafnian

/-- PRL Eq. (2): the observable is the hafnian of the transpose Gram matrix.
The finite perfect matching sum is the definition of `gramHafnian`. -/
theorem eq2_model (n k : ℕ) (X : ComplexColumnMatrix n k) :
    gramHafnianObservable n k X = gramHafnian (rowMatrix X) := by
  rfl

/-- PRL Eq. (3): the standard deviation is the literal second absolute
moment of the Gaussian Gram hafnian. -/
theorem eq3_variance_is_actual_second_moment
    (k n : ℕ) (hk : 0 < k) :
    gramHafnianSigma k n ^ 2 = actualGramFirstMomentReal k n :=
  gramHafnianSigma_sq_eq_actualSecondMoment k n hk

/-- PRL Eq. (3), displayed finite product form.  `oddPairingNat n` is the
project's exact encoding of `(2n-1)!!`. -/
theorem eq3_variance_product (k n : ℕ) (hk : 0 < k) :
    gramHafnianSigma k n ^ 2 =
      (oddPairingNat n : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ) := by
  rw [gramHafnianSigma_sq k n hk]
  rfl

/-- PRL Eq. (4): uniformly shifted quadratic small ball theorem, including
the probability cap. -/
theorem eq4_shifted_small_ball
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    gramHafnianShiftedSmallBallProbability k n z eps ≤
      min 1 (shiftedAnticoncentrationConstant k n * eps ^ 2) :=
  gaussianGramHafnianShiftedAnticoncentration_min n k hn hk z eps heps

/-- PRL Eq. (5): exact product definition of the finite coefficient. -/
theorem eq5_coefficient_product (k n : ℕ) :
    shiftedAnticoncentrationConstant k n =
      (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n *
        ((k : ℝ) / ((k : ℝ) - 1)) *
        ∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1)) := by
  rfl

/-- PRL Eq. (6): the three cofactor quantities are literal definitions.
This conjunction makes their coordinate formulas available as one audited
endpoint. -/
theorem eq6_cofactor_quantities
    {r k : ℕ} (hr : 1 ≤ r) (X : ComplexColumnMatrix r k) :
    oddCofactorW hr X =
        ∑ j : OddCofactorIndex r hr,
          Complex.normSq (oddHafnianCofactorVector hr X j) ∧
      oddCofactorV hr X =
        ∑ a : Fin k,
          Complex.normSq (oddCofactorColumnCombination hr X a) := by
  exact ⟨rfl, rfl⟩

/-- PRL Eq. (7), algebraic part: expansion in the exposed final column. -/
theorem eq7_last_column_expansion
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) :
    gramHafnianObservable r k (lastColumnProductEquiv r k hr p) =
      conditionalCircularLinearForm (pastCofactorCombination hr) p :=
  gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm hr p

/-- PRL Eq. (7), law part: conditionally on fixed past columns, the exposed
linear form is a circular complex Gaussian scaled by `sqrt V_r`. -/
theorem eq7_fixed_past_gaussian_law
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    (Measure.pi fun _ : Fin k ↦ circularGaussian).map
        (iidCircularTransposeLinearForm (pastCofactorCombination hr A)) =
      circularGaussian.map
        (fun z : ℂ ↦ Real.sqrt (pastCofactorV hr A) • z) := by
  simpa [pastCofactorV_eq_coefficientEnergy] using
    (map_iidCircularTransposeLinearForm_eq_scaled_circular
      (pastCofactorCombination hr A))

/-- PRL Eq. (8): the exact shifted disk estimate before normalization. -/
theorem eq8_disk_bound
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos : ∀ᵐ A ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
      circularGaussianVector k), 0 < pastCofactorV hr A)
    (z : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (circularGaussianColumnMatrixMeasure r k)
        {X | ‖gramHafnianObservable r k X - z‖ ≤ rho} ≤
      ENNReal.ofReal (rho ^ 2) *
        ennInverseMoment
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k)
          (pastCofactorV hr) :=
  circularGaussianColumnMatrix_shiftedSmallBall_le_pastInverseMoment
    hr hVpos z rho hrho

/-- PRL Eq. (9): Fourier cofactor inverse moment comparison. -/
theorem eq9_fourier
    (k r : ℕ) (hr : 2 ≤ r) (hk : 4 * r ≤ k) :
    pastCofactorWInverseMoment k r ≤
      pastCofactorVInverseMoment k (r - 1) *
        ENNReal.ofReal (((2 : ℝ) * r - 2)⁻¹) :=
  pastCofactorWInverseMoment_le_fourier k r hr (by omega)

/-- PRL Eq. (10): conditional Wishart inverse moment comparison. -/
theorem eq10_wishart
    (k r : ℕ) (hr : 2 ≤ r) (hk : 4 * r ≤ k) :
    pastCofactorVInverseMoment k r ≤
      pastCofactorWInverseMoment k r *
        ENNReal.ofReal (((k : ℝ) - 4 * r + 1)⁻¹) :=
  Wishart.pastCofactorVInverseMoment_le_wishart k r hr hk

/-- PRL Eq. (11): the iterated inverse variance product, in the exact
extended nonnegative expectation representation used by the proof. -/
theorem eq11_inverse_variance
    (k n : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    pastCofactorVInverseMoment k n ≤
      ENNReal.ofReal (inverseVarianceBound k n) := by
  apply pastCofactorVInverseMoment_le_inverseVarianceBound_of_steps k n hn hk
  · intro r hr hrn
    exact pastCofactorWInverseMoment_le_fourier k r hr (by omega)
  · intro r hr hrn
    exact Wishart.pastCofactorVInverseMoment_le_wishart k r hr (by omega)

/-- The first level used in PRL Eq. (11) is exactly `(k-1)^{-1}`. -/
theorem eq11_base_inverse_moment (k : ℕ) (hk : 2 ≤ k) :
    pastCofactorVInverseMoment k 1 =
      ENNReal.ofReal (((k : ℝ) - 1)⁻¹) :=
  pastCofactorVInverseMoment_level_one hk

/-- The normalized coefficient is exactly second moment times the inverse
variance product.  This is the final algebraic step from Eqs. (3) and (11)
to Eqs. (4) and (5). -/
theorem eq3_mul_eq11_is_eq5 (k n : ℕ) (hn : 1 ≤ n) :
    closedFirstMoment k n * inverseVarianceBound k n =
      shiftedAnticoncentrationConstant k n :=
  closedFirstMoment_mul_inverseVarianceBound k n hn

end

end LogdetLean.GramHafnian.CurrentPRL
