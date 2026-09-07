import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary bounds for the Gaussian radial factor

This experimental module isolates the scalar inequalities used in the radial
lower bound.  It contains no probabilistic or hafnian input.
-/

namespace LogdetLean.GramHafnian

noncomputable section

/-- The exact contribution of `2n-1` independent `Gamma(k,1)` radii to the
product of a first moment and an inverse first moment. -/
def cofactorRadialFactor (k n : ℕ) : ℝ :=
  (((k : ℝ) / ((k : ℝ) - 1)) ^ (2 * n - 1))

/-- The logarithm of one radial factor lies between `1/k` and `2/k`. -/
theorem one_div_le_log_radialBase_le_two_div
    (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / k ≤ Real.log ((k : ℝ) / ((k : ℝ) - 1)) ∧
      Real.log ((k : ℝ) / ((k : ℝ) - 1)) ≤ 2 / k := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkm1pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hbasepos : (0 : ℝ) < (k : ℝ) / ((k : ℝ) - 1) :=
    div_pos hkpos hkm1pos
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hbasepos
    calc
      (1 : ℝ) / k = 1 - (((k : ℝ) / ((k : ℝ) - 1))⁻¹) := by
        field_simp
        ring
      _ ≤ Real.log ((k : ℝ) / ((k : ℝ) - 1)) := h
  · have h := Real.log_le_sub_one_of_pos hbasepos
    calc
      Real.log ((k : ℝ) / ((k : ℝ) - 1))
          ≤ (k : ℝ) / ((k : ℝ) - 1) - 1 := h
      _ = 1 / ((k : ℝ) - 1) := by
        field_simp
        ring
      _ ≤ 2 / k := by
        apply (div_le_div_iff₀ hkm1pos hkpos).2
        nlinarith

/-- The exact radial factor is at least `exp((2n-1)/k)`. -/
theorem exp_two_mul_sub_one_div_le_cofactorRadialFactor
    (k n : ℕ) (hk : 2 ≤ k) :
    Real.exp ((((2 * n - 1 : ℕ) : ℝ)) / (k : ℝ)) ≤
      cofactorRadialFactor k n := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkm1pos : (0 : ℝ) < (k : ℝ) - 1 := by
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hbasepos : (0 : ℝ) < (k : ℝ) / ((k : ℝ) - 1) :=
    div_pos hkpos hkm1pos
  have hlog := (one_div_le_log_radialBase_le_two_div k hk).1
  have hmul :
      (((2 * n - 1 : ℕ) : ℝ)) / (k : ℝ) ≤
        ((2 * n - 1 : ℕ) : ℝ) *
          Real.log ((k : ℝ) / ((k : ℝ) - 1)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hlog) (by positivity)
  calc
    Real.exp ((((2 * n - 1 : ℕ) : ℝ)) / (k : ℝ)) ≤
        Real.exp (((2 * n - 1 : ℕ) : ℝ) *
          Real.log ((k : ℝ) / ((k : ℝ) - 1))) :=
      Real.exp_le_exp.mpr hmul
    _ = cofactorRadialFactor k n := by
      rw [show ((2 * n - 1 : ℕ) : ℝ) = (2 * n - 1 : ℕ) by rfl,
        Real.exp_nat_mul, Real.exp_log hbasepos]
      rfl

/-- The simpler lower bound `exp(n/k)` forced by the Gaussian radii. -/
theorem exp_n_div_le_cofactorRadialFactor
    (k n : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) :
    Real.exp ((n : ℝ) / (k : ℝ)) ≤ cofactorRadialFactor k n := by
  apply le_trans (Real.exp_le_exp.mpr ?_)
    (exp_two_mul_sub_one_div_le_cofactorRadialFactor k n hk)
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  apply (div_le_div_iff_of_pos_right hkpos).2
  exact_mod_cast (show n ≤ 2 * n - 1 by omega)

/-- The exact radial factor is at most `exp(2(2n-1)/k)`. -/
theorem cofactorRadialFactor_le_exp_two_mul
    (k n : ℕ) (hk : 2 ≤ k) :
    cofactorRadialFactor k n ≤
      Real.exp (2 * (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ))) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkm1pos : (0 : ℝ) < (k : ℝ) - 1 := by
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hbasepos : (0 : ℝ) < (k : ℝ) / ((k : ℝ) - 1) :=
    div_pos hkpos hkm1pos
  have hlog := (one_div_le_log_radialBase_le_two_div k hk).2
  have hmul :
      ((2 * n - 1 : ℕ) : ℝ) *
          Real.log ((k : ℝ) / ((k : ℝ) - 1)) ≤
        2 * (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) := by
    rw [show 2 * (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) =
      ((2 * n - 1 : ℕ) : ℝ) * (2 / (k : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  calc
    cofactorRadialFactor k n =
        Real.exp (((2 * n - 1 : ℕ) : ℝ) *
          Real.log ((k : ℝ) / ((k : ℝ) - 1))) := by
      rw [show ((2 * n - 1 : ℕ) : ℝ) = (2 * n - 1 : ℕ) by rfl,
        Real.exp_nat_mul, Real.exp_log hbasepos]
      rfl
    _ ≤ Real.exp (2 * (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ))) :=
      Real.exp_le_exp.mpr hmul

end

end LogdetLean.GramHafnian
