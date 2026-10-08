import A4.DirectMomentsAnalytic
import A4.MatchingGram

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

/-- The first direct contraction has expectation `beta` times the scale
contraction, for arbitrary complex test matrices and every slot permutation. -/
theorem W_d.expectation_T_first {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (g : Equiv.Perm (Fin (2 * 1)))
    (m : Fin 1 → ComplexMatrix d) :
    expectation W (fun w ↦ T g w.1 m) = (beta : ℂ) * T g sigma.1 m := by
  rw [W.expectation_T_eq_entryMoments]
  simp only [Fin.prod_univ_one, W.integral_entry, Complex.ofReal_mul]
  unfold T
  simp only [Fin.prod_univ_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- In degree one a symmetric matrix contraction is independent of the two-slot
permutation. This uses only matrix symmetry, without restrictions on the test. -/
theorem T_first_eq_identity {d : ℕ} (g : Equiv.Perm (Fin (2 * 1)))
    (x : RealMatrix d) (hx : x.IsSymm) (m : Fin 1 → ComplexMatrix d) :
    T g x m = T 1 x m := by
  have hg : (g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 1 ∧ g 1 = 0) := by
    have hne : g 0 ≠ g 1 := g.injective.ne (by decide)
    by_cases h0 : g 0 = 0
    · exact Or.inl ⟨h0, Fin.eq_one_of_ne_zero (g 1)
        (by intro h1; exact hne (h0.trans h1.symm))⟩
    · have hg0 := Fin.eq_one_of_ne_zero (g 0) h0
      have hg1 : g 1 = 0 := by
        by_contra h1
        exact hne (hg0.trans (Fin.eq_one_of_ne_zero (g 1) h1).symm)
      exact Or.inr ⟨hg0, hg1⟩
  unfold T
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.prod_univ_one]
  rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simp [leftSlot, rightSlot, h0, h1]
  · simp [leftSlot, rightSlot, h0, h1, hx.apply (j 0) (j 1)]

/-- The degree-one instance of A4's exact direct perfect-matching formula.
This is a checked base case, not a replacement for the all-degree target. -/
theorem W_d.direct_matching_moment_one {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (m : Fin 1 → ComplexMatrix d)
    (g : Equiv.Perm (Fin (2 * 1))) :
    expectation W (fun w ↦ T g w.1 m) =
      (2 : ℂ) ^ (-(1 : ℤ)) *
        ∑ matching : PerfectMatching 1,
          (((2 * beta) ^ kappa (g⁻¹ * matching.toPerm) : ℝ) : ℂ) *
            T matching.toPerm sigma.1 m := by
  rw [W.expectation_T_first]
  have hsigma : sigma.1.IsSymm := by
    simpa only [Matrix.isHermitian_iff_isSymm] using sigma.2.isHermitian
  rw [T_first_eq_identity g sigma.1 hsigma m, sum_canonicalMatching_one]
  simp only [standardCanonicalMatching_toPerm, kappa_one, pow_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat, _root_.zpow_neg_one]
  norm_num
  ring

end MatsumotoPaper
