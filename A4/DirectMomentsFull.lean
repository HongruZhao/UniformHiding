import A4.DirectMomentsInterpolation
import A4.MatchingGramProduct

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- The direct entry product for an arbitrary source permutation, rewritten
in the literal canonical matching notation of the A4 target. -/
theorem W_d.direct_permuted_entry_moment {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (g : Equiv.Perm (Fin (2 * n))) (j : Fin (2 * n) → Fin d) :
    (∫ w, ∏ i : Fin n,
      w.1 (j (g (leftSlot i))) (j (g (rightSlot i))) ∂W.toMeasure) =
      (2 : ℝ) ^ (-(n : ℤ)) *
        ∑ N : PerfectMatching n, (2 * beta) ^ kappa (g⁻¹ * N.toPerm) *
          ∏ i : Fin n,
            sigma.1 (j (N.toPerm (leftSlot i))) (j (N.toPerm (rightSlot i))) := by
  classical
  have hprod (w : SymPosDef d) :
      (∏ i : Fin n, w.1 (j (g (leftSlot i))) (j (g (rightSlot i)))) =
        ∏ i : (transportedPairPartition g).pairReps,
          w.1 (j i.1) (j (transportedPairPartition g i.1)) :=
    prod_symmetric_pairWeight_transport g (fun i q ↦ w.1 (j i) (j q))
      (fun i q ↦ (Matrix.isHermitian_iff_isSymm.mp w.2.isHermitian).apply (j q) (j i))
  simp_rw [hprod]
  rw [W.direct_pairPartition_moment]
  congr 1
  rw [← sum_canonical_eq_sum_pairPartition]
  apply Finset.sum_congr rfl
  intro N _
  rw [kappa_relative]
  congr 1
  exact (prod_symmetric_pairWeight_transport N.toPerm
    (fun i q ↦ sigma.1 (j i) (j q))
    (fun i q ↦ (Matrix.isHermitian_iff_isSymm.mp sigma.2.isHermitian).apply (j q) (j i))).symm

/-- A4's complete direct branch: all degrees, arbitrary real shape and SPD
scale, arbitrary complex test matrices, and an arbitrary source permutation.
Every scientific premise is exactly the original `W_d` characterization. -/
theorem W_d.direct_matching_moment {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (m : Fin n → ComplexMatrix d) (g : Equiv.Perm (Fin (2 * n))) :
    expectation W (fun w ↦ T g w.1 m) =
      (2 : ℂ) ^ (-(n : ℤ)) *
        ∑ N : PerfectMatching n,
          (((2 * beta) ^ kappa (g⁻¹ * N.toPerm) : ℝ) : ℂ) * T N.toPerm sigma.1 m := by
  classical
  rw [W.expectation_T_eq_entryMoments]
  simp_rw [W.direct_permuted_entry_moment]
  simp only [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_prod]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N _
  unfold T
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end MatsumotoPaper
