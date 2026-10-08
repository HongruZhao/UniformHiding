import A4.WishartDensityInverseIntegrability
import A4.InverseMomentAlgebra
import A4.MatchingGramProduct

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- Exact transport of an independently proved inverse entry tensor to the
canonical matching notation of the original source. -/
theorem W_d.inverse_permuted_entry_moment_of_pairFormula
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hpair : ∀ (M : PM n) (j : Fin (2 * n) → Fin d),
      Complex.ofReal (∫ w : SymPosDef d, ∏ i : M.pairReps,
        w.1⁻¹ (j i.1) (j (M i.1)) ∂W.toMeasure) =
        ∑ N : PM n, modifiedGramInverse n gamma M N *
          ∏ i : N.pairReps, (sigma.1⁻¹ (j i.1) (j (N i.1)) : ℂ))
    (g : Equiv.Perm (Fin (2 * n))) (j : Fin (2 * n) → Fin d) :
    Complex.ofReal (∫ w : SymPosDef d, ∏ i : Fin n,
      w.1⁻¹ (j (g (leftSlot i))) (j (g (rightSlot i))) ∂W.toMeasure) =
      ∑ N : PerfectMatching n, wgTilde (g⁻¹ * N.toPerm) gamma *
        ∏ i : Fin n,
          (sigma.1⁻¹ (j (N.toPerm (leftSlot i))) (j (N.toPerm (rightSlot i))) : ℂ) := by
  classical
  have hprod (w : SymPosDef d) :
      (∏ i : Fin n, w.1⁻¹ (j (g (leftSlot i))) (j (g (rightSlot i)))) =
        ∏ i : (transportedPairPartition g).pairReps,
          w.1⁻¹ (j i.1) (j (transportedPairPartition g i.1)) :=
    prod_symmetric_pairWeight_transport g (fun i q ↦ w.1⁻¹ (j i) (j q))
      (fun i q ↦ (Matrix.isHermitian_iff_isSymm.mp w.2.inv.isHermitian).apply (j q) (j i))
  simp_rw [hprod]
  rw [hpair]
  rw [← sum_canonical_eq_sum_pairPartition]
  apply Finset.sum_congr rfl
  intro N _
  rw [wgTilde_relative]
  congr 1
  exact (prod_symmetric_pairWeight_transport N.toPerm
    (fun i q ↦ (sigma.1⁻¹ (j i) (j q) : ℂ))
    (fun i q ↦ congrArg Complex.ofReal
      ((Matrix.isHermitian_iff_isSymm.mp sigma.2.inv.isHermitian).apply (j q) (j i)))).symm

/-- The complete finite contraction of the inverse entry tensor is exactly
the literal inverse `T_g` formula, including arbitrary complex test matrices.
Its displayed entry premise is discharged by the full inverse proof. -/
theorem W_d.inverse_matching_moment_of_pairFormula
    {d n : ℕ} {beta gamma : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (hpair : ∀ (M : PM n) (j : Fin (2 * n) → Fin d),
      Complex.ofReal (∫ w : SymPosDef d, ∏ i : M.pairReps,
        w.1⁻¹ (j i.1) (j (M i.1)) ∂W.toMeasure) =
        ∑ N : PM n, modifiedGramInverse n gamma M N *
          ∏ i : N.pairReps, (sigma.1⁻¹ (j i.1) (j (N i.1)) : ℂ))
    (m : Fin n → ComplexMatrix d) (g : Equiv.Perm (Fin (2 * n))) :
    expectation W (fun w ↦ T g (SymPosDef.inverse w).1 m) =
      ∑ N : PerfectMatching n, wgTilde (g⁻¹ * N.toPerm) gamma *
        T N.toPerm (SymPosDef.inverse sigma).1 m := by
  classical
  change expectation W (fun w ↦ T g w.1⁻¹ m) = _
  rw [W.expectation_inverse_T_eq_entryMoments hgamma hgap]
  simp_rw [W.inverse_permuted_entry_moment_of_pairFormula hpair]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N _
  unfold T
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change _ = wgTilde (g⁻¹ * N.toPerm) gamma *
    ((∏ i : Fin n, m i (j (leftSlot i)) (j (rightSlot i))) *
      ∏ i : Fin n, (sigma.1⁻¹ (j (N.toPerm (leftSlot i)))
        (j (N.toPerm (rightSlot i))) : ℂ))
  ring

end MatsumotoPaper
