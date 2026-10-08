import A4.DirectMomentsMixedShape
import A4.DirectMomentsGaussianWick

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- The degree-`n` real shape polynomial for an arbitrary product of entries. -/
def entryProductShapePolynomial {d n : ℕ} (r s : Fin n → Fin d)
    (sigma : RealMatrix d) : Polynomial ℝ :=
  mixedShapeMomentPolynomial (fun i ↦ entryTraceDirection (r i) (s i)) sigma

theorem natDegree_entryProductShapePolynomial_le {d n : ℕ}
    (r s : Fin n → Fin d) (sigma : RealMatrix d) :
    (entryProductShapePolynomial r s sigma).natDegree ≤ n :=
  natDegree_mixedShapeMomentPolynomial_le _ _

theorem W_d.integral_prod_entries_eq_eval_entryProductShapePolynomial
    {d n : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (r s : Fin n → Fin d) :
    (∫ w, ∏ i : Fin n, w.1 (r i) (s i) ∂W.toMeasure) =
      (entryProductShapePolynomial r s sigma.1).eval beta := by
  simpa only [entryProductShapePolynomial, traceObservable_entryTraceDirection] using
    W.integral_prod_traceObservable_eq_eval_mixedShapeMomentPolynomial
      (fun i ↦ entryTraceDirection (r i) (s i))

/-- Entry moments indexed by the actual involution matching and a slot map. -/
def pairPartitionEntryShapePolynomial {d n : ℕ} (sigma : RealMatrix d)
    (M : PM n) (j : Fin (2 * n) → Fin d) : Polynomial ℝ :=
  entryProductShapePolynomial
    (fun i ↦ j (matchingPairOrder M i))
    (fun i ↦ j (M (matchingPairOrder M i))) sigma

theorem natDegree_pairPartitionEntryShapePolynomial_le {d n : ℕ}
    (sigma : RealMatrix d) (M : PM n) (j : Fin (2 * n) → Fin d) :
    (pairPartitionEntryShapePolynomial sigma M j).natDegree ≤ n :=
  natDegree_entryProductShapePolynomial_le _ _ _

theorem W_d.integral_pairPartition_entries_eq_eval_shapePolynomial
    {d n : ℕ} {beta : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (M : PM n) (j : Fin (2 * n) → Fin d) :
    (∫ w, ∏ i : M.pairReps, w.1 (j i.1) (j (M i.1)) ∂W.toMeasure) =
      (pairPartitionEntryShapePolynomial sigma.1 M j).eval beta := by
  rw [show (fun w : SymPosDef d ↦
      ∏ i : M.pairReps, w.1 (j i.1) (j (M i.1))) =
      fun w ↦ ∏ i : Fin n, w.1 (j (matchingPairOrder M i))
        (j (M (matchingPairOrder M i))) by
    funext w
    exact ((wickMatchingPairRepsEquiv M).prod_comp
      (fun i : M.pairReps ↦ w.1 (j i.1) (j (M i.1)))).symm]
  exact W.integral_prod_entries_eq_eval_entryProductShapePolynomial _ _

/-- A4's direct matching coefficient as a polynomial in the real shape. -/
def matchingEntryMomentPolynomial {d n : ℕ} (sigma : RealMatrix d)
    (M : PM n) (j : Fin (2 * n) → Fin d) : Polynomial ℝ :=
  ((2 : ℝ) ^ (-(n : ℤ))) •
    ∑ N : PM n,
      Polynomial.C (∏ i : N.pairReps, sigma (j i.1) (j (N i.1))) *
        (Polynomial.C 2 * Polynomial.X) ^ matchingKappa M N

theorem natDegree_matchingEntryMomentPolynomial_le {d n : ℕ}
    (sigma : RealMatrix d) (M : PM n) (j : Fin (2 * n) → Fin d) :
    (matchingEntryMomentPolynomial sigma M j).natDegree ≤ n := by
  unfold matchingEntryMomentPolynomial
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro N _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have hbase : (Polynomial.C (2 : ℝ) * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have h := Polynomial.natDegree_pow_le_of_le (matchingKappa M N) hbase
  simpa using h.trans (by simpa using matchingKappa_le M N)

theorem eval_matchingEntryMomentPolynomial {d n : ℕ} (sigma : RealMatrix d)
    (M : PM n) (j : Fin (2 * n) → Fin d) (beta : ℝ) :
    (matchingEntryMomentPolynomial sigma M j).eval beta =
      (2 : ℝ) ^ (-(n : ℤ)) * ∑ N : PM n, (2 * beta) ^ matchingKappa M N *
        ∏ i : N.pairReps, sigma (j i.1) (j (N i.1)) := by
  simp only [matchingEntryMomentPolynomial, Polynomial.eval_smul,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro N _
  ring

/-- The exact all-degree interpolation step from distinct comparison shapes
to the complete direct entry-moment polynomial. All comparison equalities
are displayed explicitly, for application to the proved Gaussian laws. -/
theorem pairPartitionEntryShapePolynomial_eq_matching_of_samples
    {d n : ℕ} (sigma : RealMatrix d) (M : PM n) (j : Fin (2 * n) → Fin d)
    (sample : Fin (n + 1) → ℝ) (hinj : Function.Injective sample)
    (hsample : ∀ i,
      (pairPartitionEntryShapePolynomial sigma M j).eval (sample i) =
        (matchingEntryMomentPolynomial sigma M j).eval (sample i)) :
    pairPartitionEntryShapePolynomial sigma M j = matchingEntryMomentPolynomial sigma M j := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj hsample
  simpa using Nat.lt_succ_of_le (max_le
    (natDegree_pairPartitionEntryShapePolynomial_le sigma M j)
    (natDegree_matchingEntryMomentPolynomial_le sigma M j))

end MatsumotoPaper
