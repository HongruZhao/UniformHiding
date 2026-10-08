import A4.DirectMomentsEntryPolynomial
import A4.GaussianWishartMoments
import A4.WishartDensityRecursive

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- `n+1` distinct Gaussian shapes, all in the positive real-shape range. -/
def directMomentSampleRows (d n : ℕ) (i : Fin (n + 1)) : ℕ := d + 2 * n + 2 * i.val

def directMomentSample (d n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (directMomentSampleRows d n i : ℝ) / 2

theorem directMomentSample_injective (d n : ℕ) :
    Function.Injective (directMomentSample d n) := by
  intro i j hij
  apply Fin.ext
  have hcast : (i.val : ℝ) = (j.val : ℝ) := by
    dsimp [directMomentSample, directMomentSampleRows] at hij
    push_cast at hij
    linarith
  exact_mod_cast hcast

theorem directMomentSample_admissible (d n : ℕ) (i : Fin (n + 1)) :
    ((d : ℝ) - 1) / 2 < directMomentSample d n i := by
  dsimp [directMomentSample, directMomentSampleRows]
  push_cast
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg i.val
  linarith

/-- The sample law is constructed from the proved real-shape Bartlett law;
no existence assumption is used in the interpolation. -/
def directMomentSampleLaw {d n : ℕ} (sigma : SymPosDef d) (i : Fin (n + 1)) :
    W_d d (directMomentSample d n i) sigma :=
  A4Research.recursiveBartlettScaledLaw d (directMomentSample d n i) sigma
    (directMomentSample_admissible d n i)

/-- The exact matching coefficient polynomial agrees with the original
matrix-Laplace moment polynomial. Gaussian sample identities and finite
interpolation discharge all comparison obligations in every degree. -/
theorem pairPartitionEntryShapePolynomial_eq_matching {d n : ℕ}
    (sigma : SymPosDef d) (M : PM n) (j : Fin (2 * n) → Fin d) :
    pairPartitionEntryShapePolynomial sigma.1 M j =
      matchingEntryMomentPolynomial sigma.1 M j := by
  apply pairPartitionEntryShapePolynomial_eq_matching_of_samples
    sigma.1 M j (directMomentSample d n) (directMomentSample_injective d n)
  intro i
  let W := directMomentSampleLaw sigma i
  rw [← W.integral_pairPartition_entries_eq_eval_shapePolynomial,
    eval_matchingEntryMomentPolynomial]
  have h := W.integral_pairEntryProduct_half_integer_real
    (k := directMomentSampleRows d n i) j M
  have hsample : 2 * directMomentSample d n i = (directMomentSampleRows d n i : ℝ) := by
    dsimp [directMomentSample]
    ring
  simpa only [hsample] using h

/-- The full direct entry-tensor moment formula, in every tensor degree,
for arbitrary real shape and arbitrary SPD scale carried by the exact law. -/
theorem W_d.direct_pairPartition_moment {d n : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (M : PM n) (j : Fin (2 * n) → Fin d) :
    (∫ w, ∏ i : M.pairReps, w.1 (j i.1) (j (M i.1)) ∂W.toMeasure) =
      (2 : ℝ) ^ (-(n : ℤ)) * ∑ N : PM n, (2 * beta) ^ matchingKappa M N *
        ∏ i : N.pairReps, sigma.1 (j i.1) (j (N i.1)) := by
  rw [W.integral_pairPartition_entries_eq_eval_shapePolynomial,
    pairPartitionEntryShapePolynomial_eq_matching, eval_matchingEntryMomentPolynomial]

end MatsumotoPaper
