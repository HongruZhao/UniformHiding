import LogdetLean.GramHafnian.UltimateHiding.Sparse.ScalarKL
import Mathlib.Data.Fin.Rev

/-!
# Rectangular index identities for the finite sparse KL sum

This file verifies the cardinality, range, and first moment of the index
multiset appearing in the exact Haar block likelihood ratio.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

/-- Sum of the casts of `0, ..., n-1`. -/
theorem sum_fin_val_cast (n : ℕ) :
    ∑ i : Fin n, (i.1 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Nat.cast_add,
        Nat.cast_one, zero_add, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ih]
      ring

/-- The normalizer index `j + 1 + ell`, divided by the ambient dimension. -/
noncomputable def rectangularNormalizedIndex
    (p q M : ℕ) (i : Fin q × Fin p) : ℝ :=
  ((i.1.1 : ℝ) + 1 + (i.2.1 : ℝ)) / M

/-- Reflection of both rectangular coordinates.  This is the explicit
bijection matching the normalizer indices with the indices obtained by
differentiating the matrix beta integral. -/
def rectangularReflection (p q : ℕ) :
    (Fin q × Fin p) ≃ (Fin q × Fin p) :=
  Equiv.prodCongr Fin.revPerm Fin.revPerm

/-- The reflected index family appearing in the matrix beta derivative. -/
noncomputable def reflectedRectangularNormalizedIndex
    (p q M : ℕ) (i : Fin q × Fin p) : ℝ :=
  rectangularNormalizedIndex p q M (rectangularReflection p q i)

/-- The normalizer and beta derivative index multisets coincide. -/
theorem sum_reflected_rectangular_index
    (p q M : ℕ) (f : ℝ → ℝ) :
    ∑ i : Fin q × Fin p, f (reflectedRectangularNormalizedIndex p q M i) =
      ∑ i : Fin q × Fin p, f (rectangularNormalizedIndex p q M i) := by
  change
    ∑ i : Fin q × Fin p,
        (f ∘ rectangularNormalizedIndex p q M) (rectangularReflection p q i) =
      ∑ i : Fin q × Fin p, (f ∘ rectangularNormalizedIndex p q M) i
  exact (rectangularReflection p q).sum_comp
    (f ∘ rectangularNormalizedIndex p q M)

theorem rectangular_index_card (p q : ℕ) :
    (Fintype.card (Fin q × Fin p) : ℝ) = (p : ℝ) * q := by
  simp [Fintype.card_prod]
  ring

theorem rectangular_index_nonneg (p q M : ℕ) (i : Fin q × Fin p) :
    0 ≤ rectangularNormalizedIndex p q M i := by
  unfold rectangularNormalizedIndex
  positivity

theorem rectangular_index_lt_one
    {p q M : ℕ} (hp : 0 < p) (hq : 0 < q) (hs : p + q ≤ M)
    (i : Fin q × Fin p) :
    rectangularNormalizedIndex p q M i < 1 := by
  have hMnat : 0 < M := by omega
  have hnumNat : i.1.1 + 1 + i.2.1 < M := by
    have hj : i.1.1 < q := i.1.2
    have hl : i.2.1 < p := i.2.2
    omega
  have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
  rw [rectangularNormalizedIndex, div_lt_one hM]
  exact_mod_cast hnumNat

theorem sum_rectangular_index_numerator (p q : ℕ) :
    ∑ i : Fin q × Fin p, ((i.1.1 : ℝ) + 1 + (i.2.1 : ℝ)) =
      (p : ℝ) * q * ((p : ℝ) + q) / 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [sum_fin_val_cast q, sum_fin_val_cast p]
  ring

theorem sum_rectangular_normalized_index
    (p q M : ℕ) :
    ∑ i : Fin q × Fin p, rectangularNormalizedIndex p q M i =
      (p : ℝ) * q * (((p : ℝ) + q) / M) / 2 := by
  simp_rw [rectangularNormalizedIndex]
  rw [← Finset.sum_div]
  rw [sum_rectangular_index_numerator]
  ring

/-- Fully instantiated scalar KL estimate for a `p` by `q` Haar block. -/
theorem rectangular_scalar_kl_bound
    {p q M : ℕ} (hp : 0 < p) (hq : 0 < q) (hs : p + q ≤ M) :
    ∑ i : Fin q × Fin p,
        klSummand ((((p : ℝ) + q) / M))
          (rectangularNormalizedIndex p q M i)
      ≤ (p : ℝ) * q * ((p : ℝ) + q) ^ 2 / (2 * (M : ℝ) ^ 2) := by
  have hMnat : 0 < M := by omega
  have hM : (0 : ℝ) < M := by exact_mod_cast hMnat
  have hsReal : (p : ℝ) + q ≤ M := by exact_mod_cast hs
  apply finite_sparse_scalar_kl_bound (p : ℝ) q M
    (rectangularNormalizedIndex p q M)
  · exact rectangular_index_card p q
  · exact hM
  · exact hsReal
  · exact rectangular_index_lt_one hp hq hs
  · exact sum_rectangular_normalized_index p q M

end LogdetLean.GramHafnian.UltimateHiding.Sparse
