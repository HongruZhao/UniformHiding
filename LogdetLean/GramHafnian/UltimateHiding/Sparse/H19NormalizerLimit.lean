import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangRawDensity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Elementary limit of Jiang's factorial normalizer

For fixed rectangular dimensions, the factorial quotient in Jiang's
finite-dimensional density is a finite descending product.  After the
`sqrt M` change of variables contributes `M ^ (-K*N)`, every linear factor
converges to one.  Thus the scaled normalizer converges to the standard
complex-Gaussian constant `pi ^ (-K*N)`.

No asymptotic formula for the factorial or gamma function is used here.
-/

open Filter
open scoped BigOperators Topology

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- A fixed natural subtraction is negligible compared with the ambient
natural number. -/
private theorem tendsto_natCast_sub_div_self (c : ℕ) :
    Tendsto (fun M : ℕ ↦ ((M - c : ℕ) : ℝ) / (M : ℝ)) atTop (nhds 1) := by
  have hlim : Tendsto (fun M : ℕ ↦ 1 - (c : ℝ) / (M : ℝ)) atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop c, eventually_ne_atTop 0] with M hMc hM0
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM0
  rw [Nat.cast_sub hMc]
  field_simp

/-- A fixed descending factorial, divided by the corresponding power of the
ambient dimension, converges to one. -/
private theorem tendsto_descFactorial_div_pow (a K : ℕ) :
    Tendsto
      (fun M : ℕ ↦
        ((Nat.descFactorial (M - a) K : ℕ) : ℝ) / (M : ℝ) ^ K)
      atTop (nhds 1) := by
  have hprod : Tendsto
      (fun M : ℕ ↦
        ∏ i ∈ Finset.range K,
          ((M - a - i : ℕ) : ℝ) / (M : ℝ))
      atTop (nhds 1) := by
    have hraw :=
      tendsto_finsetProd (Finset.range K) fun i hi ↦
        tendsto_natCast_sub_div_self (a + i)
    have hfun :
        (fun M : ℕ ↦
          ∏ i ∈ Finset.range K,
            ((M - a - i : ℕ) : ℝ) / (M : ℝ)) =
          (fun M : ℕ ↦
            ∏ i ∈ Finset.range K,
              ((M - (a + i) : ℕ) : ℝ) / (M : ℝ)) := by
      funext M
      simp only [Nat.sub_sub]
    rw [hfun]
    simpa using hraw
  apply hprod.congr'
  filter_upwards with M
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    Finset.prod_div_distrib]
  simp

/-- Over the stable range `K ≤ m`, a real factorial quotient is exactly a
descending factorial. -/
private theorem factorial_ratio_eq_descFactorial {m K : ℕ} (hK : K ≤ m) :
    ((Nat.factorial m : ℕ) : ℝ) /
        ((Nat.factorial (m - K) : ℕ) : ℝ) =
      ((Nat.descFactorial m K : ℕ) : ℝ) := by
  have hden : ((Nat.factorial (m - K) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m - K)
  rw [div_eq_iff hden]
  norm_cast
  simpa [Nat.mul_comm] using (Nat.factorial_mul_descFactorial hK).symm

/-- One factorial quotient in Jiang's normalizer contributes asymptotically
one after division by `M^K`. -/
private theorem tendsto_factorial_ratio_div_pow (a K : ℕ) :
    Tendsto
      (fun M : ℕ ↦
        (((Nat.factorial (M - a) : ℕ) : ℝ) /
            ((Nat.factorial (M - a - K) : ℕ) : ℝ)) /
          (M : ℝ) ^ K)
      atTop (nhds 1) := by
  apply (tendsto_descFactorial_div_pow a K).congr'
  filter_upwards [eventually_ge_atTop (a + K)] with M hM
  have hK : K ≤ M - a := by omega
  rw [factorial_ratio_eq_descFactorial hK]

/-- The raw Jiang normalizer, together with the `M^(-K*N)` Jacobian produced
by `sqrt M` scaling, converges to the standard `K × N` complex Gaussian
normalizer.

The positivity and orientation assumptions match Jiang's source theorem;
the elementary scalar limit itself in fact holds for all fixed `K,N`. -/
theorem tendsto_jiangUnscaledTallHaarCornerNormalizer_mul_inv_pow
    {K N : ℕ} (_hN : 0 < N) (_hK : 0 < K) (_hNK : N ≤ K) :
    Tendsto
      (fun M : ℕ ↦
        jiangUnscaledTallHaarCornerNormalizer M K N *
          ((M : ℝ) ^ (K * N))⁻¹)
      atTop (nhds ((Real.pi ^ (K * N))⁻¹)) := by
  have hprod : Tendsto
      (fun M : ℕ ↦
        ∏ j : Fin N,
          ((((Nat.factorial (M - (j.1 + 1)) : ℕ) : ℝ) /
              ((Nat.factorial (M - (j.1 + 1) - K) : ℕ) : ℝ)) /
            (M : ℝ) ^ K))
      atTop (nhds 1) := by
    simpa using
      (tendsto_finsetProd (Finset.univ : Finset (Fin N)) fun j _ ↦
        tendsto_factorial_ratio_div_pow (j.1 + 1) K)
  have hscaled :=
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ (Real.pi ^ (K * N))⁻¹) atTop
      (nhds ((Real.pi ^ (K * N))⁻¹))).mul hprod
  have hscaled' : Tendsto
      (fun M : ℕ ↦
        (Real.pi ^ (K * N))⁻¹ *
          ∏ j : Fin N,
            ((((Nat.factorial (M - (j.1 + 1)) : ℕ) : ℝ) /
                ((Nat.factorial (M - (j.1 + 1) - K) : ℕ) : ℝ)) /
              (M : ℝ) ^ K))
      atTop (nhds ((Real.pi ^ (K * N))⁻¹)) := by
    simpa using hscaled
  apply hscaled'.congr'
  filter_upwards with M
  rw [jiangUnscaledTallHaarCornerNormalizer,
    Finset.prod_div_distrib]
  simp [pow_mul, div_eq_mul_inv, mul_assoc]

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
