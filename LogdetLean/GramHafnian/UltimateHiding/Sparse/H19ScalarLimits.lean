import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Elementary scalar limits for the direct H19 argument

These lemmas isolate the one-dimensional exponential limit behind the
fixed-size Haar-corner density.  They contain no probability or random-matrix
input.
-/

open Filter

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- Removing a fixed natural number from the exponent does not change the
classical limit `(1 - x/n)^n -> exp(-x)`. -/
theorem tendsto_one_sub_div_pow_sub_exp (x : Real) (c : Nat) :
    Tendsto (fun n : Nat => (1 - x / (n : Real)) ^ (n - c)) atTop
      (nhds (Real.exp (-x))) := by
  have hmain : Tendsto (fun n : Nat => (1 - x / (n : Real)) ^ n) atTop
      (nhds (Real.exp (-x))) := by
    convert Real.tendsto_one_add_div_pow_exp (-x) using 1
    ext n
    congr 1
    ring
  have hbase : Tendsto (fun n : Nat => 1 - x / (n : Real)) atTop
      (nhds (1 : Real)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real)) atTop
          (nhds 1)).sub (tendsto_const_div_atTop_nhds_zero_nat x))
  have hfixed : Tendsto (fun n : Nat => (1 - x / (n : Real)) ^ c) atTop
      (nhds (1 : Real)) := by
    simpa using hbase.pow c
  have hinv : Tendsto
      (fun n : Nat => ((1 - x / (n : Real)) ^ c)⁻¹) atTop
      (nhds (1 : Real)) := by
    simpa using hfixed.inv₀ (by norm_num)
  have hprod := hmain.mul hinv
  have heq :
      (fun n : Nat => (1 - x / (n : Real)) ^ n *
        ((1 - x / (n : Real)) ^ c)⁻¹) =ᶠ[atTop]
      (fun n : Nat => (1 - x / (n : Real)) ^ (n - c)) := by
    filter_upwards [eventually_ge_atTop c,
      hbase.eventually_ne (by norm_num : (1 : Real) ≠ 0)] with n hcn hn0
    rw [pow_sub₀ _ hn0 hcn]
  simpa using hprod.congr' heq

/-- Finite-product form of the same exponential limit. -/
theorem tendsto_prod_one_sub_div_pow_sub_exp
    {iota : Type*} [Fintype iota] (x : iota -> Real) (c : Nat) :
    Tendsto
      (fun n : Nat => ∏ i : iota, (1 - x i / (n : Real)) ^ (n - c))
      atTop (nhds (Real.exp (-(∑ i : iota, x i)))) := by
  classical
  have hprod := tendsto_finsetProd Finset.univ
    (fun i _ => tendsto_one_sub_div_pow_sub_exp (x i) c)
  simpa [← Real.exp_sum, Finset.sum_neg_distrib] using hprod

/-- The determinant of an affine scalar transform of a Hermitian complex
matrix, written as the product over its real eigenvalues. -/
theorem det_one_sub_smul_hermitian_eq_prod_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) (r : Complex) :
    Matrix.det (1 - r • A) =
      ∏ i : n, (1 - r * (hA.eigenvalues i : Complex)) := by
  conv_lhs => rw [hA.spectral_theorem]
  let U : Matrix.unitaryGroup n Complex := hA.eigenvectorUnitary
  let D : Matrix n n Complex :=
    Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  change Matrix.det (1 - r • ((U : Matrix n n Complex) * D *
    star (U : Matrix n n Complex))) = _
  have haffine :
      1 - r • ((U : Matrix n n Complex) * D *
        star (U : Matrix n n Complex)) =
      (U : Matrix n n Complex) * (1 - r • D) *
        star (U : Matrix n n Complex) := by
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, mul_assoc, Unitary.coe_mul_star_self]
  rw [haffine, Matrix.det_mul, Matrix.det_mul]
  have hunitdet : Matrix.det (U : Matrix n n Complex) *
      Matrix.det (star (U : Matrix n n Complex)) = 1 := by
    rw [← Matrix.det_mul, show (U : Matrix n n Complex) *
      star (U : Matrix n n Complex) = 1 from U.prop.2, Matrix.det_one]
  rw [show Matrix.det (U : Matrix n n Complex) * Matrix.det (1 - r • D) *
      Matrix.det (star (U : Matrix n n Complex)) =
      Matrix.det (1 - r • D) *
        (Matrix.det (U : Matrix n n Complex) *
          Matrix.det (star (U : Matrix n n Complex))) by ring,
    hunitdet, mul_one]
  have hdiag : 1 - r • D = Matrix.diagonal
      (fun i : n => 1 - r * (hA.eigenvalues i : Complex)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Function.comp_def]
    · simp [D, Matrix.one_apply, hij, Function.comp_def]
  rw [hdiag, Matrix.det_diagonal]

/-- Tailored determinant-power limit for the fixed-size Haar-corner density.
For a fixed Hermitian complex matrix `A`, replacing the scalar exponential
base by `det (I - A/n)` gives the exponential of minus the real trace. -/
theorem tendsto_hermitian_det_one_sub_div_pow_sub_exp
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : Matrix iota iota Complex) (hA : A.IsHermitian) (c : Nat) :
    Tendsto
      (fun n : Nat ↦
        (Matrix.det (1 - ((n : Complex)⁻¹) • A)).re ^ (n - c))
      atTop (nhds (Real.exp (-(Matrix.trace A).re))) := by
  have hprod :=
    tendsto_prod_one_sub_div_pow_sub_exp hA.eigenvalues c
  have htrace : (Matrix.trace A).re = ∑ i : iota, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  rw [htrace]
  apply hprod.congr'
  filter_upwards with n
  rw [det_one_sub_smul_hermitian_eq_prod_eigenvalues A hA
    ((n : Complex)⁻¹)]
  have hfactor (i : iota) :
      1 - ((n : Complex)⁻¹) * (hA.eigenvalues i : Complex) =
        ((1 - hA.eigenvalues i / (n : Real) : Real) : Complex) := by
    push_cast
    rw [div_eq_mul_inv, mul_comm]
  simp_rw [hfactor]
  rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_pow]

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
