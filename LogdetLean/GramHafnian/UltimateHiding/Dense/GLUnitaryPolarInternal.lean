import LogdetLean.GramHafnian.UltimateHiding.Dense.GLUnitaryGelfandAtoms
import Mathlib.Analysis.Matrix.PosDef

/-!
# Internal polar-decomposition lemma for the H2 Gelfand argument

This file proves the one finite-dimensional matrix fact used by the internal
Gelfand-trick proof: conjugate transpose preserves every `U(N)` double coset
in `GL_N(C)`.  The proof is the elementary spectral construction of the
positive square root of `Aᴴ A`.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open scoped ComplexConjugate
open scoped ComplexOrder

private theorem diagonal_sqrt_mul_self
    {N : ℕ} (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 < lambda i) :
    Matrix.diagonal (fun i ↦ (Real.sqrt (lambda i) : ℂ)) *
        Matrix.diagonal (fun i ↦ (Real.sqrt (lambda i) : ℂ)) =
      Matrix.diagonal (fun i ↦ (lambda i : ℂ)) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    norm_cast
    simpa only [pow_two] using Real.sq_sqrt (le_of_lt (hlambda i))
  · simp [Matrix.diagonal, hij]

private theorem diagonal_inv_sqrt_mul_sqrt
    {N : ℕ} (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 < lambda i) :
    Matrix.diagonal (fun i ↦ ((Real.sqrt (lambda i))⁻¹ : ℂ)) *
        Matrix.diagonal (fun i ↦ (Real.sqrt (lambda i) : ℂ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Real.sqrt_ne_zero'.mpr (hlambda i)]
  · simp [Matrix.one_apply, Matrix.diagonal, hij]

private theorem diagonal_sqrt_mul_inv_sqrt
    {N : ℕ} (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 < lambda i) :
    Matrix.diagonal (fun i ↦ (Real.sqrt (lambda i) : ℂ)) *
        Matrix.diagonal (fun i ↦ ((Real.sqrt (lambda i))⁻¹ : ℂ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Real.sqrt_ne_zero'.mpr (hlambda i)]
  · simp [Matrix.one_apply, Matrix.diagonal, hij]

/-- Conjugate transpose lies in the same `U(N)` double coset as an invertible
complex matrix.  The same unitary occurs on both sides, which is stronger than
the orbit statement needed below. -/
theorem exists_unitary_conjTranspose_eq_mul_self_mul
    {N : ℕ} (g : ComplexMatrixGL N) :
    ∃ W : Matrix.unitaryGroup (Fin N) ℂ,
      star (g : Matrix (Fin N) (Fin N) ℂ) =
        (W : Matrix (Fin N) (Fin N) ℂ) *
          (g : Matrix (Fin N) (Fin N) ℂ) *
          (W : Matrix (Fin N) (Fin N) ℂ) := by
  let A : Matrix (Fin N) (Fin N) ℂ := g
  have hAunit : IsUnit A := Units.isUnit g
  have hAinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_of_isUnit hAunit
  let H : Matrix (Fin N) (Fin N) ℂ := A.conjTranspose * A
  have hHpos : Matrix.PosDef H := by
    exact Matrix.PosDef.conjTranspose_mul_self A hAinj
  let hH : Matrix.IsHermitian H := hHpos.isHermitian
  let U : Matrix.unitaryGroup (Fin N) ℂ := hH.eigenvectorUnitary
  let lambda : Fin N → ℝ := hH.eigenvalues
  let S : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun i ↦ (Real.sqrt (lambda i) : ℂ))
  let T : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.diagonal (fun i ↦ ((Real.sqrt (lambda i))⁻¹ : ℂ))
  let P : Matrix (Fin N) (Fin N) ℂ :=
    (U : Matrix (Fin N) (Fin N) ℂ) * S *
      star (U : Matrix (Fin N) (Fin N) ℂ)
  let Pinv : Matrix (Fin N) (Fin N) ℂ :=
    (U : Matrix (Fin N) (Fin N) ℂ) * T *
      star (U : Matrix (Fin N) (Fin N) ℂ)
  have hlambda : ∀ i, 0 < lambda i := by
    intro i
    exact hHpos.eigenvalues_pos i
  have hspec : H =
      (U : Matrix (Fin N) (Fin N) ℂ) *
        Matrix.diagonal (fun i ↦ (lambda i : ℂ)) *
          star (U : Matrix (Fin N) (Fin N) ℂ) := by
    have hs : H =
        (U : Matrix (Fin N) (Fin N) ℂ) *
          Matrix.diagonal
            (((RCLike.ofReal : ℝ → ℂ)) ∘ lambda) *
            star (U : Matrix (Fin N) (Fin N) ℂ) := by
      simpa only [hH, U, lambda, Unitary.conjStarAlgAut_apply] using
        hH.spectral_theorem
    have hdiag :
        Matrix.diagonal (((RCLike.ofReal : ℝ → ℂ)) ∘ lambda) =
          Matrix.diagonal (fun i ↦ (lambda i : ℂ)) := by
      ext i j
      simp [Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
    simpa only [hdiag] using hs
  have hSS : S * S = Matrix.diagonal (fun i ↦ (lambda i : ℂ)) := by
    exact diagonal_sqrt_mul_self lambda hlambda
  have hTS : T * S = 1 := diagonal_inv_sqrt_mul_sqrt lambda hlambda
  have hST : S * T = 1 := diagonal_sqrt_mul_inv_sqrt lambda hlambda
  have hstarS : star S = S := by
    exact Matrix.isHermitian_diagonal_iff.mpr (by
      intro i
      rw [isSelfAdjoint_iff, RCLike.star_def, Complex.conj_ofReal])
  have hstarT : star T = T := by
    exact Matrix.isHermitian_diagonal_iff.mpr (by
      intro i
      rw [isSelfAdjoint_iff, RCLike.star_def, map_inv₀,
        Complex.conj_ofReal])
  have hUstarU :
      star (U : Matrix (Fin N) (Fin N) ℂ) *
          (U : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hUUstar :
      (U : Matrix (Fin N) (Fin N) ℂ) *
          star (U : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self U
  have hPP : P * P = H := by
    calc
      P * P = (U : Matrix (Fin N) (Fin N) ℂ) *
          S * (star (U : Matrix (Fin N) (Fin N) ℂ) *
            (U : Matrix (Fin N) (Fin N) ℂ)) * S *
              star (U : Matrix (Fin N) (Fin N) ℂ) := by
        simp only [P]
        noncomm_ring
      _ = (U : Matrix (Fin N) (Fin N) ℂ) * (S * S) *
          star (U : Matrix (Fin N) (Fin N) ℂ) := by
        rw [hUstarU]
        simp [Matrix.mul_assoc]
      _ = H := by rw [hSS, ← hspec]
  have hPinvP : Pinv * P = 1 := by
    calc
      Pinv * P = (U : Matrix (Fin N) (Fin N) ℂ) *
          T * (star (U : Matrix (Fin N) (Fin N) ℂ) *
            (U : Matrix (Fin N) (Fin N) ℂ)) * S *
              star (U : Matrix (Fin N) (Fin N) ℂ) := by
        simp only [Pinv, P]
        noncomm_ring
      _ = (U : Matrix (Fin N) (Fin N) ℂ) * (T * S) *
          star (U : Matrix (Fin N) (Fin N) ℂ) := by
        rw [hUstarU]
        simp [Matrix.mul_assoc]
      _ = 1 := by rw [hTS]; simpa using hUUstar
  have hPPinv : P * Pinv = 1 := by
    calc
      P * Pinv = (U : Matrix (Fin N) (Fin N) ℂ) *
          S * (star (U : Matrix (Fin N) (Fin N) ℂ) *
            (U : Matrix (Fin N) (Fin N) ℂ)) * T *
              star (U : Matrix (Fin N) (Fin N) ℂ) := by
        simp only [Pinv, P]
        noncomm_ring
      _ = (U : Matrix (Fin N) (Fin N) ℂ) * (S * T) *
          star (U : Matrix (Fin N) (Fin N) ℂ) := by
        rw [hUstarU]
        simp [Matrix.mul_assoc]
      _ = 1 := by rw [hST]; simpa using hUUstar
  have hstarP : star P = P := by
    simp only [P, star_mul, hstarS, star_star]
    simp [Matrix.mul_assoc]
  have hstarPinv : star Pinv = Pinv := by
    simp only [Pinv, star_mul, hstarT, star_star]
    simp [Matrix.mul_assoc]
  let Q : Matrix (Fin N) (Fin N) ℂ := A * Pinv
  have hAQ : A = Q * P := by
    simp only [Q]
    rw [Matrix.mul_assoc, hPinvP, Matrix.mul_one]
  have hQunit : star Q * Q = 1 := by
    calc
      star Q * Q = Pinv * (star A * A) * Pinv := by
        simp only [Q, star_mul, hstarPinv]
        noncomm_ring
      _ = Pinv * H * Pinv := by
        rw [Matrix.star_eq_conjTranspose]
      _ = Pinv * (P * P) * Pinv := by rw [hPP]
      _ = 1 := by
        rw [← Matrix.mul_assoc Pinv P P, hPinvP, Matrix.one_mul,
          hPPinv]
  let Qunit : Matrix.unitaryGroup (Fin N) ℂ :=
    ⟨Q, Matrix.mem_unitaryGroup_iff'.2 hQunit⟩
  refine ⟨star Qunit, ?_⟩
  change star A = star Q * A * star Q
  calc
    star A = P * star Q := by rw [hAQ, star_mul, hstarP]
    _ = (star Q * Q) * P * star Q := by rw [hQunit, Matrix.one_mul]
    _ = star Q * (Q * P) * star Q := by simp [Matrix.mul_assoc]
    _ = star Q * A * star Q := by rw [← hAQ]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
